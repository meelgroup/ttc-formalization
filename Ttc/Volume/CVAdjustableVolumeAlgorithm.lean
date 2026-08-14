/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVConcreteRunwiseAdjustable
import Ttc.Volume.CVGuardedVolumeAlgorithm

/-!
# Public adjustable-radius Cousins--Vempala volume algorithm

The radius is selected noncomputably, per input, from the adjustable Gaussian tail theorem.
Invalid inputs use radius `2` and are totalized in the usual way.  On every admissible input
the selected radius fits the one-run sampler budget, so no fixed-radius guard or Monte Carlo
fallback is needed.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive
open scoped ENNReal

variable {n : Nat}

/-- A total, input-indexed radius.  On the valid branch it is a witness of the adjustable
tail theorem; the fallback is irrelevant to public correctness. -/
noncomputable def adjustablePublicQ (a : VolumeInput n) : Real := by
  classical
  exact if h : 1 <= n ∧ 0 < runwiseSamplerCalls (guardedM a) (guardedK a) then
    Classical.choose (exists_adaptiveTerminalRadiusQ h.1 h.2
      (by norm_num : (0 : Real) < 1 / 20))
  else 2

theorem adjustablePublicQ_spec (a : VolumeInput n) (hn : 1 <= n)
    (hA : 0 < runwiseSamplerCalls (guardedM a) (guardedK a)) :
    2 <= adjustablePublicQ a ∧
      AdjustableRadiusTailFits n (runwiseSamplerCalls (guardedM a) (guardedK a))
        (1 / 20) (adjustablePublicQ a) := by
  classical
  unfold adjustablePublicQ
  rw [dif_pos ⟨hn, hA⟩]
  exact Classical.choose_spec (exists_adaptiveTerminalRadiusQ hn hA
    (by norm_num : (0 : Real) < 1 / 20))

abbrev AdjustablePublicRunCoin (n : Nat) (a : VolumeInput n) :=
  Fin (guardedR a) -> Fin (guardedM a + 1) -> Fin (guardedK a) -> Space n

noncomputable def adjustablePublicPhaseLaw (a : VolumeInput n) :
    Fin (guardedM a + 1) -> Fin (guardedK a) -> Measure (Space n) :=
  fun i _ => adaptiveTerminalWarmLawQ (adjustablePublicQ a)
    (guardedC a ^ 2 * n) (guardedS0 a) endpointRho (guardedMix a) a.1 i

noncomputable def adjustablePublicRawRunLaw (a : VolumeInput n) :
    Measure (AdjustablePublicRunCoin n a) :=
  runMeasure (packedPhaseLaw
    (Ttc.CVRunwise.iidRunFamily (r := guardedR a) (adjustablePublicPhaseLaw a)))

/-- Total probability law, including outside the correctness contract. -/
noncomputable def adjustablePublicRunLaw (a : VolumeInput n) :
    Measure (AdjustablePublicRunCoin n a) := by
  classical
  exact if IsProbabilityMeasure (adjustablePublicRawRunLaw a) then
    adjustablePublicRawRunLaw a else Measure.dirac (fun _ _ _ => 0)

instance isProbabilityMeasure_adjustablePublicRunLaw (a : VolumeInput n) :
    IsProbabilityMeasure (adjustablePublicRunLaw a) := by
  classical
  unfold adjustablePublicRunLaw
  split_ifs with h
  · exact h
  · infer_instance

theorem adjustablePublicRunLaw_eq_raw (a : VolumeInput n)
    (h : IsProbabilityMeasure (adjustablePublicRawRunLaw a)) :
    adjustablePublicRunLaw a = adjustablePublicRawRunLaw a := by
  classical
  simp [adjustablePublicRunLaw, h]

noncomputable def adjustablePublicScore (a : VolumeInput n) :
    Fin (guardedM a + 1) -> Fin (guardedK a) -> Space n -> Real :=
  fun i _ => phaseScore (guardedM a + 1)
    (adaptiveSigmaSq (guardedC a ^ 2 * n) (guardedS0 a)) a.1 i

noncomputable def adjustablePublicRawEstimator (a : VolumeInput n)
    (omega : AdjustablePublicRunCoin n a) : Real :=
  medianSel fun t =>
    (2 * Real.pi * guardedS0 a) ^ ((n : Real) / 2) *
      ∏ i, oneRunPhaseAvg (guardedK a) (adjustablePublicScore a) i (omega t)

noncomputable def adjustablePublicEstimator (a : VolumeInput n)
    (omega : AdjustablePublicRunCoin n a) : Real := by
  classical
  exact if MeasurableSet a.1 then adjustablePublicRawEstimator a omega else 0

theorem measurable_adjustablePublicRawEstimator (a : VolumeInput n)
    (hKm : MeasurableSet a.1) : Measurable (adjustablePublicRawEstimator a) := by
  unfold adjustablePublicRawEstimator
  apply measurable_medianSel
  intro t
  apply measurable_const.mul
  apply Finset.measurable_fun_prod
  intro i hi
  exact (measurable_oneRunPhaseAvg
    (fun i l => measurable_phaseScore hKm i) i).comp (measurable_pi_apply t)

theorem measurable_adjustablePublicEstimator (a : VolumeInput n) :
    Measurable (adjustablePublicEstimator a) := by
  classical
  by_cases hKm : MeasurableSet a.1
  · unfold adjustablePublicEstimator
    simpa only [if_pos hKm] using measurable_adjustablePublicRawEstimator a hKm
  · unfold adjustablePublicEstimator
    simpa only [if_neg hKm] using
      (measurable_const : Measurable (fun _ : AdjustablePublicRunCoin n a => (0 : Real)))

theorem adjustablePublicEstimator_eq_raw (a : VolumeInput n) (hKm : MeasurableSet a.1) :
    adjustablePublicEstimator a = adjustablePublicRawEstimator a := by
  classical
  unfold adjustablePublicEstimator
  funext omega
  simp only [if_pos hKm]

/-- On admissible closed inputs, the raw q-parametric run law is a probability measure. -/
theorem isProbabilityMeasure_adjustablePublicRawRunLaw
    (hn : 21 <= n) (a : VolumeInput n)
    (heps : 0 < a.2.1)
    (hKc : Convex Real a.1) (hKcl : IsClosed a.1)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ a.1) :
    IsProbabilityMeasure (adjustablePublicRawRunLaw a) := by
  have hn2 : 2 <= n := by omega
  have hn1 : 1 <= n := by omega
  have hacc : 0 < guardedAccuracy a := by
    unfold guardedAccuracy
    positivity
  have heta : 0 < guardedEta a := by unfold guardedEta; positivity
  have hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos hn1 heta
  have hN : 0 < guardedC a ^ 2 * (n : Real) := by
    have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
    positivity
  have hk : 0 < guardedK a := by
    exact concreteEstimatorSamples_pos (guardedJ a) (guardedAccuracy a / 4)
  have hA : 0 < runwiseSamplerCalls (guardedM a) (guardedK a) :=
    runwiseSamplerCalls_pos (guardedM a) hk
  have hq := (adjustablePublicQ_spec a hn1 hA).1
  have hepsMix0 : 0 < guardedMix a := runwiseChosenMixError_pos (guardedM a) hk
  have hepsMix32 : guardedMix a <= 1 / 32 :=
    runwiseChosenMixError_le_one_div_32 (guardedM a) hk
  have hbelow : forall j, j + 1 < guardedM a + 1 ->
      adaptiveChunkStart (guardedC a ^ 2 * n) (guardedS0 a)
        (adaptivePhaseChunk (guardedC a ^ 2 * n) (guardedS0 a) j) <=
          guardedC a ^ 2 * n := by
    intro j hj
    have hjm : j < guardedM a := by omega
    have hchunk : adaptivePhaseChunk (guardedC a ^ 2 * n) (guardedS0 a) j < guardedJ a :=
      adaptivePhaseChunk_lt_of_lt_offset hN hs0 hjm
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs0 hchunk).le
  have hcold : 4 * (n : Real) * guardedS0 a <= endpointRho ^ 2 :=
    polynomialEndpointSigmaSq_coldBall hn1 heta (by
      have hacc1 : guardedAccuracy a <= 1 := min_le_right _ _
      unfold guardedEta
      linarith)
  letI hphaseProb : forall i l,
      IsProbabilityMeasure (adjustablePublicPhaseLaw a i l) := fun i l =>
    isProbabilityMeasure_adaptiveTerminalWarmLawQ hn hq hN hs0 hKcl.measurableSet hKc
      hclosedBall endpointRho_pos (endpointRho_lt_shrink hn2) hcold hbelow
      hepsMix0 hepsMix32 i
  letI : forall t i l, IsProbabilityMeasure
      (Ttc.CVRunwise.iidRunFamily (r := guardedR a)
        (adjustablePublicPhaseLaw a) t i l) :=
    fun t i l => hphaseProb i l
  unfold adjustablePublicRawRunLaw
  infer_instance

/-- Fixed-q form of the tail-unconditional concrete capstone, used by the public chooser. -/
theorem concrete_adaptive_runwise_volume_accuracy_q
    (hn : 21 <= n) {q : Real} (hq : 2 <= q)
    {K : Set (Space n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C epsilon p : Real} (hC : 0 < C) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon <= 1) (hp : 0 < p) (hp1 : p < 1)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (hfit : let eta := epsilon / 4
      let s0 := polynomialEndpointSigmaSq n eta
      let J := adaptiveTerminalChunk (C ^ 2 * n) s0
      let m := adaptiveChunkOffset (C ^ 2 * n) s0 J
      let k := concreteEstimatorSamples J (epsilon / 4)
      AdjustableRadiusTailFits n (runwiseSamplerCalls m k) (1 / 20) q) :
    let eta := epsilon / 4
    let epsEst := epsilon / 4
    let s0 := polynomialEndpointSigmaSq n eta
    let J := adaptiveTerminalChunk (C ^ 2 * n) s0
    let m := adaptiveChunkOffset (C ^ 2 * n) s0 J
    let k := concreteEstimatorSamples J epsEst
    let r := concreteRunwiseReps p
    let epsMix := runwiseChosenMixError m k
    let nu : Fin (m + 1) -> Fin k -> Measure (Space n) := fun i _ =>
      adaptiveTerminalWarmLawQ q (C ^ 2 * n) s0 endpointRho epsMix K i
    let g : Fin (m + 1) -> Fin k -> Space n -> Real := fun i _ =>
      phaseScore (m + 1) (adaptiveSigmaSq (C ^ 2 * n) s0) K i
    1 - p <=
      (runMeasure (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))).real
        {omega | medianSel (fun t =>
          (2 * Real.pi * s0) ^ ((n : Real) / 2) *
            ∏ i, oneRunPhaseAvg k g i (omega t)) ∈
          Ttc.relErr epsilon (volume K).toReal} := by
  dsimp only at hfit ⊢
  let eta : Real := epsilon / 4
  let epsEst : Real := epsilon / 4
  let s0 : Real := polynomialEndpointSigmaSq n eta
  let J : Nat := adaptiveTerminalChunk (C ^ 2 * n) s0
  let m : Nat := adaptiveChunkOffset (C ^ 2 * n) s0 J
  let k : Nat := concreteEstimatorSamples J epsEst
  let r : Nat := concreteRunwiseReps p
  let epsMix : Real := runwiseChosenMixError m k
  let nu : Fin (m + 1) -> Fin k -> Measure (Space n) := fun i _ =>
    adaptiveTerminalWarmLawQ q (C ^ 2 * n) s0 endpointRho epsMix K i
  let g : Fin (m + 1) -> Fin k -> Space n -> Real := fun i _ =>
    phaseScore (m + 1) (adaptiveSigmaSq (C ^ 2 * n) s0) K i
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta < 1 := by dsimp [eta]; linarith
  have hepsEst : 0 < epsEst := by dsimp [epsEst]; positivity
  have hparams := concreteEstimator_parameter_bundle J hepsEst
  have hk : 0 < k := by simpa only [k] using hparams.1
  have hkappa : 0 <= concreteEstimatorKappa epsEst := hparams.2.1
  have hk42 : 42 <= (k : Real) := by simpa only [k] using hparams.2.2.1
  have hsamples : 7 * (J : Real) <= (k : Real) * concreteEstimatorKappa epsEst := by
    simpa only [k] using hparams.2.2.2.1
  have hbudget := hparams.2.2.2.2
  have hr : 0 < r := by simpa only [r] using concreteRunwiseReps_pos p
  have hrp : Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2) <= (r : Real) := by
    simpa only [r] using concreteRunwiseReps_spec p
  have hepsMix0 : 0 < epsMix := by
    simpa only [epsMix] using runwiseChosenMixError_pos m hk
  have hepsMix32 : epsMix <= 1 / 32 := by
    simpa only [epsMix] using runwiseChosenMixError_le_one_div_32 m hk
  have hsampler : (((m + 1) * k : Nat) : Real) *
      (64 * ENNReal.ofReal epsMix +
        ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)).toReal <= 1 / 10 := by
    apply runwise_sampler_adjustable_toReal_budget n m hk
    simpa only [eta, epsEst, s0, J, m, k] using hfit
  have hn2 : 2 <= n := by omega
  have hn1 : 1 <= n := by omega
  have hN : 0 < C ^ 2 * (n : Real) := by positivity
  have hs0 : 0 < s0 := by
    dsimp [s0]
    exact polynomialEndpointSigmaSq_pos hn1 heta
  have hbelow : forall j, j + 1 < m + 1 ->
      adaptiveChunkStart (C ^ 2 * n) s0
        (adaptivePhaseChunk (C ^ 2 * n) s0 j) <= C ^ 2 * n := by
    intro j hj
    have hjm : j < m := by omega
    have hchunk : adaptivePhaseChunk (C ^ 2 * n) s0 j < J :=
      adaptivePhaseChunk_lt_of_lt_offset hN hs0 hjm
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs0 hchunk).le
  have hcold : 4 * (n : Real) * s0 <= endpointRho ^ 2 := by
    dsimp [s0]
    exact polynomialEndpointSigmaSq_coldBall hn1 heta heta1.le
  letI hnuProb : forall i l, IsProbabilityMeasure (nu i l) := fun i l =>
    isProbabilityMeasure_adaptiveTerminalWarmLawQ hn hq hN hs0 hKcl.measurableSet hKc
      hclosedBall endpointRho_pos (endpointRho_lt_shrink hn2) hcold hbelow
      hepsMix0 hepsMix32 i
  letI hiidProb : forall t i l,
      IsProbabilityMeasure (Ttc.CVRunwise.iidRunFamily (r := r) nu t i l) :=
    fun t i l => hnuProb i l
  letI : IsProbabilityMeasure
      (runMeasure (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))) := by
    infer_instance
  have hmain := median_accuracy_concrete_adaptive_runwise_polynomial_q
    (n := n) (k := k) (r := r) hn hk hr hq hKc hKcl hKb hvol hclosedBall hfin
    hC hkappa hepsEst heta heta1 hk42 hsamples hKR hbudget hp hrp
    hepsMix0 hepsMix32 hsampler
  have hmain' : 1 - p <=
      (runMeasure (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))).real
        {omega | medianSel (fun t =>
          (2 * Real.pi * s0) ^ ((n : Real) / 2) *
            ∏ i, oneRunPhaseAvg k g i (omega t)) ∈
          Ttc.relErr ((epsEst + eta) / (1 - eta)) (volume K).toReal} := by
    simpa only [terminalTarget, terminalPhaseCount, terminalChunk, terminalSigmaSq,
      s0, J, m, nu, g] using hmain
  have herr : (epsEst + eta) / (1 - eta) <= epsilon := by
    apply terminal_relative_error_split hepsilon.le hepsilon1 hepsEst.le
    · dsimp [epsEst]
      linarith
    · exact heta.le
    · dsimp [eta]
      linarith
  refine hmain'.trans (measureReal_mono ?_)
  intro omega homega
  exact Ttc.CV.relErr_mono herr (volume K).toReal_nonneg homega

/-! ## Unconditional public constructor -/

/-- Public adjustable-radius CV volume algorithm.  Correctness has no tail guard and uses no
fallback algorithm.  This declaration intentionally makes no runtime claim. -/
noncomputable def adjustableConcreteVolumeAlgorithm (n : Nat) (hn : 21 <= n) :
    Ttc.VolumeAlgorithm n :=
  Ttc.VolumeAlgorithm.ofClosedInputLaws n (by omega)
    (AdjustablePublicRunCoin n) adjustablePublicRunLaw adjustablePublicEstimator
    measurable_adjustablePublicEstimator
    (fun K eps p heps hp hp1 hKc hKcl hKb hvol hclosedBall hfin => by
      let a : VolumeInput n := (K, eps, p)
      have hrawProb : IsProbabilityMeasure (adjustablePublicRawRunLaw a) :=
        isProbabilityMeasure_adjustablePublicRawRunLaw hn a heps hKc hKcl hclosedBall
      have hlaw : adjustablePublicRunLaw a = adjustablePublicRawRunLaw a :=
        adjustablePublicRunLaw_eq_raw a hrawProb
      have hest : adjustablePublicEstimator a = adjustablePublicRawEstimator a :=
        adjustablePublicEstimator_eq_raw a hKcl.measurableSet
      have hgeom := closure_concrete_geometry (n := n) (by omega) hKc
        (ball_subset_closedBall.trans hclosedBall) hfin
      have hKR : K ⊆ closedBall 0 (Ttc.CV.cvRadius K * Real.sqrt n) := by
        simpa [hKcl.closure_eq] using hgeom.2.2.2.2.2.2.2
      have hn1 : 1 <= n := by omega
      have hacc : 0 < guardedAccuracy a := by
        unfold guardedAccuracy
        positivity
      have hacc1 : guardedAccuracy a <= 1 := min_le_right _ _
      have hk : 0 < guardedK a :=
        concreteEstimatorSamples_pos (guardedJ a) (guardedAccuracy a / 4)
      have hA : 0 < runwiseSamplerCalls (guardedM a) (guardedK a) :=
        runwiseSamplerCalls_pos (guardedM a) hk
      have hqspec := adjustablePublicQ_spec a hn1 hA
      have hmain := concrete_adaptive_runwise_volume_accuracy_q hn hqspec.1 hKc hKcl hKb
        hvol hclosedBall hfin (Ttc.CV.cvRadius_pos K) hacc hacc1 hp hp1 hKR
        (by
          simpa only [a, guardedAccuracy, guardedEta, guardedC, guardedS0, guardedJ,
            guardedM, guardedK] using hqspec.2)
      have hmain' : 1 - p <= (adjustablePublicRawRunLaw a).real
          {omega | adjustablePublicRawEstimator a omega ∈
            Ttc.relErr (guardedAccuracy a) (volume K).toReal} := by
        convert hmain using 1 <;>
          simp only [a, guardedAccuracy, guardedEta, guardedC, guardedS0, guardedJ,
            guardedM, guardedK, guardedR, adjustablePublicRawRunLaw,
            adjustablePublicRawEstimator] <;> rfl
      letI : IsProbabilityMeasure (adjustablePublicRawRunLaw a) := hrawProb
      have hmono : (adjustablePublicRawRunLaw a).real
          {omega | adjustablePublicRawEstimator a omega ∈
            Ttc.relErr (guardedAccuracy a) (volume K).toReal} <=
          (adjustablePublicRawRunLaw a).real
          {omega | adjustablePublicRawEstimator a omega ∈
            Ttc.relErr eps (volume K).toReal} := by
        apply measureReal_mono
        · intro omega homega
          exact Ttc.CV.relErr_mono (min_le_left _ _) (volume K).toReal_nonneg homega
        · exact measure_ne_top _ _
      rw [hlaw, hest]
      exact hmain'.trans hmono)

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.adjustablePublicQ_spec
#print axioms Ttc.CVAdaptive.measurable_adjustablePublicEstimator
#print axioms Ttc.CVAdaptive.isProbabilityMeasure_adjustablePublicRawRunLaw
#print axioms Ttc.CVAdaptive.concrete_adaptive_runwise_volume_accuracy_q
#print axioms Ttc.CVAdaptive.adjustableConcreteVolumeAlgorithm

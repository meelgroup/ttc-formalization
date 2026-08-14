/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVAdjustableVolumeAlgorithm

/-!
# An explicit polynomial adjustable radius

For `A >= 0`, `b > 0`, set `q = A / b + 3`.  The elementary estimate

`q * exp (-(q^2-1)/2) <= 1/q`

for `q >= 3` implies that this radius fits `A` calls and tail budget `b` in every positive
dimension.  At the public budget `b=1/20`, this is `q=20A+3`.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive
open scoped ENNReal

variable {n : Nat}

noncomputable def explicitAdaptiveRadiusQ (A b : Real) : Real := A / b + 3

private theorem gaussianRadiusBase_le_inv {q : Real} (hq : 3 <= q) :
    q * Real.exp (-(q ^ 2 - 1) / 2) <= 1 / q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hlog := Real.log_le_sub_one_of_pos hq0
  have hprod : 0 <= (q - 1) * (q - 3) := mul_nonneg (by linarith) (by linarith)
  have hexpArg : 2 * Real.log q <= (q ^ 2 - 1) / 2 := by
    nlinarith
  have hsqexp : q ^ 2 <= Real.exp ((q ^ 2 - 1) / 2) := by
    calc
      q ^ 2 = Real.exp (2 * Real.log q) := by
        rw [show 2 * Real.log q = Real.log q + Real.log q by ring,
          Real.exp_add, Real.exp_log hq0]
        ring
      _ <= Real.exp ((q ^ 2 - 1) / 2) := Real.exp_le_exp.mpr hexpArg
  rw [le_div_iff₀ hq0]
  calc
    q * Real.exp (-(q ^ 2 - 1) / 2) * q =
        q ^ 2 * Real.exp (-(q ^ 2 - 1) / 2) := by ring
    _ <= Real.exp ((q ^ 2 - 1) / 2) * Real.exp (-(q ^ 2 - 1) / 2) :=
      mul_le_mul_of_nonneg_right hsqexp (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; ring_nf; simp

/-- `A/b+3` is an explicit tail-fitting radius. -/
theorem explicitAdaptiveRadiusQ_tailFits (hn : 1 <= n) {A b : Real}
    (hA : 0 <= A) (hb : 0 < b) :
    AdjustableRadiusTailFits n A b (explicitAdaptiveRadiusQ A b) := by
  let q := explicitAdaptiveRadiusQ A b
  have hdiv0 : 0 <= A / b := div_nonneg hA hb.le
  have hq3 : 3 <= q := by dsimp [q, explicitAdaptiveRadiusQ]; linarith
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) hq3
  have hbase0 : 0 <= q * Real.exp (-(q ^ 2 - 1) / 2) := by positivity
  have hinv0 : 0 <= 1 / q := by positivity
  have hinv1 : 1 / q <= 1 := by
    rw [div_le_one hq0]
    linarith
  have hbase := gaussianRadiusBase_le_inv hq3
  have hpow : (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n <= (1 / q) ^ n := by
    gcongr
  have hpown : (1 / q) ^ n <= 1 / q := by
    cases n with
    | zero => omega
    | succ m =>
      rw [pow_succ]
      exact mul_le_of_le_one_left hinv0 (pow_le_one₀ hinv0 hinv1)
  have hAq : A / q <= b := by
    rw [div_le_iff₀ hq0]
    have hAb : A <= (A / b) * b := by
      rw [div_mul_cancel₀ A hb.ne']
    dsimp [q, explicitAdaptiveRadiusQ]
    nlinarith
  constructor
  · exact hq1
  · calc
      A * (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n
          <= A * (1 / q) := mul_le_mul_of_nonneg_left (hpow.trans hpown) hA
      _ = A / q := by ring
      _ <= b := hAq

/-- The public `1/20` allocation gives the visibly linear radius `20*A+3`. -/
theorem explicitAdaptiveRadiusQ_one_div_twenty (A : Real) :
    explicitAdaptiveRadiusQ A (1 / 20) = 20 * A + 3 := by
  unfold explicitAdaptiveRadiusQ
  ring

/-- Consequently the conductance/mixing radius factor is an explicit quadratic polynomial. -/
theorem explicitAdaptiveRadiusQ_one_div_twenty_sq (A : Real) :
    explicitAdaptiveRadiusQ A (1 / 20) ^ 2 = (20 * A + 3) ^ 2 := by
  rw [explicitAdaptiveRadiusQ_one_div_twenty]

theorem max_eight_two_explicitAdaptiveRadiusQ_le (A : Real) (hA : 0 <= A) :
    max 8 (2 * explicitAdaptiveRadiusQ A (1 / 20)) <= 40 * A + 14 := by
  rw [explicitAdaptiveRadiusQ_one_div_twenty]
  apply max_le
  · linarith
  · linarith

/-- The squared radius factor appearing in the adjustable mixing deadline is polynomial. -/
theorem max_eight_two_explicitAdaptiveRadiusQ_sq_le (A : Real) (hA : 0 <= A) :
    max 8 (2 * explicitAdaptiveRadiusQ A (1 / 20)) ^ 2 <= (40 * A + 14) ^ 2 := by
  have hfac := max_eight_two_explicitAdaptiveRadiusQ_le A hA
  have hleft : 0 <= max 8 (2 * explicitAdaptiveRadiusQ A (1 / 20)) :=
    le_trans (by norm_num : (0 : Real) <= 8) (le_max_left _ _)
  have hright : 0 <= 40 * A + 14 := by positivity
  nlinarith

/-! ## Explicit public law -/

noncomputable def explicitPublicQ (a : VolumeInput n) : Real :=
  explicitAdaptiveRadiusQ (runwiseSamplerCalls (guardedM a) (guardedK a)) (1 / 20)

theorem explicitPublicQ_eq (a : VolumeInput n) :
    explicitPublicQ a = 20 * runwiseSamplerCalls (guardedM a) (guardedK a) + 3 := by
  exact explicitAdaptiveRadiusQ_one_div_twenty _

theorem explicitPublicQ_spec (a : VolumeInput n) (hn : 1 <= n) :
    2 <= explicitPublicQ a ∧
      AdjustableRadiusTailFits n (runwiseSamplerCalls (guardedM a) (guardedK a))
        (1 / 20) (explicitPublicQ a) := by
  have hA : 0 <= runwiseSamplerCalls (guardedM a) (guardedK a) := by
    unfold runwiseSamplerCalls
    positivity
  constructor
  · rw [explicitPublicQ_eq]
    linarith
  · exact explicitAdaptiveRadiusQ_tailFits hn hA (by norm_num)

abbrev ExplicitPublicRunCoin (n : Nat) (a : VolumeInput n) :=
  AdjustablePublicRunCoin n a

noncomputable def explicitPublicPhaseLaw (a : VolumeInput n) :
    Fin (guardedM a + 1) -> Fin (guardedK a) -> Measure (Space n) :=
  fun i _ => adaptiveTerminalWarmLawQ (explicitPublicQ a)
    (guardedC a ^ 2 * n) (guardedS0 a) endpointRho (guardedMix a) a.1 i

noncomputable def explicitPublicRawRunLaw (a : VolumeInput n) :
    Measure (ExplicitPublicRunCoin n a) :=
  runMeasure (packedPhaseLaw
    (Ttc.CVRunwise.iidRunFamily (r := guardedR a) (explicitPublicPhaseLaw a)))

noncomputable def explicitPublicRunLaw (a : VolumeInput n) :
    Measure (ExplicitPublicRunCoin n a) := by
  classical
  exact if IsProbabilityMeasure (explicitPublicRawRunLaw a) then
    explicitPublicRawRunLaw a else Measure.dirac (fun _ _ _ => 0)

instance isProbabilityMeasure_explicitPublicRunLaw (a : VolumeInput n) :
    IsProbabilityMeasure (explicitPublicRunLaw a) := by
  classical
  unfold explicitPublicRunLaw
  split_ifs with h
  · exact h
  · infer_instance

theorem explicitPublicRunLaw_eq_raw (a : VolumeInput n)
    (h : IsProbabilityMeasure (explicitPublicRawRunLaw a)) :
    explicitPublicRunLaw a = explicitPublicRawRunLaw a := by
  classical
  simp [explicitPublicRunLaw, h]

noncomputable def explicitPublicEstimator (a : VolumeInput n) :
    ExplicitPublicRunCoin n a -> Real := adjustablePublicEstimator a

theorem measurable_explicitPublicEstimator (a : VolumeInput n) :
    Measurable (explicitPublicEstimator a) := measurable_adjustablePublicEstimator a

theorem explicitPublicEstimator_eq_raw (a : VolumeInput n) (hKm : MeasurableSet a.1) :
    explicitPublicEstimator a = adjustablePublicRawEstimator a :=
  adjustablePublicEstimator_eq_raw a hKm

theorem isProbabilityMeasure_explicitPublicRawRunLaw
    (hn : 21 <= n) (a : VolumeInput n)
    (heps : 0 < a.2.1)
    (hKc : Convex Real a.1) (hKcl : IsClosed a.1)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ a.1) :
    IsProbabilityMeasure (explicitPublicRawRunLaw a) := by
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
  have hk : 0 < guardedK a :=
    concreteEstimatorSamples_pos (guardedJ a) (guardedAccuracy a / 4)
  have hq := (explicitPublicQ_spec a hn1).1
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
      IsProbabilityMeasure (explicitPublicPhaseLaw a i l) := fun i l =>
    isProbabilityMeasure_adaptiveTerminalWarmLawQ hn hq hN hs0 hKcl.measurableSet hKc
      hclosedBall endpointRho_pos (endpointRho_lt_shrink hn2) hcold hbelow
      hepsMix0 hepsMix32 i
  letI : forall t i l, IsProbabilityMeasure
      (Ttc.CVRunwise.iidRunFamily (r := guardedR a) (explicitPublicPhaseLaw a) t i l) :=
    fun t i l => hphaseProb i l
  unfold explicitPublicRawRunLaw
  infer_instance

/-- Unconditional public CV volume algorithm with the explicit radius `q=20*A+3`.

This replaces the opaque choice-based radius.  No runtime claim is bundled into
`VolumeAlgorithm`; the preceding identities expose the quadratic q dependence needed by a
separate complexity certificate.
-/
noncomputable def explicitAdjustableConcreteVolumeAlgorithm (n : Nat) (hn : 21 <= n) :
    Ttc.VolumeAlgorithm n :=
  Ttc.VolumeAlgorithm.ofClosedInputLaws n (by omega)
    (ExplicitPublicRunCoin n) explicitPublicRunLaw explicitPublicEstimator
    measurable_explicitPublicEstimator
    (fun K eps p heps hp hp1 hKc hKcl hKb hvol hclosedBall hfin => by
      let a : VolumeInput n := (K, eps, p)
      have hrawProb : IsProbabilityMeasure (explicitPublicRawRunLaw a) :=
        isProbabilityMeasure_explicitPublicRawRunLaw hn a heps hKc hKcl hclosedBall
      have hlaw : explicitPublicRunLaw a = explicitPublicRawRunLaw a :=
        explicitPublicRunLaw_eq_raw a hrawProb
      have hest : explicitPublicEstimator a = adjustablePublicRawEstimator a :=
        explicitPublicEstimator_eq_raw a hKcl.measurableSet
      have hgeom := closure_concrete_geometry (n := n) (by omega) hKc
        (ball_subset_closedBall.trans hclosedBall) hfin
      have hKR : K ⊆ closedBall 0 (Ttc.CV.cvRadius K * Real.sqrt n) := by
        simpa [hKcl.closure_eq] using hgeom.2.2.2.2.2.2.2
      have hn1 : 1 <= n := by omega
      have hacc : 0 < guardedAccuracy a := by
        unfold guardedAccuracy
        positivity
      have hacc1 : guardedAccuracy a <= 1 := min_le_right _ _
      have hqspec := explicitPublicQ_spec a hn1
      have hmain := concrete_adaptive_runwise_volume_accuracy_q hn hqspec.1 hKc hKcl hKb
        hvol hclosedBall hfin (Ttc.CV.cvRadius_pos K) hacc hacc1 hp hp1 hKR
        (by
          simpa only [a, guardedAccuracy, guardedEta, guardedC, guardedS0, guardedJ,
            guardedM, guardedK] using hqspec.2)
      have hmain' : 1 - p <= (explicitPublicRawRunLaw a).real
          {omega | adjustablePublicRawEstimator a omega ∈
            Ttc.relErr (guardedAccuracy a) (volume K).toReal} := by
        convert hmain using 1 <;>
          simp only [a, guardedAccuracy, guardedEta, guardedC, guardedS0, guardedJ,
            guardedM, guardedK, guardedR, explicitPublicRawRunLaw,
            adjustablePublicRawEstimator] <;> rfl
      letI : IsProbabilityMeasure (explicitPublicRawRunLaw a) := hrawProb
      have hmono : (explicitPublicRawRunLaw a).real
          {omega | adjustablePublicRawEstimator a omega ∈
            Ttc.relErr (guardedAccuracy a) (volume K).toReal} <=
          (explicitPublicRawRunLaw a).real
          {omega | adjustablePublicRawEstimator a omega ∈
            Ttc.relErr eps (volume K).toReal} := by
        apply measureReal_mono
        · intro omega homega
          exact Ttc.CV.relErr_mono (min_le_left _ _) (volume K).toReal_nonneg homega
        · exact measure_ne_top _ _
      rw [hlaw, hest]
      exact hmain'.trans hmono)

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.explicitAdaptiveRadiusQ_tailFits
#print axioms Ttc.CVAdaptive.max_eight_two_explicitAdaptiveRadiusQ_sq_le
#print axioms Ttc.CVAdaptive.explicitPublicQ_spec
#print axioms Ttc.CVAdaptive.isProbabilityMeasure_explicitPublicRawRunLaw
#print axioms Ttc.CVAdaptive.explicitAdjustableConcreteVolumeAlgorithm

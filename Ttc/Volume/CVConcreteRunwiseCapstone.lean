/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptiveTerminalRunwiseAccuracy
import Ttc.Volume.CVConcreteEstimatorParameters
import Ttc.Volume.CVRunwiseSamplerParameters

/-!
# Fully parameterized runwise adaptive volume accuracy

This file keeps the polynomial cold endpoint throughout, chooses the estimator sample count,
mixing accuracy, walk deadlines, and median repetitions explicitly, and leaves only the
fixed radius-four tail feasibility condition.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive
open scoped ENNReal

variable {n k r : Nat}

/-- Polynomial-endpoint version of the final concrete runwise wrapper. -/
theorem median_accuracy_concrete_adaptive_runwise_polynomial
    (hn : 21 <= n) (hk : 0 < k) (hr : 0 < r)
    {K : Set (Space n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C kappa epsEst eta p epsMix : Real}
    (hC : 0 < C) (hkappa : 0 <= kappa) (hepsEst : 0 < epsEst)
    (heta : 0 < eta) (heta1 : eta < 1)
    (hk42 : 42 <= (k : Real))
    (hsamples : 7 * (adaptiveTerminalChunk (C ^ 2 * n)
      (polynomialEndpointSigmaSq n eta) : Real) <= (k : Real) * kappa)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (hbudget : Real.exp (kappa + (Real.exp (1 / 2) - 1) / (k : Real)) - 1 <=
      epsEst ^ 2 / 5)
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2) <= (r : Real))
    (hepsMix0 : 0 < epsMix) (hepsMix32 : epsMix <= 1 / 32)
    (steps : Fin (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1) -> Nat)
    (hsteps : forall i : Fin (terminalPhaseCount n C
      (polynomialEndpointSigmaSq n eta) + 1),
      ¬ 4 * (n : Real) * terminalSigmaSq n C (polynomialEndpointSigmaSq n eta) i <= 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma (terminalTarget n C)
          (polynomialEndpointSigmaSq n eta) i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix)) /
            (adaptiveTerminalDelta (n := n) (terminalTarget n C)
              (polynomialEndpointSigmaSq n eta) i * Real.log 2) ^ 2 + 1 <= (steps i : Real))
    (hsampler :
      (((terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1) * k : Nat) : Real) *
        (64 * ENNReal.ofReal epsMix +
          ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)).toReal <= 1 / 10) :
    let nu : Fin (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1) ->
        Fin k -> Measure (Space n) :=
      fun i _ => adaptiveTerminalWarmLaw (terminalTarget n C)
        (polynomialEndpointSigmaSq n eta) endpointRho K steps i
    let g : Fin (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1) ->
        Fin k -> Space n -> Real :=
      fun i _ => phaseScore (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1)
        (terminalSigmaSq n C (polynomialEndpointSigmaSq n eta)) K i
    1 - p <=
      (runMeasure (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))).real
        {omega | medianSel (fun t =>
          (2 * Real.pi * polynomialEndpointSigmaSq n eta) ^ ((n : Real) / 2) *
            ∏ i, oneRunPhaseAvg k g i (omega t)) ∈
          Ttc.relErr ((epsEst + eta) / (1 - eta)) (volume K).toReal} := by
  dsimp only
  let N : Real := C ^ 2 * n
  let s0 : Real := polynomialEndpointSigmaSq n eta
  let J := adaptiveTerminalChunk N s0
  let m := adaptiveChunkOffset N s0 J
  let sigmaSq := adaptiveSigmaSq N s0
  let nu : Fin (m + 1) -> Fin k -> Measure (Space n) :=
    fun i _ => adaptiveTerminalWarmLaw N s0 endpointRho K steps i
  let nuExact : Fin (m + 1) -> Fin k -> Measure (Space n) :=
    fun i _ => coolLaw (m + 1) sigmaSq K i
  let g : Fin (m + 1) -> Fin k -> Space n -> Real :=
    fun i _ => phaseScore (m + 1) sigmaSq K i
  have hn2 : 2 <= n := by omega
  have hn1 : 1 <= n := by omega
  have hball : ball (0 : Space n) 1 ⊆ K := ball_subset_closedBall.trans hclosedBall
  have hN : 0 < N := by dsimp [N]; positivity
  have hs0 : 0 < s0 := polynomialEndpointSigmaSq_pos hn1 heta
  have hsigma : forall q, 0 < sigmaSq q := fun q => adaptiveSigmaSq_pos hN hs0 q
  have hbelow : forall j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) <= N := by
    intro j hj
    have hjm : j < m := by omega
    have hchunk : adaptivePhaseChunk N s0 j < J :=
      adaptivePhaseChunk_lt_of_lt_offset hN hs0 hjm
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs0 hchunk).le
  have hcoldStart : 4 * (n : Real) * s0 <= endpointRho ^ 2 :=
    polynomialEndpointSigmaSq_coldBall hn1 heta heta1.le
  have hrho : 0 < endpointRho := endpointRho_pos
  have hrhoc : endpointRho < 1 - 1 / (2 * (n : Real)) := endpointRho_lt_shrink hn2
  letI hnuProb : forall i l, IsProbabilityMeasure (nu i l) := fun i l =>
    isProbabilityMeasure_adaptiveTerminalWarmLaw hn hN hs0 hKcl.measurableSet hKc
      hclosedBall hfin hrho hrhoc hcoldStart hbelow hepsMix0 hepsMix32 steps hsteps i
  letI hnuExactProb : forall i l, IsProbabilityMeasure (nuExact i l) := fun i l => by
    dsimp only [nuExact]
    exact coolLaw_isProbabilityMeasure hsigma hball hfin i
  letI (i : Fin (m + 1)) (l : Fin k) : IsProbabilityMeasure (nu i l) := hnuProb i l
  letI (i : Fin (m + 1)) (l : Fin k) : IsProbabilityMeasure (nuExact i l) :=
    hnuExactProb i l
  let b : ENNReal := 64 * ENNReal.ofReal epsMix +
    ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)
  have hb : b ≠ ⊤ := by
    dsimp [b]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have htv : forall i l, TVLe (nu i l) (nuExact i l) b := by
    intro i l
    exact tvLe_adaptiveTerminalWarmLaw hn hN hs0 hKcl.measurableSet hKc hclosedBall
      hfin hrho hrhoc hcoldStart hbelow hepsMix0 hepsMix32 steps hsteps i
  have hg : forall i l, Measurable (g i l) := fun i l =>
    measurable_phaseScore hKcl.measurableSet i
  have hg0 : forall i l x, 0 <= g i l x := fun i l x =>
    phaseScore_nonneg (m + 1) sigmaSq K i x
  have hsigma0 : sigmaSq 0 = polynomialEndpointSigmaSq n eta := by
    dsimp [sigmaSq, s0]
    simpa [adaptiveChunkStart] using adaptiveSigmaSq_offset hN hs0 0
  have hballRho : closedBall (0 : Space n) endpointRho ⊆ K :=
    (closedBall_subset_closedBall (by norm_num [endpointRho])).trans hclosedBall
  have hcoldPkg := chain_zero_polynomial_endpoint_package (n := n) (eta := eta) (m := m + 1)
    (by omega) hsigma0 hKcl.measurableSet hfin hn1 hballRho heta heta1.le
  have hexact := oneRun_accuracy_adaptive_first_terminal_exact hn2 hk hKc hKcl hKb hvol
    hball hfin hC hs0 hkappa hepsEst hk42 hsamples hKR hbudget
  exact @median_accuracy_runwise_of_exact_and_cold (m + 1) k r (Space n) _
    nu nuExact hnuProb hnuExactProb g hg hg0 hk
    (chain (m + 1) sigmaSq K 0) ((2 * Real.pi * s0) ^ ((n : Real) / 2))
    (volume K).toReal epsEst eta
    (chain_pos hsigma hball hfin 0) (by positivity) hepsEst.le heta.le heta1
    hcoldPkg.1 hcoldPkg.2 b hb htv hsampler
    (by simpa only [N, s0, J, m, sigmaSq, nuExact, g] using hexact) hr p hp hrp

/-! ## Fully explicit capstone -/

/-- Requested-accuracy runwise volume theorem with every numeric parameter fixed. -/
theorem concrete_adaptive_runwise_volume_accuracy
    (hn : 21 <= n)
    {K : Set (Space n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C epsilon p : Real} (hC : 0 < C) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon <= 1) (hp : 0 < p) (hp1 : p < 1)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (htail : let eta := epsilon / 4
      let s0 := polynomialEndpointSigmaSq n eta
      let J := adaptiveTerminalChunk (C ^ 2 * n) s0
      let m := adaptiveChunkOffset (C ^ 2 * n) s0 J
      let k := concreteEstimatorSamples J (epsilon / 4)
      RunwiseRadiusFourTailFits n m k) :
    let eta := epsilon / 4
    let epsEst := epsilon / 4
    let s0 := polynomialEndpointSigmaSq n eta
    let J := adaptiveTerminalChunk (C ^ 2 * n) s0
    let m := adaptiveChunkOffset (C ^ 2 * n) s0 J
    let k := concreteEstimatorSamples J epsEst
    let r := concreteRunwiseReps p
    let epsMix := runwiseChosenMixError m k
    let steps := runwiseMixingSteps n (C ^ 2 * n) s0 m k
    let nu : Fin (m + 1) -> Fin k -> Measure (Space n) := fun i _ =>
      adaptiveTerminalWarmLaw (C ^ 2 * n) s0 endpointRho K steps i
    let g : Fin (m + 1) -> Fin k -> Space n -> Real := fun i _ =>
      phaseScore (m + 1) (adaptiveSigmaSq (C ^ 2 * n) s0) K i
    1 - p <=
      (runMeasure (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))).real
        {omega | medianSel (fun t =>
          (2 * Real.pi * s0) ^ ((n : Real) / 2) *
            ∏ i, oneRunPhaseAvg k g i (omega t)) ∈
          Ttc.relErr epsilon (volume K).toReal} := by
  dsimp only
  let eta : Real := epsilon / 4
  let epsEst : Real := epsilon / 4
  let s0 : Real := polynomialEndpointSigmaSq n eta
  let J : Nat := adaptiveTerminalChunk (C ^ 2 * n) s0
  let m : Nat := adaptiveChunkOffset (C ^ 2 * n) s0 J
  let k : Nat := concreteEstimatorSamples J epsEst
  let r : Nat := concreteRunwiseReps p
  let epsMix : Real := runwiseChosenMixError m k
  let steps : Fin (m + 1) -> Nat := runwiseMixingSteps n (C ^ 2 * n) s0 m k
  let nu : Fin (m + 1) -> Fin k -> Measure (Space n) := fun i _ =>
    adaptiveTerminalWarmLaw (C ^ 2 * n) s0 endpointRho K steps i
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
  have hsteps : forall i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq (C ^ 2 * n) s0 i <= 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma (C ^ 2 * n) s0 i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix)) /
            (adaptiveTerminalDelta (n := n) (C ^ 2 * n) s0 i * Real.log 2) ^ 2 + 1 <=
        (steps i : Real) := by
    intro i _
    simpa only [epsMix, steps] using
      runwiseMixingSteps_spec n (C ^ 2 * n) s0 m k i
  have hsampler : (((m + 1) * k : Nat) : Real) *
      (64 * ENNReal.ofReal epsMix +
        ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)).toReal <= 1 / 10 := by
    simpa only [epsMix] using runwise_sampler_toReal_budget n m hk htail
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
    isProbabilityMeasure_adaptiveTerminalWarmLaw hn hN hs0 hKcl.measurableSet hKc
      hclosedBall hfin endpointRho_pos (endpointRho_lt_shrink hn2) hcold hbelow
      hepsMix0 hepsMix32 steps hsteps i
  letI hiidProb : forall t i l,
      IsProbabilityMeasure (Ttc.CVRunwise.iidRunFamily (r := r) nu t i l) :=
    fun t i l => hnuProb i l
  letI : IsProbabilityMeasure
      (runMeasure (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))) := by
    infer_instance
  have hmain := median_accuracy_concrete_adaptive_runwise_polynomial
    (n := n) (k := k) (r := r) hn hk hr hKc hKcl hKb hvol hclosedBall hfin
    hC hkappa hepsEst heta heta1 hk42 hsamples hKR hbudget hp hrp
    hepsMix0 hepsMix32 steps hsteps hsampler
  have hmain' : 1 - p <=
      (runMeasure (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))).real
        {omega | medianSel (fun t =>
          (2 * Real.pi * s0) ^ ((n : Real) / 2) *
            ∏ i, oneRunPhaseAvg k g i (omega t)) ∈
          Ttc.relErr ((epsEst + eta) / (1 - eta)) (volume K).toReal} := by
    convert hmain using 1 <;>
      simp only [terminalTarget, terminalPhaseCount, terminalChunk, terminalSigmaSq,
        s0, J, m, nu, g] <;> rfl
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

/-! ### Axiom audit -/

#print axioms median_accuracy_concrete_adaptive_runwise_polynomial
#print axioms concrete_adaptive_runwise_volume_accuracy

end Ttc.CVAdaptive

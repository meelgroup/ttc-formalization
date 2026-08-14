/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptivePolynomialEndpointParameters
import Ttc.Volume.AdaptiveTerminalWarmLaw
import Ttc.Volume.CVAdaptiveFirstTerminalExact
import Ttc.Volume.CVTerminalCouplingAccuracy

/-!
# Accuracy of the concrete adaptive Cousins--Vempala phase sampler

The sampled law here is no longer an abstract `TVLe` input.  Cold coordinates use ambient
Gaussian rejection; warm coordinates use the radius-four truncated lazy speedy walk followed
by the source's rescaling/reweighting rejection.  Every coordinate is independently restarted
from the explicit cold ball law.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive
open scoped ENNReal

variable {n r k : ℕ}

/-- Accuracy of the concrete first-terminal CV estimator.  All remaining premises are
numeric choices (samples, repetitions, mixing steps, and error allocation) or the standard
convex-body geometry. -/
theorem packed_median_accuracy_concrete_adaptive
    (hn : 21 ≤ n) (hk : 0 < k) (hr : 0 < r)
    {K : Set (Space n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C κ epsEst eta p epsMix rhoError : ℝ}
    (hC : 0 < C) (hκ : 0 ≤ κ) (hepsEst : 0 < epsEst)
    (heta : 0 < eta) (heta1 : eta < 1)
    (hk42 : 42 ≤ (k : ℝ))
    (hsamples : 7 * (adaptiveTerminalChunk (C ^ 2 * n) (polynomialEndpointSigmaSq n eta) : ℝ) ≤
      (k : ℝ) * κ)
    (hKR : K ⊆ closedBall 0 (C * √n))
    (hbudget : Real.exp (κ + (Real.exp (1 / 2) - 1) / (k : ℝ)) - 1 ≤
      epsEst ^ 2 / 5)
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ))
    (hepsMix0 : 0 < epsMix) (hepsMix32 : epsMix ≤ 1 / 32)
    (steps : Fin (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1) → ℕ)
    (hsteps : ∀ i : Fin (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1),
      ¬ 4 * (n : ℝ) * terminalSigmaSq n C (polynomialEndpointSigmaSq n eta) i ≤ 1 →
      4 * 640 ^ 2 * adaptiveTerminalSigma (terminalTarget n C)
          (polynomialEndpointSigmaSq n eta) i ^ 2 * (n : ℝ) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix)) /
            (adaptiveTerminalDelta (n := n) (terminalTarget n C)
              (polynomialEndpointSigmaSq n eta) i * Real.log 2) ^ 2 + 1
        ≤ (steps i : ℝ))
    (htensor : (((r * (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1) * k : ℕ) : ℝ) *
      (64 * ENNReal.ofReal epsMix +
        ENNReal.ofReal ((4 * Real.exp (-(15 : ℝ) / 2)) ^ n)).toReal) ≤ rhoError) :
    let nu : Fin r → Fin (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1) →
        Fin k → Measure (Space n) :=
      adaptiveTerminalWarmLawFamily (terminalTarget n C) (polynomialEndpointSigmaSq n eta)
        endpointRho K steps
    let g : Fin r → Fin (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1) →
        Fin k → Space n → ℝ :=
      fun _ i _ => phaseScore (terminalPhaseCount n C (polynomialEndpointSigmaSq n eta) + 1)
        (terminalSigmaSq n C (polynomialEndpointSigmaSq n eta)) K i
    1 - p - rhoError ≤ (runMeasure (packedPhaseLaw nu)).real
      {omega | medianSel
        (fun t => (2 * Real.pi * polynomialEndpointSigmaSq n eta) ^ ((n : ℝ) / 2) *
          ∏ i, Ttc.CVPacked.phaseAvg g t i omega) ∈
            Ttc.relErr ((epsEst + eta) / (1 - eta)) (volume K).toReal} := by
  dsimp only
  let N : ℝ := C ^ 2 * n
  let s0 := polynomialEndpointSigmaSq n eta
  let J := adaptiveTerminalChunk N s0
  let m := adaptiveChunkOffset N s0 J
  let sigmaSq := adaptiveSigmaSq N s0
  let nu : Fin r → Fin (m + 1) → Fin k → Measure (Space n) :=
    adaptiveTerminalWarmLawFamily N s0 endpointRho K steps
  let nuExact : Fin r → Fin (m + 1) → Fin k → Measure (Space n) :=
    fun _ i _ => coolLaw (m + 1) sigmaSq K i
  let g : Fin r → Fin (m + 1) → Fin k → Space n → ℝ :=
    fun _ i _ => phaseScore (m + 1) sigmaSq K i
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hball : ball (0 : Space n) 1 ⊆ K := ball_subset_closedBall.trans hclosedBall
  have hN : 0 < N := by dsimp [N]; positivity
  have hs0 : 0 < s0 := polynomialEndpointSigmaSq_pos hn1 heta
  have hsigma : ∀ q, 0 < sigmaSq q := fun q => adaptiveSigmaSq_pos hN hs0 q
  have hbelow : ∀ j, j + 1 < m + 1 →
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N := by
    intro j hj
    have hjm : j < m := by omega
    have hchunk : adaptivePhaseChunk N s0 j < J :=
      adaptivePhaseChunk_lt_of_lt_offset hN hs0 hjm
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs0 hchunk).le
  have hcoldStart : 4 * (n : ℝ) * s0 ≤ endpointRho ^ 2 :=
    polynomialEndpointSigmaSq_coldBall hn1 heta heta1.le
  have hrho : 0 < endpointRho := endpointRho_pos
  have hrhoc : endpointRho < 1 - 1 / (2 * (n : ℝ)) := endpointRho_lt_shrink hn2
  letI hnuProb : ∀ t i l, IsProbabilityMeasure (nu t i l) := fun t i l =>
    isProbabilityMeasure_adaptiveTerminalWarmLawFamily hn hN hs0 hKcl.measurableSet hKc
      hclosedBall hfin hrho hrhoc hcoldStart hbelow hepsMix0 hepsMix32 steps hsteps t i l
  letI hnuExactProb : ∀ t i l, IsProbabilityMeasure (nuExact t i l) := fun t i l => by
    dsimp only [nuExact]
    exact coolLaw_isProbabilityMeasure hsigma hball hfin i
  let b : ℝ≥0∞ := 64 * ENNReal.ofReal epsMix +
    ENNReal.ofReal ((4 * Real.exp (-(15 : ℝ) / 2)) ^ n)
  have hb : b ≠ ⊤ := by
    dsimp [b]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have htv : ∀ t i l, TVLe (nu t i l) (nuExact t i l) b := by
    intro t i l
    exact tvLe_adaptiveTerminalWarmLawFamily hn hN hs0 hKcl.measurableSet hKc
      hclosedBall hfin hrho hrhoc hcoldStart hbelow hepsMix0 hepsMix32 steps hsteps t i l
  have hg : ∀ t i l, Measurable (g t i l) := fun t i l =>
    measurable_phaseScore hKcl.measurableSet i
  have hg0 : ∀ t i l x, 0 ≤ g t i l x := fun t i l x =>
    phaseScore_nonneg (m + 1) sigmaSq K i x
  have hsigma0 : sigmaSq 0 = polynomialEndpointSigmaSq n eta := by
    dsimp [sigmaSq, s0]
    simpa [adaptiveChunkStart] using adaptiveSigmaSq_offset hN hs0 0
  have hballRho : closedBall (0 : Space n) endpointRho ⊆ K :=
    (closedBall_subset_closedBall (by norm_num [endpointRho])).trans hclosedBall
  have hcoldPkg := chain_zero_polynomial_endpoint_package (n := n) (eta := eta) (m := m + 1)
    (by omega) hsigma0 hKcl.measurableSet hfin hn1 hballRho heta heta1.le
  have hexact := packed_median_accuracy_adaptive_first_terminal_exact hn2 hk hr hKc hKcl
    hKb hvol hball hfin hC hs0 hκ hepsEst hk42 hsamples hKR hbudget hp hrp
  exact @packed_terminal_accuracy_of_tv_and_cold r (m + 1) k (Space n) _ nu nuExact
    hnuProb hnuExactProb g hg hg0 hk hr (chain (m + 1) sigmaSq K 0)
    ((2 * Real.pi * s0) ^ ((n : ℝ) / 2)) (volume K).toReal epsEst eta p
    (chain_pos hsigma hball hfin 0) (by positivity) hepsEst.le heta.le heta1
    hcoldPkg.1 hcoldPkg.2 b hb htv rhoError htensor
    (by simpa only [N, s0, J, m, sigmaSq, nuExact, g] using hexact)

#print axioms packed_median_accuracy_concrete_adaptive

end Ttc.CVAdaptive

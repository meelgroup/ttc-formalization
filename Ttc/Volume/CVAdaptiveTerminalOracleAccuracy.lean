/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVAdaptiveFirstTerminalExact
import Ttc.Volume.CVTerminalCouplingAccuracy
import Ttc.Volume.AdaptiveTerminalSamplerLaw

/-!
# Accuracy of the branch-selected terminal CV volume oracle

This theorem joins the first-terminal exact estimator to the operational cold rejection /+warm truncated-walk law.  Its only sampling premise is the warm-coordinate `TVLe` bound;
the cold coordinates are exact by construction.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive
open scoped ENNReal

variable {n r k : ℕ}

noncomputable def terminalTarget (n : ℕ) (C : ℝ) : ℝ := C ^ 2 * n

noncomputable def terminalChunk (n : ℕ) (C s₀ : ℝ) : ℕ :=
  adaptiveTerminalChunk (terminalTarget n C) s₀

noncomputable def terminalPhaseCount (n : ℕ) (C s₀ : ℝ) : ℕ :=
  adaptiveChunkOffset (terminalTarget n C) s₀ (terminalChunk n C s₀)

noncomputable def terminalSigmaSq (n : ℕ) (C s₀ : ℝ) : ℕ → ℝ :=
  adaptiveSigmaSq (terminalTarget n C) s₀

/-- The first-terminal branch-selected estimator is accurate.  The exact target is
`volume K`; `eta` is solely the error for replacing the unknown cold normalizer by `Z0`,
and `rho` is solely the tensorized sampler error. -/
theorem packed_median_accuracy_adaptive_terminal_oracle
    (hn : 2 ≤ n) (hk : 0 < k) (hr : 0 < r)
    {K : Set (Space n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s₀ κ ε p : ℝ} (hC : 0 < C) (hs₀ : 0 < s₀) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hk42 : 42 ≤ (k : ℝ))
    (hsamples : 7 * (terminalChunk n C s₀ : ℝ) ≤ (k : ℝ) * κ)
    (hKR : K ⊆ closedBall 0 (C * √n))
    (hbudget : Real.exp (κ + (Real.exp (1 / 2) - 1) / (k : ℝ)) - 1 ≤ ε ^ 2 / 5)
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ))
    (truncatedLaw : Fin r → Fin (terminalPhaseCount n C s₀ + 1) → Fin k →
      Measure (Space n))
    [htrunc : ∀ t i l, IsProbabilityMeasure (truncatedLaw t i l)]
    {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hWarmTV : ∀ (t : Fin r) (i : Fin (terminalPhaseCount n C s₀ + 1)) (l : Fin k),
      ¬ 4 * (n : ℝ) * terminalSigmaSq n C s₀ i ≤ 1 →
      TVLe (truncatedLaw t i l)
        (coolLaw (terminalPhaseCount n C s₀ + 1) (terminalSigmaSq n C s₀) K i) b)
    {rho Z0 eta : ℝ}
    (hrho : (((r * (terminalPhaseCount n C s₀ + 1) * k : ℕ) : ℝ) * b.toReal) ≤ rho)
    (hZ0 : 0 < Z0) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hcoldLe : chain (terminalPhaseCount n C s₀ + 1) (terminalSigmaSq n C s₀) K 0 ≤ Z0)
    (hcold : chain (terminalPhaseCount n C s₀ + 1) (terminalSigmaSq n C s₀) K 0 ∈
      Ttc.relErr eta Z0) :
    let nu := adaptiveTerminalPackedSamplerFamily (terminalSigmaSq n C s₀) K truncatedLaw
    let g : Fin r → Fin (terminalPhaseCount n C s₀ + 1) → Fin k → Space n → ℝ :=
      fun _ i _ => phaseScore (terminalPhaseCount n C s₀ + 1)
        (terminalSigmaSq n C s₀) K i
    1 - p - rho ≤ (runMeasure (packedPhaseLaw nu)).real
      {omega | medianSel (fun t => Z0 * ∏ i, Ttc.CVPacked.phaseAvg g t i omega) ∈
        Ttc.relErr ((ε + eta) / (1 - eta)) (volume K).toReal} := by
  dsimp only
  let N : ℝ := terminalTarget n C
  let J := terminalChunk n C s₀
  let m := terminalPhaseCount n C s₀
  let sigmaSq := terminalSigmaSq n C s₀
  let nu := adaptiveTerminalPackedSamplerFamily sigmaSq K truncatedLaw
  let nuExact : Fin r → Fin (m + 1) → Fin k → Measure (Space n) :=
    fun _ i _ => coolLaw (m + 1) sigmaSq K i
  let g : Fin r → Fin (m + 1) → Fin k → Space n → ℝ :=
    fun _ i _ => phaseScore (m + 1) sigmaSq K i
  have hn1 : 1 ≤ n := by omega
  have hball : ball (0 : Space n) 1 ⊆ K := ball_subset_closedBall.trans hclosedBall
  have hN : 0 < N := by dsimp [N, terminalTarget]; positivity
  have hsigma : ∀ q, 0 < sigmaSq q := fun q => adaptiveSigmaSq_pos hN hs₀ q
  letI hnuProb : ∀ t i l, IsProbabilityMeasure (nu t i l) := fun t i l =>
    isProbabilityMeasure_adaptiveTerminalPackedSamplerFamily hsigma hKcl.measurableSet
      truncatedLaw t i l
  letI hnuExactProb : ∀ t i l, IsProbabilityMeasure (nuExact t i l) := fun t i l => by
    dsimp only [nuExact]
    exact coolLaw_isProbabilityMeasure hsigma hball hfin i
  have htv : ∀ t i l, TVLe (nu t i l) (nuExact t i l) b := by
    intro t i l
    exact adaptiveTerminalPackedSamplerFamily_tv hsigma hKcl.measurableSet hfin hn1
      hclosedBall truncatedLaw hWarmTV t i l
  have hg : ∀ t i l, Measurable (g t i l) := fun t i l =>
    measurable_phaseScore hKcl.measurableSet i
  have hg0 : ∀ t i l x, 0 ≤ g t i l x := fun t i l x =>
    phaseScore_nonneg (m + 1) sigmaSq K i x
  have hA0 : 0 < chain (m + 1) sigmaSq K 0 := chain_pos hsigma hball hfin 0
  have hexact := packed_median_accuracy_adaptive_first_terminal_exact hn hk hr hKc hKcl
    hKb hvol hball hfin hC hs₀ hκ hε hk42 hsamples hKR hbudget hp hrp
  exact @packed_terminal_accuracy_of_tv_and_cold r (m + 1) k (Space n) _ nu nuExact
    hnuProb hnuExactProb g hg hg0 hk hr (chain (m + 1) sigmaSq K 0) Z0
    (volume K).toReal ε eta p hA0 hZ0 hε.le heta0 heta1 hcoldLe hcold b hb htv rho
    hrho (by
      change 1 - p ≤ (runMeasure (packedPhaseLaw nuExact)).real
        {omega | medianSel
          (fun t => chain (m + 1) sigmaSq K 0 *
            ∏ i, Ttc.CVPacked.phaseAvg g t i omega) ∈
              Ttc.relErr ε (volume K).toReal}
      convert hexact using 1 <;>
        simp only [m, sigmaSq, terminalTarget, terminalChunk, terminalPhaseCount,
          terminalSigmaSq, nuExact, g]
      congr 1)

#print axioms packed_median_accuracy_adaptive_terminal_oracle

end Ttc.CVAdaptive

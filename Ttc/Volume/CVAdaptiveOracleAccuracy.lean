/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVAdaptiveExact
import Ttc.Volume.CVPackedCouplingAccuracy
import Ttc.Volume.CVEndpointAccuracy

/-!
# Accuracy capstone for the adaptive CV volume estimator

This joins the exact adaptive variance theorem, a total-variation approximation for every
elementary phase draw, and the cold/hot endpoint corrections.  The remaining sampler work is
therefore isolated in the `TVLe` premise; no exact-law phase sampler is hidden in the result.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open scoped ENNReal

variable {n r k J : ℕ}

/-- The adaptive Gaussian-cooling estimator is accurate under coordinatewise sampler TV
guarantees and the two endpoint comparisons. -/
theorem packed_median_accuracy_adaptive_of_tv
    (hn : 2 ≤ n) (hk : 0 < k) (hr : 0 < r)
    {K : Set (Space n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s₀ κ ε p : ℝ} (hC : 0 < C) (hs₀ : 0 < s₀) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hk42 : 42 ≤ (k : ℝ))
    (hbelow : ∀ j < J, adaptiveChunkStart (C ^ 2 * n) s₀ j ≤ C ^ 2 * n)
    (hsamples : 7 * (J : ℝ) ≤ (k : ℝ) * κ)
    (hKR : K ⊆ closedBall 0 (C * √n))
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5) (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ))
    {ν : Fin r → Fin (adaptiveChunkOffset (C ^ 2 * n) s₀ J) → Fin k →
      Measure (Space n)}
    (hν : ∀ t i l, IsProbabilityMeasure (ν t i l))
    {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (htv : ∀ t i l, Arlib.TVLe (ν t i l)
      (coolLaw (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
        (adaptiveSigmaSq (C ^ 2 * n) s₀) K i) b)
    {ρ : ℝ} (hρ : ((r * adaptiveChunkOffset (C ^ 2 * n) s₀ J * k : ℕ) : ℝ) *
      b.toReal ≤ ρ)
    {Z₀ V eta theta : ℝ} (hZ₀ : 0 < Z₀)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (htheta0 : 0 ≤ theta) (hV : 0 ≤ V)
    (hcoldLe : chain (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
      (adaptiveSigmaSq (C ^ 2 * n) s₀) K 0 ≤ Z₀)
    (hcold : chain (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
      (adaptiveSigmaSq (C ^ 2 * n) s₀) K 0 ∈ relErr eta Z₀)
    (hhot : chain (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
      (adaptiveSigmaSq (C ^ 2 * n) s₀) K
        (adaptiveChunkOffset (C ^ 2 * n) s₀ J) ∈ relErr theta V) :
    let m := adaptiveChunkOffset (C ^ 2 * n) s₀ J
    let σsq := adaptiveSigmaSq (C ^ 2 * n) s₀
    let g : Fin r → Fin m → Fin k → Space n → ℝ :=
      fun _ i _ => phaseScore (m + 1) σsq K i
    1 - p - ρ ≤ (Arlib.Probability.runMeasure (packedPhaseLaw ν)).real
      {ω | Arlib.Probability.medianSel
        (fun t => Z₀ * ∏ i, Ttc.CVPacked.phaseAvg g t i ω)
          ∈ relErr ((ε + eta) / (1 - eta) + theta +
            ((ε + eta) / (1 - eta)) * theta) V} := by
  dsimp only
  let N : ℝ := C ^ 2 * n
  let m := adaptiveChunkOffset N s₀ J
  let σsq := adaptiveSigmaSq N s₀
  let ν' : Fin r → Fin m → Fin k → Measure (Space n) :=
    fun _ i _ => coolLaw (m + 1) σsq K i
  let g : Fin r → Fin m → Fin k → Space n → ℝ :=
    fun _ i _ => phaseScore (m + 1) σsq K i
  have hN : 0 < N := by dsimp [N]; positivity
  have hσ : ∀ q, 0 < σsq q := fun q => adaptiveSigmaSq_pos hN hs₀ q
  have hm : 0 < m + 1 := by omega
  have hA0 : 0 < chain (m + 1) σsq K 0 := chain_pos hσ hball hfin 0
  letI hνprob : ∀ (t : Fin r) (i : Fin m) (l : Fin k),
      IsProbabilityMeasure (ν t i l) := hν
  letI hν'prob : ∀ (t : Fin r) (i : Fin m) (l : Fin k),
      IsProbabilityMeasure (ν' t i l) := fun t i l => by
    dsimp only [ν']
    exact coolLaw_isProbabilityMeasure hσ hball hfin i
  have hexact := packed_median_accuracy_adaptive_exact hn hk hr hKc hKcl hKb hvol
    hball hfin hC hs₀ hκ hε hk42 hbelow hsamples hKR hbudget hp hrp
  have hg : ∀ t i l, Measurable (g t i l) := by
    intro t i l
    exact measurable_phaseScore hKcl.measurableSet i
  let X : Fin r → Arlib.Probability.RunSpace (Fin k → Space n) r m → ℝ :=
    fun t ω => ∏ i, Ttc.CVPacked.phaseAvg g t i ω
  have hmedMeas : Measurable (fun ω => Arlib.Probability.medianSel
      (fun t => chain (m + 1) σsq K 0 * X t ω)) :=
    Arlib.Probability.measurable_medianSel fun t => measurable_const.mul
      (Finset.measurable_fun_prod _ fun i _ => Ttc.CVPacked.measurable_phaseAvg hg t i)
  have hcoupled : 1 - p - ρ ≤
      (Arlib.Probability.runMeasure (packedPhaseLaw ν)).real
        {ω | Arlib.Probability.medianSel
          (fun t => chain (m + 1) σsq K 0 * X t ω) ∈
            relErr ε (chain (m + 1) σsq K m)} := by
    have htv' : ∀ t i l, Arlib.TVLe (ν t i l) (ν' t i l) b := by
      intro t i l
      simpa only [ν', N, m, σsq] using htv t i l
    have hρ' : ((r * m * k : ℕ) : ℝ) * b.toReal ≤ ρ := by
      simpa only [N, m] using hρ
    have hexact' : 1 - p ≤
        (Arlib.Probability.runMeasure (packedPhaseLaw ν')).real
          {ω | Arlib.Probability.medianSel
            (fun t => chain (m + 1) σsq K 0 * X t ω) ∈
              relErr ε (chain (m + 1) σsq K m)} := by
      simpa only [N, m, σsq, ν', g, X] using hexact
    exact @Ttc.CVPacked.measureReal_median_relErr_ge_of_tvLe r m k (Space n) _
      ν ν' hνprob hν'prob b hb htv' ρ hρ'
      (fun ω => Arlib.Probability.medianSel
        (fun t => chain (m + 1) σsq K 0 * X t ω)) hmedMeas
      (chain (m + 1) σsq K m) ε p hexact'
  have hX0 : ∀ t ω, 0 ≤ X t ω := by
    intro t ω
    apply Finset.prod_nonneg
    intro i _
    unfold Ttc.CVPacked.phaseAvg Ttc.CVEst.avgOf
    exact div_nonneg (Finset.sum_nonneg fun l _ => phaseScore_nonneg (m + 1) σsq K i _) (by positivity)
  haveI : IsProbabilityMeasure (Arlib.Probability.runMeasure (packedPhaseLaw ν)) := by
    unfold Arlib.Probability.runMeasure
    infer_instance
  have hend : 1 - (p + ρ) ≤
      (Arlib.Probability.runMeasure (packedPhaseLaw ν)).real
        {ω | Arlib.Probability.medianSel (fun t => Z₀ * X t ω) ∈
          relErr ((ε + eta) / (1 - eta) + theta +
            ((ε + eta) / (1 - eta)) * theta) V} := by
    apply Ttc.CV.measureReal_median_replace_cold_and_hot hr hA0 hZ₀ hX0
      hε.le heta0 heta1 htheta0 hV
    · simpa only [N, m, σsq] using hcoldLe
    · simpa only [N, m, σsq] using hcold
    · simpa only [N, m, σsq] using hhot
    · simpa only [sub_add_eq_sub_sub] using hcoupled
  simpa only [N, m, σsq, g, X, sub_add_eq_sub_sub] using hend

#print axioms packed_median_accuracy_adaptive_of_tv

end Ttc.CVAdaptive

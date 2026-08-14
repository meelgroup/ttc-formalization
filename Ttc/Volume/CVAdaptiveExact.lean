/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVEstimatorExactAccuracy

/-!
# The adaptive accelerated CV estimator under exact phase laws

This is the fully assembled exact-law half of the polynomial volume oracle.  It instantiates
the packed estimator with the actual adaptive `phaseScore` and `coolLaw`, discharges its
measurability, independence, `L²`, exact means, nonuniform second moments, and chunk-product
budget, and returns the median accuracy theorem.  Sampler approximation and endpoint error
are intentionally separate layers.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked

variable {n r k J : ℕ}

/-- Median accuracy of the finite adaptive Gaussian block, with every elementary sample
drawn independently from its exact phase law. -/
theorem packed_median_accuracy_adaptive_exact (hn : 2 ≤ n) (hk : 0 < k) (hr : 0 < r)
    {K : Set (Space n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s₀ κ ε p : ℝ} (hC : 0 < C) (hs₀ : 0 < s₀) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hk42 : 42 ≤ (k : ℝ))
    (hbelow : ∀ j < J, adaptiveChunkStart (C ^ 2 * n) s₀ j ≤ C ^ 2 * n)
    (hsamples : 7 * (J : ℝ) ≤ (k : ℝ) * κ)
    (hKR : K ⊆ closedBall 0 (C * √n))
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5) (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ)) :
    let m := adaptiveChunkOffset (C ^ 2 * n) s₀ J
    let σsq := adaptiveSigmaSq (C ^ 2 * n) s₀
    let ν : Fin r → Fin m → Fin k → Measure (Space n) :=
      fun _ i _ => coolLaw (m + 1) σsq K i
    let g : Fin r → Fin m → Fin k → Space n → ℝ :=
      fun _ i _ => phaseScore (m + 1) σsq K i
    1 - p ≤ (Arlib.Probability.runMeasure (packedPhaseLaw ν)).real
      {ω | Arlib.Probability.medianSel
        (fun t => chain (m + 1) σsq K 0 * ∏ i, Ttc.CVPacked.phaseAvg g t i ω)
          ∈ Ttc.relErr ε (chain (m + 1) σsq K m)} := by
  dsimp only
  let N : ℝ := C ^ 2 * n
  let m := adaptiveChunkOffset N s₀ J
  let σsq := adaptiveSigmaSq N s₀
  let ν : Fin r → Fin m → Fin k → Measure (Space n) :=
    fun _ i _ => coolLaw (m + 1) σsq K i
  let g : Fin r → Fin m → Fin k → Space n → ℝ :=
    fun _ i _ => phaseScore (m + 1) σsq K i
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  have hσ : ∀ q, 0 < σsq q := fun q => adaptiveSigmaSq_pos hN hs₀ q
  letI hνprob (t : Fin r) (i : Fin m) (l : Fin k) :
      IsProbabilityMeasure (ν t i l) := by
    dsimp only [ν]
    exact coolLaw_isProbabilityMeasure hσ hball hfin i
  have hνall : ∀ t i l, IsProbabilityMeasure (ν t i l) := fun t i l => hνprob t i l
  haveI hpackedProb : ∀ t i, IsProbabilityMeasure (packedPhaseLaw ν t i) := by
    intro t i
    exact @packedPhaseLaw_isProbabilityMeasure r m k (Space n) _ ν hνall t i
  haveI hrunProb : IsProbabilityMeasure
      (Arlib.Probability.runMeasure (packedPhaseLaw ν)) := by
    unfold Arlib.Probability.runMeasure
    infer_instance
  have hg : ∀ t i l, Measurable (g t i l) := by
    intro t i l
    exact measurable_phaseScore hKcl.measurableSet i
  have hscoreBound : ∀ t i l x, |g t i l x| ≤ Real.exp ((C * √n) ^ 2 / (2 * σsq i)) := by
    intro t i l x
    rw [abs_of_nonneg (phaseScore_nonneg (m + 1) σsq K i x)]
    exact phaseScore_le hσ hKR i x
  have hL2 : ∀ t i l, MemLp (g t i l) 2 (ν t i l) := by
    intro t i l
    letI : IsProbabilityMeasure (ν t i l) := hνprob t i l
    exact MemLp.of_bound (hg t i l).aestronglyMeasurable
      (Real.exp ((C * √n) ^ 2 / (2 * σsq i)))
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hscoreBound t i l x)
  have hprod : ∀ t, MemLp (fun ω => ∏ i, Ttc.CVPacked.phaseAvg g t i ω) 2
      (Arlib.Probability.runMeasure (packedPhaseLaw ν)) := by
    intro t
    let B : ℝ := ∏ i : Fin m, Real.exp ((C * √n) ^ 2 / (2 * σsq i))
    have hmeas : Measurable (fun ω => ∏ i, Ttc.CVPacked.phaseAvg g t i ω) :=
      Finset.measurable_fun_prod _ fun i _ => Ttc.CVPacked.measurable_phaseAvg hg t i
    refine MemLp.of_bound hmeas.aestronglyMeasurable B ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => by
      exact Ttc.CVPacked.abs_phaseAvg_le hk (fun _t _i _l x => hscoreBound t i _l x) t i ω
  have hmean : ∀ t i l, ∫ x, g t i l x ∂(ν t i l) =
      chain (m + 1) σsq K ((i : ℕ) + 1) / chain (m + 1) σsq K i := by
    intro t i l
    exact integral_phaseScore_coolLaw hKcl.measurableSet
      (chain_pos hσ hball hfin i)
  have hsq : ∀ t i l, ∫ x, (g t i l x) ^ 2 ∂(ν t i l) ≤
      adaptiveGlobalPhaseVarFactor 1 N s₀ i *
        (chain (m + 1) σsq K ((i : ℕ) + 1) / chain (m + 1) σsq K i) ^ 2 := by
    intro t i l
    have hphase := Ttc.CV.adaptivePhaseScore_sq_moment_le hn hKc hKcl hKb hvol
      hball hfin hC hs₀ hbelow hKR i
    rw [integral_phaseScore_coolLaw hKcl.measurableSet (chain_pos hσ hball hfin i)] at hphase
    simpa only [N, m, σsq, ν, g] using hphase
  have hfactor : (∏ i : Fin m,
      (1 + (adaptiveGlobalPhaseVarFactor 1 N s₀ i - 1) / (k : ℝ))) ≤ Real.exp κ := by
    simp_rw [Ttc.CVEst.averaged_adaptiveGlobalPhaseVarFactor_eq]
    rw [Fin.prod_univ_eq_prod_range]
    exact prod_globalPhaseVarFactor_le_exp hk42 hN hs₀ hbelow hsamples
  exact @Ttc.CVPacked.packed_median_accuracy_exact r m k (Space n) _ ν hνall g hg hk hr
    (fun q => chain (m + 1) σsq K q)
    (fun i => adaptiveGlobalPhaseVarFactor 1 N s₀ i) κ ε p hκ hε
    (fun q => chain_pos hσ hball hfin q) hL2 hprod hmean hsq hfactor hbudget hp hrp

#print axioms packed_median_accuracy_adaptive_exact

end Ttc.CVAdaptive

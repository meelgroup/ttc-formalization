/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVEstimatorExactAccuracy
import Ttc.Volume.AdaptivePhaseScoreVariance
import Arlib.Convexity.GaussianCooling.TerminalPhase

/-!
# The adaptive CV estimator with the final Gaussian-to-uniform phase

The accelerated chunks estimate Gaussian-to-Gaussian ratios.  Cousins--Vempala then use one
separate terminal score to pass from the last Gaussian normalizer to `volume K` exactly.  Its
relative second moment is bounded by `exp (1/2)` once the last variance reaches the squared
circumscribed radius.  Averaging `k` terminal samples therefore contributes only the factor
`1 + (exp (1/2) - 1) / k`.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked

variable {n r k J : ℕ}

/-- Exact-law accuracy of the adaptive schedule including the paper's final
Gaussian-to-uniform ratio.  The target is exactly `volume K`, not a hot Gaussian proxy. -/
theorem packed_median_accuracy_adaptive_terminal_exact (hn : 2 ≤ n) (hk : 0 < k)
    (hr : 0 < r) {K : Set (Space n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s₀ κ ε p : ℝ} (hC : 0 < C) (hs₀ : 0 < s₀) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hk42 : 42 ≤ (k : ℝ))
    (hbelow : ∀ j < J, adaptiveChunkStart (C ^ 2 * n) s₀ j ≤ C ^ 2 * n)
    (hterminal : C ^ 2 * n ≤ adaptiveChunkStart (C ^ 2 * n) s₀ J)
    (hsamples : 7 * (J : ℝ) ≤ (k : ℝ) * κ)
    (hKR : K ⊆ closedBall 0 (C * √n))
    (hbudget : Real.exp (κ + (Real.exp (1 / 2) - 1) / (k : ℝ)) - 1 ≤ ε ^ 2 / 5)
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ)) :
    let m := adaptiveChunkOffset (C ^ 2 * n) s₀ J
    let σsq := adaptiveSigmaSq (C ^ 2 * n) s₀
    let ν : Fin r → Fin (m + 1) → Fin k → Measure (Space n) :=
      fun _ i _ => coolLaw (m + 1) σsq K i
    let g : Fin r → Fin (m + 1) → Fin k → Space n → ℝ :=
      fun _ i _ => phaseScore (m + 1) σsq K i
    1 - p ≤ (Arlib.Probability.runMeasure (packedPhaseLaw ν)).real
      {ω | Arlib.Probability.medianSel
        (fun t => chain (m + 1) σsq K 0 * ∏ i, Ttc.CVPacked.phaseAvg g t i ω)
          ∈ Ttc.relErr ε (volume K).toReal} := by
  dsimp only
  let N : ℝ := C ^ 2 * n
  let m := adaptiveChunkOffset N s₀ J
  let σsq := adaptiveSigmaSq N s₀
  let ν : Fin r → Fin (m + 1) → Fin k → Measure (Space n) :=
    fun _ i _ => coolLaw (m + 1) σsq K i
  let g : Fin r → Fin (m + 1) → Fin k → Space n → ℝ :=
    fun _ i _ => phaseScore (m + 1) σsq K i
  let c : Fin (m + 1) → ℝ := fun i =>
    if hi : (i : ℕ) < m then
      adaptiveGlobalPhaseVarFactor 1 N s₀ i
    else Real.exp (1 / 2)
  let κtot : ℝ := κ + (Real.exp (1 / 2) - 1) / (k : ℝ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  have hσ : ∀ q, 0 < σsq q := fun q => adaptiveSigmaSq_pos hN hs₀ q
  letI hνprob : ∀ (t : Fin r) (i : Fin (m + 1)) (l : Fin k),
      IsProbabilityMeasure (ν t i l) := fun t i l => by
    dsimp only [ν]
    exact coolLaw_isProbabilityMeasure hσ hball hfin i
  haveI hpackedProb : ∀ t i, IsProbabilityMeasure (packedPhaseLaw ν t i) := by
    intro t i
    exact @packedPhaseLaw_isProbabilityMeasure r (m + 1) k (Space n) _ ν hνprob t i
  haveI hrunProb : IsProbabilityMeasure
      (Arlib.Probability.runMeasure (packedPhaseLaw ν)) := by
    unfold Arlib.Probability.runMeasure
    infer_instance
  have hg : ∀ t i l, Measurable (g t i l) := by
    intro t i l
    exact measurable_phaseScore hKcl.measurableSet i
  have hscoreBound : ∀ t i l x,
      |g t i l x| ≤ Real.exp ((C * √n) ^ 2 / (2 * σsq i)) := by
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
  have hprodLp : ∀ t, MemLp (fun ω => ∏ i, Ttc.CVPacked.phaseAvg g t i ω) 2
      (Arlib.Probability.runMeasure (packedPhaseLaw ν)) := by
    intro t
    let B : ℝ := ∏ i : Fin (m + 1), Real.exp ((C * √n) ^ 2 / (2 * σsq i))
    have hmeas : Measurable (fun ω => ∏ i, Ttc.CVPacked.phaseAvg g t i ω) :=
      Finset.measurable_fun_prod _ fun i _ => Ttc.CVPacked.measurable_phaseAvg hg t i
    refine MemLp.of_bound hmeas.aestronglyMeasurable B ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ =>
      Ttc.CVPacked.abs_phaseAvg_le hk
        (fun _t _i _l x => hscoreBound t i _l x) t i ω
  have hmean : ∀ t i l, ∫ x, g t i l x ∂(ν t i l) =
      chain (m + 1) σsq K ((i : ℕ) + 1) / chain (m + 1) σsq K i := by
    intro t i l
    exact integral_phaseScore_coolLaw hKcl.measurableSet (chain_pos hσ hball hfin i)
  have hterminalSigma : N ≤ σsq m := by
    change N ≤ adaptiveSigmaSq N s₀ (adaptiveChunkOffset N s₀ J)
    rw [adaptiveSigmaSq_offset hN hs₀ J]
    simpa only [N] using hterminal
  have hR2 : (C * √n) ^ 2 ≤ σsq m := by
    have hsqrt : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnpos.le
    rw [mul_pow, hsqrt]
    simpa only [N] using hterminalSigma
  have hsq : ∀ t i l, ∫ x, (g t i l x) ^ 2 ∂(ν t i l) ≤
      c i * (chain (m + 1) σsq K ((i : ℕ) + 1) /
        chain (m + 1) σsq K i) ^ 2 := by
    intro t i l
    by_cases hi : (i : ℕ) < m
    · let i' : Fin m := ⟨i, hi⟩
      have hphase := Ttc.CV.adaptivePhaseScore_sq_moment_le hn hKc hKcl hKb hvol
        hball hfin hC hs₀ hbelow hKR i'
      rw [integral_phaseScore_coolLaw hKcl.measurableSet
        (chain_pos hσ hball hfin i')] at hphase
      simpa only [ν, g, c, hi, dif_pos, i'] using hphase
    · have him : (i : ℕ) = m := by omega
      have hilast : i = Fin.last m := by
        apply Fin.ext
        simpa using him
      subst i
      have hterm := coolLaw_sq_moment_le_terminal_paper (m := m + 1) hσ
        hKcl.measurableSet hball hfin hKR (i := m) (by exact le_rfl) hR2
      rw [integral_phaseScore_coolLaw hKcl.measurableSet
        (chain_pos hσ hball hfin m)] at hterm
      change ∫ x, phaseScore (m + 1) σsq K m x ^ 2 ∂(coolLaw (m + 1) σsq K m) ≤
        c (Fin.last m) *
          (chain (m + 1) σsq K (m + 1) / chain (m + 1) σsq K m) ^ 2
      rw [show c (Fin.last m) = Real.exp (1 / 2) by simp [c]]
      exact hterm
  have hinterior : (∏ i : Fin m,
      (1 + (adaptiveGlobalPhaseVarFactor 1 N s₀ i - 1) / (k : ℝ))) ≤ Real.exp κ := by
    simp_rw [Ttc.CVEst.averaged_adaptiveGlobalPhaseVarFactor_eq]
    rw [Fin.prod_univ_eq_prod_range]
    exact prod_globalPhaseVarFactor_le_exp hk42 hN hs₀ hbelow hsamples
  have htermExcess : 0 ≤ (Real.exp (1 / 2) - 1) / (k : ℝ) := by
    exact div_nonneg (by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]) (by positivity)
  have hfactor : (∏ i : Fin (m + 1),
      (1 + (c i - 1) / (k : ℝ))) ≤ Real.exp κtot := by
    rw [Fin.prod_univ_castSucc]
    have hcast : (∏ i : Fin m, (1 + (c i.castSucc - 1) / (k : ℝ))) =
        ∏ i : Fin m,
          (1 + (adaptiveGlobalPhaseVarFactor 1 N s₀ i - 1) / (k : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [c, Fin.coe_castSucc, i.isLt, dif_pos]
    rw [hcast]
    have hlast : c (Fin.last m) = Real.exp (1 / 2) := by
      simp [c]
    rw [hlast]
    calc
      (∏ i : Fin m,
          (1 + (adaptiveGlobalPhaseVarFactor 1 N s₀ i - 1) / (k : ℝ))) *
          (1 + (Real.exp (1 / 2) - 1) / (k : ℝ)) ≤
          Real.exp κ * Real.exp ((Real.exp (1 / 2) - 1) / (k : ℝ)) := by
            gcongr
            simpa [add_comm] using
              (Real.add_one_le_exp ((Real.exp (1 / 2) - 1) / (k : ℝ)))
      _ = Real.exp κtot := by rw [← Real.exp_add]
  have hκtot : 0 ≤ κtot := add_nonneg hκ htermExcess
  have hAend : chain (m + 1) σsq K (m + 1) = (volume K).toReal := chain_end _ _ _
  rw [← hAend]
  exact @Ttc.CVPacked.packed_median_accuracy_exact r (m + 1) k (Space n) _ ν hνprob
    g hg hk hr (fun q => chain (m + 1) σsq K q) c κtot ε p hκtot hε
    (fun q => chain_pos hσ hball hfin q) hL2 hprodLp hmean hsq hfactor hbudget hp hrp

#print axioms packed_median_accuracy_adaptive_terminal_exact

end Ttc.CVAdaptive

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVHybridPhaseScoreVariance
import Ttc.Volume.CVEstimatorExactAccuracy

/-!
# Exact-law accuracy on the source hybrid schedule

This is the exact-sampling estimator theorem for the same fixed-then-accelerated schedule
whose runtime is counted in `CVHybridRuntimeAccounting`.
-/

namespace Ttc.CVHybridSchedule

open MeasureTheory ProbabilityTheory Metric Set
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked

variable {n r k J : Nat}

theorem packed_median_accuracy_exact (hn : 3 <= n) (hk : 0 < k) (hr : 0 < r)
    {K : Set (Space n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s0 kappaCold kappaHot eps p : Real} (hC : 0 < C) (hs0 : 0 < s0)
    (hkappaCold : 0 <= kappaCold) (hkappaHot : 0 <= kappaHot) (heps : 0 < eps)
    (hk42 : 42 <= (k : Real))
    (hcoldBudget : 2 * (coldPhases n s0 : Real) / (n : Real) <= k * kappaCold)
    (hbelow : ∀ j < J,
      adaptiveChunkStart (C ^ 2 * n) (coldEnd n s0) j <= C ^ 2 * n)
    (hhotBudget : 7 * (J : Real) <= k * kappaHot)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (hbudget : Real.exp (kappaCold + kappaHot) - 1 <= eps ^ 2 / 5)
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) <= (r : Real)) :
    let m := coldPhases n s0 +
      adaptiveChunkOffset (C ^ 2 * n) (coldEnd n s0) J
    let sched := sigmaSq n (C ^ 2 * n) s0
    let nu : Fin r -> Fin m -> Fin k -> Measure (Space n) :=
      fun _ i _ => coolLaw (m + 1) sched K i
    let g : Fin r -> Fin m -> Fin k -> Space n -> Real :=
      fun _ i _ => phaseScore (m + 1) sched K i
    1 - p <= (Arlib.Probability.runMeasure (packedPhaseLaw nu)).real
      {omega | Arlib.Probability.medianSel
        (fun t => chain (m + 1) sched K 0 *
          ∏ i, Ttc.CVPacked.phaseAvg g t i omega)
          ∈ Ttc.relErr eps (chain (m + 1) sched K m)} := by
  dsimp only
  let N : Real := C ^ 2 * n
  let m := coldPhases n s0 + adaptiveChunkOffset N (coldEnd n s0) J
  let sched := sigmaSq n N s0
  let nu : Fin r -> Fin m -> Fin k -> Measure (Space n) :=
    fun _ i _ => coolLaw (m + 1) sched K i
  let g : Fin r -> Fin m -> Fin k -> Space n -> Real :=
    fun _ i _ => phaseScore (m + 1) sched K i
  have hn1 : 1 <= n := by omega
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  have hsched : ∀ q, 0 < sched q := fun q => sigmaSq_pos hn1 hN hs0 q
  letI hnuProb (t : Fin r) (i : Fin m) (l : Fin k) :
      IsProbabilityMeasure (nu t i l) := by
    dsimp only [nu]
    exact coolLaw_isProbabilityMeasure hsched hball hfin i
  have hnuAll : ∀ t i l, IsProbabilityMeasure (nu t i l) := fun t i l => hnuProb t i l
  haveI hpackedProb : ∀ t i, IsProbabilityMeasure (packedPhaseLaw nu t i) := by
    intro t i
    exact @packedPhaseLaw_isProbabilityMeasure r m k (Space n) _ nu hnuAll t i
  haveI hrunProb : IsProbabilityMeasure
      (Arlib.Probability.runMeasure (packedPhaseLaw nu)) := by
    unfold Arlib.Probability.runMeasure
    infer_instance
  have hg : ∀ t i l, Measurable (g t i l) := by
    intro t i l
    exact measurable_phaseScore hKcl.measurableSet i
  have hscoreBound : ∀ t i l x,
      |g t i l x| <= Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sched i)) := by
    intro t i l x
    rw [abs_of_nonneg (phaseScore_nonneg (m + 1) sched K i x)]
    exact phaseScore_le hsched hKR i x
  have hL2 : ∀ t i l, MemLp (g t i l) 2 (nu t i l) := by
    intro t i l
    letI : IsProbabilityMeasure (nu t i l) := hnuProb t i l
    exact MemLp.of_bound (hg t i l).aestronglyMeasurable
      (Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sched i)))
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hscoreBound t i l x)
  have hprod : ∀ t, MemLp (fun omega => ∏ i, Ttc.CVPacked.phaseAvg g t i omega) 2
      (Arlib.Probability.runMeasure (packedPhaseLaw nu)) := by
    intro t
    let B : Real := ∏ i : Fin m, Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sched i))
    have hmeas : Measurable (fun omega => ∏ i, Ttc.CVPacked.phaseAvg g t i omega) :=
      Finset.measurable_fun_prod _ fun i _ => Ttc.CVPacked.measurable_phaseAvg hg t i
    refine MemLp.of_bound hmeas.aestronglyMeasurable B ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ =>
      Ttc.CVPacked.abs_phaseAvg_le hk
        (fun _t _i _l x => hscoreBound t i _l x) t i omega
  have hmean : ∀ t i l, ∫ x, g t i l x ∂(nu t i l) =
      chain (m + 1) sched K ((i : Nat) + 1) / chain (m + 1) sched K i := by
    intro t i l
    exact integral_phaseScore_coolLaw hKcl.measurableSet
      (chain_pos hsched hball hfin i)
  have hsq : ∀ t i l, ∫ x, (g t i l x) ^ 2 ∂(nu t i l) <=
      phaseVarFactor n 1 N s0 i *
        (chain (m + 1) sched K ((i : Nat) + 1) /
          chain (m + 1) sched K i) ^ 2 := by
    intro t i l
    have hphase := phaseScore_sq_moment_le hn hKc hKcl hKb hvol hball hfin hC hs0
      hbelow hKR i
    dsimp only at hphase
    rw [integral_phaseScore_coolLaw hKcl.measurableSet
      (chain_pos hsched hball hfin i)] at hphase
    simpa only [N, m, sched, nu, g] using hphase
  have hfactor : (∏ i : Fin m,
      (1 + (phaseVarFactor n 1 N s0 i - 1) / (k : Real))) <=
      Real.exp (kappaCold + kappaHot) := by
    simp_rw [averaged_phaseVarFactor_eq]
    rw [Fin.prod_univ_eq_prod_range]
    exact prod_phaseVarFactor_le_exp hn1 hk42 hN hs0 hcoldBudget hbelow hhotBudget
  exact @Ttc.CVPacked.packed_median_accuracy_exact r m k (Space n) _ nu hnuAll g hg hk hr
    (fun q => chain (m + 1) sched K q) (fun i => phaseVarFactor n 1 N s0 i)
    (kappaCold + kappaHot) eps p (add_nonneg hkappaCold hkappaHot) heps
    (fun q => chain_pos hsched hball hfin q) hL2 hprod hmean hsq hfactor hbudget hp hrp

end Ttc.CVHybridSchedule

#print axioms Ttc.CVHybridSchedule.packed_median_accuracy_exact

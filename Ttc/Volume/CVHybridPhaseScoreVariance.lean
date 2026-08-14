/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVHybridVarianceBudget
import Ttc.Volume.AdaptivePhaseScoreVariance

/-!
# Per-phase variance for the hybrid CV schedule

The cold block uses the fixed-rate Cousins--Vempala estimate.  The hot block reuses the
localization-free compact-convex estimate at the actual chunk-constant accelerated rate.
-/

namespace Ttc.CVHybridSchedule

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked

/-- Every nonterminal hybrid phase has the raw relative-second-moment factor recorded by
`phaseVarFactor 1`. -/
theorem phaseScore_sq_moment_le {n J : Nat} (hn : 3 <= n)
    {K : Set (EuclSpace n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s0 : Real} (hC : 0 < C) (hs0 : 0 < s0)
    (hbelow : ∀ j < J,
      adaptiveChunkStart (C ^ 2 * n) (coldEnd n s0) j <= C ^ 2 * n)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (i : Fin (coldPhases n s0 +
      adaptiveChunkOffset (C ^ 2 * n) (coldEnd n s0) J)) :
    let m := coldPhases n s0 +
      adaptiveChunkOffset (C ^ 2 * n) (coldEnd n s0) J
    let sched := sigmaSq n (C ^ 2 * n) s0
    ∫ x, phaseScore (m + 1) sched K i x ^ 2 ∂(coolLaw (m + 1) sched K i) <=
      phaseVarFactor n 1 (C ^ 2 * n) s0 i *
        (∫ x, phaseScore (m + 1) sched K i x ∂(coolLaw (m + 1) sched K i)) ^ 2 := by
  dsimp only
  let N : Real := C ^ 2 * n
  let c : Nat := coldPhases n s0
  let aoff : Nat := adaptiveChunkOffset N (coldEnd n s0) J
  let m : Nat := c + aoff
  let sched := sigmaSq n N s0
  have hn1 : 1 <= n := by omega
  have hn2 : 2 <= n := by omega
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  have hend : 0 < coldEnd n s0 := coldEnd_pos hn1 hs0
  have hsched : ∀ q, 0 < sched q := fun q => sigmaSq_pos hn1 hN hs0 q
  have hi : (i : Nat) + 1 < m + 1 := by
    have hii := i.isLt
    change (i : Nat) < m at hii
    omega
  by_cases hicold : (i : Nat) < c
  · have hrate : sched ((i : Nat) + 1) = sched i * (1 + 1 / (n : Real)) := by
      have hs := sigmaSq_succ hn1 hN hs0 i
      rw [phaseRate, if_pos hicold] at hs
      exact hs
    have hraw := coolLaw_sq_moment_le hsched hKc hKcl.measurableSet hball hfin hi hn hrate
    rw [phaseVarFactor, if_pos hicold]
    norm_num at hraw ⊢
    exact hraw
  · let t : Nat := (i : Nat) - c
    have hit : (i : Nat) = c + t := by dsimp [t]; omega
    have ht : t < aoff := by
      have hii := i.isLt
      change (i : Nat) < c + aoff at hii
      omega
    have hchunk : adaptivePhaseChunk N (coldEnd n s0) t < J :=
      adaptivePhaseChunk_lt_of_lt_offset hN hend ht
    let u : Real := adaptiveSigmaSq N (coldEnd n s0) t
    let alpha : Real := adaptivePhaseRate N (coldEnd n s0) t
    have hu : 0 < u := adaptiveSigmaSq_pos hN hend t
    have hstart : 0 < adaptiveChunkStart N (coldEnd n s0)
        (adaptivePhaseChunk N (coldEnd n s0) t) := adaptiveChunkStart_pos hN hend _
    have hstartu : adaptiveChunkStart N (coldEnd n s0)
        (adaptivePhaseChunk N (coldEnd n s0) t) <= u :=
      adaptiveChunkStart_le_geom hN hend _ (adaptiveLocalPhase N (coldEnd n s0) t)
    have halpha : alpha = adaptiveChunkStart N (coldEnd n s0)
        (adaptivePhaseChunk N (coldEnd n s0) t) / (2 * N) := rfl
    have ha0 : 0 <= alpha := by rw [halpha]; positivity
    have ha2 : alpha <= 1 / 2 := by
      rw [halpha, div_le_iff₀ (by positivity : 0 < 2 * N)]
      nlinarith [hbelow _ hchunk]
    have hsched_i : sched i = u := by
      change sigmaSq n N s0 i = adaptiveSigmaSq N (coldEnd n s0) t
      rw [sigmaSq, if_neg hicold]
    have hrate : sched ((i : Nat) + 1) = sched i * (1 + alpha) := by
      have hs := sigmaSq_succ hn1 hN hs0 i
      rw [phaseRate, if_neg hicold] at hs
      simpa only [t] using hs
    have hraw := Ttc.CV.compactConvex_phaseScore_sq_moment_le hn2 hsched hKc hKcl hKb
      hvol hball hfin hi ha0 ha2 hrate hKR
    have hexp : Real.exp (2 * N * alpha ^ 2 / (u * (1 + alpha))) <= 1 + u / N :=
      chunkConstantRate_exp_le hN hstart (hbelow _ hchunk) hstartu halpha
    have hR : (C * Real.sqrt (n : Real)) ^ 2 = N := by
      dsimp [N]
      rw [mul_pow, Real.sq_sqrt hnR.le]
    have hsched_succ : sched ((i : Nat) + 1) = u * (1 + alpha) := by
      rw [hrate, hsched_i]
    rw [hR, hsched_succ] at hraw
    rw [phaseVarFactor, if_neg hicold]
    rw [adaptiveGlobalPhaseVarFactor]
    norm_num
    change _ <= (1 + u / N) * _
    exact hraw.trans (mul_le_mul_of_nonneg_right hexp (sq_nonneg _))

end Ttc.CVHybridSchedule

#print axioms Ttc.CVHybridSchedule.phaseScore_sq_moment_le

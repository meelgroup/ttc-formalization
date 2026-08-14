/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVAdaptiveTerminalExact
import Ttc.Volume.AdaptiveChunkEndpoints

/-!
# Exact CV accuracy at the first terminal adaptive chunk

This removes the two schedule-range hypotheses from
`packed_median_accuracy_adaptive_terminal_exact`: the chunk index is chosen to be the
first one whose actual start reaches `C^2 n`, so minimality supplies every earlier bound
and `Nat.find_spec` supplies the terminal bound.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive

variable {n r k : ℕ}

/-- Exact-law CV volume accuracy when the accelerated block stops at its first terminal
chunk and is followed by the Gaussian-to-uniform phase. -/
theorem packed_median_accuracy_adaptive_first_terminal_exact
    (hn : 2 ≤ n) (hk : 0 < k) (hr : 0 < r)
    {K : Set (Space n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s₀ κ ε p : ℝ} (hC : 0 < C) (hs₀ : 0 < s₀) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hk42 : 42 ≤ (k : ℝ))
    (hsamples : 7 * (adaptiveTerminalChunk (C ^ 2 * n) s₀ : ℝ) ≤ (k : ℝ) * κ)
    (hKR : K ⊆ closedBall 0 (C * √n))
    (hbudget : Real.exp (κ + (Real.exp (1 / 2) - 1) / (k : ℝ)) - 1 ≤ ε ^ 2 / 5)
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ)) :
    let N : ℝ := C ^ 2 * n
    let J := adaptiveTerminalChunk N s₀
    let m := adaptiveChunkOffset N s₀ J
    let σsq := adaptiveSigmaSq N s₀
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
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  have hbelow : ∀ j < adaptiveTerminalChunk N s₀, adaptiveChunkStart N s₀ j ≤ N := by
    intro j hj
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs₀ hj).le
  have hterminal : N ≤ adaptiveChunkStart N s₀ (adaptiveTerminalChunk N s₀) :=
    target_le_adaptiveTerminalChunk hN hs₀
  exact packed_median_accuracy_adaptive_terminal_exact hn hk hr hKc hKcl hKb hvol
    hball hfin hC hs₀ hκ hε hk42 hbelow hterminal hsamples hKR hbudget hp hrp

#print axioms packed_median_accuracy_adaptive_first_terminal_exact

end Ttc.CVAdaptive

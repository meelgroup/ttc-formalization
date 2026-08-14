/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVAdaptiveRuntime
import Arlib.Convexity.GaussianCooling.ChunkedSchedule

/-!
# The source two-regime Cousins--Vempala schedule

The source algorithm does **not** use the accelerated rate from the initial variance.
It first uses the fixed rate `1/n` until variance at least `1`, and only then uses the
variance-adaptive chunks.  Starting the adaptive chunks at the exponentially small cold
variance gives `O(N/s0)` phases and loses a factor `n`; starting them at variance at least
one gives `O(N)` hot phases, as required by Theorem 1.1.

This file constructs the concatenated schedule and proves the phase-count bound

`2 n log(1/s0) + 1 + 5 N + 2`.
-/

namespace Ttc.CVHybridSchedule

open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive Ttc.CVAdaptive

/-- Number of fixed-rate phases.  The `max` makes the definition total when the supplied
start is already hot. -/
noncomputable def coldPhases (n : Nat) (s0 : Real) : Nat :=
  ⌈max 0 (Real.log (1 / s0)) / Real.log (1 + 1 / (n : Real))⌉₊

/-- Endpoint of the fixed-rate block. -/
noncomputable def coldEnd (n : Nat) (s0 : Real) : Real :=
  geomSchedule s0 (1 / (n : Real)) (coldPhases n s0)

theorem coldPhases_cast_lt_add_one {n : Nat} (hn : 1 <= n) (s0 : Real) :
    (coldPhases n s0 : Real) <
      2 * (n : Real) * max 0 (Real.log (1 / s0)) + 1 := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnR1 : (1 : Real) <= n := by exact_mod_cast hn
  have ha0 : 0 <= 1 / (n : Real) := by positivity
  have ha1 : 1 / (n : Real) <= 1 := by
    rw [div_le_one hnR]
    exact hnR1
  have hlogLower : 1 / (2 * (n : Real)) <= Real.log (1 + 1 / (n : Real)) := by
    have h := Arlib.GaussianCooling.half_le_log_one_add ha0 ha1
    rw [show 1 / (2 * (n : Real)) = (1 / (n : Real)) / 2 by field_simp]
    exact h
  have hlogBase : 0 < Real.log (1 + 1 / (n : Real)) :=
    Real.log_pos (lt_add_of_pos_right 1 (by positivity))
  have hone : 1 <= 2 * (n : Real) * Real.log (1 + 1 / (n : Real)) := by
    have h := mul_le_mul_of_nonneg_left hlogLower
      (show 0 <= 2 * (n : Real) by positivity)
    have hcancel : 2 * (n : Real) * (1 / (2 * (n : Real))) = 1 := by
      field_simp
    rwa [hcancel] at h
  have hratio : max 0 (Real.log (1 / s0)) /
      Real.log (1 + 1 / (n : Real)) <=
      2 * (n : Real) * max 0 (Real.log (1 / s0)) := by
    rw [div_le_iff₀ hlogBase]
    have hmax : 0 <= max 0 (Real.log (1 / s0)) := le_max_left _ _
    nlinarith [mul_nonneg hmax (sub_nonneg.2 hone)]
  have hceil := Nat.ceil_lt_add_one
    (show 0 <= max 0 (Real.log (1 / s0)) /
      Real.log (1 + 1 / (n : Real)) by positivity)
  unfold coldPhases
  exact hceil.trans_le (by linarith)

theorem coldEnd_pos {n : Nat} (hn : 1 <= n) {s0 : Real} (hs0 : 0 < s0) :
    0 < coldEnd n s0 := by
  unfold coldEnd
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  exact geomSchedule_pos hs0 (by positivity) _

/-- The fixed block reaches variance one by its declared phase count. -/
theorem one_le_coldEnd {n : Nat} (hn : 1 <= n) {s0 : Real}
    (hs0 : 0 < s0) (hs01 : s0 <= 1) :
    1 <= coldEnd n s0 := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnR1 : (1 : Real) <= n := by exact_mod_cast hn
  have ha0 : 0 <= 1 / (n : Real) := by positivity
  have ha1 : 1 / (n : Real) <= 1 := by
    rw [div_le_one hnR]
    exact hnR1
  have hlogLower : 1 / (2 * (n : Real)) <= Real.log (1 + 1 / (n : Real)) := by
    have h := Arlib.GaussianCooling.half_le_log_one_add ha0 ha1
    rw [show 1 / (2 * (n : Real)) = (1 / (n : Real)) / 2 by field_simp]
    exact h
  have hlog0 : 0 <= Real.log (1 / s0) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hs0]
    simpa using hs01
  have hp : Real.log (1 / s0) / Real.log (1 + 1 / (n : Real)) <=
      (coldPhases n s0 : Real) := by
    rw [coldPhases, max_eq_right hlog0]
    exact Nat.le_ceil _
  have hprod : Real.log (1 / s0) <=
      (coldPhases n s0 : Real) * Real.log (1 + 1 / (n : Real)) := by
    rw [div_le_iff₀ (Real.log_pos
      (lt_add_of_pos_right 1 (by positivity)))] at hp
    exact hp
  have hbase : 0 < 1 + 1 / (n : Real) := by positivity
  have hexp : 1 / s0 <= (1 + 1 / (n : Real)) ^ coldPhases n s0 := by
    calc
      1 / s0 = Real.exp (Real.log (1 / s0)) := by
        rw [Real.exp_log]
        positivity
      _ <= Real.exp ((coldPhases n s0 : Real) *
          Real.log (1 + 1 / (n : Real))) := Real.exp_le_exp.2 hprod
      _ = (1 + 1 / (n : Real)) ^ coldPhases n s0 := by
        rw [Real.exp_nat_mul, Real.exp_log hbase]
  unfold coldEnd geomSchedule
  have := mul_le_mul_of_nonneg_left hexp hs0.le
  have hs0inv : s0 * (1 / s0) = 1 := by field_simp
  nlinarith

/-- The fixed-rate block stops immediately after crossing one, so it overshoots by less
than a single cooling factor. -/
theorem coldEnd_lt_one_add_inv {n : Nat} (hn : 1 <= n) {s0 : Real}
    (hs0 : 0 < s0) (hs01 : s0 <= 1) :
    coldEnd n s0 < 1 + 1 / (n : Real) := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  let b : Real := 1 + 1 / (n : Real)
  have hb : 1 < b := by
    dsimp [b]
    exact lt_add_of_pos_right 1 (by positivity)
  have hb0 : 0 < b := one_pos.trans hb
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hlog0 : 0 <= Real.log (1 / s0) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hs0]
    simpa using hs01
  have hceil := Nat.ceil_lt_add_one
    (show 0 <= max 0 (Real.log (1 / s0)) / Real.log b by positivity)
  have hp : (coldPhases n s0 : Real) < Real.log (1 / s0) / Real.log b + 1 := by
    simpa only [coldPhases, b, max_eq_right hlog0] using hceil
  have hpLog : (coldPhases n s0 : Real) * Real.log b <
      Real.log (1 / s0) + Real.log b := by
    have := mul_lt_mul_of_pos_right hp hlogb
    field_simp at this ⊢
    linarith
  have hpow : b ^ coldPhases n s0 < (1 / s0) * b := by
    have hexp := Real.exp_lt_exp.2 hpLog
    rw [Real.exp_nat_mul, Real.exp_log hb0,
      Real.exp_add, Real.exp_log (by positivity : 0 < 1 / s0), Real.exp_log hb0] at hexp
    exact hexp
  unfold coldEnd geomSchedule
  change s0 * b ^ coldPhases n s0 < b
  have := mul_lt_mul_of_pos_left hpow hs0
  have hs0inv : s0 * (1 / s0) = 1 := by field_simp
  nlinarith

/-- The source schedule: fixed cooling before `coldPhases`, then the already-formalized
adaptive chunks starting at the actual fixed-block endpoint. -/
noncomputable def sigmaSq (n : Nat) (N s0 : Real) (i : Nat) : Real :=
  if i < coldPhases n s0 then
    geomSchedule s0 (1 / (n : Real)) i
  else
    adaptiveSigmaSq N (coldEnd n s0) (i - coldPhases n s0)

theorem sigmaSq_pos {n : Nat} (hn : 1 <= n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (i : Nat) :
    0 < sigmaSq n N s0 i := by
  unfold sigmaSq
  split_ifs
  · have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    exact geomSchedule_pos hs0 (by positivity) _
  · exact adaptiveSigmaSq_pos hN (coldEnd_pos hn hs0) _

/-- The concatenation has no jump: the first adaptive phase is exactly the fixed-block
endpoint. -/
theorem sigmaSq_cold_boundary {n : Nat} (hn : 1 <= n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) :
    sigmaSq n N s0 (coldPhases n s0) = coldEnd n s0 := by
  rw [sigmaSq, if_neg (Nat.lt_irrefl _), Nat.sub_self]
  have hcold := coldEnd_pos hn hs0
  simpa [coldEnd, adaptiveChunkStart] using adaptiveSigmaSq_offset hN hcold 0

/-- Total number of nonterminal phases in the hybrid schedule. -/
noncomputable def terminalPhases (n : Nat) (N s0 : Real) : Nat :=
  coldPhases n s0 +
    adaptiveChunkOffset N (coldEnd n s0)
      (adaptiveTerminalChunk N (coldEnd n s0))

/-- Source-faithful phase count: `O(n log(1/s0) + N)`, rather than the
`O(N/s0)` count obtained by accelerating directly from the cold start. -/
theorem terminalPhases_lt {n : Nat} (hn : 1 <= n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hs01 : s0 <= 1) :
    (terminalPhases n N s0 : Real) <
      2 * (n : Real) * Real.log (1 / s0) + 5 * N + 3 := by
  have hcoldCast := coldPhases_cast_lt_add_one hn s0
  have hlog0 : 0 <= Real.log (1 / s0) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hs0]
    simpa using hs01
  rw [max_eq_right hlog0] at hcoldCast
  have hend1 := one_le_coldEnd hn hs0 hs01
  have hend0 := coldEnd_pos hn hs0
  have hhot := adaptiveTerminalOffset_lt_five_mul_div_add_two hN hend0
  have hratio : 5 * N / coldEnd n s0 <= 5 * N := by
    rw [div_le_iff₀ hend0]
    nlinarith
  unfold terminalPhases
  push_cast
  linarith

end Ttc.CVHybridSchedule

#print axioms Ttc.CVHybridSchedule.one_le_coldEnd
#print axioms Ttc.CVHybridSchedule.coldEnd_lt_one_add_inv
#print axioms Ttc.CVHybridSchedule.sigmaSq_pos
#print axioms Ttc.CVHybridSchedule.sigmaSq_cold_boundary
#print axioms Ttc.CVHybridSchedule.terminalPhases_lt

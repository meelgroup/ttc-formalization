/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVHybridVarianceBudget
import Ttc.Volume.CVCorrectedRuntime

/-!
# Runtime accounting for the source two-regime schedule

The fixed block has `coldPhases n s0` phases and the accelerated block starts only after
the variance has crossed one.  Consequently the hot `sigma^2` cancellation costs `O(NJ)`,
while the cold phase count is `O(n log(1/s0))`.  This is the deterministic arithmetic in
the runtime paragraph after `lem:accuracy`; attaching it to a query-count random variable
is deliberately a separate execution-semantics theorem.
-/

namespace Ttc.CVHybridSchedule

open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive Ttc.CVAdaptive
open Ttc.CVCorrectedRuntime

/-- Proposal accounting for the actual source hybrid schedule.  The first summand charges
the fixed block uniformly; the second uses the accelerated `sigma^2`-weighted charge. -/
noncomputable def proposalAccounting
    (n : Nat) (N s0 : Real) (J k r : Nat) (q : Real) : Real :=
  (r : Real) * k *
    (2 * coldPhases n s0 +
      4 * q ^ 2 * (n : Real) ^ 2 * adaptiveSourceHotSigmaMass N (coldEnd n s0) J)

/-- Exact source cancellation: after the fixed block reaches variance one, the accelerated
part costs at most `24 q^2 n^2 N J`, and the fixed part retains its logarithmic count. -/
theorem proposalAccounting_le {n J k r : Nat} (hn : 1 <= n) {N s0 q : Real}
    (hN : 0 < N) (hs0 : 0 < s0)
    (hbelow : ∀ j < J, adaptiveChunkStart N (coldEnd n s0) j <= N) :
    proposalAccounting n N s0 J k r q <=
      (r : Real) * k *
        (2 * coldPhases n s0 + 24 * q ^ 2 * (n : Real) ^ 2 * N * J) := by
  have hend := coldEnd_pos hn hs0
  have hhot := adaptiveSourceHotSigmaMass_le hN hend hbelow
  unfold proposalAccounting
  have hrk : 0 <= (r : Real) * k := by positivity
  apply mul_le_mul_of_nonneg_left _ hrk
  have hcoef : 0 <= 4 * q ^ 2 * (n : Real) ^ 2 := by positivity
  calc
    2 * (coldPhases n s0 : Real) +
        4 * q ^ 2 * (n : Real) ^ 2 *
          adaptiveSourceHotSigmaMass N (coldEnd n s0) J <=
      2 * (coldPhases n s0 : Real) +
        4 * q ^ 2 * (n : Real) ^ 2 * (6 * N * J) := by
          gcongr
    _ = 2 * (coldPhases n s0 : Real) +
        24 * q ^ 2 * (n : Real) ^ 2 * N * J := by ring

/-- Real-valued source phase-count bound, in the form used by runtime multiplication. -/
theorem terminalPhases_cast_lt {n : Nat} (hn : 1 <= n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hs01 : s0 <= 1) :
    (terminalPhases n N s0 : Real) <
      2 * (n : Real) * Real.log (1 / s0) + 5 * N + 3 :=
  terminalPhases_lt hn hN hs0 hs01

/-- In the paper's polynomial endpoint branch, the fixed starting variance is exactly
`1/(16n)`, hence the hybrid phase count is `O(n log n + N)`. -/
theorem terminalPhases_source_lt {n : Nat} (hn : 1 <= n) {N eta : Real}
    (hN : 0 < N) (heta : 0 < eta)
    (hsource : (1 / 2 : Real) ^ n <= eta) :
    (terminalPhases n N (polynomialEndpointSigmaSq n eta) : Real) <
      2 * (n : Real) * Real.log (16 * n) + 5 * N + 3 := by
  have hs0 := polynomialEndpointSigmaSq_pos hn heta
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnR1 : (1 : Real) <= n := by exact_mod_cast hn
  have hs01 : polynomialEndpointSigmaSq n eta <= 1 := by
    rw [polynomialEndpointSigmaSq, if_pos hsource]
    unfold operationalEndpointSigmaSq
    rw [div_le_one (by positivity : 0 < 16 * (n : Real))]
    nlinarith
  have h := terminalPhases_lt hn hN hs0 hs01
  rw [polynomialEndpointSigmaSq, if_pos hsource] at h ⊢
  unfold operationalEndpointSigmaSq at h ⊢
  have hinv : 1 / (1 / (16 * (n : Real))) = 16 * (n : Real) := by field_simp
  rw [hinv] at h
  exact h

end Ttc.CVHybridSchedule

#print axioms Ttc.CVHybridSchedule.proposalAccounting_le
#print axioms Ttc.CVHybridSchedule.terminalPhases_source_lt

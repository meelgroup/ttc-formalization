/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.ChargedCV18.OperationCost

/-!
# The charged CV18 program: equivalence and costs

arlib-community proves CV18's Theorem 1.1 for its `cv18Program`, which counts membership
queries only (`cv18TheoremOneOne`).  The charged `cv18Program` of this directory is the
same algorithm with its arithmetic run through arlib's charged operations.  This file
connects the two and adds the arithmetic cost.

* **Equivalence** (`cv18Program_erase_refines`): deleting the charges from the charged
  program gives arlib-community's `cv18Program`, except that each random point is drawn
  from random numbers (a standard Gaussian vector, a uniform number) with the same law.
  Hence the two have the same output law on every body (`cv18Program_runEstimate_eq`),
  and the charged one makes no more membership queries (`cv18Program_queryCost_le_community`).
* **Theorem 1.1** for the charged program follows from arlib-community's
  (`cv18Program_accuracy`, `cv18Program_queryCost_le`).
* **Arithmetic cost** (`cv18_operation_cost`): an explicit bound on the operations, besides
  the membership calls, on every execution.
* **Queries answered by computation** (`cv18_answerWith_volume_accuracy`,
  `cv18_answerWith_cost`): a caller that decides membership by arithmetic, as TTC does for
  a polytope, runs the same program with each query replaced by that arithmetic.
-/

open MeasureTheory

namespace ttc.ChargedCV18

open ArlibCommunity.Algorithms.CV18

/-! ## Equivalence with arlib-community's program -/

/-- **Deleting the charges gives arlib-community's `cv18Program`**, up to how the random
points are drawn: each point is drawn from random numbers pushed through arithmetic,
with the law arlib-community's program draws it from. -/
theorem cv18Program_erase_refines (q : VolumeParams) :
    Refines (ArlibCommunity.Algorithms.CV18.cv18Program q) (cv18Program q).erase := by
  rw [ArlibCommunity.Algorithms.CV18.cv18Program_eq]
  exact cv18Program_refines q

/-- **Same output law.**  On every body with a correct membership oracle, the charged
program and arlib-community's `cv18Program` have the same output law. -/
theorem cv18Program_runEstimate_eq (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) :
    (cv18Program q).runEstimate oracle.query =
      (ArlibCommunity.Algorithms.CV18.cv18Program q).runEstimate oracle.query := by
  have hmeas : (ArlibCommunity.Algorithms.CV18.cv18Program q).StronglyMeasurable
      oracle.query := by
    rw [ArlibCommunity.Algorithms.CV18.cv18Program_eq]
    exact (amplifyOracleProgram_semantics figureOneFinalScheduledCappedValueProgram q
      oracle.query (figureOneFinalScheduledCappedValueProgram_stronglyMeasurable q I oracle)).1
  rw [← ChargedProgram.runEstimate_erase,
    (cv18Program_erase_refines q).runEstimate_eq oracle.query hmeas]

/-- **No more membership queries** than arlib-community's `cv18Program`, on every
execution. -/
theorem cv18Program_queryCost_le_community (q : VolumeParams) :
    (cv18Program q).queryCost ≤ (ArlibCommunity.Algorithms.CV18.cv18Program q).queryCost := by
  rw [← ChargedProgram.queryCost_erase]
  exact (cv18Program_erase_refines q).queryCost_le

/-! ## Theorem 1.1 for the charged program -/

/-- **Cousins–Vempala 2018, Theorem 1.1, accuracy**, for the charged program: on a
well-rounded body with a correct membership oracle, the estimate is within relative error
`ε` of the volume with probability at least `1 - p`.  It is arlib-community's
`cv18TheoremOneOne`, through the equal output laws. -/
theorem cv18Program_accuracy (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I) :
    1 - q.p ≤ outcomeProbability ((cv18Program q).runEstimate oracle.query)
      (accurateOutcome q I) := by
  rw [cv18Program_runEstimate_eq q I oracle]
  exact (cv18TheoremOneOne q I oracle hrounded).1

/-- The `confidenceRepetitions q` runs, each capped at `⌈C₀ · rate q⌉` calls, make at most
`⌈9 (C₀ + 1) · rate q · protectedLog (1/p)⌉` calls together. -/
private theorem amplifiedCalls_le_of_rate (rate : VolumeParams → ℝ) (hrate : ∀ q, 1 ≤ rate q)
    (C₀ : ℝ) (hC₀ : 0 < C₀) (q : VolumeParams) {B : ℕ}
    (hB : B ≤ Nat.ceil (C₀ * rate q)) :
    confidenceRepetitions q * B ≤
      Nat.ceil (9 * (C₀ + 1) * (rate q * protectedLog (1 / q.p))) := by
  let R : ℝ := rate q
  let L : ℝ := protectedLog (1 / q.p)
  let m : ℕ := confidenceRepetitions q
  have hR : 1 ≤ R := hrate q
  have hL : 1 ≤ L := le_max_left _ _
  have hm_nonneg : 0 ≤ 8 * L := by positivity
  have hm_real : (m : ℝ) ≤ 9 * L := by
    have hceil : (m : ℝ) < 8 * L + 1 := by
      simpa [m, confidenceRepetitions, L] using Nat.ceil_lt_add_one hm_nonneg
    linarith
  have hraw_nonneg : 0 ≤ C₀ * R := mul_nonneg hC₀.le (by linarith)
  have hceil_real : ((Nat.ceil (C₀ * R) : ℕ) : ℝ) < C₀ * R + 1 := by
    simpa using Nat.ceil_lt_add_one hraw_nonneg
  have hB_real : (B : ℝ) ≤ (C₀ + 1) * R := by
    have hB' : B ≤ Nat.ceil (C₀ * R) := by simpa [R] using hB
    have hBceil : (B : ℝ) ≤ (Nat.ceil (C₀ * R) : ℝ) := by
      exact_mod_cast hB'
    nlinarith
  have hreal : ((m * B : ℕ) : ℝ) ≤ 9 * (C₀ + 1) * (rate q * protectedLog (1 / q.p)) := by
    rw [Nat.cast_mul]
    calc
      (m : ℝ) * (B : ℝ) ≤ (9 * L) * ((C₀ + 1) * R) :=
        mul_le_mul hm_real hB_real (Nat.cast_nonneg _) (by positivity)
      _ = 9 * (C₀ + 1) * (rate q * protectedLog (1 / q.p)) := by
        dsimp [R, L]
        ring
  exact_mod_cast le_trans hreal
    (Nat.le_ceil (9 * (C₀ + 1) * (rate q * protectedLog (1 / q.p))))

/-- **Cousins–Vempala 2018, Theorem 1.1, membership queries**, for the charged program:
on every body and every execution, at most `⌈queryRate q⌉` membership calls. -/
theorem cv18Program_queryCost_le (q : VolumeParams) :
    (cv18Program q).queryCost ≤ Nat.ceil (queryRate q) := by
  refine (cv18Program_queryCost_le_community q).trans ?_
  rw [ArlibCommunity.Algorithms.CV18.cv18Program_eq]
  refine (amplifyOracleProgram_queryBound _ q
    (figureOneFinalScheduledCappedValueProgram_queryBound q)).queryCost_le.trans ?_
  have hcalls := amplifiedCalls_le_of_rate runRate runRate_one_le (64 * runCostConstant)
    (mul_pos (by norm_num) runCostConstant_pos) q (B := queryBudget q) le_rfl
  have hconst : 9 * (64 * runCostConstant + 1) * (runRate q * protectedLog (1 / q.p)) =
      queryRate q := by
    unfold queryRate queryConstant runCostConstant
    ring
  rw [hconst] at hcalls
  exact_mod_cast hcalls

/-! ## The arithmetic cost -/

/-- **The arithmetic cost of the charged `cv18Program`.**  Besides its membership calls,
every execution performs at most

`11T + 176 + m · (numPhases·(2n + 83) + 7n + 88 + (12n + 31)·B) + 4m²`

operations (`opCost`) on sealed numbers, where `T = terminalPhaseSteps q`,
`m = confidenceRepetitions q` and `B = queryBudget q`: the constants of the call, `m` runs
each allowed `B` queries at `12n + 31` operations apiece plus `2n + 83` per phase, and the
median.  The proof is `OperationCost.lean`. -/
theorem cv18_operation_cost (q : VolumeParams) :
    (cv18Program q).opCost ≤
      ((11 * terminalPhaseSteps q + 176 +
        confidenceRepetitions q * (numPhases q * (2 * q.n + 83) + (7 * q.n + 88) +
          (12 * q.n + 31) * queryBudget q) +
        4 * confidenceRepetitions q ^ 2 : ℕ) : ℕ∞) :=
  cv18Program_opCost_le q

/-! ## Answering the queries by computation -/

/-- **Accuracy, with the queries answered by computation.**  If `member x` decides
membership in the body, the charged `cv18Program` with its queries answered by `member`
is accurate as in Theorem 1.1. -/
theorem cv18_answerWith_volume_accuracy (q : VolumeParams) (I : VolumeInput q.n)
    (member : AmbientSpace q.n → Counted Bool)
    (hmember : ∀ x, (member x).value = true ↔ x ∈ (I.body : Set (AmbientSpace q.n)))
    (hrounded : WellRounded q I) (oracle : AmbientSpace q.n → Bool) :
    1 - q.p ≤ outcomeProbability (((cv18Program q).answerWith member).runEstimate oracle)
      (accurateOutcome q I) := by
  rw [ChargedProgram.runEstimate_answerWith]
  exact cv18Program_accuracy q I ⟨_, hmember⟩ hrounded

/-- **Cost, with the queries answered by computation.**  If every membership test
`member x` spends at most `M` operations, the charged `cv18Program` with its queries
answered by `member` makes no queries and performs at most the operations of
`cv18_operation_cost` plus `M` for each of its at most `⌈queryRate q⌉` membership tests. -/
theorem cv18_answerWith_cost (q : VolumeParams) (member : AmbientSpace q.n → Counted Bool)
    {M : ℕ} (hM : ∀ x, (member x).cost ≤ M) :
    ((cv18Program q).answerWith member).queryCost = 0 ∧
      ((cv18Program q).answerWith member).opCost ≤
        ((11 * terminalPhaseSteps q + 176 +
          confidenceRepetitions q * (numPhases q * (2 * q.n + 83) + (7 * q.n + 88) +
            (12 * q.n + 31) * queryBudget q) +
          4 * confidenceRepetitions q ^ 2 + M * Nat.ceil (queryRate q) : ℕ) : ℕ∞) := by
  refine ⟨ChargedProgram.queryCost_answerWith member _, ?_⟩
  refine (ChargedProgram.opCost_answerWith_le member hM _).trans ?_
  refine (add_le_add (cv18_operation_cost q)
    (mul_le_mul_right (cv18Program_queryCost_le q) _)).trans (le_of_eq ?_)
  push_cast
  ring

#print axioms cv18Program_erase_refines
#print axioms cv18Program_runEstimate_eq
#print axioms cv18Program_accuracy
#print axioms cv18Program_queryCost_le
#print axioms cv18_operation_cost
#print axioms cv18_answerWith_volume_accuracy
#print axioms cv18_answerWith_cost

end ttc.ChargedCV18

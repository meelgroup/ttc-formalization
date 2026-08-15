import Ttc.Exec.CVGlobalRadiusDependenceBudget
import Ttc.Volume.CVHybridSchedule

/-! The global truncation selector instantiated at the literal source phase count. -/

set_option autoImplicit false

namespace Ttc.CVGlobalRadiusSourceSchedule

open Ttc.CVHybridSchedule Ttc.CVGlobalRadiusDependenceBudget
open Ttc.CVGlobalLogarithmicRadius
open Ttc.CVContinuingRetryParameters
open Ttc.CVCorrected
open Ttc.CVHybridRadiusQCanonicalOperational
open Ttc.CVGaussianScoreAwareParameters

/-- Exact number of source hybrid phases, retaining the `N` dependence. -/
noncomputable def sourceHybridPhaseCount (n : Nat) (N : Real) : Nat :=
  terminalPhases n N (1 / (16 * (n : Real)))

/-- Dependence-aware call allocation at the exact source phase count. -/
noncomputable def sourceDependenceRadiusCalls
    (n k : Nat) (N eps : Real) : Real :=
  let m := sourceHybridPhaseCount n N
  max 1 (2 * ((k : Real) + 1) * ((m : Real) + 1) /
    (5 * correctedNu m eps))

theorem one_le_sourceDependenceRadiusCalls (n k : Nat) (N eps : Real) :
    1 ≤ sourceDependenceRadiusCalls n k N eps := by
  unfold sourceDependenceRadiusCalls
  exact le_max_left _ _

/-- The selected radius used by the literal source schedule. -/
noncomputable def sourceGlobalLogarithmicRadiusQ
    (n k : Nat) (N eps : Real) : Real :=
  globalLogarithmicRadiusQ n (sourceDependenceRadiusCalls n k N eps)

theorem four_le_sourceGlobalLogarithmicRadiusQ
    {n : Nat} (hn : 1 ≤ n) (k : Nat) (N eps : Real) :
    4 ≤ sourceGlobalLogarithmicRadiusQ n k N eps :=
  four_le_globalLogarithmicRadiusQ hn
    (one_le_sourceDependenceRadiusCalls n k N eps)

/-- The exact source phase count is `O(n log n + N)`.  In particular, substituting
`N=C²n` retains the `C²n` term; it is not silently collapsed to `O(n log n)`. -/
theorem sourceHybridPhaseCount_lt
    {n : Nat} (hn : 1 ≤ n) {N : Real} (hN : 1 ≤ N) :
    (sourceHybridPhaseCount n N : Real) <
      2 * (n : Real) * Real.log (16 * (n : Real)) + 5 * N + 3 := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hs0 : 0 < (1 / (16 * (n : Real)) : Real) := by positivity
  have hs01 : (1 / (16 * (n : Real)) : Real) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : Real) < 16 * (n : Real))]
    nlinarith
  have h := terminalPhases_lt hn (zero_lt_one.trans_le hN) hs0 hs01
  unfold sourceHybridPhaseCount
  convert h using 1 <;> field_simp

theorem sourceHybridPhaseCount_C_sq_mul_n_lt
    {n : Nat} (hn : 1 ≤ n) {C : Real} (hC : 1 ≤ C) :
    (sourceHybridPhaseCount n (C ^ 2 * n) : Real) <
      2 * (n : Real) * Real.log (16 * (n : Real)) +
        5 * C ^ 2 * (n : Real) + 3 := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hN : 1 ≤ C ^ 2 * (n : Real) := by nlinarith [sq_nonneg C]
  convert (sourceHybridPhaseCount_lt hn (N := C ^ 2 * (n : Real)) hN) using 1
  <;> ring

/-- The literal source selector spends the required dependence-tail share, with the
actual `O(n log n + N)` phase count appearing inside `correctedNu`. -/
theorem sourceGlobalLogarithmicRadius_tail_le
    {n k : Nat} (hn : 1 ≤ n) {N eps : Real} (heps : 0 < eps) :
    (sourceGlobalLogarithmicRadiusQ n k N eps *
        Real.exp (-(sourceGlobalLogarithmicRadiusQ n k N eps ^ 2 - 1) / 2)) ^ n ≤
      correctedNu (sourceHybridPhaseCount n N) eps /
        (8 * ((k : Real) + 1) *
          ((sourceHybridPhaseCount n N : Real) + 1)) := by
  let m := sourceHybridPhaseCount n N
  let nu := correctedNu m eps
  let kp : Real := (k : Real) + 1
  let mp : Real := (m : Real) + 1
  let A := sourceDependenceRadiusCalls n k N eps
  let q := sourceGlobalLogarithmicRadiusQ n k N eps
  let tail := (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n
  have hnu : 0 < nu := correctedNu_pos heps
  have hkp : 0 < kp := by dsimp only [kp]; positivity
  have hmp : 0 < mp := by dsimp only [mp]; positivity
  have hA1 : 1 ≤ A := one_le_sourceDependenceRadiusCalls n k N eps
  have htail0 : 0 ≤ tail := by
    dsimp only [tail, q, sourceGlobalLogarithmicRadiusQ]
    exact pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) n
  have htotal : A * tail ≤ 1 / 20 := by
    simpa only [tail, q, sourceGlobalLogarithmicRadiusQ, A] using
      (globalLogarithmicRadiusQ_totalTail_le hn hA1)
  have hbase : 2 * kp * mp / (5 * nu) ≤ A := by
    dsimp only [A, sourceDependenceRadiusCalls, m, nu, kp, mp]
    exact le_max_right _ _
  have hsmall : (2 * kp * mp / (5 * nu)) * tail ≤ 1 / 20 :=
    (mul_le_mul_of_nonneg_right hbase htail0).trans htotal
  have hscaled : 8 * kp * mp * tail ≤ nu := by
    have hden : 0 < 5 * nu := by positivity
    have h := (div_le_iff₀ hden).mp (by
      simpa only [div_mul_eq_mul_div, mul_assoc] using hsmall)
    nlinarith
  dsimp only [m, nu, kp, mp, A, q, tail] at hscaled ⊢
  apply (le_div_iff₀ (by positivity :
    0 < 8 * ((k : Real) + 1) * ((sourceHybridPhaseCount n N : Real) + 1))).2
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hscaled

theorem sourceGlobalLogarithmicRadius_tail_le_phase
    {n k : Nat} (hn : 1 ≤ n) {N eps : Real} (heps : 0 < eps) :
    (sourceGlobalLogarithmicRadiusQ n k N eps *
        Real.exp (-(sourceGlobalLogarithmicRadiusQ n k N eps ^ 2 - 1) / 2)) ^ n ≤
      correctedNu (sourceHybridPhaseCount n N) eps /
        (8 * ((k : Real) + 1)) := by
  have h := sourceGlobalLogarithmicRadius_tail_le (n := n) (k := k) hn
    (N := N) heps
  have hnu0 : 0 ≤ correctedNu (sourceHybridPhaseCount n N) eps :=
    correctedNu_nonneg
  apply h.trans
  apply div_le_div_of_nonneg_left hnu0
  · positivity
  · have hm0 : (0 : Real) ≤ (sourceHybridPhaseCount n N : Real) := by positivity
    have hm : (1 : Real) ≤ (sourceHybridPhaseCount n N : Real) + 1 := by linarith
    nlinarith [show 0 < (8 : Real) * ((k : Real) + 1) by positivity]

/-- Exact source-phase operational dependence budget at the stream×phase-aware global
radius. -/
theorem sourceGlobalLogarithmicRadius_mixError_budget
    {n k : Nat} (hn : 1 ≤ n) {N eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) (i : Nat) :
    let m := sourceHybridPhaseCount n N
    let q := sourceGlobalLogarithmicRadiusQ n k N eps
    (k : Real) * (2 *
      (hybridRadiusQCanonicalMixError n q
        (scoreAwareEta m k eps slack boundSq)
        (scoreAwareZeta m k eps slack boundSq)
        (scoreAwareRetries m k eps slack boundSq) i).toReal) ≤ correctedNu m eps := by
  dsimp only
  have hq0 : 0 ≤ sourceGlobalLogarithmicRadiusQ n k N eps :=
    Real.sqrt_nonneg _
  exact hybridRadiusQCanonicalMixError_scoreAware_budget_of_tail hq0 heps heps1
    hslack hbound (sourceGlobalLogarithmicRadius_tail_le_phase hn heps) i

/-- Exact selected-radius square.  The logarithm contains the literal source phase
count above, hence its `N=C²n` dependence is visible to runtime accounting. -/
theorem sourceGlobalLogarithmicRadius_sq
    {n k : Nat} (hn : 1 ≤ n) {N eps : Real} :
    sourceGlobalLogarithmicRadiusQ n k N eps ^ 2 =
      16 + 4 * Real.log (20 * sourceDependenceRadiusCalls n k N eps) /
        (n : Real) := by
  exact globalLogarithmicRadiusQ_sq hn
    (one_le_sourceDependenceRadiusCalls n k N eps)

#print axioms sourceHybridPhaseCount_lt
#print axioms four_le_sourceGlobalLogarithmicRadiusQ
#print axioms sourceHybridPhaseCount_C_sq_mul_n_lt
#print axioms sourceGlobalLogarithmicRadius_tail_le
#print axioms sourceGlobalLogarithmicRadius_tail_le_phase
#print axioms sourceGlobalLogarithmicRadius_mixError_budget
#print axioms sourceGlobalLogarithmicRadius_sq

end Ttc.CVGlobalRadiusSourceSchedule

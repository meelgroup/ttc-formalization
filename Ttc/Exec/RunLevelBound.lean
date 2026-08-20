/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Runtime
import Ttc.Findings.SmallBody
import Ttc.Process.Truncation

/-!
# The level the run reaches, deterministically

`Ttc.ElemRunCostTelescope.elemRunCost_le_telescope` charges the whole loop
`(thr + 1) * finalLevel`, so what is left of the run's cost is one number: the level the
fold ends at.  This file bounds it.

`Ttc.absorbLevel_le_of_budgetMet` bounds the *overflow* loop by `Lb` levels above `j₁`, not
above the entry level `j₀`.  The gap `haltLevel - j₀` is the early-reduce jump, and it is
not bounded by `Lb`.  But `Ttc.haltLevel P t j = max j (H t)` only ever raises the level
*to* `H t`, and the level never rewinds — so the jumps telescope against the running maximum
exactly as the thinning charges did, and their total is at most `maxᵢ H(tᵢ)`.
-/

namespace Ttc.RunLevelBound

open Ttc

variable {n : ℕ} {ι : Type*} (P : Params) (O : Oracles n ι)

/-- The early-reduce exit is at most the entry level or `H t`, whichever is larger. -/
theorem haltLevel_le_max (t : ℝ) (j H : ℕ)
    (hH : sInf {j' | ¬ P.thresh / t ≤ (1 / 2 : ℝ) ^ j'} ≤ H) :
    haltLevel P t j ≤ max j H := by
  unfold haltLevel
  exact max_le_max le_rfl hH

/-- **One cube's level increment**, split into the early-reduce jump and the overflow loop.
On `Ttc.BudgetMet Lb` the second is at most `Lb`, and the first only raises the level to
`H t`. -/
theorem step_level_le (ρ : ℤ) {Lb : ℕ} (hb : BudgetMet P O Lb) (st : SketchState n) (i : ι)
    (H : ℕ) (hH : sInf {j' | ¬ P.thresh / (O.vol i) ≤ (1 / 2 : ℝ) ^ j'} ≤ H) :
    (step P O ρ st i).level ≤ max st.level H + Lb := by
  have hstep : (step P O ρ st i).level
      = absorbLevel P O i (O.vol i) (dropCovered O i st.X) st.level
          (haltLevel P (O.vol i) st.level) := rfl
  rw [hstep]
  refine le_trans (absorbLevel_le_of_budgetMet hb i (O.vol i) (dropCovered O i st.X)
    st.level (haltLevel P (O.vol i) st.level)) ?_
  have := haltLevel_le_max P (O.vol i) st.level H hH
  omega

/-- **The run's final level**, on `Ttc.BudgetMet Lb` with every early-reduce target at most
`H`: at most `max st.level H + m·Lb`.  Stated with the `max` inside so the induction
carries: the level never rewinds, so a cube that jumps to `H` cannot jump again. -/
theorem foldl_level_le (ρ : ℤ) {Lb : ℕ} (hb : BudgetMet P O Lb) (H : ℕ)
    (cubes : List ι)
    (hH : ∀ i ∈ cubes, sInf {j' | ¬ P.thresh / (O.vol i) ≤ (1 / 2 : ℝ) ^ j'} ≤ H) :
    ∀ st : SketchState n,
      (cubes.foldl (step P O ρ) st).level ≤ max st.level H + cubes.length * Lb := by
  induction cubes with
  | nil => intro st; simp
  | cons i rest ih =>
      intro st
      have hi := hH i List.mem_cons_self
      have h1 : (step P O ρ st i).level ≤ max st.level H + Lb :=
        step_level_le P O ρ hb st i H hi
      have h2 := ih (fun i' hi' => hH i' (List.mem_cons_of_mem _ hi')) (step P O ρ st i)
      have h3 : max (step P O ρ st i).level H ≤ max st.level H + Lb := by
        refine max_le h1 ?_
        exact le_trans (le_max_right st.level H) (Nat.le_add_right _ _)
      simp only [List.foldl_cons, List.length_cons]
      have h4 : (rest.length + 1) * Lb = rest.length * Lb + Lb := by ring
      omega

/-- **At the run's own start**, `st = ⟨0, 0⟩`, so the `max` collapses to `H`. -/
theorem run_level_le (ρ : ℤ) {Lb : ℕ} (hb : BudgetMet P O Lb) (H : ℕ)
    (cubes : List ι)
    (hH : ∀ i ∈ cubes, sInf {j' | ¬ P.thresh / (O.vol i) ≤ (1 / 2 : ℝ) ^ j'} ≤ H) :
    (cubes.foldl (step P O ρ) ⟨0, 0⟩).level ≤ H + cubes.length * Lb := by
  simpa using foldl_level_le P O ρ hb H cubes hH ⟨0, 0⟩

#print axioms haltLevel_le_max
#print axioms step_level_le
#print axioms foldl_level_le
#print axioms run_level_le

end Ttc.RunLevelBound

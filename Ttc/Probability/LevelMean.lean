/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.RunLevelBound
import Ttc.Monadic.EventMeasurable
import Ttc.Probability.ThinMean

/-!
# The level's mean under `Ttc.trajLaw`

`Ttc.ElemRunCostTelescope.elemRunCost_le_telescope` reduced the loop's whole cost to
`(thr + 1) * finalLevel`, and `Ttc.RunLevelBound.run_level_le` bounds that level by
`H + m * Lb` on `Ttc.BudgetMet Lb`.  What remains is the expectation, and
`Ttc.trajLaw_not_budgetMet_le` prices the budget's failure at `2Λ/2^Lb`.

This file supplies the two structural pieces: the level is measurable, and exceeding
`H + m * Lb` implies the budget failed.

`Ttc.RunLevelBound.run_level_le` says `finalLevel ≤ H + m·Lb` on `Ttc.BudgetMet Lb`, and
`Ttc.trajLaw_not_budgetMet_le` says the budget fails with probability at most `2Λ/2^Lb`.
Layering the first over `Lb` and paying with the second is the whole argument.
-/

namespace Ttc.LevelMean

open MeasureTheory Ttc Ttc.RunLevelBound

variable {n L : ℕ} {ι : Type*}

/-- The final level of the fold is measurable — `Ttc.countablyDetermined_foldl_step` at a
deterministic volume oracle. -/
theorem measurable_finalLevel {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (P : Params) (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    (ρ : ℤ) (cubes : List ι) :
    Measurable fun ω : ℕ → (Fin L → ℕ) =>
      (cubes.foldl (step P (trajOracles hpt vol covered mem ω) ρ) ⟨0, 0⟩).level := by
  have hcd := countablyDetermined_foldl_step (hpt := hpt) (V := fun _ ↦ vol)
    (covered := covered) (mem := mem) (T := fun ω : ℕ → (Fin L → ℕ) ↦ ω) P ρ
    (fun k ↦ countablyDetermined_apply k)
    (fun i j ↦ countablyDetermined_const _)
    cubes (fun _ ↦ ⟨0, 0⟩) (countablyDetermined_const _)
  exact (hcd.map (fun S : SketchState n ↦ S.level)).measurable

/-- **The level exceeds `H + m·Lb` only if the budget fails.**  Contrapositive of
`Ttc.RunLevelBound.run_level_le`. -/
theorem level_gt_subset {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (P : Params) (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    (ρ : ℤ) (H Lb : ℕ) (cubes : List ι)
    (hH : ∀ i ∈ cubes,
      sInf {j' | ¬ P.thresh / (vol i) ≤ (1 / 2 : ℝ) ^ j'} ≤ H) :
    {ω : ℕ → (Fin L → ℕ) | H + cubes.length * Lb
        < (cubes.foldl (step P (trajOracles hpt vol covered mem ω) ρ) ⟨0, 0⟩).level}
      ⊆ {ω : ℕ → (Fin L → ℕ) |
          ¬ BudgetMet P (trajOracles hpt vol covered mem ω) Lb} := by
  intro ω hω hbud
  exact absurd (run_level_le P (trajOracles hpt vol covered mem ω) ρ hbud H cubes hH)
    (by simpa using hω)

#print axioms measurable_finalLevel
#print axioms level_gt_subset

end Ttc.LevelMean

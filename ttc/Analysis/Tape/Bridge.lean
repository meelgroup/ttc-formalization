/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.MeasTrees

/-!
# The sealed program on the random tape

The run of the sealed TTC program on a tape (`SealedRun.execution`) has the output and the
operation count of its tree (`execution_eq`), and on the random tape their joint law is the
tree's law with every random number drawn fresh (`tapeLaw_map_execution`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.SealedRun (execution tapeLaw)

variable {d : ℕ}

/-- **The run on a tape is the tree's run**: the same output, and the same operations. -/
theorem execution_eq (fuel : ℕ) (cs : List (ComponentInput d)) (eps delta : ℝ) (t : Tape d) :
    (execution fuel cs eps delta t).val.1 = (Tree.exec (estimatorT (cv18T d) fuel cs eps delta) 0 t).1 ∧
      opsTotal (execution fuel cs eps delta t).cost =
        (Tree.exec (estimatorT (cv18T d) fuel cs eps delta) 0 t).2.1 := by
  obtain ⟨hv, hc⟩ := (agree_estimatorT fuel cs eps delta).run 0 t
  refine ⟨?_, hc⟩
  have : (execution fuel cs eps delta t).val = _ := hv
  rw [this]

/-- What a run records: its output and its operation count. -/
def outputAndOps {α : Type} (o : Tree.Outcome α) : Option α × ℕ := (o.1, o.2.1)

theorem measurable_outputAndOps {α : Type} [MeasurableSpace α] :
    Measurable (outputAndOps (α := α)) :=
  measurable_fst.prodMk measurable_snd.fst

/-- **The output and operation count of the sealed program on the random tape** have the law
of its tree with every random number drawn fresh. -/
theorem tapeLaw_map_execution (fuel : ℕ) (cs : List (ComponentInput d)) (eps delta : ℝ) :
    (tapeLaw d).map (fun t => ((execution fuel cs eps delta t).val.1,
        opsTotal (execution fuel cs eps delta t).cost)) =
      (Tree.law (estimatorT (cv18T d) fuel cs eps delta) 0).map outputAndOps := by
  have hfun : (fun t => ((execution fuel cs eps delta t).val.1,
      opsTotal (execution fuel cs eps delta t).cost)) =
      outputAndOps ∘ fun t => Tree.outcome (Tree.exec (estimatorT (cv18T d) fuel cs eps delta) 0 t) := by
    funext t
    obtain ⟨h1, h2⟩ := execution_eq fuel cs eps delta t
    simp only [Function.comp_apply, outputAndOps, Tree.outcome, h1, h2]
  have hm := measurable_exec_estimatorT fuel cs eps delta 0
  rw [hfun, ← Measure.map_map measurable_outputAndOps hm,
    Tree.tapeLaw_map_exec _ 0 hm]

end ttc.Tape

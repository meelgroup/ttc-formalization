/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.OpsExp

/-!
# From bounded-fuel costs to the cost of the first finishing run

We count the operations of a run once it finishes, not the work of trying
successively larger fuels. The finished-run tallies increase pointwise to the
tally that the model reads at the least sufficient fuel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ttc.Tape

open Arlib.Computation (Num)
open ttc.Model.Operations
open ttc.SealedRun
open ttc.Tape.Tree

variable {d k : ℕ}
variable (cs : List (ComponentInput d)) (eps delta : ℝ)

theorem measurableSet_finishes (f : ℕ) :
    MeasurableSet {t : Tape d | Finishes f cs eps delta t} := by
  have h : {t : Tape d | Finishes f cs eps delta t} = res cs eps delta f ⁻¹' {none}ᶜ := by
    ext t
    rw [Set.mem_ofPred_eq, finishes_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    cases res cs eps delta f t <;> simp
  rw [h]
  exact (measurable_res cs eps delta f) measurableSet_none.compl

/-- The cost of the run with fuel `f`, read only on the tapes where it finishes. -/
def finishedOps (f : ℕ) (t : Tape d) : ENNReal :=
  {t | Finishes f cs eps delta t}.indicator
    (fun t => ((exec (estimatorT (cv18T d) f cs eps delta) 0 t).2.1 : ENNReal)) t

theorem measurable_finishedOps (f : ℕ) :
    Measurable (finishedOps cs eps delta f) :=
  (measurable_ops.comp (measurable_exec_estimatorT f cs eps delta 0)).indicator
    (measurableSet_finishes cs eps delta f)

theorem finishedOps_le (f : ℕ) (t : Tape d) :
    finishedOps cs eps delta f t ≤ ((exec (estimatorT (cv18T d) f cs eps delta) 0 t).2.1 : ENNReal) :=
  indicator_le_self' (fun _ _ => bot_le) _

theorem finishedOps_eq_operations {f : ℕ} {t : Tape d} (h : Finishes f cs eps delta t) :
    finishedOps cs eps delta f t = operations cs eps delta t := by
  have hmin : Finishes (fuelNeeded cs eps delta t) cs eps delta t :=
    Nat.sInf_mem (s := {f | Finishes f cs eps delta t}) ⟨f, h⟩
  have hle : fuelNeeded cs eps delta t ≤ f :=
    Nat.sInf_le (s := {f | Finishes f cs eps delta t}) h
  have he := fuelLE_estimatorT hle cs eps delta 0 t
    ((finishes_iff cs eps delta _ t).mp hmin)
  have ht : t ∈ {t | Finishes f cs eps delta t} := h
  rw [finishedOps, indicator_of_mem ht, he, operations, runOn, (execution_eq _ cs eps delta t).2]

theorem monotone_finishedOps : Monotone (finishedOps cs eps delta) := by
  intro f g hfg t
  by_cases h : Finishes f cs eps delta t
  · have he := fuelLE_estimatorT hfg cs eps delta 0 t ((finishes_iff cs eps delta _ t).mp h)
    have hg : Finishes g cs eps delta t := by
      rw [finishes_iff, res, he]
      exact (finishes_iff cs eps delta _ t).mp h
    rw [finishedOps_eq_operations cs eps delta h, finishedOps_eq_operations cs eps delta hg]
  · have ht : t ∉ {t | Finishes f cs eps delta t} := h
    rw [finishedOps, indicator_of_notMem ht]
    exact bot_le

theorem iSup_finishedOps_eq_operations {t : Tape d} (ht : ∃ f, Finishes f cs eps delta t) :
    (⨆ f, finishedOps cs eps delta f t) = operations cs eps delta t := by
  obtain ⟨f, hf⟩ := ht
  apply le_antisymm
  · refine iSup_le fun g => ?_
    by_cases hg : Finishes g cs eps delta t
    · exact (finishedOps_eq_operations cs eps delta hg).le
    · have ht : t ∉ {t | Finishes g cs eps delta t} := hg
      rw [finishedOps, indicator_of_notMem ht]
      exact bot_le
  · rw [← finishedOps_eq_operations cs eps delta hf]
    exact le_iSup (fun g => finishedOps cs eps delta g t) f

/-- On certified formula inputs, some fuel suffices on almost every random tape. -/
theorem ae_exists_finishes (hn : 21 ≤ d) (F : LRAFormula d k)
    (hb : Bornology.IsBounded (solutionSet F)) (p : ApproxParams) (prep : TTCPreprocessor d k) :
    ∀ᵐ t ∂tapeLaw d, ∃ f, Finishes f (componentsOf (prep.run F hb)) p.epsilon p.delta t := by
  let cs := componentsOf (prep.run F hb)
  let never : Set (Tape d) := {t | ¬ ∃ f, Finishes f cs p.epsilon p.delta t}
  have hle (f : ℕ) : tapeLaw d never ≤
      (vlaw (estimatorT (cv18T d) f cs p.epsilon p.delta) 0).map outOf {none} := by
    have hm := measurable_exec_estimatorT f cs p.epsilon p.delta 0
    rw [vlaw, ← tapeLaw_map_exec _ 0 hm, Measure.map_map measurable_fst hm,
      Measure.map_map measurable_outOf (measurable_fst.comp hm),
      Measure.map_apply (measurable_outOf.comp (measurable_fst.comp hm)) measurableSet_none]
    refine measure_mono fun t ht => ?_
    have hf : ¬ Finishes f cs p.epsilon p.delta t := fun h => ht ⟨f, h⟩
    rw [finishes_iff] at hf
    change outOf (res cs p.epsilon p.delta f t) ∈ ({none} : Set (Option NNReal))
    cases h : res cs p.epsilon p.delta f t with
    | none => rfl
    | some a => exact (hf (by rw [h]; rfl)).elim
  exact ae_iff.mpr (le_antisymm (ge_of_tendsto' (approx_output hn F hb p prep).stop hle) bot_le)

/-- Any bound uniform in fuel bounds the expected tally of the sealed run, including
all of its charged arithmetic and draws. -/
theorem expectedOperations_le_of_uniform (hn : 21 ≤ d) (F : LRAFormula d k)
    (hb : Bornology.IsBounded (solutionSet F)) (p : ApproxParams) (prep : TTCPreprocessor d k)
    (B : ENNReal)
    (hB : ∀ f, Eops (estimatorT (cv18T d) f (componentsOf (prep.run F hb))
      p.epsilon p.delta) 0 ≤ B) :
    expectedOperations F hb p prep ≤ B := by
  let cs := componentsOf (prep.run F hb)
  change (∫⁻ t, (operations cs p.epsilon p.delta t : ENNReal) ∂tapeLaw d) ≤ B
  rw [lintegral_congr_ae ((ae_exists_finishes hn F hb p prep).mono fun t ht =>
    (iSup_finishedOps_eq_operations cs p.epsilon p.delta ht).symm),
    lintegral_iSup (measurable_finishedOps cs p.epsilon p.delta)
      (monotone_finishedOps cs p.epsilon p.delta)]
  refine iSup_le fun f => (lintegral_mono (finishedOps_le cs p.epsilon p.delta f)).trans ?_
  rw [← Eops_eq_tape _ _ (measurable_exec_estimatorT f cs p.epsilon p.delta 0)]
  exact hB f

end ttc.Tape

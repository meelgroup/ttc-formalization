/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.StepRate

/-!
# One step, part two: the samples

The step calls the sampler `N` times and appends each sample to the list of copies; the run
stops if one call does.  The law of the samples appended is `N` independent sampler draws in
sequence (`seqLaw`, `vlaw_sampleLoop`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ArlibCommunity.Algorithms.CV18 (measurable_some)

variable {d : ℕ}

/-! ## Discrete structure -/

section Discrete

variable {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]

instance optionSingletonClass : MeasurableSingletonClass (Option α) := ⟨fun o => by
  rcases o with _ | a
  · exact measurableSet_none
  · have : ({some a} : Set (Option α)) = some '' {a} := by simp
    rw [this]
    exact measurableSet_image_some (measurableSet_singleton a)⟩

instance listSingletonClass : MeasurableSingletonClass (List α) := ⟨fun l => by
  have : ({l} : Set (List α)) = {l' | l'.length = l.length} ∩
      ⋂ i : ℕ, {l' | l'[i]? = l[i]?} := by
    ext l'
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro rfl; exact ⟨rfl, fun _ => rfl⟩
    · rintro ⟨_, h⟩; exact List.ext_getElem? h
  rw [this]
  exact (List.measurable_length (measurableSet_singleton _)).inter
    (MeasurableSet.iInter fun i => (List.measurable_getElem? i) (measurableSet_singleton _))⟩

end Discrete

/-! ## Draws in sequence -/

section Seq

variable {α : Type} [MeasurableSpace α]

/-- **`k` draws in sequence** from a law `ν` that may stop (`none`): the list of draws, or
`none` if one stops. -/
def seqLaw (ν : Measure (Option α)) : ℕ → Measure (Option (List α))
  | 0 => Measure.dirac (some [])
  | k + 1 => ν.bind fun o => o.elim (Measure.dirac none) fun z =>
      (seqLaw ν k).map (Option.map (z :: ·))

end Seq

/-! ## The sampling loop -/

section Loop

/-- One round of the sampling loop, with sampler `S`. -/
def sampleBody (S : Tree d (Fin d → Num ℤ)) (acc : List (Fin d → Num ℤ) × Num ℕ) :
    Tree d ((List (Fin d → Num ℤ) × Num ℕ) ⊕ Empty) :=
  S.bind fun z =>
    (compute (A.push acc.1 z)).bind fun ys =>
    (compute (do
      let one ← A.lit (1 : ℕ)
      A.add acc.2 one)).bind fun c =>
    .pure (.inl (ys, c))

/-- The loop's result, read as the list of points and the count. -/
def loopView (r : (List (Fin d → Num ℤ) × Num ℕ) ⊕ Empty) : List (Fin d → Num ℤ) × ℕ :=
  ((r.elim id Empty.elim).1, (r.elim id Empty.elim).2.get)

theorem measurable_loopView : Measurable (loopView (d := d)) := by
  have h : Measurable fun r : (List (Fin d → Num ℤ) × Num ℕ) ⊕ Empty => r.elim id Empty.elim :=
    measurable_id.sumElim measurable_from_top
  exact (measurable_fst.comp h).prodMk (Num.measurable_get.comp (measurable_snd.comp h))

end Loop

section LoopLaw

variable (S : Tree d (Fin d → Num ℤ)) (hS : ∀ (Q : Type) [MeasurableSpace Q], MeasFam fun _ : Q => S)
  (hfree : Free S)

include hS in
theorem mf_sampleBody {Q : Type} [MeasurableSpace Q] :
    MeasFam fun p : Q × (List (Fin d → Num ℤ) × Num ℕ) => sampleBody S p.2 := by
  unfold sampleBody
  refine MeasFam.bind' (hS _) ?_
  refine MeasFam.compute (mp_push (by fun_prop) measurable_snd) ?_
  apply MeasFam.compute
  · exact MP.bind' (MP.const _) (mp_addN (by fun_prop) measurable_snd)
  exact MeasFam.pure (measurable_inl.comp (by fun_prop))

/-- The loop's result, read with integer points. -/
def loopZ (r : (List (Fin d → Num ℤ) × Num ℕ) ⊕ Empty) : List (Fin d → ℤ) × ℕ :=
  ((loopView r).1.map getZ, (loopView r).2)

theorem measurable_loopZ : Measurable (loopZ (d := d)) :=
  ((List.measurable_map measurable_getZ).comp (measurable_fst.comp measurable_loopView)).prodMk
    (measurable_snd.comp measurable_loopView)

include hS hfree in
/-- **`k` rounds of the sampling loop append `k` sampler draws in sequence.** -/
theorem vlaw_loopRounds_sample (b : ℕ) :
    ∀ (k : ℕ) (acc : List (Fin d → Num ℤ) × Num ℕ),
      (vlaw (loopRounds (sampleBody S) k acc) b).map (Option.map loopZ) =
        (seqLaw ((vlaw S b).map (Option.map getZ)) k).map
          (Option.map fun zs => (acc.1.map getZ ++ zs, acc.2.get + zs.length))
  | 0, acc => by
      show (vlaw (Tree.pure (Sum.inl acc)) b).map _ = _
      rw [vlaw_pure, Measure.map_dirac' (measurable_optionMap measurable_loopZ), seqLaw,
        Measure.map_dirac' (measurable_of_countable _)]
      simp [loopZ, loopView]
  | k + 1, acc => by
      have hloop : loopRounds (sampleBody S) (k + 1) acc =
          S.bind fun z => (compute (A.push acc.1 z)).bind fun ys =>
            (compute (do
              let one ← A.lit (1 : ℕ)
              A.add acc.2 one)).bind fun c => loopRounds (sampleBody S) k (ys, c) := by
        show (sampleBody S acc).bind _ = _
        simp only [sampleBody, Tree.bind_assoc]
        rfl
      have hf : MeasFam fun z : Fin d → Num ℤ => (compute (A.push acc.1 z)).bind fun ys =>
          (compute (do
            let one ← A.lit (1 : ℕ)
            A.add acc.2 one)).bind fun c => loopRounds (sampleBody S) k (ys, c) := by
        refine MeasFam.compute (mp_push measurable_const measurable_id) ?_
        apply MeasFam.compute
        · exact MP.const _
        exact (MeasFam.loopRounds (A := Unit) (body := fun _ => sampleBody S)
          (mf_sampleBody S hS) k).comp
          (φ := fun q : ((Fin d → Num ℤ) × List (Fin d → Num ℤ)) × Num ℕ => ((), (q.1.2, q.2)))
          (measurable_const.prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      have hm : Measurable fun t => outcome (exec S b t) := (hS Unit).outcome () b
      rw [hloop, vlaw_bind hf hfree b hm,
        Measure.map_bind (measurable_optionKernel (hf.measurable_vlaw b)).aemeasurable
          (measurable_optionMap measurable_loopZ).aemeasurable, seqLaw,
        Measure.bind_map (measurable_optionMap measurable_getZ).aemeasurable
          (measurable_of_countable _).aemeasurable,
        Measure.map_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
      congr 1
      funext o
      rcases o with _ | z
      · simp only [Option.elim, Option.map_none]
        rw [Measure.map_dirac' (measurable_optionMap measurable_loopZ),
          Measure.map_dirac' (measurable_of_countable _)]
        rfl
      · simp only [Option.elim, Option.map_some]
        rw [vlaw_compute_bind, vlaw_compute_bind,
          vlaw_loopRounds_sample b k, Measure.map_map (measurable_of_countable _)
            (measurable_of_countable _)]
        congr 1
        funext o'
        rcases o' with _ | zs
        · rfl
        · simp [A.push, ttc.Model.Operations.push, A.add, A.lit, Num.get_add]
          omega

end LoopLaw

end ttc.Tape

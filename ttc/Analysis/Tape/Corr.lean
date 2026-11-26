/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.CV18Component

/-!
# Comparing two processes through views

The sealed program and the old model keep their state differently (a list of points, a set
of labelled copies), so their laws are compared through a common *view* (here: `p`, the
multiset of points, counts).  A correspondence `Corr` gives the views, the invariants under
which they determine the state well enough, and a measurable *section* choosing a sealed
state for each view.

`Corr.bind_eq`: if two laws agree on views and keep the invariants almost surely, and two
continuations agree on any pair of states with equal views and the invariants, the composites
agree.  This is how the two algorithms are compared one piece at a time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

/-- **A correspondence** between sealed states `αN` and old states `αO` through views `W`. -/
structure Corr (αN αO W : Type) [MeasurableSpace αN] [MeasurableSpace αO] [MeasurableSpace W] where
  vN : αN → W
  vO : αO → W
  invN : αN → Prop
  invO : αO → Prop
  secN : W → αN
  measurable_vN : Measurable vN
  measurable_vO : Measurable vO
  measurable_secN : Measurable secN
  /-- Every sealed state has an old partner with the same view. -/
  partner : ∀ x, invN x → ∃ y, invO y ∧ vO y = vN x
  /-- The section gives an old state's view back, as a sealed state. -/
  sec_spec : ∀ y, invO y → invN (secN (vO y)) ∧ vN (secN (vO y)) = vO y

namespace Corr

variable {αN αO W γ : Type} [MeasurableSpace αN] [MeasurableSpace αO] [MeasurableSpace W]
  [MeasurableSpace γ] (C : Corr αN αO W)

/-- Two states correspond: equal views, and the invariants. -/
def Rel (x : αN) (y : αO) : Prop := C.invN x ∧ C.invO y ∧ C.vN x = C.vO y

/-- **Composing through a correspondence.** -/
theorem bind_eq {μN : Measure αN} {μO : Measure αO} (hμ : μN.map C.vN = μO.map C.vO)
    (hN : ∀ᵐ x ∂μN, C.invN x) (hO : ∀ᵐ y ∂μO, C.invO y)
    {KN : αN → Measure γ} {KO : αO → Measure γ} (hKN : Measurable KN)
    (hK : ∀ x y, C.Rel x y → KN x = KO y) : μN.bind KN = μO.bind KO := by
  let H : W → Measure γ := KN ∘ C.secN
  have hH : Measurable H := hKN.comp C.measurable_secN
  have hO' : ∀ y, C.invO y → KO y = H (C.vO y) := by
    intro y hy
    obtain ⟨h1, h2⟩ := C.sec_spec y hy
    exact (hK _ y ⟨h1, hy, h2⟩).symm
  have hN' : ∀ x, C.invN x → KN x = H (C.vN x) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := C.partner x hx
    rw [hK x y ⟨hx, hy, hxy.symm⟩, hO' y hy, hxy]
  calc μN.bind KN = μN.bind (H ∘ C.vN) := Measure.bind_congr_right (hN.mono fun x hx => hN' x hx)
    _ = (μN.map C.vN).bind H := (Measure.bind_map C.measurable_vN.aemeasurable hH.aemeasurable).symm
    _ = (μO.map C.vO).bind H := by rw [hμ]
    _ = μO.bind (H ∘ C.vO) := Measure.bind_map C.measurable_vO.aemeasurable hH.aemeasurable
    _ = μO.bind KO := (Measure.bind_congr_right (hO.mono fun y hy => hO' y hy)).symm

/-- The correspondence lifted to optional states: a stop corresponds to a stop. -/
def option : Corr (Option αN) (Option αO) (Option W) where
  vN := Option.map C.vN
  vO := Option.map C.vO
  invN := fun x => ∀ a ∈ x, C.invN a
  invO := fun y => ∀ a ∈ y, C.invO a
  secN := Option.map C.secN
  measurable_vN := measurable_optionMap C.measurable_vN
  measurable_vO := measurable_optionMap C.measurable_vO
  measurable_secN := measurable_optionMap C.measurable_secN
  partner := by
    rintro (_ | x) hx
    · exact ⟨none, fun a ha => by simp at ha, rfl⟩
    · obtain ⟨y, hy, h⟩ := C.partner x (hx x rfl)
      exact ⟨some y, fun a ha => by simp at ha; subst ha; exact hy, by simp [h]⟩
  sec_spec := by
    rintro (_ | y) hy
    · exact ⟨fun a ha => by simp at ha, rfl⟩
    · obtain ⟨h1, h2⟩ := C.sec_spec y (hy y rfl)
      exact ⟨fun a ha => by simp at ha; subst ha; exact h1, by simp [h2]⟩

end Corr


/-! ## The algorithm's state -/

section State

open ttc.Program
open ttc.Model.Operations
open Arlib.Computation (Num Charged)
open ttc (TTCState)

variable {d : ℕ}

theorem encMS_injective : Function.Injective (encMS (n := d)) :=
  (Countable.exists_injective_nat (Multiset (Fin d → ℤ))).choose_spec

/-- A multiset back from its number. -/
def decMS (k : ℕ) : Multiset (Fin d → ℤ) := Function.invFun encMS k

theorem decMS_encMS (M : Multiset (Fin d → ℤ)) : decMS (encMS M) = M :=
  Function.leftInverse_invFun encMS_injective M

/-- The old state with copies `l`, labelled `0, 1, …`, at precision `b`. -/
def mkOld (b : ℕ) (p : NNReal) (l : List (Fin d → ℤ)) : TTCState d :=
  ⟨p, ((List.range l.length).zip l |>.map fun iz => (iz.1, (b, iz.2))).toFinset, l.length⟩

/-- The sealed state's view: `p` and the multiset of its points. -/
def stVN (x : State d) : ℝ × ℕ := (x.p.get, encMS ((x.X.map getZ : List _) : Multiset (Fin d → ℤ)))

/-- The old state's view. -/
def stVO (y : TTCState d) : ℝ × ℕ := ((y.p : ℝ), encMS (y.X.val.map fun c => c.2.2))

/-- A sealed state for a view. -/
def stSec (w : ℝ × ℕ) : State d :=
  ⟨(sealDraw w.1).val, (decMS (d := d) w.2).toList.map sealZ,
    (sealDraw (decMS (d := d) w.2).toList.length).val⟩

theorem mkOld_labels (b : ℕ) (l : List (Fin d → ℤ)) :
    (((List.range l.length).zip l).map fun iz => (iz.1, (b, iz.2))).map (·.1) = List.range l.length := by
  rw [List.map_map]
  have : ((fun c : ttc.SampleCopy d => c.1) ∘ fun iz : ℕ × (Fin d → ℤ) => (iz.1, (b, iz.2))) =
      Prod.fst := rfl
  rw [this, List.map_fst_zip]
  simp

theorem mkOld_points (b : ℕ) (l : List (Fin d → ℤ)) :
    (((List.range l.length).zip l).map fun iz => (iz.1, (b, iz.2))).map (fun c => c.2.2) = l := by
  rw [List.map_map]
  have : ((fun c : ttc.SampleCopy d => c.2.2) ∘ fun iz : ℕ × (Fin d → ℤ) => (iz.1, (b, iz.2))) =
      Prod.snd := rfl
  rw [this, List.map_snd_zip]
  simp

theorem mkOld_nodup (b : ℕ) (l : List (Fin d → ℤ)) :
    (((List.range l.length).zip l).map fun iz => (iz.1, (b, iz.2))).Nodup := by
  exact List.Nodup.of_map (fun c : ttc.SampleCopy d => c.1)
    (by rw [mkOld_labels]; exact List.nodup_range)

/-- **The state correspondence at precision `b`.** -/
def stCorr (b : ℕ) : Corr (State d) (TTCState d) (ℝ × ℕ) where
  vN := stVN
  vO := stVO
  invN := fun x => 0 ≤ x.p.get
  invO := fun y => y.LabelsFresh ∧ ∀ c ∈ y.X, c.2.1 = b
  secN := stSec
  measurable_vN := by
    refine (Num.measurable_get.comp State.measurable_p).prodMk ?_
    have hL : Measurable fun l : List (Fin d → Num ℤ) =>
        encMS ((l.map getZ : List _) : Multiset (Fin d → ℤ)) := by
      have := measurable_of_ofFn (X := Unit) (α := Fin d → Num ℤ)
        (F := fun p => encMS ((p.2.map getZ : List _) : Multiset (Fin d → ℤ)))
        (fun k => measurable_of_countable _)
      exact this.comp ((measurable_const (a := ())).prodMk measurable_id)
    exact hL.comp State.measurable_X
  measurable_vO := by
    have hst : Measurable fun s : TTCState d => (s.p, s.X, s.nextLabel) :=
      Measurable.of_comap_le le_rfl
    exact (measurable_coe_nnreal_real.comp (measurable_fst.comp hst)).prodMk
      ((measurable_of_countable (fun X : Finset (ttc.SampleCopy d) =>
        encMS (X.val.map fun c : ttc.SampleCopy d => c.2.2))).comp ((measurable_fst.comp measurable_snd).comp hst))
  measurable_secN := State.measurable_mk (Tree.measurable_sealDraw.comp measurable_fst)
    ((measurable_from_top (f := fun k : ℕ => (decMS (d := d) k).toList.map sealZ)).comp measurable_snd)
    ((measurable_from_top (f := fun k : ℕ => (sealDraw (decMS (d := d) k).toList.length).val)).comp
      measurable_snd)
  partner := by
    classical
    rintro x hp
    refine ⟨mkOld b (Real.toNNReal x.p.get) (x.X.map getZ), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro c hc
      simp only [mkOld, List.mem_toFinset, List.mem_map] at hc
      obtain ⟨iz, hiz, rfl⟩ := hc
      exact List.mem_range.mp (List.of_mem_zip hiz).1
    · intro c hc c' hc' h
      simp only [mkOld, List.mem_toFinset] at hc hc'
      have hnd := mkOld_labels b (x.X.map getZ) ▸ (List.nodup_range (n := (x.X.map getZ).length))
      exact List.inj_on_of_nodup_map hnd hc hc' h
    · intro c hc
      simp only [mkOld, List.mem_toFinset, List.mem_map] at hc
      obtain ⟨iz, _, rfl⟩ := hc
      rfl
    · simp only [stVO, stVN, mkOld, Real.coe_toNNReal _ hp, Prod.mk.injEq, true_and]
      rw [List.toFinset_val, List.dedup_eq_self.mpr (mkOld_nodup b _), Multiset.map_coe,
        mkOld_points]
  sec_spec := by
    rintro y ⟨_, _⟩
    refine ⟨?_, ?_⟩
    · simp [stSec, stVO]
    · simp only [stVN, stSec, stVO, get_sealDraw, List.map_map, Prod.mk.injEq, true_and]
      have : (getZ ∘ sealZ (k := d)) = id := funext fun w => getZ_sealZ w
      rw [this, List.map_id, Multiset.coe_toList, decMS_encMS]

end State


/-! ## Listing the old copies in the sealed order -/

section Listing

open ttc.Program
open ttc (TTCState)

theorem exists_perm_map {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → β) :
    ∀ (l₁ : List β) (l₂ : List α), (l₁ : Multiset β) = ((l₂.map g : List β) : Multiset β) →
      ∃ l₂' : List α, l₂'.Perm l₂ ∧ l₂'.map g = l₁
  | [], l₂, h => by
      have : l₂ = [] := by
        have := congrArg Multiset.card h
        simp at this
        exact List.eq_nil_of_length_eq_zero this.symm
      exact ⟨[], by simp [this], rfl⟩
  | y :: l₁, l₂, h => by
      have hy : y ∈ (l₂.map g) := by
        have : y ∈ ((l₂.map g : List β) : Multiset β) := h ▸ Multiset.mem_coe.mpr (List.mem_cons_self ..)
        exact Multiset.mem_coe.mp this
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
      have hrest : (l₁ : Multiset β) = (((l₂.erase a).map g : List β) : Multiset β) := by
        have h2 : ((l₂.map g : List β) : Multiset β) =
            (((a :: l₂.erase a).map g : List β) : Multiset β) :=
          Multiset.coe_eq_coe.mpr ((List.perm_cons_erase ha).map g)
        rw [h2, List.map_cons, ← Multiset.cons_coe, ← Multiset.cons_coe] at h
        exact (Multiset.cons_inj_right _).mp h
      obtain ⟨l', hperm, hmap⟩ := exists_perm_map g l₁ (l₂.erase a) hrest
      exact ⟨a :: l', (hperm.cons a).trans (List.perm_cons_erase ha).symm, by simp [hmap]⟩

variable {d : ℕ}

/-- **Related states list the same copies**: the old copies, in the sealed list's order,
with distinct labels below the next label, at precision `b`. -/
theorem stCorr_rel_list {b : ℕ} {x : State d} {y : TTCState d} (h : (stCorr b).Rel x y) :
    ∃ Ls : List (ttc.SampleCopy d), x.X.map getZ = Ls.map (fun c => c.2.2) ∧ Ls.toFinset = y.X ∧
      (Ls.map (·.1)).Nodup ∧ (∀ c ∈ Ls, c.1 < y.nextLabel ∧ c.2.1 = b) ∧
      x.p.get = y.p := by
  classical
  obtain ⟨_, ⟨⟨hlt, hdist⟩, hcode⟩, hv⟩ := h
  simp only [stCorr, stVN, stVO, Prod.mk.injEq] at hv hlt hdist hcode
  obtain ⟨hp, he⟩ := hv
  have hms : ((x.X.map getZ : List _) : Multiset (Fin d → ℤ)) =
      ((y.X.toList.map fun c => c.2.2 : List _) : Multiset (Fin d → ℤ)) := by
    rw [encMS_injective he, ← Multiset.map_coe, Finset.coe_toList]
  obtain ⟨Ls, hperm, hmap⟩ := exists_perm_map (fun c : ttc.SampleCopy d => c.2.2) _ _ hms
  have hmem : ∀ c, c ∈ Ls ↔ c ∈ y.X := fun c => by rw [hperm.mem_iff, Finset.mem_toList]
  refine ⟨Ls, hmap.symm, ?_, ?_, fun c hc => ⟨hlt c ((hmem c).1 hc), hcode c ((hmem c).1 hc)⟩,
    hp⟩
  · rw [List.toFinset_eq_of_perm _ _ hperm, Finset.toList_toFinset]
  · refine List.Nodup.map_on (fun c hc c' hc' hcc => hdist c ((hmem c).1 hc) c' ((hmem c').1 hc') hcc) ?_
    exact hperm.nodup_iff.mpr (Finset.nodup_toList _)

end Listing

end ttc.Tape

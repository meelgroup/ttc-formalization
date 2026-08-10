/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Api
import Ttc.Coupling.Family
import Ttc.Monadic.Kernel

/-!
# `Monadic/EventMeasurable`: the headline's own event is measurable

`Ttc.ttc_volume_estimate`'s accuracy conjunct is an iterated integral whose
integrand is the trajectory law applied to

```
{t | ttcAlgOutput … (ttcOracleBundle … c t) ∈ relErr ε (volSol (atomSet atoms) φ)}
```

`Ttc.lintegral_trajLaw_ttcRates_eq_bind` (`Monadic/Kernel`) can fold that iterated
integral into one measure, but only for a **measurable** event.  This file proves
the event measurable — for each fixed `c` (`Ttc.measurableSet_good_event`) and,
what the rewrite actually needs, jointly in `c` and `t`
(`Ttc.measurableSet_good_event_joint`) — and then performs the fold:
`Ttc.ttc_accuracy_single_measure` is the accuracy guarantee over **one** measure on
**one** space.

## Why this is not `fun_prop`, and what replaces it

Three obstructions, none of them a size problem:

* `Ttc.ttcAlgOutput` is `Ttc.run`, a `List.foldl` of `Ttc.step`, and the
  intermediate state `Ttc.SketchState n` carries a `Multiset (Space n)` — a type
  with **no** measurable structure.  "The fold is measurable" cannot even be
  stated pointwise.
* `Ttc.absorbLevel` (`alg:ttc` lines 39–42) is an **unbounded** `Nat.sInf` search
  over the trajectory, with a junk value when the loop never exits.
* the volume coins `c` enter through `Ttc.mcVol`, a genuinely real-valued
  quantity, so the joint statement is not a discrete-space statement either.

What replaces `fun_prop` is `Ttc.CountablyDetermined`: `f` takes countably many
values and every fibre `f ⁻¹' {b}` is measurable.  It is stated for an **arbitrary**
target type, so it applies to the sketch state; it is closed under post-composition
with arbitrary functions, pairing, pre-composition with measurable maps, and — the
one that drives the induction — *dependent gluing*
(`Ttc.CountablyDetermined.bind`); and it implies measurability of **every**
preimage, measurable or not (`Ttc.CountablyDetermined.measurableSet_preimage`).

## The route, in dependency order

1. `Ttc.countablyDetermined_apply` — a single trajectory coordinate; `Fin L → ℕ`
   is countable with measurable singletons.
2. `Ttc.countablyDetermined_natSInf` — an unbounded `Nat.sInf` of measurable
   conditions.  The fibre `{ω | sInf = k}` splits into "`k` holds and nothing below
   it does" and, at `k = 0`, "nothing holds at all" — the junk branch, a countable
   intersection.
3. `Ttc.countablyDetermined_haltLevel` (lines 32–35, deterministic, reads the
   volume estimate) and `Ttc.countablyDetermined_absorbLevel` (lines 39–42, reads
   the trajectory).  The latter is the crux; `Ttc.measurableSet_absorbLevel_eq` is
   it in set form.
4. `Ttc.countablyDetermined_step` — one iteration.  It factors through the pair
   `(exit level, trajectory at that level)`, because `Ttc.trajOracles`' three
   random fields each read the trajectory at one level and never read `vol`
   (`Ttc.trajOracles_thin_congr`, `_pois_congr`, `_gen_congr`).
5. `Ttc.countablyDetermined_foldl_step` — the fold, by induction on the cube
   prefix, gluing at each cube.
6. `Ttc.countablyDetermined_run`, `Ttc.countablyDetermined_run_div`,
   `Ttc.countablyDetermined_ttcAlgOutput`(`_joint`), and the events.

## What is *not* claimed

Nothing here is assumed.  In particular no measurability hypothesis is added to any
statement: `Ttc.ttc_accuracy_single_measure` has exactly
`Ttc.ttc_volume_estimate`'s binders.

One correction to the picture the spike left: the headline's event depends on the
volume coins `c` as well as on the trajectory, so
`Ttc.lintegral_trajLaw_ttcRates_eq_bind`, which fixes *one* event, is not by itself
enough — `MeasureTheory.Measure.compProd_apply` is, and it wants the **joint**
measurability proved here.  `Ttc.measurableSet_good_event` (fixed `c`) is still
exactly what that lemma's hypothesis asks for at each `c`.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory

/-! ## Part 0.  Countably determined maps -/

/-- **`f` is countably determined**: it takes only countably many values, and every
fibre is measurable.

This is exactly the right notion for the run: the intermediate state of `Ttc.run`
lives in `Ttc.SketchState n`, whose `X` field is a `Multiset (Space n)` — a type
carrying *no* measurable structure — so "measurable" cannot even be stated for it.
"Countably determined" can: it is a statement about the fibres of `f` in `Ω`, and
the target is an arbitrary type.

It composes in all the ways the fold needs (`Ttc.CountablyDetermined.map`,
`.prodMk`, `.bind`, `.of_factors`), and it *implies* measurability whenever the
target does carry a measurable structure
(`Ttc.CountablyDetermined.measurableSet_preimage`, `.measurable`) — for **every**
set of the target, measurable or not. -/
def CountablyDetermined {Ω : Type*} [MeasurableSpace Ω] {β : Type*} (f : Ω → β) : Prop :=
  (Set.range f).Countable ∧ ∀ b : β, MeasurableSet (f ⁻¹' {b})

namespace CountablyDetermined

variable {Ω : Type*} [MeasurableSpace Ω] {β γ : Type*}

/-- **Every preimage is measurable** — not just the preimages of measurable sets.
A countably determined map has countably many fibres, each measurable, so any
preimage is a countable union of them. -/
theorem measurableSet_preimage {f : Ω → β} (hf : CountablyDetermined f) (S : Set β) :
    MeasurableSet (f ⁻¹' S) := by
  have hrw : f ⁻¹' S = ⋃ b ∈ Set.range f ∩ S, f ⁻¹' {b} := by
    ext ω
    constructor
    · intro h
      exact Set.mem_biUnion (⟨⟨ω, rfl⟩, h⟩ : f ω ∈ Set.range f ∩ S) rfl
    · intro h
      obtain ⟨b, hb, hωb⟩ := Set.mem_iUnion₂.1 h
      have hb' : f ω = b := hωb
      show f ω ∈ S
      rw [hb']
      exact hb.2
  rw [hrw]
  exact MeasurableSet.biUnion (hf.1.mono Set.inter_subset_left) fun b _ => hf.2 b

/-- A countably determined map into a measurable space is measurable. -/
theorem measurable [MeasurableSpace β] {f : Ω → β} (hf : CountablyDetermined f) :
    Measurable f := fun S _ => hf.measurableSet_preimage S

/-- **Post-composition with an arbitrary function.** No measurability of `g` is
needed: the fibres of `g ∘ f` are unions of fibres of `f`. -/
theorem map {f : Ω → β} (hf : CountablyDetermined f) (g : β → γ) :
    CountablyDetermined fun ω => g (f ω) := by
  refine ⟨?_, fun c => hf.measurableSet_preimage (g ⁻¹' {c})⟩
  refine (hf.1.image g).mono ?_
  rintro _ ⟨ω, rfl⟩
  exact ⟨f ω, ⟨ω, rfl⟩, rfl⟩

/-- **Pre-composition with a measurable map.** -/
theorem precomp {Ω' : Type*} [MeasurableSpace Ω'] {f : Ω → β} (hf : CountablyDetermined f)
    {g : Ω' → Ω} (hg : Measurable g) : CountablyDetermined fun ω' => f (g ω') := by
  refine ⟨hf.1.mono ?_, fun b => hg (hf.2 b)⟩
  rintro _ ⟨ω', rfl⟩
  exact ⟨g ω', rfl⟩

/-- **Pairing.** -/
theorem prodMk {f : Ω → β} {g : Ω → γ} (hf : CountablyDetermined f)
    (hg : CountablyDetermined g) : CountablyDetermined fun ω => (f ω, g ω) := by
  refine ⟨(hf.1.prod hg.1).mono ?_, fun bc => ?_⟩
  · rintro _ ⟨ω, rfl⟩
    exact ⟨⟨ω, rfl⟩, ⟨ω, rfl⟩⟩
  · have hrw : (fun ω => (f ω, g ω)) ⁻¹' {bc} = f ⁻¹' {bc.1} ∩ g ⁻¹' {bc.2} := by
      ext ω
      simp [Prod.ext_iff]
    rw [hrw]
    exact (hf.2 _).inter (hg.2 _)

/-- **Dependent gluing.**  If `f` is countably determined and, for *each* value `b`
it can take, `g b` is countably determined, then so is the diagonal
`ω ↦ g (f ω) ω`.  This is what turns "the state after the prefix is countably
determined" into "the state after one more cube is". -/
theorem bind {f : Ω → β} (hf : CountablyDetermined f) {g : β → Ω → γ}
    (hg : ∀ b, CountablyDetermined (g b)) :
    CountablyDetermined fun ω => g (f ω) ω := by
  refine ⟨(hf.1.biUnion fun b _ => (hg b).1).mono ?_, fun c => ?_⟩
  · rintro _ ⟨ω, rfl⟩
    exact Set.mem_biUnion (⟨ω, rfl⟩ : f ω ∈ Set.range f) ⟨ω, rfl⟩
  · have hrw : (fun ω => g (f ω) ω) ⁻¹' {c}
        = ⋃ b ∈ Set.range f, f ⁻¹' {b} ∩ (g b) ⁻¹' {c} := by
      ext ω
      constructor
      · intro h
        exact Set.mem_biUnion (⟨ω, rfl⟩ : f ω ∈ Set.range f) ⟨rfl, h⟩
      · intro h
        obtain ⟨b, _, hb1, hb2⟩ := Set.mem_iUnion₂.1 h
        have hfb : f ω = b := hb1
        show g (f ω) ω = c
        rw [hfb]
        exact hb2
    rw [hrw]
    exact MeasurableSet.biUnion hf.1 fun b _ => (hf.2 b).inter ((hg b).2 c)

/-- **Factoring.**  Anything that only depends on `ω` through a countably
determined `f` is itself countably determined — without having to name the
function it factors through. -/
theorem of_factors {f : Ω → β} (hf : CountablyDetermined f) {h : Ω → γ}
    (hfac : ∀ ω ω', f ω = f ω' → h ω = h ω') : CountablyDetermined h := by
  constructor
  · refine (hf.1.biUnion fun b _ => ?_ : (⋃ b ∈ Set.range f, h '' (f ⁻¹' {b})).Countable).mono ?_
    · refine Set.Subsingleton.countable ?_
      rintro _ ⟨ω, hω, rfl⟩ _ ⟨ω', hω', rfl⟩
      exact hfac ω ω' (by rw [show f ω = b from hω, show f ω' = b from hω'])
    · rintro _ ⟨ω, rfl⟩
      exact Set.mem_biUnion (⟨ω, rfl⟩ : f ω ∈ Set.range f) ⟨ω, rfl, rfl⟩
  · intro c
    have hrw : h ⁻¹' {c} = ⋃ b ∈ {b ∈ Set.range f | ∃ ω, f ω = b ∧ h ω = c}, f ⁻¹' {b} := by
      ext ω
      constructor
      · intro hω
        exact Set.mem_biUnion (⟨⟨ω, rfl⟩, ω, rfl, hω⟩ :
          f ω ∈ {b ∈ Set.range f | ∃ ω, f ω = b ∧ h ω = c}) rfl
      · intro hω
        obtain ⟨b, hb, hωb⟩ := Set.mem_iUnion₂.1 hω
        obtain ⟨-, ω', hω'b, hω'c⟩ := hb
        have : f ω = f ω' := by rw [show f ω = b from hωb, hω'b]
        exact (hfac ω ω' this).trans hω'c
    rw [hrw]
    exact MeasurableSet.biUnion (hf.1.mono fun _ hb => hb.1) fun b _ => hf.2 b

/-- **A property that only depends on `ω` through a countably determined `f`
carves out a measurable set.** -/
theorem measurableSet_setOf {f : Ω → β} (hf : CountablyDetermined f) {Q : Ω → Prop}
    (hQ : ∀ ω ω', f ω = f ω' → (Q ω ↔ Q ω')) : MeasurableSet {ω | Q ω} := by
  have h : CountablyDetermined fun ω => (Q ω : Prop) :=
    hf.of_factors fun ω ω' hh => propext (hQ ω ω' hh)
  have h2 := h.measurableSet_preimage {True}
  have hrw : (fun ω => (Q ω : Prop)) ⁻¹' {True} = {ω | Q ω} := by
    ext ω
    simp
  rwa [hrw] at h2

end CountablyDetermined

/-- **A constant is countably determined.** -/
theorem countablyDetermined_const {Ω : Type*} [MeasurableSpace Ω] {β : Type*} (b : β) :
    CountablyDetermined fun _ : Ω => b := by
  refine ⟨(Set.countable_singleton b).mono ?_, fun b' => ?_⟩
  · rintro _ ⟨ω, rfl⟩; rfl
  · by_cases h : b = b'
    · subst h
      have : (fun _ : Ω => b) ⁻¹' {b} = Set.univ := by ext ω; simp
      rw [this]; exact MeasurableSet.univ
    · have : (fun _ : Ω => b) ⁻¹' {b'} = ∅ := by ext ω; simp [h]
      rw [this]; exact MeasurableSet.empty

/-- **A single coordinate of a sequence with countable, discrete values is
countably determined.**  This is the base case of everything below: the trajectory
space is `ℕ → Fin L → ℕ`, and `Fin L → ℕ` is countable with measurable
singletons. -/
theorem countablyDetermined_apply {Y : Type*} [MeasurableSpace Y] [Countable Y]
    [MeasurableSingletonClass Y] (k : ℕ) :
    CountablyDetermined fun τ : ℕ → Y => τ k :=
  ⟨Set.to_countable _, fun y => measurable_pi_apply k (measurableSet_singleton y)⟩

/-- **`Nat.sInf` of a countable family of measurable conditions is countably
determined.**  The unbounded search of `Ttc.absorbLevel` is exactly of this shape,
including the degenerate branch where the search never succeeds and `Nat.sInf`
returns its junk value `0`. -/
theorem countablyDetermined_natSInf {Ω : Type*} [MeasurableSpace Ω] (Pr : ℕ → Ω → Prop)
    (h : ∀ j, MeasurableSet {ω | Pr j ω}) :
    CountablyDetermined fun ω => sInf {j | Pr j ω} := by
  refine ⟨Set.to_countable _, fun k => ?_⟩
  show MeasurableSet {ω | sInf {j | Pr j ω} = k}
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hrw : {ω | sInf {j | Pr j ω} = 0}
        = {ω | Pr 0 ω} ∪ ⋂ j, {ω | Pr j ω}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iInter, Set.mem_compl_iff,
        Nat.sInf_eq_zero]
      constructor
      · rintro (h0 | he)
        · exact Or.inl h0
        · exact Or.inr fun j hj => by
            have : j ∈ ({j | Pr j ω} : Set ℕ) := hj
            rw [he] at this; exact this
      · rintro (h0 | he)
        · exact Or.inl h0
        · exact Or.inr (Set.eq_empty_iff_forall_notMem.2 he)
    rw [hrw]
    exact (h 0).union (MeasurableSet.iInter fun j => (h j).compl)
  · have hrw : {ω | sInf {j | Pr j ω} = k}
        = {ω | Pr k ω} ∩ ⋂ j ∈ Finset.range k, {ω | Pr j ω}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
        Finset.mem_range]
      constructor
      · intro hs
        have hne : ({j | Pr j ω} : Set ℕ).Nonempty := by
          by_contra hc
          rw [Set.not_nonempty_iff_eq_empty] at hc
          rw [hc, Nat.sInf_empty] at hs
          omega
        refine ⟨hs ▸ Nat.sInf_mem hne, fun j hj hjm => ?_⟩
        exact Nat.notMem_of_lt_sInf (by rw [hs]; exact hj) hjm
      · rintro ⟨hk', hlt⟩
        have hle : sInf {j | Pr j ω} ≤ k := Nat.sInf_le hk'
        have hne : ({j | Pr j ω} : Set ℕ).Nonempty := ⟨k, hk'⟩
        by_contra hne'
        exact hlt _ (lt_of_le_of_ne hle hne') (Nat.sInf_mem hne)
    rw [hrw]
    exact (h k).inter (MeasurableSet.biInter (Set.to_countable _) fun j _ => (h j).compl)

/-! ## Part 1.  The trajectory bundle reads the trajectory one level at a time

`Ttc.trajOracles`' three random fields — `thin`, `pois`, `gen` — each consult the
trajectory at exactly one level and never consult `vol`.  That is the whole reason
the fold below is tractable: an iteration's dependence on the trajectory collapses
to its dependence at the single level the absorption loop exits at. -/

section Traj

variable {n L : ℕ} {ι : Type*} {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)

@[simp] theorem trajOracles_vol (vol : ι → ℝ) (τ : ℕ → Fin L → ℕ) :
    (trajOracles hpt vol covered mem τ).vol = vol := rfl

@[simp] theorem trajOracles_covered (vol : ι → ℝ) (τ : ℕ → Fin L → ℕ) :
    (trajOracles hpt vol covered mem τ).covered = covered := rfl

theorem trajOracles_thin (vol : ι → ℝ) (τ : ℕ → Fin L → ℕ) (j₀ j' : ℕ)
    (X : Multiset (Space n)) :
    (trajOracles hpt vol covered mem τ).thin j₀ j' X
      = toMultiset pt fun s => min (τ j' s) (Multiset.count (pt s) X) := rfl

theorem trajOracles_pois (vol : ι → ℝ) (τ : ℕ → Fin L → ℕ) (i : ι) (j' : ℕ) (lam : ℝ) :
    (trajOracles hpt vol covered mem τ).pois i j' lam
      = ∑ s ∈ Finset.univ.filter fun s => mem i s = true, τ j' s := rfl

theorem dropCovered_trajOracles (vol : ι → ℝ) (τ : ℕ → Fin L → ℕ) (i : ι)
    (X : Multiset (Space n)) :
    dropCovered (trajOracles hpt vol covered mem τ) i X
      = Multiset.filter (fun s => covered s i = false) X := rfl

/-- **`thin` reads the trajectory at one level, and never reads `vol`.** -/
theorem trajOracles_thin_congr {vol vol' : ι → ℝ} {τ τ' : ℕ → Fin L → ℕ} {j' : ℕ}
    (h : τ j' = τ' j') (j₀ : ℕ) (X : Multiset (Space n)) :
    (trajOracles hpt vol covered mem τ).thin j₀ j' X
      = (trajOracles hpt vol' covered mem τ').thin j₀ j' X := by
  rw [trajOracles_thin, trajOracles_thin, h]

/-- **`pois` reads the trajectory at one level, and never reads its rate or
`vol`.** -/
theorem trajOracles_pois_congr {vol vol' : ι → ℝ} {τ τ' : ℕ → Fin L → ℕ} {j' : ℕ}
    (h : τ j' = τ' j') (i : ι) (lam lam' : ℝ) :
    (trajOracles hpt vol covered mem τ).pois i j' lam
      = (trajOracles hpt vol' covered mem τ').pois i j' lam' := by
  rw [trajOracles_pois, trajOracles_pois, h]

/-- **`gen` reads the trajectory at one level, and never reads `vol`.** -/
theorem trajOracles_gen_congr {vol vol' : ι → ℝ} {τ τ' : ℕ → Fin L → ℕ} {j' : ℕ}
    (h : τ j' = τ' j') (i : ι) (N : ℕ) (ρ : ℤ) :
    (trajOracles hpt vol covered mem τ).gen i j' N ρ
      = (trajOracles hpt vol' covered mem τ').gen i j' N ρ := by
  show (if Multiset.card (toMultiset pt fun s => if mem i s then τ j' s else 0) = N then
      toMultiset pt (fun s => if mem i s then τ j' s else 0)
    else Multiset.replicate N (padPoint pt mem i))
    = (if Multiset.card (toMultiset pt fun s => if mem i s then τ' j' s else 0) = N then
      toMultiset pt (fun s => if mem i s then τ' j' s else 0)
    else Multiset.replicate N (padPoint pt mem i))
  rw [h]

end Traj

/-! ## Part 2.  The two loops of one iteration

Both `while` loops of `alg:ttc` lines 32–42 are unbounded `Nat.sInf` searches.  The
halting loop (lines 32–35) is deterministic and reads only the volume estimate; the
absorption loop (lines 39–42) reads the trajectory, one level per trial. -/

/-- **`alg:ttc` lines 32–35, the halting loop.**  Its exit level is countably
determined in whatever the volume estimate is measurable in: for each candidate
level the test `Thresh/t ≤ 2^{-j'}` is a preimage of a ray under `t`. -/
theorem countablyDetermined_haltLevel {Ω : Type*} [MeasurableSpace Ω] (P : Params)
    (V : Ω → ℝ) (hV : Measurable V) (j : ℕ) :
    CountablyDetermined fun ω => haltLevel P (V ω) j := by
  have hsi : CountablyDetermined fun ω => sInf {j' | ¬ P.thresh / V ω ≤ (1 / 2 : ℝ) ^ j'} := by
    refine countablyDetermined_natSInf _ fun j' => ?_
    have hrw : {ω | ¬ P.thresh / V ω ≤ (1 / 2 : ℝ) ^ j'}
        = (fun ω => P.thresh / V ω) ⁻¹' Set.Ioi ((1 / 2 : ℝ) ^ j') := by
      ext ω; simp [not_le]
    rw [hrw]
    exact (measurable_const.div hV) measurableSet_Ioi
  exact hsi.map fun m => max j m

section Fold

variable {n L : ℕ} {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]
    {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (V : Ω → ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    (T : Ω → ℕ → Fin L → ℕ)

/-- **The crux.**  `alg:ttc` lines 39–42's absorption loop exits at a countably
determined level.

The search is unbounded: `Nat.sInf {j' | j₁ ≤ j' ∧ ¬ Thresh < Nᵢ(j') + |thin(j')|}`.
But each trial reads the trajectory at the *single* level `j'`
(`Ttc.trajOracles_pois_congr`, `Ttc.trajOracles_thin_congr`) and reads nothing of
the rate it is handed, so each trial is a measurable event, and
`Ttc.countablyDetermined_natSInf` assembles the search — degenerate branch (the
loop never exits, `Nat.sInf` returns `0`) included. -/
theorem countablyDetermined_absorbLevel (P : Params) (i : ι) (X : Multiset (Space n))
    (j₀ : ℕ) (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (J : Ω → ℕ) (hJ : CountablyDetermined J) :
    CountablyDetermined fun ω : Ω =>
      absorbLevel P (trajOracles hpt (V ω) covered mem (T ω)) i (V ω i) X j₀ (J ω) := by
  refine hJ.bind (g := fun j₁ ω =>
    absorbLevel P (trajOracles hpt (V ω) covered mem (T ω)) i (V ω i) X j₀ j₁)
    fun j₁ => ?_
  have hsi : CountablyDetermined fun ω : Ω =>
      sInf {j' | j₁ ≤ j' ∧ ¬ P.thresh <
        ((trajOracles hpt (V ω) covered mem (T ω)).pois i j' (V ω i * (1 / 2 : ℝ) ^ j') : ℝ)
          + (Multiset.card
              ((trajOracles hpt (V ω) covered mem (T ω)).thin j₀ j' X) : ℝ)} := by
    refine countablyDetermined_natSInf _ fun j' => ?_
    refine (hT j').measurableSet_setOf ?_
    intro ω ω' h
    rw [trajOracles_pois_congr hpt covered mem h i (V ω i * (1 / 2 : ℝ) ^ j')
        (V ω' i * (1 / 2 : ℝ) ^ j'), trajOracles_thin_congr hpt covered mem h j₀ X]
  exact hsi.map fun m => max j₁ m

/-- **The crux, as a measurable set.**  For every level `k`, the event "this
iteration's absorption loop exits at level `k`" is measurable. -/
theorem measurableSet_absorbLevel_eq (P : Params) (i : ι) (X : Multiset (Space n))
    (j₀ : ℕ) (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (J : Ω → ℕ) (hJ : CountablyDetermined J) (k : ℕ) :
    MeasurableSet {ω : Ω |
      absorbLevel P (trajOracles hpt (V ω) covered mem (T ω)) i (V ω i) X j₀ (J ω) = k} :=
  (countablyDetermined_absorbLevel hpt V covered mem T P i X j₀ hT J hJ).2 k

/-- **One iteration of `alg:ttc`'s main loop is countably determined**, from any
countably determined incoming state.

The iteration reads its randomness in exactly two places: the absorption loop's
search (`Ttc.countablyDetermined_absorbLevel`), and then the surviving sketch, the
Poisson draw and the `GenerateSamples` append — all three at the *single* level the
search returned.  So the whole iteration factors through the pair
`(exit level, trajectory at that level)`, which is countably determined. -/
theorem countablyDetermined_step (P : Params) (ρ : ℤ) (i : ι) (S : SketchState n)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hH : ∀ j : ℕ, CountablyDetermined fun ω : Ω => haltLevel P (V ω i) j) :
    CountablyDetermined fun ω : Ω =>
      step P (trajOracles hpt (V ω) covered mem (T ω)) ρ S i := by
  set X₀ : Multiset (Space n) := Multiset.filter (fun s => covered s i = false) S.X with hX₀
  set K : Ω → ℕ := fun ω =>
    absorbLevel P (trajOracles hpt (V ω) covered mem (T ω)) i (V ω i) X₀ S.level
      (haltLevel P (V ω i) S.level) with hK
  have key : ∀ ω : Ω,
      step P (trajOracles hpt (V ω) covered mem (T ω)) ρ S i
        = ⟨(trajOracles hpt (V ω) covered mem (T ω)).thin S.level (K ω) X₀
            + (trajOracles hpt (V ω) covered mem (T ω)).gen i (K ω)
                ((trajOracles hpt (V ω) covered mem (T ω)).pois i (K ω)
                  (V ω i * (1 / 2 : ℝ) ^ K ω)) ρ, K ω⟩ := fun ω => rfl
  have hKcd : CountablyDetermined K :=
    countablyDetermined_absorbLevel hpt V covered mem T P i X₀ S.level hT _ (hH S.level)
  have hpair : CountablyDetermined fun ω => (K ω, T ω (K ω)) :=
    hKcd.prodMk (hKcd.bind fun k => hT k)
  refine hpair.of_factors fun ω ω' h => ?_
  have hK' : K ω = K ω' := congrArg Prod.fst h
  have hy : T ω (K ω) = T ω' (K ω') := congrArg Prod.snd h
  have hy' : T ω (K ω) = T ω' (K ω) := hy.trans (by rw [hK'])
  rw [key ω, key ω', ← hK',
    trajOracles_pois_congr hpt covered mem hy' i (V ω i * (1 / 2 : ℝ) ^ K ω)
      (V ω' i * (1 / 2 : ℝ) ^ K ω),
    trajOracles_thin_congr hpt covered mem hy' S.level X₀,
    trajOracles_gen_congr hpt covered mem hy' i _ ρ]

/-- **The fold lemma.**  The state of `alg:ttc` after *any* prefix of the cube list
is a countably determined function of the randomness, from any countably determined
starting state.  Induction on the prefix, with `Ttc.countablyDetermined_step` and
dependent gluing (`Ttc.CountablyDetermined.bind`) at each cube. -/
theorem countablyDetermined_foldl_step (P : Params) (ρ : ℤ)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hH : ∀ (i : ι) (j : ℕ), CountablyDetermined fun ω : Ω => haltLevel P (V ω i) j) :
    ∀ (cubes : List ι) (st : Ω → SketchState n), CountablyDetermined st →
      CountablyDetermined fun ω : Ω =>
        cubes.foldl (step P (trajOracles hpt (V ω) covered mem (T ω)) ρ) (st ω) := by
  intro cubes
  induction cubes with
  | nil => exact fun st hst => hst
  | cons i cs ih =>
      exact fun st hst =>
        ih _ (hst.bind fun S =>
          countablyDetermined_step hpt V covered mem T P ρ i S hT (hH i))

/-- **`alg:ttc` lines 22–46 are countably determined.** -/
theorem countablyDetermined_run (P : Params) (ρ : ℤ) (cubes : List ι)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hH : ∀ (i : ι) (j : ℕ), CountablyDetermined fun ω : Ω => haltLevel P (V ω i) j) :
    CountablyDetermined fun ω : Ω =>
      run P (trajOracles hpt (V ω) covered mem (T ω)) ρ cubes :=
  (countablyDetermined_foldl_step hpt V covered mem T P ρ hT hH cubes
      (fun _ => (⟨0, 0⟩ : SketchState n)) (countablyDetermined_const _)).map
    fun S => (Multiset.card S.X : ℝ) / S.p

/-- **`Ttc.run` rescaled** — the shape `Ttc.ttcAlgOutput` has (line A13), with the
halting loop's hypothesis replaced by the measurability of the volume estimate it
reads (`Ttc.countablyDetermined_haltLevel`). -/
theorem countablyDetermined_run_div (P : Params) (ρ : ℤ) (cubes : List ι) (q : ℝ)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hV : ∀ i, Measurable fun ω : Ω => V ω i) :
    CountablyDetermined fun ω : Ω =>
      run P (trajOracles hpt (V ω) covered mem (T ω)) ρ cubes / q :=
  (countablyDetermined_run hpt V covered mem T P ρ cubes hT
    fun i j => countablyDetermined_haltLevel P _ (hV i) j).map fun r => r / q

end Fold

/-! ## Part 3.  The headline's own event -/

section Headline

variable {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

/-- **`TTC`'s output is countably determined in the sample coins**, at every value
of the volume coins `c`.  `Ttc.ttcOracleBundle` is a `Ttc.trajOracles` bundle at
the Monte-Carlo volume estimate — a *constant* function of `t` — so this is
`Ttc.countablyDetermined_run_div`. -/
theorem countablyDetermined_ttcAlgOutput (c : ℕ → Space n) :
    CountablyDetermined fun t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ =>
      ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
        (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) := by
  refine countablyDetermined_run_div
    (Ω := ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ)
    (latticeEnum_injective _ _ _) _ _ _ _ _ _ _ _ ?_ ?_
  · exact fun k => countablyDetermined_apply
      (Y := Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) k
  · exact fun _ => measurable_const

/-- **The algorithm's output is a measurable function of the sample coins**, at
every value of the volume coins `c`. -/
theorem measurable_ttcAlgOutput_of_traj (c : ℕ → Space n) :
    Measurable fun t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ =>
      ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
        (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) :=
  (countablyDetermined_ttcAlgOutput atoms φ ε δ hε0 hε1 hn hφ hpos c).measurable

/-- **The headline's own event is measurable**, at every value of the volume coins
`c`.  This is `Ttc.ttc_volume_estimate`'s accuracy conjunct's event, verbatim. -/
theorem measurableSet_good_event (c : ℕ → Space n) :
    MeasurableSet {t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ |
      ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t)
        ∈ relErr ε (volSol (atomSet atoms) φ)} :=
  (countablyDetermined_ttcAlgOutput atoms φ ε δ hε0 hε1 hn hφ hpos c).measurableSet_preimage _

/-! ### Jointly in both coin sequences

The headline's event depends on the volume coins `c` as well as on the trajectory —
`Ttc.ttcOracleBundle` is applied to both — so `Ttc.lintegral_trajLaw_ttcRates_eq_bind`,
which fixes one event, does not by itself fold the iterated integral into a single
measure.  What does is `MeasureTheory.Measure.compProd_apply`, and it needs the
event measurable **jointly**.  It is: the volume coins enter the run only through
the volume estimate, and the volume estimate only through the halting loop's exit
level, which `Ttc.countablyDetermined_haltLevel` handles from
`Ttc.measurable_mcVol`. -/

/-- **`TTC`'s output is countably determined in both coin sequences at once.** -/
theorem countablyDetermined_ttcAlgOutput_joint :
    CountablyDetermined fun p : (ℕ → Space n)
        × (ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) =>
      ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
        (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos p.1 p.2) := by
  refine countablyDetermined_run_div
    (Ω := (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ))
    (latticeEnum_injective _ _ _) _ _ _ _ _ _ _ _ ?_ ?_
  · exact fun k => (countablyDetermined_apply
      (Y := Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) k).precomp measurable_snd
  · exact fun i => (measurable_mcVol _ _ _ _ _ _ i).comp measurable_fst

/-- **The headline's own event is measurable jointly in the volume coins and the
trajectory.** -/
theorem measurableSet_good_event_joint :
    MeasurableSet {p : (ℕ → Space n)
        × (ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) |
      ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos p.1 p.2)
        ∈ relErr ε (volSol (atomSet atoms) φ)} :=
  (countablyDetermined_ttcAlgOutput_joint atoms φ ε δ hε0 hε1 hn hφ hpos).measurableSet_preimage _

/-- **The payoff: the headline's accuracy conjunct is one measure of one event.**

The iterated integral of `Ttc.ttc_volume_estimate` — outer over the volume coins,
inner the trajectory law at the rates that run produced — is the composition–product
of the coin law with `Ttc.ttcTrajKernel`, applied to the *joint* good event.  No
hypothesis: the measurability the rewrite needs is
`Ttc.measurableSet_good_event_joint`. -/
theorem lintegral_good_event_eq_compProd :
    (∫⁻ c, trajLaw (ttcRates atoms φ ε δ hε0 hε1 hn hφ hpos c)
        {t | ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
                (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t)
              ∈ relErr ε (volSol (atomSet atoms) φ)} ∂(MonteCarlo.coins n))
      = (MonteCarlo.coins n ⊗ₘ ttcTrajKernel atoms φ ε δ hε0 hε1 hn hφ hpos)
          {p | ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
                  (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos p.1 p.2)
                ∈ relErr ε (volSol (atomSet atoms) φ)} := by
  exact (Measure.compProd_apply (μ := MonteCarlo.coins n)
    (κ := ttcTrajKernel atoms φ ε δ hε0 hε1 hn hφ hpos)
    (measurableSet_good_event_joint atoms φ ε δ hε0 hε1 hn hφ hpos)).symm

/-- **The headline's accuracy conjunct, over a single program.**

`Ttc.ttc_volume_estimate`'s accuracy half (equivalently `Ttc.ttc_volume_api`'s),
with its iterated integral replaced by one measure — the composition–product of the
volume coins with the coin-indexed trajectory kernel — applied to one event of one
space.  Nothing is assumed: the rewrite is
`Ttc.lintegral_good_event_eq_compProd`. -/
theorem ttc_accuracy_single_measure (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ ((MonteCarlo.coins n ⊗ₘ ttcTrajKernel atoms φ ε δ hε0 hε1 hn hφ hpos)
        {p | ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
                (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos p.1 p.2)
              ∈ relErr ε (volSol (atomSet atoms) φ)}).toReal := by
  have h : 1 - δ ≤
      (∫⁻ c, trajLaw (ttcRates atoms φ ε δ hε0 hε1 hn hφ hpos c)
          {t | ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
                  (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t)
                ∈ relErr ε (volSol (atomSet atoms) φ)} ∂(MonteCarlo.coins n)).toReal :=
    (ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos).1
  rwa [lintegral_good_event_eq_compProd] at h

end Headline

#print axioms CountablyDetermined
#print axioms CountablyDetermined.measurableSet_preimage
#print axioms CountablyDetermined.measurable
#print axioms CountablyDetermined.map
#print axioms CountablyDetermined.precomp
#print axioms CountablyDetermined.prodMk
#print axioms CountablyDetermined.bind
#print axioms CountablyDetermined.of_factors
#print axioms CountablyDetermined.measurableSet_setOf
#print axioms countablyDetermined_const
#print axioms countablyDetermined_apply
#print axioms countablyDetermined_natSInf
#print axioms countablyDetermined_haltLevel
#print axioms countablyDetermined_absorbLevel
#print axioms measurableSet_absorbLevel_eq
#print axioms countablyDetermined_step
#print axioms countablyDetermined_foldl_step
#print axioms countablyDetermined_run
#print axioms countablyDetermined_run_div
#print axioms countablyDetermined_ttcAlgOutput
#print axioms measurable_ttcAlgOutput_of_traj
#print axioms measurableSet_good_event
#print axioms countablyDetermined_ttcAlgOutput_joint
#print axioms measurableSet_good_event_joint
#print axioms lintegral_good_event_eq_compProd
#print axioms ttc_accuracy_single_measure

end Ttc

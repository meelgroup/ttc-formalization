/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.EventMeasurable

/-!
# `Monadic/Pair`: the run's *cost* is a measurable read-off too

`Monadic/EventMeasurable` proves that `alg:ttc`'s **output** is a countably determined
— hence measurable — function of the run `p = (c, t)`.  This file does the same for
`alg:ttc`'s charged **cost** `Ttc.runCost`, which is what lets `Monadic/Program` push
`Ttc.ttcLaw` forward along the pair read-off `p ↦ (output p, cost p)` and obtain a
single `Measure (ℝ × ℕ)` — the `Measure`-level analogue of nfalean's
`ApproxNFA.countNFAM : PMF (ℝ × ℕ)`.

## Why this needs a separate argument

`Ttc.runCost` is *not* a function of `Ttc.run`.  It is a second fold along the same
cube list, accumulating `Ttc.stepCost cVol cSample Nᵢ` where `Nᵢ` is the Poisson draw
that survived iteration `i`'s absorption loop — a quantity `Ttc.run` throws away.  So
the existing fold lemma (`Ttc.countablyDetermined_foldl_step`, whose state is a
`Ttc.SketchState n`) does not cover it; the state here is `ℕ × Ttc.SketchState n`.

Everything else is reused verbatim.  The new content is exactly one lemma —
`Ttc.countablyDetermined_stepPre_snd`, that iteration `i`'s surviving Poisson count is
countably determined — proved by the same factorisation
`Ttc.CountablyDetermined.of_factors` through `(exit level, trajectory at that level)`
that `Ttc.countablyDetermined_step` uses.  The fold and the `TTC`-level specialisation
then follow the shape of `Monadic/EventMeasurable`'s Part 2 and Part 3.

## The pushforward lemma

`Ttc.map_apply_of_countablyDetermined` is the second half of the file and is what makes
the transfer lemmas of `Monadic/Program` **unconditional** in the event.  Mathlib's
`MeasureTheory.Measure.map_apply` evaluates a pushforward only at *measurable* sets;
but a countably determined map has a countable range, so `A ∩ range f` is countable —
hence measurable in a `MeasurableSingletonClass` target — and
`(A ∩ range f) ∪ (range f)ᶜ` is a measurable superset of `A` with the same preimage.
So the pushforward of a countably determined map agrees with the preimage measure at
**every** set, measurable or not.  This is the exact analogue of the fact that
nfalean's `PMF.toOuterMeasure` needs no measurability hypothesis at all.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory

/-! ## Part 1.  The charged cost of a run is countably determined -/

section CostFold

variable {n L : ℕ} {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]
    {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (V : Ω → ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    (T : Ω → ℕ → Fin L → ℕ)

/-- **The surviving Poisson count of one iteration is countably determined.**

`Ttc.stepPre`'s second component is `Nᵢ`, the draw the absorption loop exited on —
the number `Ttc.stepCost` charges `cSample` per unit of.  Like the state
(`Ttc.countablyDetermined_step`), it reads the trajectory only at the single level
the search returned, so it factors through the pair
`(exit level, trajectory at that level)`. -/
theorem countablyDetermined_stepPre_snd (P : Params) (i : ι) (S : SketchState n)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hH : ∀ j : ℕ, CountablyDetermined fun ω : Ω => haltLevel P (V ω i) j) :
    CountablyDetermined fun ω : Ω =>
      (stepPre P (trajOracles hpt (V ω) covered mem (T ω)) S i).2 := by
  set X₀ : Multiset (Space n) := Multiset.filter (fun s => covered s i = false) S.X with hX₀
  set K : Ω → ℕ := fun ω =>
    absorbLevel P (trajOracles hpt (V ω) covered mem (T ω)) i (V ω i) X₀ S.level
      (haltLevel P (V ω i) S.level) with hK
  have key : ∀ ω : Ω,
      (stepPre P (trajOracles hpt (V ω) covered mem (T ω)) S i).2
        = (trajOracles hpt (V ω) covered mem (T ω)).pois i (K ω)
            (V ω i * (1 / 2 : ℝ) ^ K ω) := fun ω => rfl
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
      (V ω' i * (1 / 2 : ℝ) ^ K ω)]

/-- **The cost fold lemma.**  `Ttc.runCost`'s accumulator-and-state pair, after *any*
prefix of the cube list, is a countably determined function of the randomness.

The same induction as `Ttc.countablyDetermined_foldl_step`, but over the richer state
`ℕ × Ttc.SketchState n`: at each cube the new accumulator is
`Ttc.countablyDetermined_stepPre_snd` post-composed with `Ttc.stepCost`, and the new
sketch is `Ttc.countablyDetermined_step`. -/
theorem countablyDetermined_foldl_cost (P : Params) (ρ : ℤ) (cVol cSample : ℕ)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hH : ∀ (i : ι) (j : ℕ), CountablyDetermined fun ω : Ω => haltLevel P (V ω i) j) :
    ∀ (cubes : List ι) (acc : Ω → ℕ × SketchState n), CountablyDetermined acc →
      CountablyDetermined fun ω : Ω =>
        cubes.foldl
          (fun (a : ℕ × SketchState n) i =>
            (a.1 + stepCost cVol cSample
                (stepPre P (trajOracles hpt (V ω) covered mem (T ω)) a.2 i).2,
              step P (trajOracles hpt (V ω) covered mem (T ω)) ρ a.2 i))
          (acc ω) := by
  intro cubes
  induction cubes with
  | nil => exact fun _ hacc => hacc
  | cons i cs ih =>
      intro acc hacc
      refine ih _ (hacc.bind (g := fun (a : ℕ × SketchState n) (ω : Ω) =>
        (a.1 + stepCost cVol cSample
            (stepPre P (trajOracles hpt (V ω) covered mem (T ω)) a.2 i).2,
          step P (trajOracles hpt (V ω) covered mem (T ω)) ρ a.2 i)) fun a => ?_)
      exact ((countablyDetermined_stepPre_snd hpt V covered mem T P i a.2 hT (hH i)).map
          (fun N => a.1 + stepCost cVol cSample N)).prodMk
        (countablyDetermined_step hpt V covered mem T P ρ i a.2 hT (hH i))

/-- **`Ttc.runCost` is countably determined**, with the halting loop's hypothesis
replaced — as in `Ttc.countablyDetermined_run_div` — by the measurability of the volume
estimate it reads. -/
theorem countablyDetermined_runCost (P : Params) (ρ : ℤ) (cVol cSample : ℕ) (cubes : List ι)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hV : ∀ i, Measurable fun ω : Ω => V ω i) :
    CountablyDetermined fun ω : Ω =>
      runCost P (trajOracles hpt (V ω) covered mem (T ω)) cVol cSample ρ cubes :=
  (countablyDetermined_foldl_cost hpt V covered mem T P ρ cVol cSample hT
      (fun i j => countablyDetermined_haltLevel P _ (hV i) j)
      cubes (fun _ => ((0, ⟨0, 0⟩) : ℕ × SketchState n))
      (countablyDetermined_const _)).map Prod.fst

/-! ### The same, in the elementary cost model

`Ttc.elemStepCost` charges `Ttc.cubeCost` at the run's own data, so it reads the
randomness at three places rather than one.  All three are already known countably
determined, and the sketch argument is not random at all. -/

/-- **One iteration's elementary cost is countably determined.**

`Ttc.elemStepCost` reads the run at the early-reduce exit level, the overflow exit level
and the surviving Poisson count.  Its sketch argument `Ttc.dropCovered` does not depend on
the randomness at all — `covered` is a fixed function — so the whole charge factors through
a triple of countably determined values. -/
theorem countablyDetermined_elemStepCost (P : Params) (r Q Tw : ℕ) (i : ι)
    (S : SketchState n)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hH : ∀ j : ℕ, CountablyDetermined fun ω : Ω => haltLevel P (V ω i) j) :
    CountablyDetermined fun ω : Ω =>
      elemStepCost P (trajOracles hpt (V ω) covered mem (T ω)) r Q Tw S i := by
  set X₀ : Multiset (Space n) := Multiset.filter (fun s => covered s i = false) S.X with hX₀
  have hhalt : CountablyDetermined fun ω : Ω => haltLevel P (V ω i) S.level := hH S.level
  have habs : CountablyDetermined fun ω : Ω =>
      absorbLevel P (trajOracles hpt (V ω) covered mem (T ω)) i (V ω i) X₀ S.level
        (haltLevel P (V ω i) S.level) :=
    countablyDetermined_absorbLevel hpt V covered mem T P i X₀ S.level hT _ hhalt
  have hN : CountablyDetermined fun ω : Ω =>
      (stepPre P (trajOracles hpt (V ω) covered mem (T ω)) S i).2 :=
    countablyDetermined_stepPre_snd hpt V covered mem T P i S hT hH
  exact ((hhalt.prodMk habs).prodMk hN).map
    (fun p => cubeCost r X₀ (p.1.1 - S.level) (p.1.2 - p.1.1) p.2 Q Tw)

/-- **The elementary cost fold lemma.**  `Ttc.elemRunCost`'s accumulator-and-state pair,
after any prefix of the cube list, is countably determined.  Same induction as
`Ttc.countablyDetermined_foldl_cost`, with `Ttc.elemStepCost` in place of `Ttc.stepCost`. -/
theorem countablyDetermined_foldl_elemCost (P : Params) (ρ : ℤ) (r Q Tw : ℕ)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hH : ∀ (i : ι) (j : ℕ), CountablyDetermined fun ω : Ω => haltLevel P (V ω i) j) :
    ∀ (cubes : List ι) (acc : Ω → ℕ × SketchState n), CountablyDetermined acc →
      CountablyDetermined fun ω : Ω =>
        cubes.foldl
          (fun (a : ℕ × SketchState n) i =>
            (a.1 + elemStepCost P (trajOracles hpt (V ω) covered mem (T ω)) r Q Tw a.2 i,
              step P (trajOracles hpt (V ω) covered mem (T ω)) ρ a.2 i))
          (acc ω) := by
  intro cubes
  induction cubes with
  | nil => exact fun _ hacc => hacc
  | cons i cs ih =>
      intro acc hacc
      refine ih _ (hacc.bind (g := fun (a : ℕ × SketchState n) (ω : Ω) =>
        (a.1 + elemStepCost P (trajOracles hpt (V ω) covered mem (T ω)) r Q Tw a.2 i,
          step P (trajOracles hpt (V ω) covered mem (T ω)) ρ a.2 i)) fun a => ?_)
      exact ((countablyDetermined_elemStepCost hpt V covered mem T P r Q Tw i a.2 hT
            (hH i)).map (fun c => a.1 + c)).prodMk
        (countablyDetermined_step hpt V covered mem T P ρ i a.2 hT (hH i))

/-- **`Ttc.elemRunCost` is countably determined**, hence measurable — the gate for making
it the cost coordinate of a law. -/
theorem countablyDetermined_elemRunCost (P : Params) (ρ : ℤ) (r Q Tw : ℕ) (cubes : List ι)
    (hT : ∀ k, CountablyDetermined fun ω => T ω k)
    (hV : ∀ i, Measurable fun ω : Ω => V ω i) :
    CountablyDetermined fun ω : Ω =>
      elemRunCost P (trajOracles hpt (V ω) covered mem (T ω)) r Q Tw ρ cubes :=
  (countablyDetermined_foldl_elemCost hpt V covered mem T P ρ r Q Tw hT
      (fun i j => countablyDetermined_haltLevel P _ (hV i) j)
      cubes (fun _ => ((0, ⟨0, 0⟩) : ℕ × SketchState n))
      (countablyDetermined_const _)).map Prod.fst

#print axioms countablyDetermined_elemStepCost
#print axioms countablyDetermined_elemRunCost

end CostFold

/-! ## Part 2.  `TTC`'s charged cost, jointly in both coin sequences -/

section TtcCost

variable {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

/-- **`TTC`'s charged cost is countably determined in both coin sequences at once**, at
every pair of per-call charges `(cVol, cSample)`.

The volume coins enter only through the Monte-Carlo estimate (`Ttc.measurable_mcVol`,
feeding the halting loop) and the sample coins only one level at a time
(`Ttc.countablyDetermined_apply`) — exactly as for the output
(`Ttc.countablyDetermined_ttcAlgOutput_joint`). -/
theorem countablyDetermined_ttcCost_joint (cVol cSample : ℕ) :
    CountablyDetermined fun p : (ℕ → Space n)
        × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ) =>
      ttcCost atoms φ ε δ p.1 p.2 cVol cSample := by
  refine countablyDetermined_runCost
    (Ω := (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ))
    (latticeEnum_injective _ _ _) _ _ _ _ _ _ _ _ _ ?_ ?_
  · exact fun k => (countablyDetermined_apply
      (Y := Fin (ttcIndex atoms φ ε δ) → ℕ) k).precomp measurable_snd
  · exact fun i => (measurable_mcVol _ _ _ _ _ _ i).comp measurable_fst

/-- **`TTC`'s charged cost is a measurable function of the run.** -/
theorem measurable_ttcCost_joint (cVol cSample : ℕ) :
    Measurable fun p : (ℕ → Space n)
        × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ) =>
      ttcCost atoms φ ε δ p.1 p.2 cVol cSample :=
  (countablyDetermined_ttcCost_joint atoms φ ε δ cVol cSample).measurable

end TtcCost

/-! ## Part 3.  Pushing a countably determined map forward, at *every* set -/

/-- **A countably determined map's pushforward is the preimage measure at every set.**

`MeasureTheory.Measure.map_apply` needs the target set measurable.  Here it is not
needed: `Set.range f` is countable, so `(A ∩ range f) ∪ (range f)ᶜ` is a *measurable*
superset of `A` whose preimage is exactly `f ⁻¹' A`, giving `≤`; and
`MeasureTheory.le_map_apply` gives `≥`.

This is what makes `Ttc.PrR_ttcPairLaw` (`Monadic/Program`) hypothesis-free, matching
nfalean's `PMF`-level transfer, whose outer measure is defined on every set. -/
theorem map_apply_of_countablyDetermined {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [MeasurableSingletonClass β] {f : Ω → β}
    (hf : CountablyDetermined f) (μ : Measure Ω) (A : Set β) :
    μ.map f A = μ (f ⁻¹' A) := by
  have hfm : Measurable f := hf.measurable
  set B : Set β := (A ∩ Set.range f) ∪ (Set.range f)ᶜ with hB
  have hBmeas : MeasurableSet B :=
    ((hf.1.mono Set.inter_subset_right).measurableSet).union hf.1.measurableSet.compl
  have hAB : A ⊆ B := by
    intro x hx
    by_cases hr : x ∈ Set.range f
    · exact Or.inl ⟨hx, hr⟩
    · exact Or.inr hr
  have hpre : f ⁻¹' B = f ⁻¹' A := by
    ext ω
    constructor
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact absurd (Set.mem_range_self ω) h
    · intro h
      exact Or.inl ⟨h, Set.mem_range_self ω⟩
  refine le_antisymm ?_ (Measure.le_map_apply hfm.aemeasurable A)
  calc μ.map f A ≤ μ.map f B := measure_mono hAB
    _ = μ (f ⁻¹' B) := Measure.map_apply hfm hBmeas
    _ = μ (f ⁻¹' A) := by rw [hpre]

/-- **For a countably determined read-off, a.e. truth *is* the `PMF`-support notion.**

nfalean's `All[x ← p; E x]` is `PMF.support p ⊆ {x | E x}` — "`E` holds at every outcome
of positive mass".  The named hypothesis `hf : CountablyDetermined f` is exactly what
makes that notion collapse onto `∀ᵐ` for the pushforward `μ.map f`: `Set.range f` is
countable, its complement is null, and a countable union of null singletons is null, so
"no atom violates `E`" already forces the violating set to be null.  Without the
hypothesis the collapse fails — for an atomless measure the right-hand side is vacuous
while the left-hand side is not.

So a support-based quantifier is *constructible* for such a pushforward, and it buys
nothing over `∀ᵐ`.  What is genuinely stronger is a statement over all of
`Set.range f`, which admits no exceptional outcome, null or otherwise. -/
theorem ae_map_iff_atoms_of_countablyDetermined {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [MeasurableSingletonClass β] {f : Ω → β}
    (hf : CountablyDetermined f) (μ : Measure Ω) (E : β → Prop) :
    (∀ᵐ r ∂(μ.map f), E r) ↔ ∀ r : β, μ.map f {r} ≠ 0 → E r := by
  constructor
  · intro h r hr
    by_contra hE
    exact hr (measure_mono_null (Set.singleton_subset_iff.2 hE) (MeasureTheory.ae_iff.1 h))
  · intro h
    refine MeasureTheory.ae_iff.2 ?_
    have hout : μ.map f (Set.range f)ᶜ = 0 := by
      rw [map_apply_of_countablyDetermined hf]
      have hpre : f ⁻¹' (Set.range f)ᶜ = ∅ := by ext p; simp
      rw [hpre, measure_empty]
    have hin : μ.map f ({r | ¬ E r} ∩ Set.range f) = 0 := by
      have hcount : ({r : β | ¬ E r} ∩ Set.range f).Countable :=
        hf.1.mono Set.inter_subset_right
      have hrw : ({r : β | ¬ E r} ∩ Set.range f)
          = ⋃ r ∈ ({r : β | ¬ E r} ∩ Set.range f), ({r} : Set β) := by
        ext r; simp
      rw [hrw, measure_biUnion_null_iff hcount]
      intro r hr
      by_contra hne
      exact hr.1 (h r hne)
    refine le_antisymm ?_ zero_le
    calc μ.map f {r | ¬ E r}
        ≤ μ.map f (({r | ¬ E r} ∩ Set.range f) ∪ (Set.range f)ᶜ) := by
          refine measure_mono fun r hr => ?_
          by_cases hrr : r ∈ Set.range f
          · exact Or.inl ⟨hr, hrr⟩
          · exact Or.inr hrr
      _ ≤ μ.map f ({r | ¬ E r} ∩ Set.range f) + μ.map f (Set.range f)ᶜ := measure_union_le _ _
      _ = 0 := by rw [hin, hout, add_zero]

#print axioms Ttc.countablyDetermined_stepPre_snd
#print axioms Ttc.countablyDetermined_foldl_cost
#print axioms Ttc.countablyDetermined_runCost
#print axioms Ttc.countablyDetermined_ttcCost_joint
#print axioms Ttc.measurable_ttcCost_joint
#print axioms Ttc.map_apply_of_countablyDetermined
#print axioms Ttc.ae_map_iff_atoms_of_countablyDetermined

end Ttc

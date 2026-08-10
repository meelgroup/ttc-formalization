/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Coupling.Run
import Ttc.Runtime

/-!
# `Exec/Coverage`: the coverage test, constructed — and the construction shown harmless

`Ttc.ttc_volume` (`Model/Endgoal.lean`) carries the implementation's membership
test as **four** binders:

```lean
(cover : Space n → Cube A → Bool) (memPt : Cube A → Fin Lidx → Bool)
(memPt_eq : ∀ i ∈ toDNF φ, ∀ s, memPt i s = true ↔ ptE s ∈ region M i)
(cover_eq : ∀ s i, cover (ptE s) i = memPt i s)
```

Two decision procedures plus their specifications.  This file does two things.

## 1. It constructs them

`Ttc.coverOfRegion M x c := decide (x ∈ region M c)` (classically decidable) and
`Ttc.memPtOfRegion M ptE c s := coverOfRegion M (ptE s) c`.  With these,
`cover_eq` is `rfl` and `memPt_eq` is `decide_eq_true_eq`, so all four binders
disappear.

## 2. It shows the construction costs nothing

Pinning a *particular* decision procedure would normally narrow the theorem: the
paper's `TTC` runs its own coverage test, and a theorem proved only for
`Ttc.coverOfRegion` would say nothing about it.  §2 below removes that objection.

The first half is the agreement statement.  `Ttc.memPt_eq_memPtOfRegion` and
`Ttc.cover_eq_coverOfRegion` say that **any** pair meeting `memPt_eq` and
`cover_eq` *is* the constructed pair wherever the algorithm looks at it: `memPt i`
is determined, as a function, at every cube of the DNF, and `cover` is determined
at every enumerated point of such a cube.  Only the values of `cover` off the
range of the enumeration, and of `memPt` at cubes outside the DNF, are left free.

The second half says those free values are never read.  `Ttc.cover` reaches the
modelled execution through exactly one door — `Ttc.dropCovered`, in `Ttc.stepPre`
— and the result is consumed only by `Ttc.trajOracles`' `thin`, which reads its
argument *solely* through the multiplicities `Multiset.count (pt s) ·`.  That is
`Ttc.count_dropCovered_trajOracles`, and it needs **no** hypothesis on the sketch
state: the two dropped multisets differ as multisets, yet agree at every
enumerated point, so `Ttc.thin_dropCovered_trajOracles_congr` makes them the same
multiset after thinning.  Together with `Ttc.pois_trajOracles_congr`,
`Ttc.gen_trajOracles_congr` and `Ttc.vol_trajOracles` — the other three fields
`Ttc.stepPre` and `Ttc.step` consume — these are the four facts a congruence for
one loop iteration is assembled from.

`Ttc.gen_trajOracles_congr` also transfers `Ttc.ttc_volume`'s `gen_mem`, the one
*hypothesis* of that theorem which mentions the pair.

**Not yet in this file.**  The step-, run-, `runCost`- and `Terminates`-level
congruences that those four facts assemble into are drafted but **not landed**:
they elaborate too slowly to check on the machine this was written on, and
`CLAUDE.md` §4 does not admit an unchecked proof.  Until they land, the claim
"substituting the construction into `Ttc.ttc_volume` loses no generality" is
supported at the level of the oracle bundle, not yet at the level of the run.

## What this does *not* say

It does not say the paper's coverage test is *correct* — `memPt_eq` is exactly the
correctness statement, and a procedure failing it is outside the theorem either
way.  It says that among *correct* procedures the modelled execution cannot tell
them apart.
-/

namespace Ttc

open Multiset

/-! ## 1. The classical coverage test -/

section Construct

variable {A X : Type*}

/-! `Ttc.coverOfRegion` and `Ttc.memPtOfRegion` themselves are in
`Model/Pseudocode`: `alg:ttc` line 27's membership query is a step of the
algorithm, and `Ttc.ttcRun` builds its oracle bundle from it, so it has to be
inside the audit surface.  What stays here is everything *about* them. -/

@[simp] theorem coverOfRegion_eq_true (M : A → Set X) (x : X) (c : Cube A) :
    coverOfRegion M x c = true ↔ x ∈ region M c := by
  simp only [coverOfRegion, decide_eq_true_eq]

variable {n L : ℕ}

@[simp] theorem memPtOfRegion_eq_true (M : A → Set (Space n)) (ptE : Fin L → Space n)
    (c : Cube A) (s : Fin L) :
    memPtOfRegion M ptE c s = true ↔ ptE s ∈ region M c :=
  coverOfRegion_eq_true _ _ _

/-- `Ttc.ttc_volume`'s `cover_eq`, for the constructed pair: `rfl`. -/
theorem coverOfRegion_memPtOfRegion (M : A → Set (Space n)) (ptE : Fin L → Space n)
    (s : Fin L) (c : Cube A) :
    coverOfRegion M (ptE s) c = memPtOfRegion M ptE c s := rfl

/-- `Ttc.ttc_volume`'s `memPt_eq`, for the constructed pair — and with no
restriction to the cubes of the DNF. -/
theorem memPtOfRegion_spec (M : A → Set (Space n)) (ptE : Fin L → Space n) (D : DNF A) :
    ∀ i ∈ D, ∀ s, memPtOfRegion M ptE i s = true ↔ ptE s ∈ region M i :=
  fun i _ s => memPtOfRegion_eq_true M ptE i s

/-! ### Any admissible pair *is* the classical one, where it is looked at -/

/-- **`memPt` is determined on the DNF's cubes.**  Any `memPt` meeting
`Ttc.ttc_volume`'s `memPt_eq` agrees with `Ttc.memPtOfRegion` at every cube of the
decomposition — as a function of the lattice index, not merely pointwise-`iff`. -/
theorem memPt_eq_memPtOfRegion {M : A → Set (Space n)} {ptE : Fin L → Space n} {D : DNF A}
    {memPt : Cube A → Fin L → Bool}
    (h : ∀ i ∈ D, ∀ s, memPt i s = true ↔ ptE s ∈ region M i) :
    ∀ i ∈ D, memPt i = memPtOfRegion M ptE i := by
  intro i hi
  funext s
  exact Bool.eq_iff_iff.2 ((h i hi s).trans (memPtOfRegion_eq_true M ptE i s).symm)

/-- **`cover` is determined on the enumerated points, at the DNF's cubes.**  Its
values anywhere else are unconstrained — and, by
`Ttc.count_dropCovered_trajOracles`, never observed. -/
theorem cover_eq_coverOfRegion {M : A → Set (Space n)} {ptE : Fin L → Space n} {D : DNF A}
    {cover : Space n → Cube A → Bool} {memPt : Cube A → Fin L → Bool}
    (hmem : ∀ i ∈ D, ∀ s, memPt i s = true ↔ ptE s ∈ region M i)
    (hcov : ∀ s i, cover (ptE s) i = memPt i s) :
    ∀ i ∈ D, ∀ s, cover (ptE s) i = coverOfRegion M (ptE s) i := by
  intro i hi s
  rw [hcov s i, memPt_eq_memPtOfRegion hmem i hi]
  rfl

end Construct

/-! ## 2. The run observes nothing else

Everything below compares two *arbitrary* pairs `(cover, mem)`, `(cover', mem')`,
each meeting `cover_eq`, at cubes where the two membership tables agree.  The
classical pair of §1 is one admissible choice; the point is that the modelled
execution cannot distinguish any two.
-/

section Congr

variable {L n : ℕ} {ι : Type*} {pt : Fin L → Space n}
  {cover cover' : Space n → ι → Bool} {mem mem' : ι → Fin L → Bool}

/-- The two coverage tests agree at every enumerated point of a cube where the two
membership tables agree. -/
theorem cover_apply_congr (hcov : ∀ s i, cover (pt s) i = mem i s)
    (hcov' : ∀ s i, cover' (pt s) i = mem' i s) {i : ι} (hi : mem i = mem' i) (s : Fin L) :
    cover (pt s) i = cover' (pt s) i := by
  rw [hcov s i, hcov' s i, hi]

/-- **`dropCovered` has the same multiplicities.**  This is the whole content: the
filtered multisets differ off the enumeration, but `Ttc.trajOracles`' `thin` reads
its argument only through `Multiset.count (pt s) ·`. -/
theorem count_dropCovered_trajOracles (hpt : Function.Injective pt) (ω : ℕ → Fin L → ℕ)
    (vol : ι → ℝ) (hcov : ∀ s i, cover (pt s) i = mem i s)
    (hcov' : ∀ s i, cover' (pt s) i = mem' i s) {i : ι} (hi : mem i = mem' i)
    (X : Multiset (Space n)) (s : Fin L) :
    Multiset.count (pt s) (dropCovered (trajOracles hpt vol cover mem ω) i X)
      = Multiset.count (pt s) (dropCovered (trajOracles hpt vol cover' mem' ω) i X) := by
  simp only [dropCovered, trajOracles, Multiset.count_filter,
    cover_apply_congr hcov hcov' hi s]

/-- **The absorption loop sees the same sketch.**  `thin` after `dropCovered` is
literally the same multiset at both pairs. -/
theorem thin_dropCovered_trajOracles_congr (hpt : Function.Injective pt) (ω : ℕ → Fin L → ℕ)
    (vol : ι → ℝ) (hcov : ∀ s i, cover (pt s) i = mem i s)
    (hcov' : ∀ s i, cover' (pt s) i = mem' i s) {i : ι} (hi : mem i = mem' i)
    (X : Multiset (Space n)) (j₀ j' : ℕ) :
    (trajOracles hpt vol cover mem ω).thin j₀ j'
        (dropCovered (trajOracles hpt vol cover mem ω) i X)
      = (trajOracles hpt vol cover' mem' ω).thin j₀ j'
        (dropCovered (trajOracles hpt vol cover' mem' ω) i X) := by
  show toMultiset pt (fun s => min (ω j' s)
      (Multiset.count (pt s) (dropCovered (trajOracles hpt vol cover mem ω) i X)))
    = toMultiset pt (fun s => min (ω j' s)
      (Multiset.count (pt s) (dropCovered (trajOracles hpt vol cover' mem' ω) i X)))
  exact congrArg (toMultiset pt) (funext fun s => congrArg (min (ω j' s))
    (count_dropCovered_trajOracles hpt ω vol hcov hcov' hi X s))

/-- The Poisson draw depends on the membership table at the processed cube only. -/
theorem pois_trajOracles_congr (hpt : Function.Injective pt) (ω : ℕ → Fin L → ℕ)
    (vol : ι → ℝ) {i : ι} (hi : mem i = mem' i) (j : ℕ) (lam : ℝ) :
    (trajOracles hpt vol cover mem ω).pois i j lam
      = (trajOracles hpt vol cover' mem' ω).pois i j lam := by
  simp only [trajOracles, hi]

/-- `Ttc.padPoint` — `gen`'s never-taken filler — likewise. -/
theorem padPoint_congr {i : ι} (hi : mem i = mem' i) :
    padPoint pt mem i = padPoint pt mem' i := by
  unfold padPoint
  simp only [hi]

/-- **`GenerateSamples` is the same call.**  `gen` never reads `cover`, and reads
`mem` only at the cube it is asked about.  This is what transfers
`Ttc.ttc_volume`'s `gen_mem` hypothesis between admissible pairs. -/
theorem gen_trajOracles_congr (hpt : Function.Injective pt) (ω : ℕ → Fin L → ℕ)
    (vol : ι → ℝ) {i : ι} (hi : mem i = mem' i) (j N : ℕ) (r : ℤ) :
    (trajOracles hpt vol cover mem ω).gen i j N r
      = (trajOracles hpt vol cover' mem' ω).gen i j N r := by
  simp only [trajOracles, hi, padPoint_congr (pt := pt) hi]

/-- The volume field of `Ttc.trajOracles` is the one it was handed. -/
theorem vol_trajOracles (hpt : Function.Injective pt) (ω : ℕ → Fin L → ℕ) (vol : ι → ℝ) :
    (trajOracles hpt vol cover mem ω).vol = vol := rfl

/-! ### From the oracle bundle to the loop -/
end Congr

/-! ## Axiom profile

Every declaration, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms coverOfRegion
#print axioms memPtOfRegion
#print axioms coverOfRegion_eq_true
#print axioms memPtOfRegion_eq_true
#print axioms memPtOfRegion_spec
#print axioms coverOfRegion_memPtOfRegion
#print axioms memPt_eq_memPtOfRegion
#print axioms cover_eq_coverOfRegion
#print axioms cover_apply_congr
#print axioms count_dropCovered_trajOracles
#print axioms thin_dropCovered_trajOracles_congr
#print axioms pois_trajOracles_congr
#print axioms padPoint_congr
#print axioms gen_trajOracles_congr
#print axioms vol_trajOracles

end Ttc

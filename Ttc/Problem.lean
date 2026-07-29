/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Convex.Basic
import Ttc.Prelude

/-!
# The problem: SMT(LRA) formulas, their solution sets, and the decomposition

This file sets up the modelling layer used by the rest of the development: linear
atoms over `Fin n → ℝ`, Boolean formulas over an abstract atom index type, the
Boolean abstraction, literals/cubes/DNF, and the polytope attached to a cube.

## Modelling decisions

* **Atoms are abstract.** A formula is a Boolean combination of *atom indices*
  drawn from a type `A`, together with an interpretation `M : A → Set (Fin n → ℝ)`.
  This is exactly the paper's pair `(F_bool, M)` produced by `BooleanAbstraction`.
  Nothing in the decomposition argument uses linearity, so we keep `M` abstract
  and specialise to half-spaces (`LinAtom`) only where geometry is needed.

* **The abstraction property is definitional.** The paper states as a *property*
  of the Boolean abstraction that a point `x` satisfies `F` iff the induced
  Boolean assignment `a ↦ (x ∈ M a)` satisfies `F_bool`. We *define* the LRA
  semantics that way (`Ttc.sol`), so the property becomes `Ttc.mem_sol_iff`
  (`rfl`). This is the honest reading: the abstraction map is the identity on
  syntax, and the interpretation is read off pointwise.

* **Negative literals give open half-spaces.** A literal `¬(⟪a,x⟫ ≤ b)` denotes
  `{x | b < ⟪a,x⟫}`. The region of a cube is therefore an intersection of closed
  and *open* half-spaces: still convex (`Ttc.convex_region`), but in general not
  closed, hence not a polytope in the usual sense. See the docstring of
  `Ttc.convex_region`.
-/

namespace Ttc

open Set

variable {A X : Type*} {n : ℕ}

/-! ## Linear atoms -/

/-- A linear atom in `n` real variables: the constraint `∑ i, coeff i * x i ≤ bound`.
This is one row `A_ij x ≤ b_ij` of the paper's constraint matrices. -/
structure LinAtom (n : ℕ) where
  /-- The coefficient vector of the linear inequality. -/
  coeff : Fin n → ℝ
  /-- The right-hand side of the linear inequality. -/
  bound : ℝ

/-- The closed half-space denoted by a linear atom. -/
def LinAtom.halfspace (a : LinAtom n) : Set (Space n) :=
  {x | ∑ i, a.coeff i * x i ≤ a.bound}

/-! ## Boolean formulas -/

/-- Boolean formulas over an atom index type `A`. This is the paper's `F_bool`,
the Boolean abstraction of an SMT(LRA) formula. -/
inductive BForm (A : Type*) where
  /-- An atom. -/
  | atom : A → BForm A
  /-- Negation. -/
  | neg : BForm A → BForm A
  /-- Conjunction. -/
  | and : BForm A → BForm A → BForm A
  /-- Disjunction. -/
  | or : BForm A → BForm A → BForm A
  deriving Repr

/-- Satisfaction of a Boolean formula under a (`Prop`-valued) assignment. -/
def BForm.holds (v : A → Prop) : BForm A → Prop
  | .atom a => v a
  | .neg φ => ¬ φ.holds v
  | .and φ ψ => φ.holds v ∧ ψ.holds v
  | .or φ ψ => φ.holds v ∨ ψ.holds v

/-! ## Literals, cubes, DNF -/

/-- A literal: an atom index together with a polarity. -/
structure Lit (A : Type*) where
  /-- The underlying atom. -/
  atom : A
  /-- `true` for a positive occurrence, `false` for a negated one. -/
  pos : Bool

/-- Satisfaction of a literal under an assignment. -/
def Lit.holds (v : A → Prop) (l : Lit A) : Prop :=
  cond l.pos (v l.atom) (¬ v l.atom)

/-- A cube is a conjunction of literals, represented as a list. -/
abbrev Cube (A : Type*) := List (Lit A)

/-- A cube holds when every one of its literals holds. -/
def Cube.holds (v : A → Prop) (c : Cube A) : Prop := ∀ l ∈ c, l.holds v

/-- A DNF is a disjunction of cubes, represented as a list. -/
abbrev DNF (A : Type*) := List (Cube A)

/-- A DNF holds when some one of its cubes holds. -/
def DNF.holds (v : A → Prop) (D : DNF A) : Prop := ∃ c ∈ D, c.holds v

/-- `D` is a DNF representation of `φ` when the two are equisatisfiable under
every Boolean assignment. This is what the paper's `ToDNF` (circuit AllSAT)
is assumed to deliver. -/
def IsDNFOf (D : DNF A) (φ : BForm A) : Prop := ∀ v : A → Prop, D.holds v ↔ φ.holds v

/-! ## Semantics over the reals -/

variable (M : A → Set X)

/-- The Boolean assignment a point induces on atoms. -/
def induced (x : X) : A → Prop := fun a => x ∈ M a

/-- The solution set of an SMT(LRA) formula: the paper's `Sol(F)`. -/
def sol (φ : BForm A) : Set X := {x | φ.holds (induced M x)}

/-- The set denoted by a literal. -/
def litSet (l : Lit A) : Set X :=
  cond l.pos (M l.atom) (M l.atom)ᶜ

/-- The region carved out by a cube: the paper's `P(c)`, the conjunction of the
linear constraints named by the cube's literals. -/
def region (c : Cube A) : Set X := {x | c.holds (induced M x)}

variable {M}

/-- The Boolean abstraction property: a point satisfies the formula exactly when
the Boolean assignment it induces satisfies the Boolean abstraction. -/
@[simp]
theorem mem_sol_iff {φ : BForm A} {x : X} :
    x ∈ sol M φ ↔ φ.holds (induced M x) := Iff.rfl

@[simp]
theorem mem_region_iff {c : Cube A} {x : X} :
    x ∈ region M c ↔ ∀ l ∈ c, l.holds (induced M x) := Iff.rfl

/-- A cube's region is the intersection of the sets denoted by its literals. -/
theorem region_eq_iInter (c : Cube A) :
    region M c = ⋂ l ∈ c, litSet M l := by
  ext x
  simp only [mem_region_iff, mem_iInter]
  refine forall_congr' fun l => forall_congr' fun _ => ?_
  cases hb : l.pos <;> simp [Lit.holds, litSet, hb, induced]

/-- Regions are monotone in the cube: adding literals shrinks the region. -/
theorem region_subset_of_sublist {c d : Cube A} (h : ∀ l ∈ c, l ∈ d) :
    region M d ⊆ region M c := fun _ hx l hl => hx l (h l hl)

/-! ## Convexity of a cube's region

The paper asserts that each cube denotes a *convex polytope*. With linear atoms
this is true for convexity, but a negated atom contributes the **open** half-space
`{x | b < ⟪a,x⟫}`, so the region is in general not closed. See below.
-/

/-- Each `litSet` of a linear atom system is convex: a positive literal gives a
closed half-space, a negative literal the complementary **open** half-space.

This substantiates the paper's claim that `P(c)` is convex. Note that it is *not*
in general a polytope in the standard (closed, `Ax ≤ b`) sense: negative literals
contribute strict inequalities. -/
theorem convex_litSet (atoms : A → LinAtom n) (l : Lit A) :
    Convex ℝ (litSet (fun a => (atoms a).halfspace) l) := by
  have hlin : IsLinearMap ℝ (fun x : Space n => ∑ i, (atoms l.atom).coeff i * x i) := by
    constructor
    · intro x y
      simp only [PiLp.add_apply, mul_add]
      exact Finset.sum_add_distrib
    · intro c x
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  cases hb : l.pos
  · have : (litSet (fun a => (atoms a).halfspace) l) =
        {x : Space n | (atoms l.atom).bound < ∑ i, (atoms l.atom).coeff i * x i} := by
      ext x; simp [litSet, hb, LinAtom.halfspace, not_le]
    rw [this]
    exact convex_halfSpace_gt hlin _
  · have : (litSet (fun a => (atoms a).halfspace) l) =
        {x : Space n | ∑ i, (atoms l.atom).coeff i * x i ≤ (atoms l.atom).bound} := by
      ext x; simp [litSet, hb, LinAtom.halfspace]
    rw [this]
    exact convex_halfSpace_le hlin _

/-- The region of a cube over linear atoms is convex. -/
theorem convex_region (atoms : A → LinAtom n) (c : Cube A) :
    Convex ℝ (region (fun a => (atoms a).halfspace) c) := by
  rw [region_eq_iInter]
  exact convex_iInter fun l => convex_iInter fun _ => convex_litSet atoms l

/-! # The decomposition lemma (`thm:decomposition`)

# The decomposition lemma

Formalisation of `thm:decomposition` of *Efficient Volume Computation
for SMT Formulas*:

> Let `F_dnf = ⋁_{i=1}^m c_i` be the DNF abstraction of the SMT formula `F`. Then
> `⋃_{i=1}^m P(c_i) = Sol(F)`.

The paper splits the argument into *soundness* (`P(c_i) ⊆ Sol(F)`) and
*completeness* (`Sol(F) ⊆ ⋃ P(c_i)`); we keep that split
(`Ttc.region_subset_sol`, `Ttc.sol_subset_iUnion_region`) and then combine.

**This module is fully proved: no hypotheses beyond `IsDNFOf`.**

## What the formalisation exposes

The paper's proof of soundness argues "by construction `ℓ_ij ⊨ F_dnf`, therefore by
the property of Boolean abstraction, if `⋀ M(ℓ_ij)` can be satisfied then `F` is
satisfied". That phrasing is a slip: an individual literal does not entail the
DNF, and the direction actually needed is that the *cube* entails the formula. The
correct and sufficient hypothesis is exactly `IsDNFOf D φ`, i.e. that `D` and `φ`
agree on every Boolean assignment — which is what a correct AllSAT/`ToDNF`
procedure delivers. Under that hypothesis both inclusions are immediate. See the
`README` for the full list of such observations.
-/


open Set

variable {A X : Type*} {n : ℕ} {M : A → Set X} {φ : BForm A} {D : DNF A}

/-- **Soundness of each cube.** Every cube of a DNF representation of `φ` denotes a
region contained in the solution set of `φ`. -/
theorem region_subset_sol (h : IsDNFOf D φ) {c : Cube A} (hc : c ∈ D) :
    region M c ⊆ sol M φ := by
  intro x hx
  exact (h (induced M x)).1 ⟨c, hc, hx⟩

/-- **Completeness of the union.** Every solution of `φ` lies in the region of some
cube of a DNF representation of `φ`. -/
theorem sol_subset_iUnion_region (h : IsDNFOf D φ) :
    sol M φ ⊆ ⋃ c ∈ D, region M c := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := (h (induced M x)).2 hx
  exact mem_biUnion hc hxc

/-- **`thm:decomposition`.** The union of the regions of the cubes of a
DNF abstraction of `F` is exactly `Sol(F)`. -/
theorem sol_eq_iUnion_region (h : IsDNFOf D φ) :
    ⋃ c ∈ D, region M c = sol M φ :=
  Subset.antisymm
    (iUnion₂_subset fun _ hc => region_subset_sol h hc)
    (sol_subset_iUnion_region h)

/-- The decomposition specialised to linear atoms: the solution set of an SMT(LRA)
formula is a finite union of convex regions. This is the form the volume
computation consumes. -/
theorem sol_eq_iUnion_convex (atoms : A → LinAtom n) (h : IsDNFOf D φ) :
    ∃ R : Cube A → Set (Space n),
      (∀ c, Convex ℝ (R c)) ∧ ⋃ c ∈ D, R c = sol (fun a => (atoms a).halfspace) φ :=
  ⟨region (fun a => (atoms a).halfspace), convex_region atoms, sol_eq_iUnion_region h⟩

end Ttc

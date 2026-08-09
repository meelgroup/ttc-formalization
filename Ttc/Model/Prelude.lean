/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `Model/Prelude`: vocabulary

Every non-Mathlib symbol the rest of `Model/` uses in a definition. Definitions
only — no algorithm, no assumptions, no proofs beyond `rfl`.

Modelling notes: atoms are abstract (an index type `A` plus an interpretation
`M`), so the Boolean-abstraction property is definitional (`mem_sol_iff`). A
negated atom denotes an *open* half-space, so a cube's region is convex but in
general not closed — see the README, finding 5.
-/

namespace Ttc

open scoped Pointwise

/-- `ℝⁿ` with the Euclidean (`ℓ₂`) norm and Lebesgue measure. The `ℓ₂` norm
matters: the paper's inscribed-ball hypotheses are about `ℓ₂`-balls. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {A X : Type*} {n : ℕ}

/-! ## Formulas -/

/-- One row `A_ij x ≤ b_ij` of the paper's constraint matrices. -/
structure LinAtom (n : ℕ) where
  /-- The coefficient vector. -/
  coeff : Fin n → ℝ
  /-- The right-hand side. -/
  bound : ℝ

/-- The closed half-space a linear atom denotes. -/
def LinAtom.halfspace (a : LinAtom n) : Set (Space n) :=
  {x | ∑ i, a.coeff i * x i ≤ a.bound}

/-- The paper's `F_bool`: a Boolean combination of atom indices. -/
inductive BForm (A : Type*) where
  /-- The empty conjunction. -/
  | tt : BForm A
  /-- An atom. -/
  | atom : A → BForm A
  /-- Negation. -/
  | neg : BForm A → BForm A
  /-- Conjunction. -/
  | and : BForm A → BForm A → BForm A
  /-- Disjunction. -/
  | or : BForm A → BForm A → BForm A
  deriving Repr

/-- Satisfaction under a `Prop`-valued assignment. -/
def BForm.holds (v : A → Prop) : BForm A → Prop
  | .tt => True
  | .atom a => v a
  | .neg φ => ¬ φ.holds v
  | .and φ ψ => φ.holds v ∧ ψ.holds v
  | .or φ ψ => φ.holds v ∨ ψ.holds v

/-- **A formula is positive when no negation occurs in it.** The count side needs
the polytopes to be intersections of *closed* half-spaces, and a negated atom
denotes an open one — see the README, finding 5. This is a condition on the
**input formula**, checkable by inspection, and it is what makes `Ttc.toDNF`'s
output positive. -/
def BForm.IsPositive : BForm A → Prop
  | .tt => True
  | .atom _ => True
  | .neg _ => False
  | .and φ ψ => φ.IsPositive ∧ ψ.IsPositive
  | .or φ ψ => φ.IsPositive ∧ ψ.IsPositive

/-- An atom index with a polarity. -/
structure Lit (A : Type*) where
  /-- The underlying atom. -/
  atom : A
  /-- `true` for a positive occurrence. -/
  pos : Bool

/-- Satisfaction of a literal. -/
def Lit.holds (v : A → Prop) (l : Lit A) : Prop :=
  cond l.pos (v l.atom) (¬ v l.atom)

/-- A conjunction of literals. -/
abbrev Cube (A : Type*) := List (Lit A)

/-- A cube holds when all its literals do. -/
def Cube.holds (v : A → Prop) (c : Cube A) : Prop := ∀ l ∈ c, l.holds v

/-- A disjunction of cubes. -/
abbrev DNF (A : Type*) := List (Cube A)

/-- A DNF holds when some cube does. -/
def DNF.holds (v : A → Prop) (D : DNF A) : Prop := ∃ c ∈ D, c.holds v

/-- `D` and `φ` agree on every Boolean assignment — what `ToDNF` (circuit AllSAT)
is assumed to deliver. -/
def IsDNFOf (D : DNF A) (φ : BForm A) : Prop := ∀ v : A → Prop, D.holds v ↔ φ.holds v

/-! ## `ToDNF` — `alg:ttc` line 16

The circuit-AllSAT call, as an actual function rather than an assumed oracle. It
carries a **polarity** so that negation never has to be pushed by rewriting the
formula, which makes the recursion structural: `dnfAux φ true` is a DNF of `φ`,
and `dnfAux φ false` a DNF of `¬φ`.
-/

/-- The pairwise conjunction of two DNFs: every cube of one glued to every cube of
the other. -/
def DNF.cross (D E : DNF A) : DNF A := D.flatMap fun c => E.map fun d => c ++ d

/-- **`ToDNF`, with a polarity.** `dnfAux φ p` is a DNF of `φ` when `p` is `true`,
and of `¬φ` when it is `false`. Structural in `φ`: the De Morgan cases flip the
polarity rather than build a bigger formula. -/
def dnfAux : BForm A → Bool → DNF A
  | .tt, true => [[]]
  | .tt, false => []
  | .atom a, p => [[⟨a, p⟩]]
  | .neg φ, p => dnfAux φ !p
  | .and φ ψ, true => (dnfAux φ true).cross (dnfAux ψ true)
  | .and φ ψ, false => dnfAux φ false ++ dnfAux ψ false
  | .or φ ψ, true => dnfAux φ true ++ dnfAux ψ true
  | .or φ ψ, false => (dnfAux φ false).cross (dnfAux ψ false)

/-- **`alg:ttc` line 16**: `F_dnf ← ToDNF(F_bool)`. A definition, not an oracle —
`Ttc.toDNF_isDNFOf` proves it correct, so nothing about the DNF is assumed. -/
def toDNF (φ : BForm A) : DNF A := dnfAux φ true

/-! ## Semantics over the reals -/

variable (M : A → Set X)

/-- The Boolean assignment a point induces on atoms. -/
def induced (x : X) : A → Prop := fun a => x ∈ M a

/-- The paper's `Sol(F)`. -/
def sol (φ : BForm A) : Set X := {x | φ.holds (induced M x)}

/-- The set a literal denotes. -/
def litSet (l : Lit A) : Set X :=
  cond l.pos (M l.atom) (M l.atom)ᶜ

/-- The paper's `P(c)`: the region a cube carves out. -/
def region (c : Cube A) : Set X := {x | c.holds (induced M x)}

variable {M}

/-- The Boolean-abstraction property, definitionally. -/
@[simp]
theorem mem_sol_iff {φ : BForm A} {x : X} :
    x ∈ sol M φ ↔ φ.holds (induced M x) := Iff.rfl

@[simp]
theorem mem_region_iff {c : Cube A} {x : X} :
    x ∈ region M c ↔ ∀ l ∈ c, l.holds (induced M x) := Iff.rfl

/-! ## Positive DNFs, and the facets they present

A negated atom denotes an **open** half-space, which is not an intersection of
closed ones, so `lem:nonconv`'s geometry is available only for DNFs all of whose
literals are positive (README, finding 5). `Ttc.FacetIndex D` names the facets of
such a DNF: one per literal of each cube.
-/

/-- A cube is **positive** when none of its literals is negated. -/
def Cube.IsPositive (c : Cube A) : Prop := ∀ l ∈ c, l.pos = true

/-- A DNF is **positive** when all of its cubes are. -/
def DNF.IsPositive (D : DNF A) : Prop := ∀ c ∈ D, Cube.IsPositive c

/-- Facets of a DNF: one per literal of each of its cubes. -/
abbrev FacetIndex (D : DNF A) := Σ c : {c : Cube A // c ∈ D}, {l : Lit A // l ∈ c.val}

/-! ## The lattices

The algorithm counts points of `𝕃ⁿ = 10^(−ρ)·ℤⁿ`; `lem:lattice` transports that
count to `ℤⁿ` by dilating. Both lattices, the dilation `10^ρ`, and the normalised
count `L = |Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)` are defined here, so that the problem
statement can *be* about a lattice count rather than about a bare real.
-/

/-- The integer lattice inside `ℝⁿ`. -/
def intLattice (n : ℕ) : Set (Space n) := {x | ∀ i, ∃ k : ℤ, x i = (k : ℝ)}

/-- The refined lattice `𝕃ⁿ = c⁻¹ · ℤⁿ`; the algorithm uses `c = 10^ρ`. -/
def fineLattice (n : ℕ) (c : ℝ) : Set (Space n) := {x | ∀ i, ∃ k : ℤ, x i = c⁻¹ * (k : ℝ)}

@[simp]
theorem mem_intLattice {x : Space n} : x ∈ intLattice n ↔ ∀ i, ∃ k : ℤ, x i = (k : ℝ) :=
  Iff.rfl

@[simp]
theorem mem_fineLattice {c : ℝ} {x : Space n} :
    x ∈ fineLattice n c ↔ ∀ i, ∃ k : ℤ, x i = c⁻¹ * (k : ℝ) := Iff.rfl

/-- The dilation `10^ρ` carrying `𝕃ⁿ = 10^(−ρ)·ℤⁿ` onto `ℤⁿ`. -/
noncomputable def latticeScale (ρ : ℤ) : ℝ := (10 : ℝ) ^ ρ

/-- **`|Sol(F) ∩ 𝕃ⁿ|`** — the lattice-point count the algorithm's estimate
targets, of the *actual* solution set. -/
noncomputable def latticeCount {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A)
    (ρ : ℤ) : ℕ :=
  ((sol M φ) ∩ fineLattice n (latticeScale ρ)).ncard

/-- **`L = |Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)`** — the paper's normalised lattice count. -/
noncomputable def normalisedCount {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A)
    (ρ : ℤ) : ℝ :=
  (latticeCount M φ ρ : ℝ) / (latticeScale ρ) ^ n

/-! ## The parameter block

The five scalars `alg:ttc` (lines 17–20) and `alg:prec` (line 86) compute before
the main loop. What each is chosen to satisfy is proved in `Constants/Parameters`.
-/

/-- Inputs to the algorithm: `n` the dimension, `m` the number of cubes, `r` the
total facet count. -/
structure Params where
  /-- The requested multiplicative accuracy. -/
  ε : ℝ
  /-- The requested failure probability. -/
  δ : ℝ
  /-- The ambient dimension. -/
  n : ℕ
  /-- The number of polytopes in the decomposition. -/
  m : ℕ
  /-- The total number of facets, `r = ∑ᵢ facet(Pᵢ)`. -/
  r : ℝ
  /-- Accuracy is in `(0,1]`. -/
  hε0 : 0 < ε
  /-- Accuracy is in `(0,1]`. -/
  hε1 : ε ≤ 1
  /-- The dimension is positive. -/
  hn : 1 ≤ n
  /-- There is at least one cube. -/
  hm : 1 ≤ m
  /-- There is at least one facet. -/
  hr : 1 ≤ r

namespace Params

variable (P : Params)

/-- `η ← ε/8` (`alg:ttc` line 17). -/
noncomputable def eta : ℝ := P.ε / 8

/-- `ε' ← ε/12` (`alg:ttc` line 18). -/
noncomputable def epsPrime : ℝ := P.ε / 12

/-- `δ' ← δ/(4m)` (`alg:ttc` line 18): the per-call failure probability handed to
`Vol_ED` **and** to `GenerateSamples`, one call of each per polytope. The `4`
(rather than the `2` of the pre-`eq:sampler` version) is what leaves room for the
sampler's own failure event alongside the volume oracle's. -/
noncomputable def deltaPrime : ℝ := P.δ / (4 * P.m)

/-- `Thresh ← max(24 ln(24/δ) / ((1−ε')ε'²), 15(ln(6/δ) + ln m))` (`alg:ttc` line 20).

The second branch's constant is `15`, not `6`: the noise estimate bounds the
level-`j*−1` rate by `(1+ε')²(1+η)·Thresh/2 ≤ 2·Thresh/3`, so `lem:chernoff`
gives `exp(−Thresh/15)` rather than `exp(−Thresh/6)`. Nothing here needs it —
this development derives `j*` from the *true* total rate (`Ttc.exists_epoch`), so
`exp(−Thresh/6)` is honest — but the constant transcribes `alg:ttc`. -/
noncomputable def thresh : ℝ :=
  max (24 * Real.log (24 / P.δ) / ((1 - P.epsPrime) * P.epsPrime ^ 2))
      (15 * (Real.log (6 / P.δ) + Real.log P.m))

/-- `κ = √(2 log(8/η)) + √(2 log r)`, the facet displacement of `lem:nonconv`.
The `8/η` (not `4/η`) is the `θ = η/2` repair; see the README, finding 1. -/
noncomputable def kappa : ℝ :=
  Real.sqrt (2 * Real.log (8 / P.eta)) + Real.sqrt (2 * Real.log P.r)

/-- `γ = (64 m n / η)·√(log(8r/η))`, the inscribed radius `GetPrecision` targets
(`alg:prec` line 86). The `m` allows the `Pᵢ` different ball centres; the `8r/η`
must match `κ` or `kappa_div_gamma_le` fails. See the README, finding 2. -/
noncomputable def gamma : ℝ :=
  (64 * P.m * P.n / P.eta) * Real.sqrt (Real.log (8 * P.r / P.eta))

/-- `ρ ← ⌈log₁₀(γ/γ̂)⌉` (`alg:prec` line 91), where `γ̂` is the **smallest**
inscribed-ball radius over the family — `alg:prec` maximises `γ/γ̂ᵢ` over the
polytopes, and `γ` does not depend on `i`, so `maxratio = γ / minᵢ γ̂ᵢ`. The LP
computing each `γ̂ᵢ` is not modelled; `γ̂` is an input. -/
noncomputable def precision (gammaHat : ℝ) : ℤ := ⌈Real.logb 10 (P.gamma / gammaHat)⌉

end Params

end Ttc

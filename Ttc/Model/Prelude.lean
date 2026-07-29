/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `Model/Prelude`: the vocabulary of the audit surface

Every symbol the other `Model/` files use in a **definition**, and which is not a
Mathlib symbol, is defined here. So a referee reading `Model/` never has to leave
it to find out what a name means:

* the ambient space, and the syntax and semantics of SMT(LRA) formulas
  (`BForm`, `Lit`, `Cube`, `DNF`, `sol`, `region`);
* the closed-form parameter block the algorithm computes before its main loop
  (`Params`, `alg:ttc` lines 17–20 and `alg:prec` line 86);
* `volSol` — the paper's `Vol(F)`, the quantity being estimated;
* `TtcAnalysis` — **every assumption of the headline theorem**, as fields.

**There are no proofs in this file** beyond `rfl`.

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
  and *open* half-spaces: still convex (`Ttc.convex_region`, proved in
  `Analysis/Decomposition`), but in general not closed, hence not a polytope in
  the usual sense. See the README, finding 5.

## Note on `γ`

`γ` must be stated with the **same** logarithm argument as `κ`. With
`κ = √(2 log(8/η)) + √(2 log r)` one has `κ ≤ 2√(log(8r/η))`, so
`γ = (64mn/η)·√(log(8r/η))` gives `κ/γ ≤ η/(32mn)` exactly
(`Ttc.Params.kappa_div_gamma_le`, in `Analysis/Parameters`). Using
`√(log(4r/η))` in `γ` while `κ` is computed at `8/η` leaves a residual factor
`√(log(8r/η)/log(4r/η))`, which is up to `√1.5 ≈ 1.23` — the bound then fails.
See the README, finding 2.
-/

namespace Ttc

/-! ## The ambient space

`Ttc.Space n` is `ℝⁿ` with the Euclidean (`ℓ₂`) norm and Lebesgue measure. Every
geometric statement in this development lives here.

Two facts about it are used pervasively and are recorded by Mathlib rather than
proved here: `finrank ℝ (Space n) = n` (`finrank_euclideanSpace_fin`), and that
`volume` is an additive Haar measure, so it scales by `|c|ⁿ` under dilation
(`MeasureTheory.Measure.addHaar_smul`).

The `ℓ₂` norm matters: the paper's inscribed-ball hypotheses are about
`ℓ₂`-balls, and `Analysis/Rounding` bounds `‖A_ij‖₂`.
-/

/-- The ambient space: `ℝⁿ` with the Euclidean norm and Lebesgue measure. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

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

/-! ## The parameter block

`TTC` (`alg:ttc`) and `GetPrecision` (`alg:prec`) compute five quantities before
the main loop runs. Each is a *choice*, and each is chosen to make one specific
inequality of the analysis true. This block defines them; the inequalities they
are chosen to satisfy are proved in `Analysis/Parameters`.

| Paper | Here | Chosen so that |
| --- | --- | --- |
| `ε' ← ε/12` (`alg:ttc`, line 18) | `Ttc.Params.epsPrime` | the two-sided `(1±ε')` losses fit inside `(1±ε/3)` |
| `Thresh ← max(…)` (`alg:ttc`, line 20) | `Ttc.Params.thresh` | each failure branch of `lem:numlattice` is `δ/6` |
| `κ` (`lem:nonconv`) | `Ttc.Params.kappa` | the rounding tail bound is `η/(4r)` per facet |
| `γ` (`alg:prec`, line 86) | `Ttc.Params.gamma` | `κ/γ ≤ η/(32mn)`, the shell bound's input |
| `ρ ← ⌈log₁₀(γ/γ̂)⌉` (`alg:prec`) | `Ttc.Params.precision` | the fine lattice `𝕃ⁿ` is fine enough |

This is the audit surface for the constants: if a constant in the paper changes,
exactly one definition here changes and the corresponding theorem in
`Analysis/Parameters` either still compiles or does not.
-/

/-- The parameters the algorithm computes from its inputs. `n` is the dimension,
`m` the number of cubes in the DNF, `r` the total facet count. -/
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

/-- `η ← ε/8`: the accuracy at which `GetPrecision` is called (`alg:ttc`, line 17). -/
noncomputable def eta : ℝ := P.ε / 8

/-- `ε' ← ε/12` (`alg:ttc`, line 18). -/
noncomputable def epsPrime : ℝ := P.ε / 12

/-- `Thresh ← max(24 ln(24/δ) / ((1−ε')ε'²), 6(ln(6/δ) + ln m))` (`alg:ttc`, line 20). -/
noncomputable def thresh : ℝ :=
  max (24 * Real.log (24 / P.δ) / ((1 - P.epsPrime) * P.epsPrime ^ 2))
      (6 * (Real.log (6 / P.δ) + Real.log P.m))

/-- `κ = √(2 log(8/η)) + √(2 log r)`, the facet displacement of `lem:nonconv`.

The `8/η` (rather than `4/η`) is the `θ = η/2` internal parameter that makes the
final combination close; see the README, finding 1. -/
noncomputable def kappa : ℝ :=
  Real.sqrt (2 * Real.log (8 / P.eta)) + Real.sqrt (2 * Real.log P.r)

/-- `γ = (64 m n / η)·√(log(8r/η))`, the inscribed radius `GetPrecision` targets
(`alg:prec`, line 86).

The factor `m` is what allows the `Pᵢ` to have *different* inscribed-ball centres
— see `Analysis/Recentred`. The `8r/η` matches `κ`. -/
noncomputable def gamma : ℝ :=
  (64 * P.m * P.n / P.eta) * Real.sqrt (Real.log (8 * P.r / P.eta))

/-- `ρ ← ⌈log₁₀(γ/γ̂)⌉` (`alg:prec`), where `γ̂` is the largest inscribed radius
found by the LP. -/
noncomputable def precision (gammaHat : ℝ) : ℤ := ⌈Real.logb 10 (P.gamma / gammaHat)⌉

end Params

/-! ## `Vol(F)`, the quantity the algorithm estimates -/

/-- The Lebesgue volume of the solution set of an SMT(LRA) formula, as a real
number. **This is the paper's `Vol(F)`, and the quantity the headline theorem
bounds.** Not a surrogate: `sol M φ` is the set of real points satisfying `φ`
under the interpretation `M`, and `volume` is Mathlib's Lebesgue measure. -/
noncomputable def volSol {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A) : ℝ :=
  (MeasureTheory.volume (sol M φ)).toReal

theorem volSol_nonneg {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A) :
    0 ≤ volSol M φ := ENNReal.toReal_nonneg

/-! ## The assumptions of `thm:volumettc`, in one place

`Ttc.TtcAnalysis` is the *abstract interface* of the development: a bundle of the
facts the correctness proof consumes, as **fields**. Every global assumption of
the headline theorem is one of them, so an auditor reads this structure and knows
exactly what is being taken on trust. There is nothing else: `Model/Theorem`
quantifies over `TtcAnalysis` and adds no hypothesis of its own.

The fields, and where each stands:

| Field | Paper | Status |
| --- | --- | --- |
| `isDNF` | `ToDNF`/circuit AllSAT is correct | assumed of the external tool; `thm:decomposition` is *proved* from it (`Ttc.sol_eq_iUnion_region`) |
| `lattice_lo`, `lattice_hi` | `lem:lattice` at `η = ε/8` | derivation from `lem:nonconv` proved (`Analysis/Lattice`, `Analysis/Nonconv`, `Analysis/Recentred`, `Analysis/Repair`); the measure-theoretic reduction inside `claim:cl` is the residual assumption |
| `sketch_lo`, `sketch_hi` | `lem:numlattice` | epoch skeleton proved (`Analysis/Sketch`, `Analysis/Poisson`); the Poisson–Chernoff estimate `lem:chernoff` is the residual assumption |

`L` is the **normalised lattice count** `|Q ∩ 𝕃ⁿ| / 10^(ρ·n)`; `est` is the value
the algorithm outputs (`|X|/p` in `Model/Pseudocode`). Neither is tied to the
object its name describes — see `Ttc.TtcAnalysis.IsOutputOf` (`Model/Pseudocode`)
for the `est` side, and `AUDIT.md` §4.

### Probability, `δ`, and scope

`Ttc.TtcAnalysis` fixes one run of the algorithm and asserts `lem:numlattice`'s
conclusion *deterministically*: the `1 − δ` failure probability of the paper is
carried by the fields `sketch_lo`/`sketch_hi` being assumed to hold, rather than
being re-derived. So what `Model/Theorem` proves is: **on the event that
`lem:numlattice`'s guarantee holds, the output is an `(1±ε)`-approximation of the
true volume.** Combining that event with `Pr ≥ 1 − δ` is exactly
`lem:numlattice`'s content and is out of scope, as is the runtime claim
(`thm:runtime`).

The interface is inhabited — see `Ttc.TtcAnalysis.ideal` (`Analysis/Capstone`)
and `Ttc.nonempty_ttcAnalysis` (`Model/Theorem`), without which the headline
could be vacuously true.
-/

/-- **The abstract interface for `thm:volumettc`.**

A bundle of the modelling facts the correctness argument consumes. `L` is the
normalised lattice count `|Q ∩ 𝕃ⁿ| / 10^(ρ·n)`; the two `lattice_*` fields are
`lem:lattice` at `η = ε/8`; the two `sketch_*` fields are `lem:numlattice`. -/
structure TtcAnalysis (A : Type*) (n : ℕ) where
  /-- The multiplicative accuracy parameter. -/
  ε : ℝ
  /-- `ε` is positive. -/
  hε0 : 0 < ε
  /-- `ε` is at most one, as required by `thm:volumettc`. -/
  hε1 : ε ≤ 1
  /-- The interpretation of atoms as sets of points (half-spaces, in the LRA case). -/
  M : A → Set (Space n)
  /-- The Boolean abstraction of the input formula. -/
  φ : BForm A
  /-- The DNF produced by circuit AllSAT. -/
  D : DNF A
  /-- `D` really is a DNF representation of `φ`. -/
  isDNF : IsDNFOf D φ
  /-- The normalised lattice count `|Q ∩ 𝕃ⁿ| / 10^(ρ·n)`. -/
  L : ℝ
  /-- A count is nonnegative. -/
  hL : 0 ≤ L
  /-- The estimate the algorithm outputs, `|X|/p`. -/
  est : ℝ
  /-- `lem:lattice`, lower half, at `η = ε/8`. -/
  lattice_lo : (1 - ε / 8) * L ≤ volSol M φ
  /-- `lem:lattice`, upper half, at `η = ε/8`. -/
  lattice_hi : volSol M φ ≤ (1 + ε / 8) * L
  /-- `lem:numlattice`, lower half. -/
  sketch_lo : (1 - ε / 3) * L ≤ est
  /-- `lem:numlattice`, upper half. -/
  sketch_hi : est ≤ (1 + ε / 3) * L

end Ttc

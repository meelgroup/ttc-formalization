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

Every symbol the two transcription files (`Model/ProblemSetting`, `Model/Pseudocode`)
use in a *definition* and which is not a Mathlib symbol is defined here, so a referee
reading `Model/` never has to leave it to find out what a name means.

**Definitions only** — no algorithm, no assumptions, no `@[simp]` lemma.  The only
exceptions are two finiteness instances, which `Ttc.facetOf` (`Ttc/Geometry/CanonPolytope`)
needs to enumerate the facets.

The file is held to a *measured* keep-set rather than to a topic: the union of the
definitional closures of `Ttc.ttc` and of the statement of `Ttc.ttc_volume`, as
`Ttc/Audit/ClosureCheck.lean` measures them.  The probability vocabulary lives in
`Ttc/Probability/` and the canonical polytope description in `Ttc/Geometry/`, both inside
the audit surface; ten further declarations were evicted downstream, keeping name, type
and docstring.

One Mathlib measure-theory import is load-bearing without being used here: it supplies the
`MeasureSpace (Ttc.Space n)` instance that `Model/ProblemSetting`'s `Ttc.volSol` needs, and
`ProblemSetting` imports this file and nothing else.  `Vol(F)` is a Lebesgue volume, so
measure theory cannot leave the audit surface without the headline ceasing to mean what it
means.

Modelling notes: atoms are abstract (an index type `A` plus an interpretation `M`), so the
Boolean-abstraction property is definitional — `x ∈ sol M φ` *is* `φ.holds (induced M x)`.
A negated atom denotes an **open** half-space, so a cube's region is convex but in general
not closed (README, finding 5).
-/

namespace Ttc

open scoped Pointwise

/-! ## The ambient space -/

/-- **`ℝⁿ`** with the Euclidean (`ℓ₂`) norm and Lebesgue measure; the paper's
inscribed-ball hypotheses are about `ℓ₂`-balls. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## The formula syntax `F_bool` -/

variable {A X : Type*} {n : ℕ}

/-- **One row `A_ij x ≤ b_ij`** of the paper's constraint matrices. -/
structure LinAtom (n : ℕ) where
  /-- The coefficient vector. -/
  coeff : Fin n → ℝ
  /-- The right-hand side. -/
  bound : ℝ

/-- The closed half-space a linear atom denotes. -/
def LinAtom.halfspace (a : LinAtom n) : Set (Space n) :=
  {x | ∑ i, a.coeff i * x i ≤ a.bound}

/-- **The paper's `F_bool`**: a Boolean combination of atom indices. -/
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

/-- Satisfaction under a `Prop`-valued assignment. -/
def BForm.holds (v : A → Prop) : BForm A → Prop
  | .tt => True
  | .atom a => v a
  | .neg φ => ¬ φ.holds v
  | .and φ ψ => φ.holds v ∧ ψ.holds v
  | .or φ ψ => φ.holds v ∨ ψ.holds v

/-- **A formula is positive when no negation occurs in it.** The count side needs the
polytopes to be intersections of *closed* half-spaces, and a negated atom denotes an open
one (README, finding 5). -/
def BForm.IsPositive : BForm A → Prop
  | .tt => True
  | .atom _ => True
  | .neg _ => False
  | .and φ ψ => φ.IsPositive ∧ ψ.IsPositive
  | .or φ ψ => φ.IsPositive ∧ ψ.IsPositive

/-- **A conjunction of atoms, as a formula** — the shape lines A3 and A6 read a cube
back as.  `BForm.tt` is what lets it stay positive. -/
def conj (L : List A) : BForm A := L.foldr (fun a φ => .and (.atom a) φ) .tt

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

/-! ## `ToDNF` — `alg:ttc` line 16: the circuit-AllSAT call, as a function, not an
oracle.  A **polarity** argument keeps the recursion structural. -/

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

/-- **`alg:ttc` line 16**: `F_dnf ← ToDNF(F_bool)`.  `Ttc.toDNF_isDNFOf` proves it
correct, so nothing about the DNF is assumed. -/
def toDNF (φ : BForm A) : DNF A := dnfAux φ true

/-! ## The semantics over the reals: `Sol(F)` and `P(c)` -/

variable (M : A → Set X)

/-- The Boolean assignment a point induces on atoms. -/
def induced (x : X) : A → Prop := fun a => x ∈ M a

/-- **The paper's `Sol(F)`.** -/
def sol (φ : BForm A) : Set X := {x | φ.holds (induced M x)}

/-- **The paper's `P(c)`**: the region a cube carves out. -/
def region (c : Cube A) : Set X := {x | c.holds (induced M x)}

variable {M}

/-! ## The facets a DNF presents.  `lem:nonconv`'s geometry needs closed half-spaces,
hence positive literals only (README, finding 5). -/

/-- Facets of a DNF: one per literal of each of its cubes. -/
abbrev FacetIndex (D : DNF A) := Σ c : {c : Cube A // c ∈ D}, {l : Lit A // l ∈ c.val}

/-- The cubes of a DNF form a finite type: the subtype is cut out by membership in a
`List`. -/
instance instFiniteCubeMem (D : DNF A) : Finite {c : Cube A // c ∈ D} :=
  List.finite_toSet D |>.to_subtype

/-- `FacetIndex D` is finite: a sigma of subtypes cut out by `List` membership. -/
instance instFiniteFacetIndex (D : DNF A) : Finite (FacetIndex D) := by
  unfold FacetIndex
  have : ∀ c : {c : Cube A // c ∈ D}, Finite {l : Lit A // l ∈ c.val} := fun c =>
    (List.finite_toSet c.val).to_subtype
  infer_instance

/-! ## The lattices `ℤⁿ` and `𝕃ⁿ`, and the count.  The algorithm counts points of
`𝕃ⁿ = 10^(−ρ)·ℤⁿ`; `lem:lattice` transports that count to `ℤⁿ` by dilating. -/

/-- **The integer lattice `ℤⁿ`** inside `ℝⁿ`. -/
def intLattice (n : ℕ) : Set (Space n) := {x | ∀ i, ∃ k : ℤ, x i = (k : ℝ)}

/-- **The refined lattice `𝕃ⁿ = c⁻¹ · ℤⁿ`**; the algorithm uses `c = 10^ρ`. -/
def fineLattice (n : ℕ) (c : ℝ) : Set (Space n) := {x | ∀ i, ∃ k : ℤ, x i = c⁻¹ * (k : ℝ)}

/-- **The dilation `10^ρ`** carrying `𝕃ⁿ = 10^(−ρ)·ℤⁿ` onto `ℤⁿ`. -/
noncomputable def latticeScale (ρ : ℤ) : ℝ := (10 : ℝ) ^ ρ

/-- **`|Sol(F) ∩ 𝕃ⁿ|`** — the lattice-point count the algorithm's estimate
targets, of the *actual* solution set. -/
noncomputable def latticeCount {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A)
    (ρ : ℤ) : ℕ :=
  ((sol M φ) ∩ fineLattice n (latticeScale ρ)).ncard

/-! ## The parameter block, `alg:ttc` lines 17–20 and `alg:prec` line 86: the scalars
the algorithm computes before the main loop.  What each satisfies is proved in
`Constants/Parameters`. -/

/-- **The inputs and standing assumptions of `TTC`**: `n` the dimension, `m` the
number of cubes, `r` the total facet count. -/
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

/-- `η ← ε/8` (`alg:ttc` line 17): the slack `Ttc.Params.kappa` and `Ttc.Params.gamma`
are budgeted against. -/
noncomputable def eta : ℝ := P.ε / 8

/-- `ε' ← ε/12` (`alg:ttc` line 18): the per-call accuracy handed to `Vol_ED`. -/
noncomputable def epsPrime : ℝ := P.ε / 12

/-- `δ' ← δ/(4m)` (`alg:ttc` line 18): the per-call failure probability handed to
`Vol_ED` **and** `GenerateSamples`.  The `4` leaves room for the sampler's own failure
event alongside the volume oracle's. -/
noncomputable def deltaPrime : ℝ := P.δ / (4 * P.m)

/-- `Thresh ← max(24 ln(24/δ) / ((1−ε')ε'²), 15(ln(6/δ) + ln m))` (`alg:ttc` line 20).
The second branch's `15` transcribes `alg:ttc`; this development derives `j*` from the
*true* total rate, so it does not need it. -/
noncomputable def thresh : ℝ :=
  max (24 * Real.log (24 / P.δ) / ((1 - P.epsPrime) * P.epsPrime ^ 2))
      (15 * (Real.log (6 / P.δ) + Real.log P.m))

/-- `γ = (64 m n / η)·√(log(8r/η))`, the inscribed radius `GetPrecision` targets
(`alg:prec` line 86).  The `8r/η` must match `κ` or `Ttc.Params.kappa_div_gamma_le`
fails (README, finding 2). -/
noncomputable def gamma : ℝ :=
  (64 * P.m * P.n / P.eta) * Real.sqrt (Real.log (8 * P.r / P.eta))

/-- `ρ ← ⌈log₁₀(γ/γ̂)⌉` (`alg:prec` line 91), at the **smallest** inscribed radius over
the family.  The LP computing each `γ̂ᵢ` is not modelled; `γ̂` is an input. -/
noncomputable def precision (gammaHat : ℝ) : ℤ := ⌈Real.logb 10 (P.gamma / gammaHat)⌉

end Params

end Ttc

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

Every symbol the two transcription files (`Model/ProblemSetting.lean`,
`Model/Pseudocode.lean`) use in a *definition*, and which is **not** a Mathlib
symbol, is defined here. So a referee reading `Model/` never has to leave it to
find out what a name means: the ambient space (`Space`), the formula syntax
(`LinAtom`, `BForm`, `Lit`, `Cube`, `DNF`) and everything it unfolds to
(`BForm.holds` → `Lit.holds` → `Cube.holds` → `DNF.holds`), the circuit-AllSAT
call of `alg:ttc` line 16 (`toDNF` → `dnfAux` → `DNF.cross`), the semantics over
the reals (`induced`, `sol` = `Sol(F)`, `region` = `P(c)`), the positivity
condition the headline is stated under and the facet index `lem:nonconv` is stated
over (`BForm.IsPositive`, `FacetIndex`), the lattices the count is taken over
(`fineLattice`, `latticeScale`, `latticeCount`), and the closed-form parameter
block (`Params`, `alg:ttc` lines 17–20 and `alg:prec` line 86).

**The file is held to a measured keep-set, not to a topic**: the union of the
definitional closures of `Ttc.ttc` and of the *statement* of
`Ttc.ttc_volume_estimate`, as `Ttc/Audit/ClosureCheck.lean` measures them, minus
what has moved to `Ttc/Probability/` (below), plus the three things those closures
cannot see but the build needs — one instance (`instFiniteCubeMem`) feeding proof
terms, and two predicates `Model/Pseudocode` names in statements of its own
(`DNF.holds`, `IsDNFOf`).  Ten declarations fell outside it and were evicted
downstream, keeping name, type and docstring: `litSet`, `mem_sol_iff`,
`mem_region_iff`, `mem_intLattice`, `mem_fineLattice` and `normalisedCount` to
`Lattice/Decomposition`; `Cube.IsPositive` and `DNF.IsPositive` to `Ttc/Dnf.lean`,
beside `toDNF_isPositive`; `Params.kappa` to `Constants/Parameters`, beside the
inequality it is chosen to satisfy; `thinKernel_apply` to `Process/Thinning`.

**The probability vocabulary is no longer here.**  Since `Ttc.ttc`
(`Model/Pseudocode`) is a *law*, the audit surface includes the ambient random
objects the algorithm's two coin sequences are governed by — the volume oracle's
coin space (`MonteCarlo.coinLaw`, `MonteCarlo.coins`), the ½-thinning and the
coupled trajectory law it generates (`half`, `thinKernel`, `chainKernel`,
`trajLaw`), and `GenerateSamples`' two laws with the step count they are run for
(`mixSteps`, `ballWalkLaw`, `kv97SampD`, `kv97ContLaw`, `e2eSampD`).  Those eleven
definitions and the two Markov-kernel instances that travel with them are in
**`Ttc/Probability/`**, under their existing names; `Ttc/Audit/ClosureCheck.lean`
audits `Ttc/Model/` together with that directory, and says why.

What stayed is the *geometry* the sampler is applied at — `facetOf`, `canonAm`,
`canonBv`, `canonDm`, `canonRfac`, the last section of this file.  It is convex
geometry read off the formula, with no randomness in it, and it is built from
`region`, `latticeScale` and `FacetIndex`, which are here.

Definitions only — no algorithm, no assumptions.  The exceptions are the two
finiteness instances (`instFiniteCubeMem`, `instFiniteFacetIndex`, which `facetOf`
needs to enumerate the facets); no other statement about the objects below is made
here, and no `@[simp]` lemma at all.

Modelling notes: atoms are abstract (an index type `A` plus an interpretation
`M`), so the Boolean-abstraction property is definitional — `x ∈ sol M φ` *is*
`φ.holds (induced M x)`, which is why `Ttc.mem_sol_iff` (`Lattice/Decomposition`)
is `Iff.rfl`. A negated atom denotes an *open* half-space, so a cube's region is
convex but in general not closed — see the README, finding 5.
-/

namespace Ttc

open scoped Pointwise

/-! ## The ambient space -/

/-- **`ℝⁿ`** with the Euclidean (`ℓ₂`) norm and Lebesgue measure. The `ℓ₂` norm
matters: the paper's inscribed-ball hypotheses are about `ℓ₂`-balls. -/
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

/-- **A conjunction of atoms, as a formula** — the shape lines A3 and A6 read a
cube back as (`Ttc.cubeForm`, `Model/Pseudocode`), and the shape the non-vacuity
witness needs. `BForm.tt` is what lets such a conjunction be written without a
tautology seed, and hence stay positive (`Ttc.isPositive_conj`, `Ttc/Dnf.lean`). -/
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

/-! ## The semantics over the reals: `Sol(F)` and `P(c)` -/

variable (M : A → Set X)

/-- The Boolean assignment a point induces on atoms. -/
def induced (x : X) : A → Prop := fun a => x ∈ M a

/-- **The paper's `Sol(F)`.** -/
def sol (φ : BForm A) : Set X := {x | φ.holds (induced M x)}

/-- **The paper's `P(c)`**: the region a cube carves out. -/
def region (c : Cube A) : Set X := {x | c.holds (induced M x)}

variable {M}

/-! ## The facets a DNF presents

A negated atom denotes an **open** half-space, which is not an intersection of
closed ones, so `lem:nonconv`'s geometry is available only for DNFs all of whose
literals are positive (`Ttc.DNF.IsPositive`, `Ttc/Dnf.lean`; README, finding 5).
`Ttc.FacetIndex D` names the facets of such a DNF: one per literal of each cube.
-/

/-- Facets of a DNF: one per literal of each of its cubes. -/
abbrev FacetIndex (D : DNF A) := Σ c : {c : Cube A // c ∈ D}, {l : Lit A // l ∈ c.val}

/-- The cubes of a DNF form a finite type: the subtype is cut out by membership in a
`List`. -/
instance instFiniteCubeMem (D : DNF A) : Finite {c : Cube A // c ∈ D} :=
  List.finite_toSet D |>.to_subtype

/-- `FacetIndex D` is finite: it is a sigma of subtypes cut out by membership in a
`List`.  Needed already here, because `Ttc.facetOf` enumerates it. -/
instance instFiniteFacetIndex (D : DNF A) : Finite (FacetIndex D) := by
  unfold FacetIndex
  have : ∀ c : {c : Cube A // c ∈ D}, Finite {l : Lit A // l ∈ c.val} := fun c =>
    (List.finite_toSet c.val).to_subtype
  infer_instance

/-! ## The lattices `ℤⁿ` and `𝕃ⁿ`, and the count `L`

The algorithm counts points of `𝕃ⁿ = 10^(−ρ)·ℤⁿ`; `lem:lattice` transports that
count to `ℤⁿ` by dilating. Both lattices, the dilation `10^ρ` and the count
`|Sol(F) ∩ 𝕃ⁿ|` are defined here, so that the problem statement can *be* about a
lattice count rather than about a bare real.  Its normalisation
`L = |Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)` (`Ttc.normalisedCount`) is not named by the
algorithm or by the headline, and lives in `Lattice/Decomposition` with the two
membership rewrites.
-/

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

/-! ## The parameter block `alg:ttc` lines 17–20, `alg:prec` line 86

The scalars the algorithm computes for itself before the main loop. What each is
chosen to satisfy is proved in `Constants/Parameters`.
-/

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

/-- `η ← ε/8` (`alg:ttc` line 17) — the slack the two geometric constants below
are budgeted against: `η` is what `Ttc.Params.kappa` and `Ttc.Params.gamma` are
written in terms of. -/
noncomputable def eta : ℝ := P.ε / 8

/-- `ε' ← ε/12` (`alg:ttc` line 18) — the per-call accuracy handed to `Vol_ED`
(`alg:ttc` line 24), one call per polytope. -/
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

/-- `γ = (64 m n / η)·√(log(8r/η))`, the inscribed radius `GetPrecision` targets
(`alg:prec` line 86). The `m` allows the `Pᵢ` different ball centres; the `8r/η`
must match `κ` (`Ttc.Params.kappa`, `Constants/Parameters`) or
`Ttc.Params.kappa_div_gamma_le` fails. See the README, finding 2. -/
noncomputable def gamma : ℝ :=
  (64 * P.m * P.n / P.eta) * Real.sqrt (Real.log (8 * P.r / P.eta))

/-- `ρ ← ⌈log₁₀(γ/γ̂)⌉` (`alg:prec` line 91), where `γ̂` is the **smallest**
inscribed-ball radius over the family — `alg:prec` maximises `γ/γ̂ᵢ` over the
polytopes, and `γ` does not depend on `i`, so `maxratio = γ / minᵢ γ̂ᵢ`. The LP
computing each `γ̂ᵢ` is not modelled; `γ̂` is an input. -/
noncomputable def precision (gammaHat : ℝ) : ℤ := ⌈Real.logb 10 (P.gamma / gammaHat)⌉

end Params

/-! # The probability vocabulary has left this file

Since `Ttc.ttc` (`Model/Pseudocode`) is a *law*, the audit surface includes the ambient
random objects the algorithm's two coin sequences are governed by.  They are no longer
defined here: they are in **`Ttc/Probability/`**, four files that between them hold
`MonteCarlo.coinLaw`/`MonteCarlo.coins`, `half`/`thinKernel`/`chainKernel`/`trajLaw` with
the two Markov-kernel instances Ionescu–Tulcea takes as instance arguments, and
`mixSteps`/`ballWalkLaw`/`kv97SampD`/`kv97ContLaw`/`e2eSampD`.  Every name is unchanged,
so nothing that used them had to change.

`Ttc/Audit/ClosureCheck.lean` audits `Ttc/Model/` **together with** `Ttc/Probability/`
for exactly this reason, and says so; read its docstring for what that costs and what
keeps it honest.

What did **not** go is the block below.  The `(Am, bv)` system, the facet count and the
diameter are the *geometry* the sampler is applied at — convex geometry read off the
formula, no randomness anywhere in it — so it stays here, with `region`, `latticeScale`
and `FacetIndex`, which is what it is built from.

## The canonical linear description of the dilated cubes

Plain geometry read off the formula — no choice is made beyond the enumeration of the
facet index. -/

section CanonicalPolytope

open MeasureTheory


/-- **The facets of `D`, enumerated.**  `Ttc.instFiniteFacetIndex` makes `FacetIndex D`
finite, so it is in bijection with `Fin (Nat.card (FacetIndex D))`.  The enumeration is
needed only because the sampler's row index lives in `Type 0` while `FacetIndex D` lives
in `A`'s universe; nothing depends on *which* bijection is chosen. -/
noncomputable def facetOf {A : Type*} (D : DNF A) :
    Fin (Nat.card (FacetIndex D)) ≃ FacetIndex D :=
  (Finite.equivFin (FacetIndex D)).symm

open scoped Classical in
/-- **The canonical normal vectors.**  Row `k` of cube `i`'s system is the coefficient
vector of the atom under row `k`'s literal when that facet belongs to `i`, and the
zero vector otherwise. -/
noncomputable def canonAm {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (D : DNF A)
    (i : {c : Cube A // c ∈ D}) (k : Fin (Nat.card (FacetIndex D))) : Space n :=
  if (facetOf D k).1 = i then WithLp.toLp 2 (atoms (facetOf D k).2.val.atom).coeff else 0

open scoped Classical in
/-- **The canonical offsets**, dilated by `s`: the atom's bound scaled by `s` on the
rows belonging to cube `i`, and `0` elsewhere. -/
noncomputable def canonBv {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (D : DNF A) (s : ℝ)
    (i : {c : Cube A // c ∈ D}) (k : Fin (Nat.card (FacetIndex D))) : ℝ :=
  if (facetOf D k).1 = i then s * (atoms (facetOf D k).2.val.atom).bound else 0

/-- **The canonical facet bound**: the exact facet count, so `hcard` holds with
equality and no slack enters `Ttc.Params.gamma` or `Ttc.Params.thresh`. -/
noncomputable def canonRfac {A : Type*} (D : DNF A) : ℝ := (Nat.card (FacetIndex D) : ℝ)

/-- **The canonical diameter bound**: the metric diameter of the dilated region
itself. -/
noncomputable def canonDm {A : Type*} {n : ℕ} (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) : ℝ :=
  Metric.diam (latticeScale ρ • region M i.val)

end CanonicalPolytope

end Ttc

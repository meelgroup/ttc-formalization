import Arlib.Prelude
import ttc.Meta.ModelClosure
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# TTC model vocabulary

This audit surface uses finite syntax for QF-LRA and Mathlib's actual Euclidean,
set, metric, and measure notions.  A normalized component is represented by its
finite closed-halfspace presentation together with its maximal inscribed `ℓ₂` ball
and boundedness.  This makes the paper's lattice arguments statements about the
same carriers whose Lebesgue volume appears in the headline, rather than about
an unrelated abstract collection of sets.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace ttc

/-- `Exp[r ← μ; f]`: the expected value of the nonnegative quantity `f` when `r` is drawn
from the distribution `μ`. It unfolds to the lower Lebesgue integral `∫⁻ r, f ∂μ`. -/
syntax "Exp[" ident " ← " term "; " term "]" : term

macro_rules
  | `(Exp[$r ← $μ; $f]) => `(∫⁻ $r:ident, $f ∂$μ)

/-- `Pr[r ← μ; P]`: the probability that `P` holds when `r` is drawn from the distribution
`μ`. It unfolds to `μ.real {r | P}`. -/
syntax "Pr[" ident " ← " term "; " term "]" : term

macro_rules
  | `(Pr[$r ← $μ; $P]) => `(MeasureTheory.Measure.real $μ {$r:ident | $P})

/-! ## Vocabulary -/

/-- Points in the positive-dimensional real ambient space used by the paper. -/
abbrev Point (n : Nat) := Fin n → Real

/-- The five relations admitted by quantifier-free linear-real arithmetic. -/
inductive LinearRelation where
  | lt | le | eq | ge | gt
  deriving DecidableEq

/-- A linear-real atom `a · x rel c`. -/
structure LinearAtom (n : Nat) where
  coefficients : Point n
  relation : LinearRelation
  constant : Real

/-- The finite QF-LRA syntax, including pure Boolean variables. -/
inductive LRAFormula (n k : Nat) where
  | atom : LinearAtom n → LRAFormula n k
  | boolVar : Fin k → LRAFormula n k
  | truth : LRAFormula n k
  | falsity : LRAFormula n k
  | neg : LRAFormula n k → LRAFormula n k
  | and : LRAFormula n k → LRAFormula n k → LRAFormula n k
  | or : LRAFormula n k → LRAFormula n k → LRAFormula n k

/-- Truth of a linear atom at a real point. -/
def LinearAtom.Holds {n : Nat} (A : LinearAtom n) (x : Point n) : Prop :=
  match A.relation with
  | .lt => dotProduct A.coefficients x < A.constant
  | .le => dotProduct A.coefficients x ≤ A.constant
  | .eq => dotProduct A.coefficients x = A.constant
  | .ge => dotProduct A.coefficients x ≥ A.constant
  | .gt => dotProduct A.coefficients x > A.constant

/-- Satisfaction uses a valuation only for the pure Boolean variables. -/
def LRAFormula.Satisfies {n k : Nat} :
    LRAFormula n k → (Fin k → Bool) → Point n → Prop
  | .atom A, _, x => A.Holds x
  | .boolVar i, β, _ => β i = true
  | .truth, _, _ => True
  | .falsity, _, _ => False
  | .neg F, β, x => ¬ F.Satisfies β x
  | .and F G, β, x => F.Satisfies β x ∧ G.Satisfies β x
  | .or F G, β, x => F.Satisfies β x ∨ G.Satisfies β x

/-- Pure Boolean variables are existentially projected out of the geometric set. -/
def solutionSet {n k : Nat} (F : LRAFormula n k) : Set (Point n) :=
  {x | ∃ β : Fin k → Bool, F.Satisfies β x}

/-- Generic finite propositional syntax used by Boolean abstraction. -/
inductive BoolFormula (α : Type*) where
  | atom : α → BoolFormula α
  | truth : BoolFormula α
  | falsity : BoolFormula α
  | neg : BoolFormula α → BoolFormula α
  | and : BoolFormula α → BoolFormula α → BoolFormula α
  | or : BoolFormula α → BoolFormula α → BoolFormula α

/-- Evaluation of finite propositional syntax. -/
def BoolFormula.Holds {α : Type*} : BoolFormula α → (α → Prop) → Prop
  | .atom a, v => v a
  | .truth, _ => True
  | .falsity, _ => False
  | .neg F, v => ¬ F.Holds v
  | .and F G, v => F.Holds v ∧ G.Holds v
  | .or F G, v => F.Holds v ∨ G.Holds v

/-- An abstracted input is either a theory atom or a pure Boolean input. -/
inductive AbstractAtom (n k : Nat) where
  | theory : LinearAtom n → AbstractAtom n k
  | pure : Fin k → AbstractAtom n k

/-- Semantics of one input of the Boolean abstraction. -/
def AbstractAtom.Holds {n k : Nat} (A : AbstractAtom n k)
    (β : Fin k → Bool) (x : Point n) : Prop :=
  match A with
  | .theory atom => atom.Holds x
  | .pure i => β i = true

/-- The paper's Boolean abstraction together with its static semantic certificate. -/
structure BooleanAbstraction {n k : Nat} (F : LRAFormula n k) where
  atomCount : Nat
  circuit : BoolFormula (Fin atomCount)
  source : Fin atomCount → AbstractAtom n k
  correct : ∀ β x, circuit.Holds (fun i => (source i).Holds β x) ↔ F.Satisfies β x

/-- A signed propositional literal. -/
structure Literal (α : Type*) where
  atom : α
  positive : Bool

/-- Truth of a signed literal. -/
def Literal.Holds {α : Type*} (l : Literal α) (v : α → Prop) : Prop :=
  if l.positive then v l.atom else ¬ v l.atom

/-- A DNF cube is a finite conjunction of signed literals. -/
abbrev Cube (α : Type*) := List (Literal α)

/-- Truth of a DNF cube. -/
def Cube.Holds {α : Type*} (C : Cube α) (v : α → Prop) : Prop :=
  ∀ l ∈ C, l.Holds v

/-- Truth of a finite list of DNF cubes. -/
def dnfHolds {α : Type*} (D : List (Cube α)) (v : α → Prop) : Prop :=
  ∃ C ∈ D, C.Holds v

/-- A certified result of converting the abstract Boolean circuit to DNF. -/
structure DNFResult {n k : Nat} {F : LRAFormula n k} (A : BooleanAbstraction F) where
  cubes : List (Cube (Fin A.atomCount))
  correct : ∀ v, dnfHolds cubes v ↔ A.circuit.Holds v

/-- A finite presentation by closed halfspaces `normal i · x ≤ offset i`. -/
structure HalfspacePresentation (n : Nat) where
  facetCount : Nat
  normal : Fin facetCount → Point n
  offset : Fin facetCount → Real

/-- The carrier of a closed-halfspace presentation. -/
def HalfspacePresentation.carrier {n : Nat} (H : HalfspacePresentation n) : Set (Point n) :=
  {x | ∀ i, dotProduct (H.normal i) x ≤ H.offset i}

/-- The closed Euclidean (`ℓ₂`) ball of radius `r` about `c`. -/
def euclideanBall {n : Nat} (c : Point n) (r : Real) : Set (Point n) :=
  {x | ‖(WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))‖ ≤ r}

/-- The coordinate identity from TTC's product space to arlib's Euclidean space. -/
def toEuclidean {n : Nat} (x : Point n) : EuclideanSpace Real (Fin n) :=
  WithLp.toLp 2 x

/-- The constraints of the Chebyshev-centre LP `maximize t s.t. aⱼ · c + t ‖aⱼ‖₂ ≤ bⱼ`
at the point `(c, t)`. -/
def HalfspacePresentation.chebyshevFeasible {n : Nat} (H : HalfspacePresentation n)
    (c : Point n) (t : Real) : Prop :=
  ∀ j, dotProduct (H.normal j) c + t * ‖toEuclidean (H.normal j)‖ ≤ H.offset j

/-- `MaxInscribedBall`: the optimum value of the Chebyshev-centre LP. -/
def HalfspacePresentation.MaxInscribedBall {n : Nat} (H : HalfspacePresentation n) : Real :=
  sSup {t | ∃ c, H.chebyshevFeasible c t}

/-- The centre returned with `MaxInscribedBall`: an optimal point `c` of the Chebyshev-centre
LP. Optimal centres need not be unique; this is one of them. -/
def HalfspacePresentation.ChebyshevCenter {n : Nat} (H : HalfspacePresentation n) : Point n :=
  Classical.epsilon fun c => H.chebyshevFeasible c H.MaxInscribedBall

/-- A surviving normalized component: a bounded, full-dimensional polytope in `ℝⁿ`, `n ≥ 1`.

Its inscribed ball is computed, not supplied: `inradius` `γ` and `incenter` `z` are the
optimum value and an optimal centre of the Chebyshev-centre LP (`MaxInscribedBall`).
`Analysis/ChebyshevCenter.lean` proves `γ > 0`, `B₂(z, γ) ⊆ P`, and that no larger `ℓ₂`
ball fits.

`outerRadius` is the paper's `R`: the radius of a ball, about any centre `outerCenter`,
enclosing the component. Taking the smallest such ball gives the paper's minimum enclosing
radius; Theorem 3 holds for every enclosing ball. The algorithm never reads it. Its sampler uses the computed
`PolytopeData.BoundingRadius` (`Model/Run.lean`), which is at most `2√n R`. `outerRadius`
enters only Theorem 3's statement, through `ρ = maxᵢ Rᵢ/γᵢ` and `R_max`. -/
structure PolytopeData (n : Nat) where
  presentation : HalfspacePresentation n
  facets_pos : 0 < presentation.facetCount
  dim_pos : 0 < n
  fullDimensional : ∃ (c : Point n) (r : Real), 0 < r ∧
    euclideanBall c r ⊆ presentation.carrier
  bounded : Bornology.IsBounded presentation.carrier
  outerCenter : Point n
  outerRadius : Real
  outerRadius_nonneg : 0 ≤ outerRadius
  outer_bound : ∀ x ∈ presentation.carrier,
    ‖(WithLp.toLp 2 (x - outerCenter) : EuclideanSpace Real (Fin n))‖ ≤ outerRadius

/-- `γ = MaxInscribedBall(P)`, the radius of a largest inscribed `ℓ₂` ball. -/
def PolytopeData.inradius {n : Nat} (P : PolytopeData n) : Real :=
  P.presentation.MaxInscribedBall

/-- `z`, the centre of that ball, as returned with `MaxInscribedBall`. -/
def PolytopeData.incenter {n : Nat} (P : PolytopeData n) : Point n :=
  P.presentation.ChebyshevCenter

/-- The geometric carrier of a normalized component. -/
abbrev PolytopeData.carrier {n : Nat} (P : PolytopeData n) : Set (Point n) :=
  P.presentation.carrier

/-- A normalized finite family whose union agrees almost everywhere with the formula.

An empty family is permitted and is the exact zero-volume branch.  Every component in a
nonempty family is already bounded, nonempty, and full-dimensional by `PolytopeData`.
-/
structure Decomposition {n k : Nat} (F : LRAFormula n k) where
  componentCount : Nat
  component : Fin componentCount → PolytopeData n
  solution_ae : ∀ᵐ x ∂(volume : Measure (Point n)),
    x ∈ ⋃ i, (component i).carrier ↔ x ∈ solutionSet F

/-- The union `Q` of all normalized components. -/
def Decomposition.union {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Set (Point n) :=
  ⋃ i, (D.component i).carrier

/-- The axis-parallel decimal lattice `10⁻ᵇ ℤⁿ`. -/
def decimalLattice (b n : Nat) : Set (Point n) :=
  {x | ∀ i, ∃ z : Int, x i = (z : Real) / (10 : Real) ^ b}

/-- The final lattice-point set `Q ∩ L_b^n`. -/
def Decomposition.latticePoints {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) : Set (Point n) :=
  D.union ∩ decimalLattice b n

/-- Total number of halfspaces in the chosen presentations. -/
def Decomposition.totalFacets {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Nat :=
  ∑ i, (D.component i).presentation.facetCount

/-- External accuracy and confidence parameters. -/
structure ApproxParams where
  epsilon : Real
  delta : Real
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1

/-- The paper's internal relative-error parameter `ε' = ε / 12`. -/
def ApproxParams.ε' (p : ApproxParams) : Real := p.epsilon / 12

/-- The per-component failure budget `δ' = δ / (4m)`; used only when `m > 0`. -/
def ApproxParams.δ' (p : ApproxParams) (m : Nat) : Real := p.delta / (4 * m)

/-- The threshold printed in Algorithm `ttc`; used only in the nonempty branch. -/
def ApproxParams.Thresh (p : ApproxParams) (m : Nat) : Real :=
  max (24 * Real.log (24 / p.delta) /
      ((1 - p.ε') * p.ε' ^ 2))
    (15 * (Real.log (6 / p.delta) + Real.log m))

/-- The inball size `(512 n / ε) √(log (32 r / ε))` that Corollary `cor:linf` asks of a
component's scaled inradius `γ / h` before `GenerateSamples` is run on it at accuracy `ε`. -/
def samplerRadiusRequirement {n : Nat} (P : PolytopeData n) (η : Real) : Real :=
  (512 * n / η) *
    Real.sqrt (Real.log (32 * P.presentation.facetCount / η))

/-- The inball size required by the finite-union lattice comparison. -/
def latticeRadiusRequirement {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Real :=
  (64 * D.componentCount * n / η) *
    Real.sqrt (Real.log (4 * D.totalFacets / η))

/-- The accuracy `ε / 96` passed to `GetPrecision` in line 3 of Algorithm `ttc`. -/
def ApproxParams.precisionEta (p : ApproxParams) : Real := p.epsilon / 96

/-! ## What the program is given

The preprocessing (`BooleanAbstraction`, `toDNF`, normalization) and the linear programs
(`MaxInscribedBall` and `BoundingRadius`) are not part of the charged program: their
results are its input.  A component is handed over as its facets and those LP results;
the program reads every number it is given into the sealed world, at the price of one
literal each. -/

/-- One component, as the program receives it: its facets `aⱼ · x ≤ bⱼ`, the centre `z`
and radius `γ` of a largest inscribed ball, and the bounding radius `R₀` about `z`. -/
structure ComponentInput (n : Nat) where
  facetCount : Nat
  normal : Fin facetCount → Point n
  offset : Fin facetCount → Real
  inradius : Real
  incenter : Point n
  boundingRadius : Real

/-! ## Cost model

### Counting arithmetic operations

`Counted α` is a value together with the number of arithmetic operations spent computing it.
Programs are built from three primitives, each costing one operation: a multiplication
`mul`, an addition `add`, and a comparison `le`. Sequencing (`do`) adds the costs. -/

/-- A value and the number of arithmetic operations used to compute it. -/
structure Counted (α : Type) where
  value : α
  cost : Nat

namespace Counted

/-- Return a value without computing anything: cost `0`. -/
def pure {α : Type} (a : α) : Counted α := ⟨a, 0⟩

/-- Run `m`, then `f` on its value; the costs add. -/
def andThen {α β : Type} (m : Counted α) (f : α → Counted β) : Counted β :=
  ⟨(f m.value).value, m.cost + (f m.value).cost⟩

instance : Monad Counted where
  pure := Counted.pure
  bind := Counted.andThen

/-- `a · b`: one operation. -/
def mul (a b : Real) : Counted Real := ⟨a * b, 1⟩

/-- `a + b`: one operation. -/
def add (a b : Real) : Counted Real := ⟨a + b, 1⟩

open Classical in
/-- The comparison `a ≤ b`: one operation. -/
def le (a b : Real) : Counted Bool := ⟨decide (a ≤ b), 1⟩

/-- `a − b`: one operation. -/
def sub (a b : Real) : Counted Real := ⟨a - b, 1⟩

/-- `⌊a⌋`: one operation. -/
def floor (a : Real) : Counted Int := ⟨⌊a⌋, 1⟩

/-- `z + k` on integers: one operation. -/
def addInt (z k : Int) : Counted Int := ⟨z + k, 1⟩

/-- `a / b`: one operation. -/
def div (a b : Real) : Counted Real := ⟨a / b, 1⟩

/-- `√a`: one operation. -/
def sqrt (a : Real) : Counted Real := ⟨Real.sqrt a, 1⟩

/-- The natural logarithm `log a`: one operation. -/
def log (a : Real) : Counted Real := ⟨Real.log a, 1⟩

/-- The `k`-th root `u^{1/k}`: one operation. -/
def root (k : Nat) (u : Real) : Counted Real := ⟨u ^ ((k : Real)⁻¹), 1⟩

open Classical in
/-- The strict comparison `a < b`: one operation. -/
def lt (a b : Real) : Counted Bool := ⟨decide (a < b), 1⟩

/-- The larger of two endpoints, where `±∞` stand for a missing endpoint: one operation. -/
def maxE (a b : EReal) : Counted EReal := ⟨max a b, 1⟩

/-- The smaller of two endpoints: one operation. -/
def minE (a b : EReal) : Counted EReal := ⟨min a b, 1⟩

/-- Read an endpoint as a real number (a missing endpoint `±∞` reads as `0`): one
operation. -/
def toReal (a : EReal) : Counted Real := ⟨a.toReal, 1⟩

/-- Read `k` random numbers (coins, Gaussians, uniforms) from the random tape: one operation
each. -/
def draw (k : Nat) : Counted Unit := ⟨(), k⟩

/-- Compute each coordinate `f i` of a vector, one after another; the costs add. -/
def forEach {α : Type} {n : Nat} (f : Fin n → Counted α) : Counted (Fin n → α) :=
  ⟨fun i => (f i).value, ∑ i, (f i).cost⟩

/-- The dot product `a₀x₀ + a₁x₁ + ⋯ + aₙ₋₁xₙ₋₁`: `n` multiplications and `n − 1`
additions. -/
def dot : (n : Nat) → (Fin n → Real) → (Fin n → Real) → Counted Real
  | 0, _, _ => Counted.pure 0
  | 1, a, x => mul (a 0) (x 0)
  | n + 2, a, x => do
      let first ← mul (a 0) (x 0)
      let rest ← dot (n + 1) (Fin.tail a) (Fin.tail x)
      add first rest

/-- Check `aⱼ · x ≤ bⱼ` for every facet `j = 0, …, r − 1`, one facet after another. -/
def allFacets {n : Nat} : (r : Nat) → (Fin r → Point n) → (Fin r → Real) → Point n →
    Counted Bool
  | 0, _, _, _ => Counted.pure true
  | r + 1, a, b, x => do
      let s ← dot n (a 0) x
      let ok ← le s (b 0)
      let rest ← allFacets r (Fin.tail a) (Fin.tail b) x
      Counted.pure (ok && rest)

end Counted

/-- The membership test `x ∈ P`: compute `aⱼ · x` and compare it with `bⱼ`, for each of
the `r` facets. `Analysis/MembershipCost.lean` proves that it answers correctly and costs
exactly `2 n r` operations. -/
def HalfspacePresentation.memberProg {n : Nat} (H : HalfspacePresentation n) (x : Point n) :
    Counted Bool :=
  Counted.allFacets H.facetCount H.normal H.offset x

/-! ### A uniform start point in the unit ball

The walk starts from a uniform point of the unit ball (the inscribed ball, in the chart
where it is the unit ball). It reads a standard Gaussian vector `g` and a uniform number
`u ∈ [0, 1]` from the tape and returns the direction `g/‖g‖` scaled to radius `u^{1/n}`.
`Analysis/BallStart.lean` proves that the result is uniform on the unit ball. -/

/-- A uniform point of the unit ball: `(u^{1/n} / ‖g‖) · g`. -/
def ballStart (n : Nat) (g : Point n) (u : Real) : Counted (Point n) := do
  Counted.draw (n + 1)
  let sq ← Counted.dot n g g
  let len ← Counted.sqrt sq
  let radius ← Counted.root n u
  let scale ← Counted.div radius len
  Counted.forEach fun i => Counted.mul scale (g i)

/-- The cost of the start point: the most `ballStart` spends on any tape. -/
noncomputable def ballStartCost (n : Nat) : Nat :=
  ⨆ (g : Point n) (u : Real), (ballStart n g u).cost

/-! ### Rounding a point to the lattice

KV97's randomized rounding: coordinate `pᵢ` becomes `⌊pᵢ⌋ + 1` with probability
`pᵢ − ⌊pᵢ⌋` and `⌊pᵢ⌋` otherwise, using a uniform `vᵢ ∈ [0, 1]` from the tape.
`Analysis/RoundPoint.lean` proves that this is KV97's rounding law. -/

/-- Round each coordinate: `⌊pᵢ⌋ + [vᵢ < pᵢ − ⌊pᵢ⌋]`. -/
def roundPoint (n : Nat) (p : Point n) (v : Fin n → Real) : Counted (Fin n → Int) :=
  Counted.forEach fun i => do
    Counted.draw 1
    let fl ← Counted.floor (p i)
    let frac ← Counted.sub (p i) fl
    let up ← Counted.lt (v i) frac
    Counted.addInt fl (if up then 1 else 0)

/-- The cost of rounding: the most `roundPoint` spends on any point and tape. -/
noncomputable def roundCost (n : Nat) : Nat :=
  ⨆ (p : Point n) (v : Fin n → Real), (roundPoint n p v).cost

/-! ### One Hit-and-Run step

The step reads its randomness from a tape: a fair `coin`, a standard Gaussian vector `g`,
and a uniform number `u ∈ [0, 1]`. If the coin shows `true` it stays put (the walk is lazy).
Otherwise it takes the direction `θ = g/‖g‖`, scans the facets for the chord
`{x + tθ} ∩ P = [lo, hi]`, and moves to `x + (lo + u (hi − lo)) θ`.
`Analysis/HitAndRunStep.lean` proves that this is arlib's lazy Hit-and-Run kernel. -/

namespace HitAndRunProg

/-- The direction `g/‖g‖`: the squared norm `g · g`, a square root, a reciprocal, and `n`
scalings. -/
def normalize (n : Nat) (g : Fin n → Real) : Counted (Fin n → Real) := do
  let sq ← Counted.dot n g g
  let len ← Counted.sqrt sq
  let inv ← Counted.div 1 len
  Counted.forEach fun i => Counted.mul inv (g i)

/-- Where the line `x + tθ` crosses the facet `a · y ≤ β`: at `t = (β − a·x)/(a·θ)`. It is a
lower endpoint if `a·θ < 0`, an upper endpoint if `a·θ > 0`, and neither (`⊥`, `⊤`)
otherwise. -/
def facetEndpoints (n : Nat) (a : Fin n → Real) (β : Real) (x θ : Fin n → Real) :
    Counted (EReal × EReal) := do
  let c ← Counted.dot n a θ
  let ax ← Counted.dot n a x
  let slack ← Counted.sub β ax
  let q ← Counted.div slack c
  let neg ← Counted.lt c 0
  let pos ← Counted.lt 0 c
  Counted.pure ((if neg then (q : EReal) else ⊥), (if pos then (q : EReal) else ⊤))

/-- The chord's endpoints: the largest lower and the smallest upper endpoint over all
facets. -/
def chord (n : Nat) : (r : Nat) → (Fin r → Fin n → Real) → (Fin r → Real) →
    (Fin n → Real) → (Fin n → Real) → Counted (EReal × EReal)
  | 0, _, _, _, _ => Counted.pure (⊥, ⊤)
  | r + 1, a, β, x, θ => do
      let first ← facetEndpoints n (a 0) (β 0) x θ
      let rest ← chord n r (Fin.tail a) (Fin.tail β) x θ
      let lo ← Counted.maxE first.1 rest.1
      let hi ← Counted.minE first.2 rest.2
      Counted.pure (lo, hi)

end HitAndRunProg

/-- One lazy Hit-and-Run step from `x` in `H`, reading a coin, a Gaussian vector `g` and a
uniform `u ∈ [0, 1]` from the tape. -/
def HalfspacePresentation.hitAndRunStep {n : Nat} (H : HalfspacePresentation n)
    (x : Point n) (coin : Bool) (g : Point n) (u : Real) : Counted (Point n) := do
  Counted.draw 1
  if coin then Counted.pure x else do
    Counted.draw n
    let θ ← HitAndRunProg.normalize n g
    let ends ← HitAndRunProg.chord n H.facetCount H.normal H.offset x θ
    let lo ← Counted.toReal ends.1
    let hi ← Counted.toReal ends.2
    let ok ← Counted.lt lo hi
    if ok then do
      Counted.draw 1
      let width ← Counted.sub hi lo
      let shift ← Counted.mul u width
      let t ← Counted.add lo shift
      Counted.forEach fun i => do
        let step ← Counted.mul t (θ i)
        Counted.add (x i) step
    else Counted.pure x

/-- The cost of one Hit-and-Run step in `H`: the most `hitAndRunStep` spends on any point and
any tape. -/
noncomputable def HalfspacePresentation.hitAndRunStepCost {n : Nat}
    (H : HalfspacePresentation n) : Nat :=
  ⨆ (x : Point n) (coin : Bool) (g : Point n) (u : Real), (H.hitAndRunStep x coin g u).cost

/-- The cost of one membership test in `H`: the most `memberProg` spends at any point.
(`Analysis/MembershipCost.lean` proves it spends the same `2 n r` at every point.) -/
noncomputable def HalfspacePresentation.memberCost {n : Nat} (H : HalfspacePresentation n) :
    Nat :=
  ⨆ x : Point n, (H.memberProg x).cost

/-! ### Charges

The deletion pass, CV18's membership queries and the sampler's rejection test are charged
`memberCost` or the actual `memberProg` cost, each Hit-and-Run step is charged
`hitAndRunStepCost`, the start point `ballStartCost`, and rounding `roundCost`
(`Model/Program.lean`, `Model/Run.lean`). The charges below are
assumed. -/

namespace TTCRuntime

/-- Unit-cost primitive operations in the requested real-RAM accounting model. -/
def deleteCopyOperations : Nat := 1
def fairCoinOperations : Nat := 1
def poissonDrawOperations : Nat := 1
def binomialDrawOperations : Nat := 1
def appendCopyOperations : Nat := 1
def scalarOperationCost : Nat := 1

/-- A rate-thinning round flips one coin for each stored copy; the two scalar
operations cover the guard and rate update. -/
def rateThinningRoundOperations (stored : Nat) : Nat :=
  stored * fairCoinOperations + 2 * scalarOperationCost

/-- A count-thinning round also draws one binomial count; its cost does not
depend on the pending count represented by that draw. -/
def countThinningRoundOperations (stored : Nat) : Nat :=
  stored * fairCoinOperations + binomialDrawOperations +
    2 * scalarOperationCost

/-! ### The quantities in Theorem 3's bound -/

/-- Maximum number of accepted samples charged per component. -/
def ThresholdCap (p : ApproxParams) (componentCount : Nat) : Nat :=
  Nat.ceil (p.Thresh componentCount)

/-- The largest facet count among TTC's normalized components. -/
def RMax {n k : Nat} {F : LRAFormula n k} (D : Decomposition F) : Nat :=
  Finset.univ.sup fun i : Fin D.componentCount =>
    (D.component i).presentation.facetCount

/-- The largest outer-radius certificate used by the corrected TTC runtime
statement. The empty family has radius zero. -/
noncomputable def theorem3OuterRadiusMax {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Real :=
  ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal (D.component i).outerRadius : NNReal) : Real)

/-- The reciprocal `1 / minᵢ γᵢ` of the smallest certified inradius; zero for the
empty family. -/
noncomputable def theorem3InverseInradiusMax {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Real :=
  ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal (1 / (D.component i).inradius) : NNReal) : Real)

/-- An input-only bound on the precision `b` chosen by `getprec` at `ε / 96`:
`1 + log₁₀⁺ γ + log₁₀⁺ (1 / minᵢ γᵢ)`, with `γ` the required radius. -/
noncomputable def theorem3PrecisionBound {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : Real :=
  1 + max 0 (Real.logb 10 (latticeRadiusRequirement D p.precisionEta)) +
    max 0 (Real.logb 10 (theorem3InverseInradiusMax D))

/-- The precision scale `1 + b + log⁺ R_max` with `b` replaced by its input-only
bound. -/
noncomputable def theorem3InputScale {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : Real :=
  1 + theorem3PrecisionBound D p + max 0 (Real.log (theorem3OuterRadiusMax D))

/-- The paper's common radius ratio `ρ = maxᵢ Rᵢ / γᵢ`, protected below by one.
The `NNReal` finite supremum gives the empty decomposition the canonical value zero before
the outer maximum is applied. -/
noncomputable def Rho {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Real :=
  max 1 ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal ((D.component i).outerRadius / (D.component i).inradius) : NNReal) : Real)

/-- The explicit bound on CV18's scheduled logarithmic factors at TTC's calls, in terms of
`n`, `ρ`, `ε'` and `δ'`: `14113440000 · (max 1 (log (20 n ρ² / (ε' δ'))))¹⁰`. -/
noncomputable def theorem3CV18LogBound (n : Nat) (rho epsilonPrime deltaPrime : Real) : Real :=
  14113440000 * (max 1 (Real.log (20 * n * rho ^ 2 / (epsilonPrime * deltaPrime)))) ^ 10

/-- The factors of Theorem 3's bound beyond `m · n⁵ · r_max · ρ² · ⌈Thresh⌉ / ε²`; they are
polylogarithmic in `n`, `m`, `ρ`, `R_max`, `1/γ_min`, `1/ε` and `1/δ`:

* `theorem3InputScale`, the precision scale `2 + log₁₀⁺ γ + log₁₀⁺ (1/γ_min) + log⁺ R_max`;
* CV18's query rate: its constant `45 · (64 · 10³⁰ + 1)` (times `576`, from `ε' = ε/12`)
  and its logarithmic factors `theorem3CV18LogBound`;
* the Hit-and-Run walk length: its constant `C = 2⁶⁸`, a factor `5` (from
  `(R'₀/γ)² ≤ 5n ρ²`, as `BoundingRadius ≤ 2√n R`), and its logarithms, including
  `log n`; and a constant for the per-component counters. -/
noncomputable def polylogFactors {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : Real :=
  theorem3InputScale D p *
    (576 * (45 * (64 * 10 ^ 30 + 1)) *
        theorem3CV18LogBound n (Rho D) p.ε' (p.δ' D.componentCount) +
      (2 : Real) ^ 68 *
        (5 * (Real.log 8 + Real.log (4 * Rho D + 1) +
          2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / p.ε') + 2) + Real.log n)) + 5)

end TTCRuntime

end ttc

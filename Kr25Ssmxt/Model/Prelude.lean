import Arlib.Prelude
import Kr25Ssmxt.Meta.ModelClosure
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

namespace Kr25Ssmxt

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

`outerRadius` is the paper's `R`: the radius of a ball about the origin enclosing the
component. The algorithm never reads it. Its sampler uses the computed
`PolytopeData.BoundingRadius` (`Model/Run.lean`), which is at most `2√n R`. `outerRadius`
enters only Theorem 3's statement, through `ρ = maxᵢ Rᵢ/γᵢ` and `R_max`. -/
structure PolytopeData (n : Nat) where
  presentation : HalfspacePresentation n
  facets_pos : 0 < presentation.facetCount
  dim_pos : 0 < n
  fullDimensional : ∃ (c : Point n) (r : Real), 0 < r ∧
    euclideanBall c r ⊆ presentation.carrier
  bounded : Bornology.IsBounded presentation.carrier
  outerRadius : Real
  outerRadius_nonneg : 0 ≤ outerRadius
  outer_bound : ∀ x ∈ presentation.carrier,
    ‖(WithLp.toLp 2 x : EuclideanSpace Real (Fin n))‖ ≤ outerRadius

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

/-! ## Runtime vocabulary -/

namespace TTCRuntime

/-- One CV18 membership call or one Hit-and-Run chord step scans the facet
presentation in dimension `n`. -/
def facetScanOperations (dimension facets : Nat) : Nat := dimension * facets

/-- Each polytope membership query is one facet scan. -/
def membershipQueryOperations (dimension facets queries : Nat) : Nat :=
  facetScanOperations dimension facets * queries

/-- Arithmetic to round one proposed point coordinatewise. -/
def roundPointOperations (dimension : Nat) : Nat := dimension

/-- One final acceptance test after rounding is another facet scan. -/
def rejectionTestOperations (dimension facets : Nat) : Nat :=
  facetScanOperations dimension facets

/-- Unit-cost primitive operations in the requested real-RAM accounting model. -/
def deleteCopyOperations : Nat := 1
def fairCoinOperations : Nat := 1
def poissonDrawOperations : Nat := 1
def binomialDrawOperations : Nat := 1
def appendCopyOperations : Nat := 1
def scalarOperationCost : Nat := 1

/-- Deleting stored copies tests each one against the current polytope and
charges one additional operation for each copy actually removed. -/
def deletionPassOperations (dimension facets checked removed : Nat) : Nat :=
  checked * facetScanOperations dimension facets +
    removed * deleteCopyOperations

/-- A rate-thinning round flips one coin for each stored copy; the two scalar
operations cover the guard and rate update. -/
def rateThinningRoundOperations (stored : Nat) : Nat :=
  stored * fairCoinOperations + 2 * scalarOperationCost

/-- A count-thinning round also draws one binomial count; its cost does not
depend on the pending count represented by that draw. -/
def countThinningRoundOperations (stored : Nat) : Nat :=
  stored * fairCoinOperations + binomialDrawOperations +
    2 * scalarOperationCost

/-- Drawing the walk's start uniformly from the inscribed ball: `n` Gaussian draws, their
norm, a uniform draw raised to the power `1/n`, the radial scaling, and the affine map onto
the ball. -/
def ballStartOperations (dimension : Nat) : Nat := 4 * dimension + 2

/-- Per rejected or accepted sampler attempt, before multiplying by its
random number of attempts: a fresh start in the inscribed ball, the walk, rounding, and
the final membership test. -/
def samplingAttemptOperations (dimension facets steps : Nat) : Nat :=
  ballStartOperations dimension + steps * facetScanOperations dimension facets +
    roundPointOperations dimension + rejectionTestOperations dimension facets

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
  `log n`; and the thinning counter. -/
noncomputable def polylogFactors {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : Real :=
  theorem3InputScale D p *
    (576 * (45 * (64 * 10 ^ 30 + 1)) *
        theorem3CV18LogBound n (Rho D) p.ε' (p.δ' D.componentCount) +
      (2 : Real) ^ 68 *
        (5 * (Real.log 8 + Real.log (4 * Rho D + 1) +
          2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / p.ε') + 2) + Real.log n)) + 21)

end TTCRuntime

end Kr25Ssmxt

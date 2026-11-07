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
finite closed-halfspace presentation together with a certified positive inball
and boundedness.  This makes the paper's lattice arguments statements about the
same carriers whose Lebesgue volume appears in the headline, rather than about
an unrelated abstract collection of sets.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace Kr25Ssmxt

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

/-- A surviving normalized component, with the geometric read-offs used by the paper.

`outerRadius` is an explicit preprocessing certificate, rather than merely a consequence
of `bounded`.  CV18's cooling schedule and running-time bound depend quantitatively on this
number, so hiding it behind classical choice would not describe an executable algorithm. -/
structure PolytopeData (n : Nat) where
  presentation : HalfspacePresentation n
  facets_pos : 0 < presentation.facetCount
  incenter : Point n
  inradius : Real
  inradius_pos : 0 < inradius
  inball : Metric.closedBall incenter inradius ⊆ presentation.carrier
  bounded : Bornology.IsBounded presentation.carrier
  outerRadius : Real
  outerRadius_nonneg : 0 ≤ outerRadius
  outer_bound : ∀ x ∈ presentation.carrier,
    ‖(WithLp.toLp 2 x : EuclideanSpace Real (Fin n))‖ ≤ outerRadius

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
def ApproxParams.epsilonPrime (p : ApproxParams) : Real := p.epsilon / 12

/-- The per-component failure budget `δ' = δ / (4m)`; used only when `m > 0`. -/
def ApproxParams.deltaPrime (p : ApproxParams) (m : Nat) : Real := p.delta / (4 * m)

/-- The threshold printed in Algorithm `ttc`; used only in the nonempty branch. -/
def ApproxParams.threshold (p : ApproxParams) (m : Nat) : Real :=
  max (24 * Real.log (24 / p.delta) /
      ((1 - p.epsilonPrime) * p.epsilonPrime ^ 2))
    (15 * (Real.log (6 / p.delta) + Real.log m))

/-- The inball size required by the finite-union lattice comparison. -/
def latticeRadiusRequirement {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Real :=
  (64 * D.componentCount * n / η) *
    Real.sqrt (Real.log (4 * D.totalFacets / η))

/-- The accuracy `ε / 96` passed to `GetPrecision` in line 3 of Algorithm `ttc`. -/
def ApproxParams.precisionEta (p : ApproxParams) : Real := p.epsilon / 96

/-- The specification of `GetPrecision(F_d, M, η)` (Algorithm `getprec`): at precision `b`
every scaled component has inradius at least `γ = (64 m n / η) √(log (4 r / η))`, with `r`
the total facet count.  TTC uses it at `η = ε / 96`. -/
def PrecisionAdequate {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) (η : Real) : Prop :=
  ∀ i, latticeRadiusRequirement D η ≤ (10 : Real) ^ b * (D.component i).inradius

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

/-- Per rejected or accepted sampler attempt, before multiplying by its
random number of attempts. -/
def samplingAttemptOperations (dimension facets steps : Nat) : Nat :=
  steps * facetScanOperations dimension facets +
    roundPointOperations dimension + rejectionTestOperations dimension facets

/-- Maximum number of accepted samples charged per component. -/
def sampleCap (p : ApproxParams) (componentCount : Nat) : Nat :=
  Nat.ceil (p.threshold componentCount)

/-- The largest facet count among TTC's normalized components. -/
def theorem3RMax {n k : Nat} {F : LRAFormula n k} (D : Decomposition F) : Nat :=
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
noncomputable def theorem3Rho {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Real :=
  max 1 ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal ((D.component i).outerRadius / (D.component i).inradius) : NNReal) : Real)

end TTCRuntime

end Kr25Ssmxt

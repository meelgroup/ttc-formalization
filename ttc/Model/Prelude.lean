import Arlib.Prelude
import Mathlib.Probability.Distributions.Bernoulli
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

open scoped BigOperators ENNReal NNReal ProbabilityTheory unitInterval
open MeasureTheory ProbabilityTheory

namespace ttc

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

/-- External accuracy and confidence parameters. -/
structure ApproxParams where
  epsilon : Real
  delta : Real
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1

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

/-! ## Lines `line:boolabs`, `line:allsat`, `line:getprec`: preprocessing and precision -/

/-- `BooleanAbstraction`, `toDNF`, and the normalization of the DNF cubes into
full-dimensional polytopes. -/
structure TTCPreprocessor (n k : Nat) where
  booleanAbstraction : (F : LRAFormula n k) → BooleanAbstraction F
  toDNF : {F : LRAFormula n k} → (A : BooleanAbstraction F) → DNFResult A
  normalize : {F : LRAFormula n k} → (A : BooleanAbstraction F) →
    DNFResult A → Bornology.IsBounded (solutionSet F) → Decomposition F

/-- Lines `line:boolabs` and `line:allsat`, then normalization: the polytopes `Pᵢ`. -/
def TTCPreprocessor.run {n k : Nat} (prep : TTCPreprocessor n k)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F)) :
    Decomposition F :=
  let abstraction := prep.booleanAbstraction F
  let cubes := prep.toDNF abstraction
  prep.normalize abstraction cubes hbounded

/-! ## Linear-program inputs -/

/-- The coordinate LP `ℓⱼ = min_{Ax ≤ b} xⱼ`. -/
def HalfspacePresentation.coordinateMin {n : Nat} (H : HalfspacePresentation n)
    (j : Fin n) : Real :=
  sInf ((fun x : Point n => x j) '' H.carrier)

/-- The coordinate LP `uⱼ = max_{Ax ≤ b} xⱼ`. -/
def HalfspacePresentation.coordinateMax {n : Nat} (H : HalfspacePresentation n)
    (j : Fin n) : Real :=
  sSup ((fun x : Point n => x j) '' H.carrier)

/-- `BoundingRadius(P) = (Σⱼ max(|ℓⱼ − zⱼ|, |uⱼ − zⱼ|)²)^{1/2}` about the inscribed ball's
centre `z`. -/
def PolytopeData.BoundingRadius {n : Nat} (P : PolytopeData n) : Real :=
  Real.sqrt (∑ j : Fin n,
    (max |P.presentation.coordinateMin j - P.incenter j|
      |P.presentation.coordinateMax j - P.incenter j|) ^ 2)

/-! ## The tape coin -/

/-- The probability `1/2`, coerced into Mathlib's unit interval. -/
def fairProbability : unitInterval :=
  Set.projIcc (0 : Real) 1 zero_le_one (1 / 2)

/-- One fair deletion coin. -/
def fairCoinLaw : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false fairProbability

/-! ## Input-only arithmetic bound

The budget is a mathematical function of the certified components and
accuracy parameters. The analysis proves that it bounds the tally of the
charged run. Evaluating this formula is not part of the estimator.
-/

/-- Total number of halfspaces in the chosen presentations. -/
def Decomposition.totalFacets {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Nat :=
  ∑ i, (D.component i).presentation.facetCount

/-- The inball size required by the finite-union lattice comparison. -/
def latticeRadiusRequirement {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Real :=
  (64 * D.componentCount * n / η) *
    Real.sqrt (Real.log (4 * D.totalFacets / η))

/-- `maxratio` of Algorithm `getprec`: the largest ratio of the required radius
`γ = (64 m n / η) √(log (4 r / η))` to a component's maximal inscribed radius `γ̂`,
starting from `1`. `γ̂` is computed by the Chebyshev-centre LP (line 7 of `getprec`). -/
def getPrecisionRatio {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Real :=
  max 1 ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal (latticeRadiusRequirement D η / (D.component i).presentation.MaxInscribedBall) :
      NNReal) : Real)

/-- Algorithm `getprec(F_d, M, η)`: return `⌈log₁₀ maxratio⌉`. -/
def GetPrecision {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Nat :=
  Nat.ceil (Real.logb 10 (getPrecisionRatio D η))

/-- A formula for the walk deadline, using only the geometry of the input. -/
def arithmeticWalkLength {d : ℕ} (P : PolytopeData d) (b : ℕ) (eps : ℝ) : ℕ :=
  let h := (10 : ℝ) ^ b
  let g := h * P.inradius
  let η := eps / 12
  let κ := Real.sqrt (2 * Real.log (4 / (η / 4))) +
    Real.sqrt (2 * Real.log P.presentation.facetCount)
  let R := (1 + κ / g) * (h * P.BoundingRadius)
  Nat.ceil (2 ^ 68 * (d : ℝ) ^ 3 * (R / g) ^ 2 * Real.log (2 * R))

/-- The population-cap numerator, before division by `ε²`. -/
def arithmeticPopulationNumerator (p : ApproxParams) (m : ℕ) : ℝ :=
  3888 * Real.log (24 / p.delta) + 15 * (Real.log (6 / p.delta) + Real.log m)

/-- Roundness of the normalized input to the volume estimator. -/
def arithmeticRoundness {d : ℕ} (P : PolytopeData d) : ℝ :=
  (max 1 (P.BoundingRadius / P.inradius)) ^ 2 / d

/-- A ceiling bound on the number of variances in the cooling schedule. -/
def arithmeticScheduleCap (d : ℕ) (p : ApproxParams) (roundness : ℝ) : ℕ :=
  let θ := p.epsilon / 24
  let T := max 1 (max (d : ℝ) (1024 * roundness * d * (max 1 (Real.log (8 / θ))) ^ 2))
  Nat.ceil (2 * (d : ℝ) * (6 + max 1 (Real.log (d / θ)))) + Nat.ceil (3 * T) + 1

/-- Number of independent cooling runs for one component. -/
def arithmeticCV18Repetitions (m : ℕ) (p : ApproxParams) : ℕ :=
  Nat.ceil (8 * max 1 (Real.log (1 / (p.delta / (8 * m)))))

/-- The amplified CV18 query-cap numerator, with its logarithmic losses explicit. -/
def arithmeticQueryNumerator (d m : ℕ) (p : ApproxParams) (roundness : ℝ) : ℝ :=
  let Λ := max 1 (Real.log ((d : ℝ) * max 1 roundness /
    ((p.epsilon / 24) * (p.delta / (8 * m)))))
  576 * (585 * (10 : ℝ) ^ 30) * (max 1 roundness * (d : ℝ) ^ 3) * (14113440000 * Λ ^ 10)

/-- Input-only cost bound for one normalized component. The capped population and
amplified query terms add, sharing a single inverse-square accuracy factor. -/
def arithmeticComponentBound {d : ℕ} (m b : ℕ) (p : ApproxParams) (P : PolytopeData d) : ℝ :=
  let r := P.presentation.facetCount
  let roundness := arithmeticRoundness P
  let S := arithmeticScheduleCap d p roundness
  let R := arithmeticCV18Repetitions m p
  let T := arithmeticWalkLength P b p.epsilon
  let perTry := 13 * d + 5 + 2 * d * r + T * (6 * d + 8 + r * (4 * d + 5))
  let base : ℕ := r * (2 * d + 2) + 20 + (200 + 12 * S) + r +
    (100 + d + r * (4 * d + 10)) + 76 +
    R * (S * (2 * d + 83) + (7 * d + 87) + (4 * R + 5))
  (base : ℝ) +
    (((d + 2 * d * r + 31 + 2 * perTry : ℕ) : ℝ) * arithmeticPopulationNumerator p m +
      ((12 * d + 31 + 2 * d * r : ℕ) : ℝ) * arithmeticQueryNumerator d m p roundness) /
      p.epsilon ^ 2

/-- Public expected arithmetic bound from the certified decomposition and
approximation parameters. No charged computation occurs on this side of the claim. -/
def ttcArithmeticBound {d k : ℕ} {F : LRAFormula d k} (D : Decomposition F)
    (p : ApproxParams) : ℝ :=
  if D.componentCount = 0 then 1 else
    let b := GetPrecision D (p.epsilon / 96)
    100 + 10 * D.componentCount + ∑ i : Fin D.componentCount,
      (((D.component i).presentation.facetCount * (d + 1) + d + 4 : ℕ) +
        arithmeticComponentBound D.componentCount b p (D.component i))

end ttc

import Kr25Ssmxt.Model.Program
import ArlibCommunity.Algorithms.CV18
import ArlibCommunity.Algorithms.HitAndRun.Model.Theorem
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.KV97.Inflate
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.RoundLaw
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.PointwiseRoute
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.Rejection

/-!
# The concrete TTC run

This file is the executable part of the audit surface. It imports the current
arlib-community CV18 and Hit-and-Run algorithms directly and adapts their laws to TTC's
component representation. Proofs that these definitions meet TTC's contracts remain under
`Analysis/`; no TTC definition in this file depends on an `Analysis/` declaration.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace

namespace Kr25Ssmxt

/-! ## Executable polytope bridges -/

/-- The coordinate identity from TTC's product space to arlib's Euclidean space. -/
def toEuclidean {n : Nat} (x : Point n) : EuclideanSpace Real (Fin n) :=
  WithLp.toLp 2 x

/-- A TTC facet normal in arlib's Euclidean representation. -/
def PolytopeData.arlibNormal {n : Nat} (P : PolytopeData n) :
    Fin P.presentation.facetCount → EuclideanSpace Real (Fin n) :=
  fun i => toEuclidean (P.presentation.normal i)

/-- The positive dilation carrying the precision-`b` decimal lattice to `ℤⁿ`. -/
def decimalScale (b : Nat) : Real := (10 : Real) ^ b

/-- Facet offsets of the decimal-dilated body. -/
def PolytopeData.scaledOffset {n : Nat} (P : PolytopeData n) (b : Nat) :
    Fin P.presentation.facetCount → Real :=
  fun i => decimalScale b * P.presentation.offset i

/-- The arlib body obtained by scaling every point of `P` by `10^b`. -/
def PolytopeData.scaledBody {n : Nat} (P : PolytopeData n) (b : Nat) :
    Set (EuclideanSpace Real (Fin n)) :=
  Arlib.Polytope.body P.arlibNormal (P.scaledOffset b)

/-- Pull the component back along `y ↦ inradius • y + incenter`. -/
def PolytopeData.cv18Body {n : Nat} (P : PolytopeData n) :
    Set (EuclideanSpace Real (Fin n)) :=
  (fun y => P.inradius • y + toEuclidean P.incenter) ⁻¹'
    Arlib.Polytope.body P.arlibNormal P.presentation.offset

/-! ## Direct CV18 law -/

namespace CommunityCV18

open ArlibCommunity.Algorithms.CV18

/-- The parameter regime of every CV18 call made by TTC. -/
def AdmissibleCV18Request (eta delta : Real) : Prop :=
  0 < eta ∧ eta ≤ 1 ∧ 0 < delta ∧ delta ≤ 1

/-- A positive roundness value computed from the actual normalized body. -/
noncomputable def roundness {n : Nat} (P : PolytopeData n) : Real :=
  |(∫ x in P.cv18Body, ‖x‖ ^ 2) / (volume P.cv18Body).toReal| + 1

/-- The CV18 parameters used by TTC. -/
def params {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) : VolumeParams where
  n := n
  dim_ok := hn
  eps := eta / 2
  heps := ⟨div_pos h.1 (by norm_num), by linarith [h.2.1]⟩
  p := delta / 2
  hp := ⟨div_pos h.2.2.1 (by norm_num), by linarith [h.2.2.2]⟩
  roundness := roundness P
  roundness_pos := by unfold roundness; positivity

/-- The current scheduled, capped, amplified CV18 membership-oracle program. -/
def algorithm : VolumeAlgorithm :=
  amplifyOracleProgram figureOneFinalScheduledCappedValueProgram

/-- Exact finite-facet membership in the normalized TTC component. -/
noncomputable def query {n : Nat} (P : PolytopeData n) :
    EuclideanSpace Real (Fin n) → Bool := by
  classical
  exact fun x => if x ∈ P.cv18Body then true else false

/-- The estimator law obtained by running the imported CV18 program. -/
def law {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) : Measure Real :=
  (algorithm (params hn P eta delta h)).runEstimate (query P)

/-- The concrete success event used to tag the CV18 estimate. -/
def successSet {n : Nat} (P : PolytopeData n) (eta : Real) : Set Real :=
  {estimate | estimate ∈ Arlib.relErr (eta / 2) (volume P.cv18Body).toReal}

/-- Boolean tag for membership in the CV18 success event. -/
noncomputable def successTag {n : Nat} (P : PolytopeData n) (eta : Real)
    (estimate : Real) : Bool := by
  classical
  exact if estimate ∈ successSet P eta then true else false

/-- CV18's estimator law with TTC's success tag and nonnegative output type. -/
def taggedLaw {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) : Measure VolumeOutcome :=
  (law hn P eta delta h).map fun estimate =>
    (successTag P eta estimate, Real.toNNReal estimate)

end CommunityCV18

/-- The positive determinant of TTC's inverse normalization chart. -/
def PolytopeData.cv18VolumeScale {n : Nat} (P : PolytopeData n) : NNReal :=
  ⟨P.inradius ^ n, pow_nonneg P.inradius_pos.le n⟩

/-- Preserve the success tag and rescale a normalized-body estimate. -/
def PolytopeData.rescaleCV18Outcome {n : Nat} (P : PolytopeData n)
    (o : VolumeOutcome) : VolumeOutcome :=
  (o.1, P.cv18VolumeScale * o.2)

/-- Push a normalized-body estimator law through determinant rescaling. -/
def PolytopeData.rescaleCV18Law {n : Nat} (P : PolytopeData n)
    (mu : Measure VolumeOutcome) : Measure VolumeOutcome :=
  mu.map P.rescaleCV18Outcome

/-- The total concrete CV18 call used by TTC. -/
def communityCV18VolumeLaw {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) : Measure VolumeOutcome := by
  classical
  exact if h : CommunityCV18.AdmissibleCV18Request eta delta then
    P.rescaleCV18Law (CommunityCV18.taggedLaw hn P eta delta h)
  else
    Measure.dirac (true, 0)

/-! ## Direct finite-step Hit-and-Run/KV97 law -/

open Arlib.Lattice.Rounding

/-- The integer lattice embedded in arlib's Euclidean state space. -/
def kv97LatEmb (n : Nat) (z : Fin n → Int) : EuclideanSpace Real (Fin n) :=
  WithLp.toLp 2 fun i => (z i : Real)

/-- The current community randomized-rounding law as a Markov kernel. -/
def kv97RoundingKernel (n : Nat) :
    Kernel (EuclideanSpace Real (Fin n)) (Fin n → Int) where
  toFun p := roundLaw (WithLp.ofLp p)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have heq : (fun p : EuclideanSpace Real (Fin n) => roundLaw (WithLp.ofLp p) s) =
        fun p => ∑' z : Fin n → Int,
          s.indicator (fun z => roundLaw (WithLp.ofLp p) {z}) z := by
      funext p
      exact (Measure.tsum_indicator_apply_singleton (roundLaw (WithLp.ofLp p)) s hs).symm
    rw [heq]
    apply Measurable.tsum
    intro z
    by_cases hz : z ∈ s
    · simp only [Set.indicator_of_mem hz, roundLaw_singleton]
      change Measurable fun p => ENNReal.ofReal (prodTent (kv97LatEmb n z) p)
      exact (measurable_prodTent (kv97LatEmb n z)).ennreal_ofReal
    · simp only [Set.indicator_of_notMem hz]
      fun_prop

instance (n : Nat) : IsMarkovKernel (kv97RoundingKernel n) := by
  constructor
  intro p
  change IsProbabilityMeasure (roundLaw (WithLp.ofLp p))
  infer_instance

/-- Draw from a continuous law, then round every coordinate independently. -/
def kv97RoundedMeasureLaw {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) : Measure (Fin n → Int) :=
  mu.bind (kv97RoundingKernel n)

/-- Attach TTC's decimal precision to an integer vector returned by KV97. -/
def encodeInteger {n : Nat} (b : Nat) (z : Fin n → Int) : LatticePoint n := (b, z)

/-- Integer vectors accepted by rejection from the scaled TTC component. -/
def acceptedIntegers {n : Nat} (P : PolytopeData n) (b : Nat) : Set (Fin n → Int) :=
  {z | kv97LatEmb n z ∈ P.scaledBody b}

/-- Round, reject outside the scaled component, and attach TTC's precision code. -/
def acceptedRoundedLatticeLaw {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) (P : PolytopeData n) (b : Nat) :
    Measure (LatticePoint n) :=
  (Arlib.condOn (kv97RoundedMeasureLaw mu) (acceptedIntegers P b)).map
    (encodeInteger b)

/-- The inflated KV97 body sampled by TTC. -/
def hitAndRunBody {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) :
    Set (EuclideanSpace Real (Fin n)) :=
  Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
    (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)

/-- The explicitly inflated offsets scanned by the finite-facet implementation. -/
def hitAndRunOffset {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) :
    Fin P.presentation.facetCount → Real :=
  fun i => P.scaledOffset b i +
    Arlib.KV97.kappaOf (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real) *
      ‖P.arlibNormal i‖

/-- The canonical geometric parameters passed to the community mixing deadline. -/
def hitAndRunDiameter {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) : Real :=
  Metric.diam (hitAndRunBody P b eta)

def hitAndRunWarmness {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) : Real :=
  (volume (hitAndRunBody P b eta) /
    volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal

def hitAndRunTolerance {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) : Real :=
  min 1 ((eta / 8) / (volume (hitAndRunBody P b eta)).toReal)

/-- The exact finite walk length selected from arlib-community's displayed deadline. -/
def hitAndRunSteps {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) : Nat :=
  Nat.ceil (ArlibCommunity.Algorithms.HitAndRun.deadline n
    (hitAndRunDiameter P b eta) (hitAndRunWarmness P b eta)
    (hitAndRunTolerance P b eta))

/-- The imported finite-step Hit-and-Run law before randomized rounding. -/
def hitAndRunContinuousLaw {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) :
    Measure (EuclideanSpace Real (Fin n)) :=
  Arlib.MarkovChains.iterate
    (Arlib.MarkovChains.lazy
      (ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep
        P.arlibNormal (hitAndRunOffset P b eta)))
    (Arlib.uniformOn volume
      (Metric.ball (decimalScale b • toEuclidean P.incenter) 1))
    (hitAndRunSteps P b eta)

/-- TTC's one-point sampler law. Proof arguments document the route certified in Analysis;
the law itself is the explicit imported algorithm above. -/
def hitAndRunPointLaw {n : Nat} (_hn : 21 ≤ n) (P : PolytopeData n) (b : Nat)
    (_hunit : 1 ≤ decimalScale b * P.inradius)
    (eta : Real) (_heta0 : 0 < eta) (_heta1 : eta ≤ 1)
    (_hfinite : (codedLatticePoints P b).Finite)
    (_hnonempty : (codedLatticePoints P b).Nonempty) : Measure (LatticePoint n) :=
  acceptedRoundedLatticeLaw (hitAndRunContinuousLaw P b eta) P b

/-- Independent restarts from a point law, tagged as an unconditionally successful batch. -/
def iidSampleBatchLaw {n count : Nat} (pointLaw : Measure (LatticePoint n)) :
    Measure (SampleBatch n count) :=
  (Measure.pi (fun _ : Fin count => pointLaw)).map (fun samples => (true, samples))

/-- A total fallback used only outside the certified preprocessing regime. -/
def failedSampleBatchLaw {n count : Nat} : Measure (SampleBatch n count) :=
  Measure.dirac (false, fun _ => default)

/-- TTC sampling calls routed directly through arlib-community Hit-and-Run and KV97. -/
def hitAndRunSamplingOracles {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k) :
    TTCOracles n k := by
  classical
  exact
    { preprocessing := prep
      computeVolume := fun P _ _ => Measure.dirac
        (true, ⟨(volume P.carrier).toReal, ENNReal.toReal_nonneg⟩)
      generateSamples := fun P count b eta _ =>
        if h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
            (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty then
          iidSampleBatchLaw
            (hitAndRunPointLaw hn P b h.1 eta h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
        else
          failedSampleBatchLaw }

/-- The concrete oracle bundle used by TTC: current community CV18 for volume and current
community finite-step Hit-and-Run followed by KV97 rounding/rejection for sampling. -/
def communityCV18HitAndRunOracles {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) : TTCOracles n k :=
  { hitAndRunSamplingOracles hn prep with
    computeVolume := communityCV18VolumeLaw (by omega) }

/-- TTC with both geometric routines fixed to the imported community implementations. -/
def communityTTC {n k : Nat} (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (prep : TTCPreprocessor n k) : Measure NNReal :=
  ttc F hbounded params (communityCV18HitAndRunOracles hn prep)

#krModelClosure communityTTC

end Kr25Ssmxt

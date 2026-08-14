import Ttc.Exec.CVGaussianOperationalMean
import Ttc.Exec.CVGaussianFactorSevenAssembly

/-!
# Operational Gaussian accuracy capstone

This module joins the score-aware factor-seven transport to the approximate operational
mean telescope.  Index zero is a constant-one dummy: `phaseProduct` and `prefixMean`
only read indices `1, ..., m`, while the corrected accuracy interface asks for positive
means at every natural index.
-/

namespace Ttc.CVGaussianOperationalAccuracy

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVIndependentStreamMoments Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianOperationalMean
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVCoordinateStatisticFactorization
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-! ## Positive-dummy coordinate factorization -/

/-- Coordinate phase family with the harmless positive dummy required by the global
positivity premises of corrected accuracy. -/
def positiveCoordinatePhases {X : Type*} {k : Nat}
    (v : Nat → (Fin k → X) → Real) :
    Nat → BlockPath X k → Real
  | 0 => fun _ => 1
  | i + 1 => fun omega => v i (blockAt (i + 1) omega)

theorem measurable_positiveCoordinatePhases
    {X : Type*} [MeasurableSpace X] {k : Nat}
    (v : Nat → (Fin k → X) → Real) (hv : ∀ i, Measurable (v i)) :
    ∀ j, Measurable (positiveCoordinatePhases v j)
  | 0 => measurable_const
  | i + 1 => (hv i).comp measurable_blockAt

/-- The recursive statistic still factors through finite history after changing only
the unused index-zero value. -/
theorem accuracyU_positiveCoordinate_eq_historyAccuracy
    {X : Type*} [MeasurableSpace X] {k : Nat}
    (mu : Measure (BlockPath X k)) (v : Nat → (Fin k → X) → Real)
    (alpha : Real) :
    ∀ i, accuracyU mu (positiveCoordinatePhases v) alpha i =
      fun omega => historyAccuracy mu v alpha i
        (fun l => Preorder.frestrictLe (π := fun _ : Nat => X) i (omega l))
  | 0 => by
      funext omega
      rfl
  | i + 1 => by
      funext omega
      rw [accuracyU_succ]
      change min
          (accuracyU mu (positiveCoordinatePhases v) alpha i omega *
            v i (blockAt (i + 1) omega))
          (alpha * prefixMean mu (positiveCoordinatePhases v) (i + 1)) = _
      rw [congrFun (accuracyU_positiveCoordinate_eq_historyAccuracy mu v alpha i)
        omega]
      have hpref : prefixMean mu (positiveCoordinatePhases v) (i + 1) =
          prefixMean mu (coordinatePhases v) (i + 1) := by
        unfold prefixMean
        apply Finset.prod_congr rfl
        intro j hj
        simp only [positiveCoordinatePhases, coordinatePhases]
      rw [hpref]
      rfl

/-- Both factorization fields needed by the independent score-aware constructor. -/
theorem positiveCoordinate_factorizations
    {X : Type*} [MeasurableSpace X] {k : Nat}
    (mu : Measure (BlockPath X k)) (v : Nat → (Fin k → X) → Real)
    (alpha : Real) :
    (∀ i, accuracyU mu (positiveCoordinatePhases v) alpha i =
      fun omega => historyAccuracy mu v alpha i
        (fun l => Preorder.frestrictLe (π := fun _ : Nat => X) i (omega l))) ∧
    (∀ i, positiveCoordinatePhases v (i + 1) =
      fun omega => v i (fun l => omega l (i + 1))) := by
  exact ⟨accuracyU_positiveCoordinate_eq_historyAccuracy mu v alpha, fun i => rfl⟩

/-- One block's empirical Gaussian score. -/
noncomputable def phaseBlockAverage {Seed : Type*} {k : Nat}
    (m : Nat) (sigmaSq : Nat → Real) (K : Set (State n)) (i : Nat) :
    (Fin k → State n × Seed) → Real :=
  streamAverage (k := k)
    (fun z => phaseScore m sigmaSq (interior K) i z.1)

theorem measurable_phaseBlockAverage {Seed : Type*} [MeasurableSpace Seed]
    {k m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)} (i : Nat) :
    Measurable (phaseBlockAverage (Seed := Seed) (k := k) m sigmaSq K i) := by
  apply measurable_streamAverage
  exact (measurable_phaseScore isOpen_interior.measurableSet i).comp measurable_fst

/-- Scalar operational score family with a positive, unused index-zero dummy. -/
noncomputable def positiveScalarPhaseFamily {Seed : Type*}
    (m : Nat) (sigmaSq : Nat → Real) (K : Set (State n)) :
    Nat → (Nat → State n × Seed) → Real
  | 0 => fun _ => 1
  | i + 1 => fun omega =>
      phaseScore m sigmaSq (interior K) i (omega (i + 1)).1

theorem measurable_positiveScalarPhaseFamily {Seed : Type*} [MeasurableSpace Seed]
    {m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (hK : MeasurableSet K) :
    ∀ j, Measurable (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)
  | 0 => measurable_const
  | i + 1 => (measurable_phaseScore isOpen_interior.measurableSet i).comp
      (measurable_fst.comp (measurable_pi_apply (i + 1)))

/-- The positive scalar empirical family is literally coordinatewise. -/
theorem streamAverage_positiveScalar_eq_positiveCoordinate
    {Seed : Type*} [MeasurableSpace Seed]
    {k m : Nat} (hk : 0 < k) {sigmaSq : Nat → Real} {K : Set (State n)} :
    (fun j => streamAverage (k := k)
      (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)) =
      positiveCoordinatePhases
        (phaseBlockAverage (Seed := Seed) (k := k) m sigmaSq K) := by
  funext j omega
  cases j with
  | zero =>
      simp [streamAverage, streamScore, Ttc.CVEst.avgOf,
        positiveScalarPhaseFamily, positiveCoordinatePhases, hk.ne']
  | succ i => rfl

/-- Ready-made finite-history factorization for the positive operational Gaussian
empirical family. -/
theorem positiveGaussianEmpirical_factorizations
    {Seed : Type*} [MeasurableSpace Seed]
    {k m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (hk : 0 < k) (mu : Measure (BlockPath (State n × Seed) k)) (alpha : Real) :
    let V := fun j => streamAverage (k := k)
      (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)
    (∀ i, accuracyU mu V alpha i =
      fun omega => historyAccuracy mu
        (phaseBlockAverage (Seed := Seed) (k := k) m sigmaSq K) alpha i
        (fun l => Preorder.frestrictLe
          (π := fun _ : Nat => State n × Seed) i (omega l))) ∧
    (∀ i, V (i + 1) = fun omega =>
      phaseBlockAverage (Seed := Seed) (k := k) m sigmaSq K i
        (fun l => omega l (i + 1))) := by
  dsimp only
  rw [streamAverage_positiveScalar_eq_positiveCoordinate hk]
  exact positiveCoordinate_factorizations mu
    (phaseBlockAverage (Seed := Seed) (k := k) m sigmaSq K) alpha

/-- Replacing the unused zero phase by one does not alter the raw prefix mean. -/
theorem prefixMean_positiveScalar_eq_empirical
    {Seed : Type*} [MeasurableSpace Seed]
    {k m : Nat} {P : Nat → Kernel (State n × Seed) (State n × Seed)}
    [∀ i, IsMarkovKernel (P i)] {mu0 : Measure (State n × Seed)}
    [IsProbabilityMeasure mu0] {sigmaSq : Nat → Real} {K : Set (State n)} :
    prefixMean (independentPathLaw k P mu0)
        (fun j => streamAverage (k := k)
          (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)) m =
      prefixMean (independentPathLaw k P mu0)
        (empiricalPhaseFamily (Seed := Seed) k m sigmaSq K) m := by
  unfold prefixMean
  apply Finset.prod_congr rfl
  intro i hi
  simp only [positiveScalarPhaseFamily, empiricalPhaseFamily]
  unfold Ttc.CVGaussianOperationalMean.scalarPhaseScore
  rfl

/-- Every sampled scalar phase has factor seven.  Active phases use the score-aware
transport budget; the terminal exact-reference phase has zero mixing error. -/
theorem positiveScalarPhaseFamily_memLp_and_factorSeven
    {Seed : Type*} [MeasurableSpace Seed]
    {k m : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eta)
    {mParam kParam : Nat} {eps R : Real} {slack boundSq : Nat → Real}
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError mParam kParam eps slack boundSq) j)
    {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (hslackDef : slack = phaseMomentSlackSeven m sigmaSq K C)
    (hboundDef : boundSq = phaseScoreTransportBoundSqSeven R sigmaSq)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw m sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7)
    (hexact : ∀ i,
      ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
          ∂(coolLaw m sigmaSq K i) ≤
        C i * (∫ x, phaseScore m sigmaSq (interior K) i x
          ∂(coolLaw m sigmaSq K i)) ^ 2) :
    ∀ j,
      MemLp (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j) 2
          (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
        ∫ omega,
            (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j omega) ^ 2
              ∂inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0 ≤
          7 * (∫ omega,
            positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j omega
              ∂inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ^ 2 := by
  intro j
  cases j with
  | zero =>
      constructor
      · simpa [positiveScalarPhaseFamily] using
          (memLp_const (μ := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)
            (c := (1 : Real)) (p := (2 : ENNReal)))
      · simp [positiveScalarPhaseFamily]
  | succ i =>
      by_cases hi : i + 1 < m
      · simpa only [positiveScalarPhaseFamily] using
          (operational_path_phaseScore_scoreAware_active_seven hop hmixError
            hslackDef hboundDef heps heps1 hsigma hKc hball hfin hKR htarget
            hC0 hC7 hexact hi)
      · have hzero : hop.mixError i = 0 := by
          rw [hmixError i, activeReferenceMixError, if_neg hi]
        have htail := operational_path_phaseScore_memLp_and_sq_moment_le_factor
          hop hsigma hKc hball hfin hKR (htarget i) (hC0 i) (hC7 i).le
          (hexact i) (T := 7) (by
            rw [hzero, ENNReal.toReal_zero, zero_mul]
            exact mul_nonneg (sub_nonneg.2 (hC7 i).le) (sq_nonneg _))
        simpa only [positiveScalarPhaseFamily] using htail

/-- Literal valid-branch `4/5` accuracy for the score-aware operational Gaussian
estimator.  Compared with the generic factor-seven assembly, the scalar `L²` facts,
all scalar moment bounds, and the approximate raw telescope are discharged here.

The remaining hypotheses are pointwise clipping/coupling facts and explicit scalar
budgets.  In particular `hmeanError` is the honest mean-side requirement on the chosen
score-aware TV shares; it is not replaced by an exact-law identity. -/
theorem scoreAware_operational_accuracy_four_fifths
    {Seed : Type*} [MeasurableSpace Seed]
    {m : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {etaInner beta gamma requested R etaMean : Real}
    {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    {slack boundSq : Nat → Real}
    (V W : Nat →
      (Fin (correctedRuntimeSamples m etaInner) → Nat → State n × Seed) → Real)
    (hop : IndependentStreamOperational (correctedRuntimeSamples m etaInner)
      (stateScheduleFromSeed Q) Q Prod.snd mu0 V m etaInner)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m (correctedRuntimeSamples m etaInner) etaInner
        slack boundSq) j)
    (hslackDef : slack = phaseMomentSlackSeven m sigmaSq K C)
    (hboundDef : boundSq = phaseScoreTransportBoundSqSeven R sigmaSq)
    (heta : 0 < etaInner) (heta1 : etaInner ≤ 1)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hetaMean : 0 ≤ etaMean)
    (hmeanBudget : 2 * (m : Real) * etaMean ≤ gamma)
    (hbudget : etaInner + beta + etaInner * beta ≤ requested)
    (hsigma : ∀ j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw m sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7)
    (hexact : ∀ i,
      ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
          ∂(coolLaw m sigmaSq K i) ≤
        C i * (∫ x, phaseScore m sigmaSq (interior K) i x
          ∂(coolLaw m sigmaSq K i)) ^ 2)
    (hmeanError : ∀ i : Fin m,
      Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) *
          (hop.mixError (i : Nat)).toReal ≤
        etaMean * (chain m sigmaSq K ((i : Nat) + 1) /
          chain m sigmaSq K (i : Nat)))
    (hm : 0 < m)
    (hWbar0 : ∀ j omega, 0 ≤ streamAverage
      (k := correctedRuntimeSamples m etaInner)
      (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j) omega)
    (hWbarEpos : ∀ j, 0 < ∫ omega, streamAverage
      (k := correctedRuntimeSamples m etaInner)
      (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j) omega
        ∂independentPathLaw (correctedRuntimeSamples m etaInner)
          (stateScheduleFromSeed Q) mu0)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega
      ∂independentPathLaw (correctedRuntimeSamples m etaInner)
        (stateScheduleFromSeed Q) mu0)
    (hVcap : ∀ j omega, V j omega ≤
      2 * correctedAlpha m etaInner * ∫ z, V j z
        ∂independentPathLaw (correctedRuntimeSamples m etaInner)
          (stateScheduleFromSeed Q) mu0)
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤
      2 * correctedAlpha m etaInner ^ 2 * ∫ z, (V j z) ^ 2
        ∂independentPathLaw (correctedRuntimeSamples m etaInner)
          (stateScheduleFromSeed Q) mu0)
    (hVdef : ∀ j omega, V j omega = min
      (streamAverage (k := correctedRuntimeSamples m etaInner)
        (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j) omega)
      (correctedAlpha m etaInner * ∫ z,
        streamAverage (k := correctedRuntimeSamples m etaInner)
          (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j) z
        ∂independentPathLaw (correctedRuntimeSamples m etaInner)
          (stateScheduleFromSeed Q) mu0))
    (hWm : ∀ j, Measurable (W j))
    {Eexact : Set
      (Fin (correctedRuntimeSamples m etaInner) → Nat → State n × Seed)}
    (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw (correctedRuntimeSamples m etaInner)
      (stateScheduleFromSeed Q) mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact,
      phaseProduct (fun j => streamAverage
        (k := correctedRuntimeSamples m etaInner)
        (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)) m omega =
      phaseProduct W m omega)
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hinitChain : initialNormalizer = chain m sigmaSq K 0)
    (htargetChain : volumeTarget = chain m sigmaSq K m)
    (hclipBudget :
      (m : Real) / (2 * correctedAlpha m etaInner) + gamma +
        ((m : Real) / (2 * correctedAlpha m etaInner)) * gamma ≤ beta) :
    4 / 5 ≤
      (independentPathLaw (correctedRuntimeSamples m etaInner)
        (stateScheduleFromSeed Q) mu0).real
        {omega | initialNormalizer * phaseProduct W m omega ∈
          Ttc.relErr requested volumeTarget} := by
  let g := positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K
  have hscalar := positiveScalarPhaseFamily_memLp_and_factorSeven hop hmixError
    hslackDef hboundDef heta heta1 hsigma hKc hball hfin hKR htarget hC0 hC7
    hexact
  have hraw0 := operational_rawPrefix_mem_relErr hop
    (correctedRuntimeSamples_pos m etaInner) hsigma hK hKc hball hfin hKR
    hetaMean hgamma1 hmeanBudget htarget hmeanError hm
  have hprefix := prefixMean_positiveScalar_eq_empirical
    (k := correctedRuntimeSamples m etaInner) (m := m) (P := stateScheduleFromSeed Q)
    (mu0 := mu0) (sigmaSq := sigmaSq) (K := K)
  have hraw : initialNormalizer *
      prefixMean (independentPathLaw (correctedRuntimeSamples m etaInner)
        (stateScheduleFromSeed Q) mu0)
        (fun j => streamAverage (k := correctedRuntimeSamples m etaInner) (g j)) m ∈
      Ttc.relErr gamma volumeTarget := by
    rw [hinitChain, hprefix, htargetChain]
    exact hraw0
  apply corrected_independentStreams_accuracy_four_fifths_biasAware_of_scalarSeven
    (g := g) (V := V) (W := W) heta heta1 hbeta hgamma hbudget
    (measurable_positiveScalarPhaseFamily hK)
    (fun j => (hscalar j).1) (fun j => (hscalar j).2)
    hWbar0 hWbarEpos hVm hV0 hEpos hVcap hV2cap hVdef hWm
    hEexact hExactFail hExact hop initialNormalizer volumeTarget hinit hvolume
    hclipBudget hraw

#print axioms prefixMean_positiveScalar_eq_empirical
#print axioms positiveCoordinate_factorizations
#print axioms positiveGaussianEmpirical_factorizations
#print axioms positiveScalarPhaseFamily_memLp_and_factorSeven
#print axioms scoreAware_operational_accuracy_four_fifths

end Ttc.CVGaussianOperationalAccuracy

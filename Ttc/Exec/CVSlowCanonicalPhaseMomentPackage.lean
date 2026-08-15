import Ttc.Exec.CVRAwareGlobalRadius
import Ttc.Exec.CVGaussianSourceWeightedMoment
import Ttc.Exec.CVScoreAwareHalfMeanBudget
import Ttc.Exec.CVSlowGaussianPhaseMoment
import Ttc.Exec.CVRelativeMeanClippingAssembly
import Ttc.Exec.CVGaussianWarmFallbackScoreMoment

/-! Phase-moment package for the R-aware slow canonical sampler. -/

set_option autoImplicit false

namespace Ttc.CVSlowCanonicalPhaseMomentPackage

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.CVIndependentStreamDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianSourceWeightedMoment Ttc.CVSlowSourceTargetTVAccuracy
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVRAwareGlobalRadius
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVRelativeMeanClippingAssembly Ttc.CVIndependentStreamMoments
open Ttc.CVCorrectedClippingArithmetic
open Ttc.CVGaussianWarmFallbackScoreMoment
open Ttc.CVSlowGaussianPhaseMoment
open Ttc.CVMinimalScoreAwareWarmLogArithmetic Ttc.CVSlowCanonicalShareBounds
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Totalized raw statistic: it agrees with the Gaussian score on every coordinate read
by the estimator and is the constant one afterwards.  This removes irrelevant
all-natural moment obligations without changing the estimator's phase product. -/
noncomputable def slowRelevantPositiveScalarFamily
    (m : Nat) (sigmaSq : Nat → Real) (K : Set (State n)) :
    Nat → (Nat → State n × State n) → Real := fun j ↦
  if j ≤ m then
    positiveScalarPhaseFamilyChainLength (Seed := State n) m sigmaSq K j
  else fun _ ↦ 1

theorem measurable_slowRelevantPositiveScalarFamily
    {m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (hK : MeasurableSet K) (j : Nat) :
    Measurable (slowRelevantPositiveScalarFamily m sigmaSq K j) := by
  unfold slowRelevantPositiveScalarFamily
  split
  · exact measurable_positiveScalarPhaseFamilyChainLength hK j
  · exact measurable_const

theorem slowRelevantPositiveScalarFamily_nonneg
    {m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (j : Nat) (omega : Nat → State n × State n) :
    0 ≤ slowRelevantPositiveScalarFamily m sigmaSq K j omega := by
  unfold slowRelevantPositiveScalarFamily
  split
  · exact positiveScalarPhaseFamilyChainLength_nonneg j omega
  · norm_num

theorem phaseProduct_slowRelevantPositiveScalarFamily
    {k m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (omega : Fin k → Nat → State n × State n) :
    phaseProduct (fun j ↦ streamAverage (k := k)
        (slowRelevantPositiveScalarFamily m sigmaSq K j)) m omega =
      phaseProduct (fun j ↦ streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j)) m omega := by
  unfold phaseProduct
  apply Finset.prod_congr rfl
  intro j hj
  have hle : j + 1 ≤ m := Finset.mem_range.mp hj
  simp only [slowRelevantPositiveScalarFamily, if_pos hle]

theorem prefixMean_slowRelevantPositiveScalarFamily
    {k m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0] :
    prefixMean (independentPathLaw k (stateScheduleFromSeed Q) mu0)
        (fun j ↦ streamAverage (k := k)
          (slowRelevantPositiveScalarFamily m sigmaSq K j)) m =
      prefixMean (independentPathLaw k (stateScheduleFromSeed Q) mu0)
        (fun j ↦ streamAverage (k := k)
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j)) m := by
  unfold prefixMean
  apply Finset.prod_congr rfl
  intro j hj
  have hle : j + 1 ≤ m := Finset.mem_range.mp hj
  simp only [slowRelevantPositiveScalarFamily, if_pos hle]

/-- Literal clipped statistic associated with the totalized raw family. -/
noncomputable def slowRelevantClippedPositiveEmpiricalFamily
    (m : Nat) (eps : Real)
    (Q : Nat → Kernel (State n) (State n × State n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (State n × State n))
    (sigmaSq : Nat → Real) (K : Set (State n)) :
    Nat → (Fin (correctedRuntimeSamples m eps) →
      Nat → State n × State n) → Real := fun j omega ↦
  let Wbar := streamAverage (k := correctedRuntimeSamples m eps)
    (slowRelevantPositiveScalarFamily m sigmaSq K j)
  min (Wbar omega) (correctedAlpha m eps *
    ∫ z, Wbar z ∂independentPathLaw (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) mu0)

theorem slowRelevantClippedPositiveEmpiricalFamily_eq_literal_upto
    {m : Nat} {eps : Real}
    {Q : Nat → Kernel (State n) (State n × State n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)}
    {sigmaSq : Nat → Real} {K : Set (State n)}
    {j : Nat} (hj : j ≤ m) :
    slowRelevantClippedPositiveEmpiricalFamily m eps Q mu0 sigmaSq K j =
      fun omega ↦
        let Wbar := streamAverage (k := correctedRuntimeSamples m eps)
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j)
        min (Wbar omega) (correctedAlpha m eps *
          ∫ z, Wbar z ∂independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) mu0) := by
  funext omega
  simp only [slowRelevantClippedPositiveEmpiricalFamily,
    slowRelevantPositiveScalarFamily, if_pos hj]

/-- Once the R-aware tail floor satisfies its explicit squared-observable scalar
budget, all local mixing and target-TV transport is discharged and each genuine slow
phase has operational factor seven. -/
theorem operational_slowCanonical_phaseScore_factorSeven
    {k m : Nat} {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real}
    {estimatorEps eps R s0 b : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m estimatorEps)
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hs0 : 0 < s0) (hb : 0 < b)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {C : Nat → Real} (hC0 : ∀ j, 0 ≤ C j) (hC7 : ∀ j, C j < 7)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m sigmaSq K C t / 2)
        (phaseScoreTransportBoundSqSeven R sigmaSq)) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw m sigmaSq K j)
      (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m j))
    (hsigmaSlow : sigmaSq = slowSourceSigmaSq n s0)
    (hexact : ∀ j,
      ∫ x, phaseScore m sigmaSq (interior K) j x ^ 2 ∂(coolLaw m sigmaSq K j) ≤
        C j * (∫ x, phaseScore m sigmaSq (interior K) j x
          ∂(coolLaw m sigmaSq K j)) ^ 2)
    (htailBudget : ∀ i : Fin m,
      b * (Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) * 15) ≤
        phaseMomentSlackSeven m sigmaSq K C (i : Nat) / 2)
    (i : Fin m) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × State n ↦
      phaseScore m sigmaSq (interior K) (i : Nat) (omega ((i : Nat) + 1)).1
    MemLp g 2 pathLaw ∧
      (∫ omega, (g omega) ^ 2 ∂pathLaw) ≤
        7 * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  have hmix : hop.mixError (i : Nat) = scoreAwareMixError (m + 1) k (eps / 2)
      (fun t ↦ phaseMomentSlackSeven m sigmaSq K C t / 2)
      (phaseScoreTransportBoundSqSeven R sigmaSq) (i : Nat) := by
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1)]
  have htransport := scoreAwareMix_add_slowTargetError_rAware_phaseBound_le
    (n := n) (m := m) (k := k) (chainLength := m) (i := (i : Nat)) hn
    (eps := eps) (R := R) (s0 := s0) (b := b) (sigmaSq := sigmaSq)
    (K := K) (C := C) heps heps1 hs0 hb i.isLt hsigma hball hfin hC7
    hsigmaSlow (htailBudget i)
  rw [← hmix] at htransport
  exact operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV
    (C := C i) (T := 7) hop hsigma hKc hball hfin hKR
    (htargetTV i) (slowTargetError_ne_top n _ m i)
    (hC0 i) (hC7 i).le (hexact i)
    (by simpa only [phaseScoreTransportBoundSqSeven,
      phaseMomentSlackSeven] using htransport)

/-- The constant clipped empirical factor associated with scalar factor seven has the
complete corrected prefix budget.  Thus after the phase theorem above is lifted through
`clipped_streamAverage_sq_moment_le_eight_of_scalar_seven`, no separate prefix-product
arithmetic remains. -/
theorem corrected_factorEight_prefix_bundle
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (∀ _j : Nat, 0 ≤ (1 + 8 / (correctedRuntimeSamples m eps : Real))) ∧
    (∀ i, i ≤ m →
      prefixMomentRatio
        (fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)) i ≤
          1 + eps ^ 2 / 6250) := by
  constructor
  · intro j
    positivity
  · intro i hi
    have hp := phaseMomentRatio_pow_le heps heps1
      (correctedRuntimeSamples_budget heps) hi
    simpa only [prefixMomentRatio, Finset.prod_const, Finset.card_range] using hp

/-- The scalar factor-seven statement, including the positive dummy coordinate, on
exactly the prefix read by the volume estimator.  This is the finite-prefix form that
the corrected recursion actually consumes; it deliberately makes no assertion about
irrelevant coordinates after `m`. -/
theorem operational_slowCanonical_positiveScalar_factorSeven_upto
    {k m : Nat} {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real}
    {estimatorEps eps R s0 b : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m estimatorEps)
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hs0 : 0 < s0) (hb : 0 < b)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {C : Nat → Real} (hC0 : ∀ j, 0 ≤ C j) (hC7 : ∀ j, C j < 7)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m sigmaSq K C t / 2)
        (phaseScoreTransportBoundSqSeven R sigmaSq)) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw m sigmaSq K j)
      (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m j))
    (hsigmaSlow : sigmaSq = slowSourceSigmaSq n s0)
    (hexact : ∀ j,
      ∫ x, phaseScore m sigmaSq (interior K) j x ^ 2 ∂(coolLaw m sigmaSq K j) ≤
        C j * (∫ x, phaseScore m sigmaSq (interior K) j x
          ∂(coolLaw m sigmaSq K j)) ^ 2)
    (htailBudget : ∀ i : Fin m,
      b * (Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) * 15) ≤
        phaseMomentSlackSeven m sigmaSq K C (i : Nat) / 2) :
    ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  intro j hj
  cases j with
  | zero =>
      constructor
      · simpa [positiveScalarPhaseFamilyChainLength] using
          (memLp_const
            (μ := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)
            (c := (1 : Real)) (p := (2 : ENNReal)))
      · simp [positiveScalarPhaseFamilyChainLength]
  | succ i =>
      have hi : i < m := Nat.lt_of_succ_le hj
      change
        MemLp (fun omega : Nat → State n × State n ↦
          phaseScore m sigmaSq (interior K) i (omega (i + 1)).1) 2
            (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
        ∫ omega,
            (phaseScore m sigmaSq (interior K) i (omega (i + 1)).1) ^ 2
            ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
          7 * (∫ omega,
            phaseScore m sigmaSq (interior K) i (omega (i + 1)).1
            ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2
      exact operational_slowCanonical_phaseScore_factorSeven hop hn heps heps1
        hs0 hb hsigma hKc hball hfin hKR hC0 hC7 hmixError htargetTV
        hsigmaSlow hexact htailBudget ⟨i, hi⟩

/-- Source-schedule specialization of the finite-prefix scalar package.  The exact-law
factor family is the literal constant two and is discharged by the slow Gaussian
moment theorem, including the terminal Gaussian-to-uniform coordinate. -/
theorem operational_slowSource_positiveScalar_factorSeven_upto
    {n k : Nat} (hn : 3 ≤ n) {N s0 R b eps : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N) (hR2 : R ^ 2 ≤ N)
    (hb : 0 < b) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real}
    {estimatorEps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V (slowSourcePhases n N s0 + 1) estimatorEps)
    (hmixError : ∀ j, hop.mixError j =
      activeReferenceMixError (slowSourcePhases n N s0 + 2)
        (scoreAwareMixError (slowSourcePhases n N s0 + 2) k (eps / 2)
          (fun t ↦ phaseMomentSlackSeven (slowSourcePhases n N s0 + 1)
            (slowSourceSigmaSq n s0) K (fun _ ↦ 2) t / 2)
          (phaseScoreTransportBoundSqSeven R (slowSourceSigmaSq n s0))) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j)
      (slowTargetError n (rAwareGlobalRadiusQ n R s0 b)
        (slowSourcePhases n N s0 + 1) j))
    (htailBudget : ∀ i : Fin (slowSourcePhases n N s0 + 1),
      b * (Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 (i : Nat))) * 15) ≤
        phaseMomentSlackSeven (slowSourcePhases n N s0 + 1)
          (slowSourceSigmaSq n s0) K (fun _ ↦ 2) (i : Nat) / 2) :
    ∀ j, j ≤ slowSourcePhases n N s0 + 1 →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  apply operational_slowCanonical_positiveScalar_factorSeven_upto hop
    (by omega) heps heps1 hs0 hb
    (slowSourceSigmaSq_pos (by omega) hs0) hKc hball hfin hKR
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) hmixError htargetTV rfl
  · intro j
    exact slowSource_phaseScore_interior_sq_moment_le_two hn hN hs0 hsN hR2
      hK hKc hball hfin hKR j
  · exact htailBudget

/-- Fully selected version of the source scalar package.  The R-aware tail floor is no
longer a premise: its mean and squared-observable halves are simultaneously positive
and fit every slow phase. -/
theorem operational_slowSource_positiveScalar_factorSeven_jointTailFloor
    {n k : Nat} (hn : 3 ≤ n) {N s0 R eps : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N) (hR2 : R ^ 2 ≤ N)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real}
    {estimatorEps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V (slowSourcePhases n N s0 + 1) estimatorEps)
    (hmixError : ∀ j, hop.mixError j =
      activeReferenceMixError (slowSourcePhases n N s0 + 2)
        (scoreAwareMixError (slowSourcePhases n N s0 + 2) k (eps / 2)
          (fun t ↦ phaseMomentSlackSeven (slowSourcePhases n N s0 + 1)
            (slowSourceSigmaSq n s0) K (fun _ ↦ 2) t / 2)
          (phaseScoreTransportBoundSqSeven R (slowSourceSigmaSq n s0))) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j)
      (slowTargetError n
        (rAwareGlobalRadiusQ n R s0
          (slowCanonicalJointTailFloor (slowSourcePhases n N s0 + 1) k eps R s0))
        (slowSourcePhases n N s0 + 1) j)) :
    ∀ j, j ≤ slowSourcePhases n N s0 + 1 →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  apply operational_slowSource_positiveScalar_factorSeven_upto hn hN hs0 hsN hR2
    (slowCanonicalJointTailFloor_pos heps) heps heps1 hK hKc hball hfin hKR
    hop hmixError htargetTV
  intro i
  let ratio := chain (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K
      ((i : Nat) + 1) /
    chain (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K (i : Nat)
  have hratio : 1 ≤ ratio := by
    dsimp only [ratio]
    exact one_le_chain_ratio_of_sigmaSq_le_succ hK hfin hball
      (slowSourceSigmaSq_pos (by omega) hs0)
      (slowSourceSigmaSq_mono_succ (by omega) hs0 i)
  have hfit := slowCanonicalJointTailFloor_moment_le
    (m := slowSourcePhases n N s0 + 1) (k := k) (eps := eps)
    (R := R) (s0 := s0) (sigma := slowSourceSigmaSq n s0 (i : Nat))
    (ratio := ratio) hs0 (initial_le_slowSourceSigmaSq (by omega) hs0 i) hratio
  simpa only [phaseMomentSlackSeven, ratio] using hfit

/-- Independent averaging turns the preceding finite-prefix scalar factor seven into
the raw factor two and supplies both integrability fields.  Positivity is kept separate:
it is a first-moment/target-TV fact, not a consequence of a second-moment upper bound. -/
theorem operational_slowCanonical_streamMoment_bundle_upto
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {sigmaSq : Nat → Real} {K : Set (State n)} (hK : MeasurableSet K)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    (hscalar : ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2) :
    ∀ j, j ≤ m →
      let Wbar := streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j)
      let pathLaw := independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) mu0
      Integrable Wbar pathLaw ∧
      Integrable (fun omega ↦ (Wbar omega) ^ 2) pathLaw ∧
      ∫ omega, (Wbar omega) ^ 2 ∂pathLaw ≤
        2 * (∫ omega, Wbar omega ∂pathLaw) ^ 2 := by
  intro j hj
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let g := positiveScalarPhaseFamilyChainLength (Seed := State n)
    m sigmaSq K j
  let k := correctedRuntimeSamples m eps
  have hk : 0 < k := correctedRuntimeSamples_pos m eps
  have hg := hscalar j hj
  have hWint := (memLp_streamAverage (k := k) scalarLaw hg.1).integrable one_le_two
  have hW2int := integrable_streamAverage_sq (k := k) scalarLaw hg.1
  have hraw := scalar_seven_to_streamAverage_two_of_six_le hk
    ((show 6 ≤ k from (eight_le_correctedRuntimeSamples heps heps1).trans'
      (by omega))) scalarLaw
    (measurable_positiveScalarPhaseFamilyChainLength hK j) hg.1 hg.2
  simpa only [g, k, scalarLaw, independentPathLaw] using
    And.intro hWint (And.intro hW2int hraw)

/-- Totalization of a finite-prefix scalar package.  After `m` the relevant family is
literally one, so the generic corrected theorem may quantify over all naturals without
introducing any new analytic premise. -/
theorem slowRelevantPositiveScalar_factorSeven_all
    {m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    (hprefix : ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2) :
    ∀ j,
      MemLp (slowRelevantPositiveScalarFamily m sigmaSq K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega, (slowRelevantPositiveScalarFamily m sigmaSq K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega, slowRelevantPositiveScalarFamily m sigmaSq K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  intro j
  by_cases hj : j ≤ m
  · simpa only [slowRelevantPositiveScalarFamily, if_pos hj] using hprefix j hj
  · rw [slowRelevantPositiveScalarFamily, if_neg hj]
    constructor
    · simpa using
        (memLp_const
          (μ := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)
          (c := (1 : Real)) (p := (2 : ENNReal)))
    · simp

/-- Target-TV first-moment transport makes every raw empirical coordinate used by the
prefix strictly positive.  This is the positivity companion to the second-moment
package above. -/
theorem operational_positiveStreamMean_upto_of_targetTV
    {k m chainLength : Nat} (hk : 0 < k)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real} {eps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R eta : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    {targetError : Nat → ENNReal}
    (htargetTV : ∀ i, TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw chainLength sigmaSq K i) (targetError i))
    (htargetError : ∀ i, targetError i ≠ ⊤)
    (herror : ∀ i : Fin m,
      (hop.mixError (i : Nat) + targetError (i : Nat)).toReal *
          Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) ≤
        eta * (chain chainLength sigmaSq K ((i : Nat) + 1) /
          chain chainLength sigmaSq K (i : Nat))) :
    ∀ j, j ≤ m → 0 < ∫ omega,
      streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          chainLength sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) := by
  intro j hj
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  cases j with
  | zero =>
      have havg := integral_streamAverage hk scalarLaw
        (g := fun _ : Nat → State n × State n ↦ (1 : Real)) measurable_const
        (integrable_const 1)
      have havg' : ∫ omega, streamAverage (k := k)
          (fun _ : Nat → State n × State n ↦ (1 : Real)) omega
          ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) = 1 := by
        simpa [independentPathLaw, scalarLaw] using havg
      simpa [positiveScalarPhaseFamilyChainLength, havg']
  | succ i =>
      have hi : i < m := Nat.lt_of_succ_le hj
      let g := Ttc.CVGaussianOperationalMean.scalarPhaseScore
        (Seed := State n) chainLength sigmaSq K i
      have hg : Measurable g :=
        Ttc.CVGaussianOperationalMean.measurable_scalarPhaseScore hK i
      have htv0 := tvLe_operational_score_eval_succ hop i
      have htv : TVLe
          (Measure.map (fun omega : Nat → State n × State n ↦
            (omega (i + 1)).1) scalarLaw)
          (coolLaw chainLength sigmaSq K i)
          (hop.mixError i + targetError i) := htv0.trans (htargetTV i)
      have hmean : ∫ omega, g omega ∂scalarLaw ∈ Ttc.relErr eta
          (chain chainLength sigmaSq K (i + 1) /
            chain chainLength sigmaSq K i) := by
        apply integral_phaseScore_interior_mem_Icc_of_tvLe hsigma hKc hball
          hfin hKR (measurable_fst.comp (measurable_pi_apply (i + 1))) htv
          (ENNReal.add_ne_top.2 ⟨hop.mixError_ne_top i, htargetError i⟩)
        simpa only [mul_comm] using herror ⟨i, hi⟩
      have hratio : 0 < chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i :=
        div_pos (chain_pos hsigma hball hfin _)
          (chain_pos hsigma hball hfin _)
      have hgInt : Integrable g scalarLaw := by
        apply Integrable.of_bound hg.aestronglyMeasurable
          (Real.exp (R ^ 2 / (2 * sigmaSq i)))
        filter_upwards with omega
        dsimp only [g, Ttc.CVGaussianOperationalMean.scalarPhaseScore]
        rw [Real.norm_eq_abs, abs_of_nonneg
          (phaseScore_nonneg chainLength sigmaSq (interior K) i _)]
        exact phaseScore_le hsigma (interior_subset.trans hKR) i _
      have hscalarPos : 0 < ∫ omega, g omega ∂scalarLaw := by
        have hlower := hmean.1
        exact (mul_pos (sub_pos.2 heta1) hratio).trans_le hlower
      have havg := integral_streamAverage hk scalarLaw hg hgInt
      simpa only [positiveScalarPhaseFamilyChainLength, independentPathLaw,
        scalarLaw, g, ← havg] using hscalarPos

theorem slowRelevantPositiveScalar_streamMean_pos_all
    {k m : Nat} (hk : 0 < k) {sigmaSq : Nat → Real} {K : Set (State n)}
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    (hprefix : ∀ j, j ≤ m → 0 < ∫ omega,
      streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) :
    ∀ j, 0 < ∫ omega,
      streamAverage (k := k)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) := by
  intro j
  by_cases hj : j ≤ m
  · simpa only [slowRelevantPositiveScalarFamily, if_pos hj] using hprefix j hj
  · let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    have havg := integral_streamAverage hk scalarLaw
      (g := fun _ : Nat → State n × State n ↦ (1 : Real)) measurable_const
      (integrable_const 1)
    have havg' : ∫ omega, streamAverage (k := k)
        (fun _ : Nat → State n × State n ↦ (1 : Real)) omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) = 1 := by
      simpa [independentPathLaw, scalarLaw] using havg
    rw [slowRelevantPositiveScalarFamily, if_neg hj, havg']
    norm_num

/-- All-natural stream and clipped moments for the totalized family.  No tail binder
remains: the irrelevant coordinates were made definitionally constant. -/
theorem slowRelevant_stream_and_clipped_moments_all
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {sigmaSq : Nat → Real} {K : Set (State n)} (hK : MeasurableSet K)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat →
      (Fin (correctedRuntimeSamples m eps) → Nat → State n × State n) → Real}
    (hscalar : ∀ j,
      MemLp (slowRelevantPositiveScalarFamily m sigmaSq K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega, (slowRelevantPositiveScalarFamily m sigmaSq K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega, slowRelevantPositiveScalarFamily m sigmaSq K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hmeanPos : ∀ j, 0 < ∫ omega,
      streamAverage (k := correctedRuntimeSamples m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) mu0))
    (hVdef : ∀ j omega, V j omega =
      min (streamAverage (k := correctedRuntimeSamples m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega)
        (correctedAlpha m eps * ∫ z,
          streamAverage (k := correctedRuntimeSamples m eps)
            (slowRelevantPositiveScalarFamily m sigmaSq K j) z
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) mu0))) :
    (∀ j,
      Integrable (streamAverage (k := correctedRuntimeSamples m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j))
        (independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) mu0)) ∧
    (∀ j, Integrable (fun omega ↦
      (streamAverage (k := correctedRuntimeSamples m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega) ^ 2)
        (independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) mu0)) ∧
    (∀ j, ∫ omega, (streamAverage (k := correctedRuntimeSamples m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega) ^ 2
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) mu0) ≤
      2 * (∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) mu0)) ^ 2) ∧
    (∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) mu0)) ∧
    (∀ j, ∫ omega, (V j omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) mu0) ≤
      (1 + 8 / (correctedRuntimeSamples m eps : Real)) *
        (∫ omega, V j omega
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) mu0)) ^ 2) := by
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let k := correctedRuntimeSamples m eps
  have hk : 0 < k := correctedRuntimeSamples_pos m eps
  have hk6 : 6 ≤ k :=
    (eight_le_correctedRuntimeSamples heps heps1).trans' (by omega)
  have hstream : ∀ j,
      Integrable (streamAverage (k := k)
        (slowRelevantPositiveScalarFamily m sigmaSq K j))
          (independentStreamLaw scalarLaw) ∧
      Integrable (fun omega ↦ (streamAverage (k := k)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega) ^ 2)
          (independentStreamLaw scalarLaw) ∧
      ∫ omega, (streamAverage (k := k)
          (slowRelevantPositiveScalarFamily m sigmaSq K j) omega) ^ 2
          ∂(independentStreamLaw scalarLaw) ≤
        2 * (∫ omega, streamAverage (k := k)
          (slowRelevantPositiveScalarFamily m sigmaSq K j) omega
          ∂(independentStreamLaw scalarLaw)) ^ 2 := by
    intro j
    refine ⟨(memLp_streamAverage (k := k) scalarLaw (hscalar j).1).integrable
        one_le_two, integrable_streamAverage_sq (k := k) scalarLaw (hscalar j).1, ?_⟩
    exact scalar_seven_to_streamAverage_two_of_six_le hk hk6 scalarLaw
      (measurable_slowRelevantPositiveScalarFamily hK j)
      (hscalar j).1 (hscalar j).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa only [k, scalarLaw, independentPathLaw] using (hstream j).1
  · intro j
    simpa only [k, scalarLaw, independentPathLaw] using (hstream j).2.1
  · intro j
    simpa only [k, scalarLaw, independentPathLaw] using (hstream j).2.2
  · intro j
    have hW0 : ∀ omega : Fin k → Nat → State n × State n,
        0 ≤ streamAverage (k := k)
          (slowRelevantPositiveScalarFamily m sigmaSq K j) omega := by
      intro omega
      unfold streamAverage Ttc.CVEst.avgOf streamScore
      apply div_nonneg
      · exact Finset.sum_nonneg fun l _ ↦
          slowRelevantPositiveScalarFamily_nonneg j (omega l)
      · positivity
    have hclip := clipped_streamAverage_sq_moment_le_eight_of_scalar_seven
      heps heps1 (mu := scalarLaw)
      (g := slowRelevantPositiveScalarFamily m sigmaSq K j)
      (measurable_slowRelevantPositiveScalarFamily hK j)
      (hscalar j).1 (hscalar j).2 hW0
      (by simpa only [k, scalarLaw, independentPathLaw] using hmeanPos j)
      (fun omega ↦ by
        simpa only [k, scalarLaw, independentPathLaw] using hVdef j omega)
    simpa only [k, scalarLaw, independentPathLaw] using hclip.1
  · intro j
    have hW0 : ∀ omega : Fin k → Nat → State n × State n,
        0 ≤ streamAverage (k := k)
          (slowRelevantPositiveScalarFamily m sigmaSq K j) omega := by
      intro omega
      unfold streamAverage Ttc.CVEst.avgOf streamScore
      apply div_nonneg
      · exact Finset.sum_nonneg fun l _ ↦
          slowRelevantPositiveScalarFamily_nonneg j (omega l)
      · positivity
    have hclip := clipped_streamAverage_sq_moment_le_eight_of_scalar_seven
      heps heps1 (mu := scalarLaw)
      (g := slowRelevantPositiveScalarFamily m sigmaSq K j)
      (measurable_slowRelevantPositiveScalarFamily hK j)
      (hscalar j).1 (hscalar j).2 hW0
      (by simpa only [k, scalarLaw, independentPathLaw] using hmeanPos j)
      (fun omega ↦ by
        simpa only [k, scalarLaw, independentPathLaw] using hVdef j omega)
    simpa only [k, scalarLaw, independentPathLaw] using hclip.2

/-- Literal clipping on the finite estimator prefix inherits the corrected factor
`1 + 8/k`.  Together with `corrected_factorEight_prefix_bundle`, this removes the
phase-moment and prefix-product fields from the slow robust certificate once raw mean
positivity is supplied. -/
theorem operational_slowCanonical_clippedMoment_bundle_upto
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {sigmaSq : Nat → Real} {K : Set (State n)} (hK : MeasurableSet K)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat →
      (Fin (correctedRuntimeSamples m eps) → Nat → State n × State n) → Real}
    (hscalar : ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hmeanPos : ∀ j, j ≤ m → 0 < ∫ omega,
      streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) mu0))
    (hVdef : ∀ j omega, j ≤ m → V j omega =
      min (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) omega)
        (correctedAlpha m eps * ∫ z,
          streamAverage (k := correctedRuntimeSamples m eps)
            (positiveScalarPhaseFamilyChainLength (Seed := State n)
              m sigmaSq K j) z
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) mu0))) :
    ∀ j, j ≤ m →
      Integrable (fun omega ↦ (V j omega) ^ 2)
        (independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega, (V j omega) ^ 2
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) mu0) ≤
        (1 + 8 / (correctedRuntimeSamples m eps : Real)) *
          (∫ omega, V j omega
            ∂(independentPathLaw (correctedRuntimeSamples m eps)
              (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  intro j hj
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let g := positiveScalarPhaseFamilyChainLength (Seed := State n)
    m sigmaSq K j
  have hW0 : ∀ omega : Fin (correctedRuntimeSamples m eps) →
      Nat → State n × State n,
      0 ≤ streamAverage (k := correctedRuntimeSamples m eps) g omega := by
    intro omega
    unfold streamAverage Ttc.CVEst.avgOf streamScore
    apply div_nonneg
    · exact Finset.sum_nonneg fun l _ ↦
        positiveScalarPhaseFamilyChainLength_nonneg j (omega l)
    · positivity
  have h := clipped_streamAverage_sq_moment_le_eight_of_scalar_seven
    heps heps1 (mu := scalarLaw) (g := g)
    (measurable_positiveScalarPhaseFamilyChainLength hK j)
    (hscalar j hj).1 (hscalar j hj).2 hW0
    (by simpa only [scalarLaw, g, independentPathLaw] using hmeanPos j hj)
    (fun omega ↦ by
      simpa only [scalarLaw, g, independentPathLaw] using hVdef j omega hj)
  simpa only [scalarLaw, g, independentPathLaw] using h

#print axioms operational_slowCanonical_phaseScore_factorSeven
#print axioms corrected_factorEight_prefix_bundle
#print axioms phaseProduct_slowRelevantPositiveScalarFamily
#print axioms operational_slowCanonical_positiveScalar_factorSeven_upto
#print axioms operational_slowSource_positiveScalar_factorSeven_upto
#print axioms operational_slowSource_positiveScalar_factorSeven_jointTailFloor
#print axioms operational_slowCanonical_streamMoment_bundle_upto
#print axioms slowRelevantPositiveScalar_factorSeven_all
#print axioms operational_positiveStreamMean_upto_of_targetTV
#print axioms slowRelevantPositiveScalar_streamMean_pos_all
#print axioms slowRelevant_stream_and_clipped_moments_all
#print axioms operational_slowCanonical_clippedMoment_bundle_upto

end Ttc.CVSlowCanonicalPhaseMomentPackage

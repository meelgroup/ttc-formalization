import Ttc.Exec.CVSlowCanonicalMomentBinders
import Ttc.Exec.CVSlowCanonicalStreamOperational

/-!
# The estimator-moment binders past the active range

`Ttc.CVSlowCanonicalMomentBinders.slowCanonical_momentBinders` discharges the frontier's
`hWint`, `hW2int`, `hWEpos`, `hrawSecond` only on the estimator prefix `j ≤ m`, because
past `m` the raw coordinate `positiveScalarPhaseFamilyChainLength m sigmaSq K j` is the
*indicator of `interior K`* rather than a cooling score (`coolRatio_of_ge`).

This file closes that gap by identifying the time-`j` state marginal of the canonical slow
schedule for `m < j`.  The route is the *stationary* branch of the schedule, and it is
even cleaner than a soft "supported in `K`" argument:

`slowCanonicalActiveSchedule … (m + 1) …` is `activeReferenceTailSchedule (m + 1) …`, so
for `m ≤ i` the time-`i` kernel is the **constant** kernel at
`slowStationaryTail n q s0 K (i + 1)`, and that law is by definition
`Measure.map (fun y ↦ ((0 : State n), y)) (slowRadiusQSeedTarget …)`.  Its score
coordinate is therefore *literally* `0`, and `0 ∈ interior K` because
`ball 0 1 ⊆ K` and `ball 0 1` is open.  Hence the tail indicator is identically `1`
almost surely, `streamAverage … j = 1` a.e., and the four moment facts are the moments of
the constant `1`.

No `interior K =ᵐ K` bridge and no quantitative mass bound are needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Ttc.CVSlowCanonicalTailPhases

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVIndependentStreamDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowCanonicalRetainedReference Ttc.CVSlowCanonicalStreamOperational
open Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVRelativeMeanClippingAssembly Ttc.CVIndependentStreamMoments
open Ttc.CVGaussianOperationalMean
open Ttc.CVSlowCanonicalMomentBinders
open Ttc.CVSlowCanonicalRobustCertificate
open Ttc.CVCorrectedClippingArithmetic
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## Step 0 — the time-`(i+1)` marginal of a path driven by a constant kernel -/

/-- If the time-`i` transition of an inhomogeneous chain is the constant kernel at `nu`,
then the time-`(i+1)` marginal of the trajectory law is exactly `nu`. -/
theorem map_eval_succ_inhomogeneousPathMeasure_of_const
    {E : Type*} [MeasurableSpace E]
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu] (i : Nat)
    (nu : Measure E) [IsProbabilityMeasure nu] (hP : P i = Kernel.const E nu) :
    Measure.map (fun omega : Nat → E ↦ omega (i + 1))
        (inhomogeneousPathMeasure P mu) = nu := by
  have hker : inhomogeneousHistoryKernel P i = Kernel.const _ nu := by
    refine Kernel.ext fun a ↦ ?_
    simp only [inhomogeneousHistoryKernel, Kernel.comap_apply, hP, Kernel.const_apply]
  have hF : Measurable
      (fun omega : Nat → E ↦ (Preorder.frestrictLe i omega, omega (i + 1))) :=
    (Preorder.measurable_frestrictLe i).prodMk (measurable_pi_apply (i + 1))
  have hjoint := map_history_next_inhomogeneousPathMeasure P mu i
  haveI : IsProbabilityMeasure
      ((inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i)) :=
    Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe i).aemeasurable
  calc Measure.map (fun omega : Nat → E ↦ omega (i + 1))
        (inhomogeneousPathMeasure P mu)
      = Measure.map Prod.snd (Measure.map
          (fun omega : Nat → E ↦ (Preorder.frestrictLe i omega, omega (i + 1)))
          (inhomogeneousPathMeasure P mu)) := by
        rw [Measure.map_map measurable_snd hF]
        rfl
    _ = Measure.map Prod.snd
          ((inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i) ⊗ₘ
            Kernel.const _ nu) := by rw [← hjoint, hker]
    _ = Measure.map Prod.snd
          (((inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i)).prod nu) := by
        rw [Measure.compProd_const]
    _ = nu := by rw [Measure.map_snd_prod, measure_univ, one_smul]

#print axioms map_eval_succ_inhomogeneousPathMeasure_of_const

/-! ## Step 1 — past the active range the canonical slow schedule is stationary -/

/-- For `m ≤ i` the canonical slow state schedule at cutoff `m + 1` is the **constant**
kernel at the stationary tail law `slowStationaryTail n q s0 K (i + 1)`. -/
theorem stateScheduleFromSeed_slowCanonical_of_ge
    (hn : 21 ≤ n) (m k : Nat) {q eps : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K) (scoreScale : Real)
    (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    {i : Nat} (hi : m ≤ i) :
    stateScheduleFromSeed Q i =
      Kernel.const (ScoreSeed n)
        (slowStationaryTail n q (slowSourceInitialVariance n) K (i + 1)) := by
  have hQi : Q i =
      Kernel.const (State n)
        (slowStationaryTail n q (slowSourceInitialVariance n) K (i + 1)) := by
    rw [hQ]
    unfold slowCanonicalActiveSchedule activeReferenceTailSchedule
    rw [if_neg (by omega)]
  refine Kernel.ext fun z ↦ ?_
  rw [stateScheduleFromSeed_factor, Kernel.comap_apply, hQi, Kernel.const_apply,
    Kernel.const_apply]

#print axioms stateScheduleFromSeed_slowCanonical_of_ge

/-! ## Step 2 — the raw coordinate past the active range is the interior indicator -/

/-- **Deliverable 1.**  Past the chain length the raw scalar coordinate is not a cooling
score but the plain indicator of `interior K` read at time `j`: by
`Arlib.GaussianCooling.coolRatio_of_ge` the ratio degenerates to `1`. -/
theorem positiveScalarPhaseFamilyChainLength_of_gt {Seed : Type*}
    (m : Nat) (sigmaSq : Nat → Real) (K : Set (State n)) {j : Nat} (hj : m < j) :
    positiveScalarPhaseFamilyChainLength (Seed := Seed) m sigmaSq K j =
      fun omega ↦ Set.indicator (interior K) (fun _ ↦ (1 : Real)) ((omega j).1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hratio : coolRatio (n := n) m sigmaSq i = fun _ ↦ (1 : Real) := by
    funext x
    exact coolRatio_of_ge (by omega) x
  funext omega
  simp only [positiveScalarPhaseFamilyChainLength, scalarPhaseScore, phaseScore, hratio]

#print axioms positiveScalarPhaseFamilyChainLength_of_gt

/-! ## Step 3 — the tail score coordinate sits in `interior K` -/

/-- The unit ball around the origin is open, so a body containing it contains the origin
in its interior. -/
theorem zero_mem_interior_of_ball_subset {K : Set (State n)}
    (hball : ball (0 : State n) 1 ⊆ K) : (0 : State n) ∈ interior K :=
  interior_maximal hball isOpen_ball (mem_ball_self one_pos)

/-- **Deliverable 2.**  Past the active range the canonical slow path's time-`j` score
coordinate lies in `interior K` almost surely.  In fact it is *identically the origin*:
the stationary tail law `slowStationaryTail` is a pushforward along `y ↦ (0, y)`. -/
theorem slowCanonical_tailScore_mem_interior_ae
    (hn : 21 ≤ n) (m k : Nat) {q eps : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    {j : Nat} (hj : m < j) :
    ∀ᵐ omega ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n)),
      (omega j).1 ∈ interior K := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hset : MeasurableSet {z : ScoreSeed n | z.1 ∈ interior K} :=
    measurable_fst isOpen_interior.measurableSet
  have hconst := stateScheduleFromSeed_slowCanonical_of_ge hn m k hq4 hK scoreScale
    slack boundSq hQ (i := i) (by omega)
  have hmap := map_eval_succ_inhomogeneousPathMeasure_of_const
    (stateScheduleFromSeed Q) (slowInitialPair n) i
    (slowStationaryTail n q (slowSourceInitialVariance n) K (i + 1)) hconst
  have htail : ∀ᵐ z ∂(slowStationaryTail n q (slowSourceInitialVariance n) K (i + 1)),
      z.1 ∈ interior K := by
    unfold slowStationaryTail
    rw [ae_map_iff (by fun_prop) hset]
    filter_upwards with y
    exact zero_mem_interior_of_ball_subset hball
  have hmp : MeasurePreserving (fun omega : Nat → ScoreSeed n ↦ omega (i + 1))
      (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n))
      (slowStationaryTail n q (slowSourceInitialVariance n) K (i + 1)) :=
    ⟨measurable_pi_apply (i + 1), hmap⟩
  exact hmp.quasiMeasurePreserving.ae htail

#print axioms slowCanonical_tailScore_mem_interior_ae

/-! ## Step 4 — the tail stream average is the constant one -/

/-- **Deliverable 3.**  Past the active range every raw stream coordinate is the indicator
of `interior K` evaluated at the origin, hence `1`; so the `k`-fold empirical average is
almost surely the constant `1`. -/
theorem slowCanonical_streamAverage_tail_eq_one
    (hn : 21 ≤ n) (m k : Nat) (hk : 0 < k) {q eps : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (sigmaSq : Nat → Real) {j : Nat} (hj : m < j) :
    (fun omega ↦ streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n) m sigmaSq K j) omega)
      =ᵐ[independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)]
      fun _ ↦ (1 : Real) := by
  have hstate := slowCanonical_tailScore_mem_interior_ae hn m k hq4 hK hball scoreScale
    slack boundSq hQ hj
  have hcoord : ∀ l : Fin k,
      ∀ᵐ omega ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)),
        (omega l j).1 ∈ interior K := fun l ↦
    (measurePreserving_streamCoord (k := k)
      (inhomogeneousPathMeasure (stateScheduleFromSeed Q)
        (slowInitialPair n)) l).quasiMeasurePreserving.ae hstate
  filter_upwards [ae_all_iff.mpr hcoord] with omega homega
  rw [positiveScalarPhaseFamilyChainLength_of_gt (Seed := State n) m sigmaSq K hj]
  have hone : ∀ l : Fin k,
      streamScore (k := k)
        (fun z : Nat → ScoreSeed n ↦
          Set.indicator (interior K) (fun _ ↦ (1 : Real)) ((z j).1)) l omega = 1 := by
    intro l
    exact Set.indicator_of_mem (homega l) (fun _ ↦ (1 : Real))
  unfold streamAverage Ttc.CVEst.avgOf
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hk.ne')

#print axioms slowCanonical_streamAverage_tail_eq_one

/-! ## Step 5 — the clipped family past the active range

The five estimator-moment binders of the frontier (and of its canonical instantiation
`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical`) are `hWint`, `hW2int`,
`hWEpos`, `hrawSecond` and `hphaseMoment`.  The first four are about the raw stream
average, closed by `slowCanonical_streamAverage_tail_eq_one`; the fifth is about the
*clipped* family, and the same tail identification closes it because past `m` the clip is
inactive: the raw mean is `1` and the clipping constant `correctedAlpha m eps` is at
least `100000`. -/

/-- Past the active range the clipped empirical family is almost surely the constant
`1`: the raw average is `1` a.e., its mean is `1`, and `1 ≤ correctedAlpha m eps`. -/
theorem slowCanonical_clippedFamily_tail_eq_one
    (hn : 21 ≤ n) (m : Nat) {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {q : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    {j : Nat} (hj : m < j) :
    (fun omega ↦ slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps
        Q (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega)
      =ᵐ[independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) := by
  have hk : 0 < correctedRuntimeSamples m eps := correctedRuntimeSamples_pos m eps
  have htail := slowCanonical_streamAverage_tail_eq_one hn m
    (correctedRuntimeSamples m eps) hk hq4 hK hball scoreScale slack boundSq hQ
    (slowSourceSigmaSq n (slowSourceInitialVariance n)) hj
  have hint : ∫ z, streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) z
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)) = 1 := by
    rw [integral_congr_ae htail]
    simp
  have halpha : (1 : Real) ≤ correctedAlpha m eps := by
    have ha := correctedAlpha_ge_hundred_thousand (m := m) heps heps1
    linarith
  filter_upwards [htail] with omega homega
  simp only [slowClippedPositiveEmpiricalFamily]
  rw [homega, hint, mul_one]
  exact min_eq_left halpha

#print axioms slowCanonical_clippedFamily_tail_eq_one

/-! ## Step 6 — the five estimator-moment binders at every index -/

/-- **Deliverable 4.**  The frontier's `hWint`, `hW2int`, `hWEpos`, `hrawSecond` and
`hphaseMoment` at **all** `j`, i.e. the guard `j ≤ m` of
`Ttc.CVSlowCanonicalMomentBinders.slowCanonical_momentBinders` removed from all five.

On `j ≤ m` each conjunct is `slowCanonical_momentBinders`; on `m < j` the raw stream
average and the clipped family are both almost surely the constant `1`
(`slowCanonical_streamAverage_tail_eq_one`, `slowCanonical_clippedFamily_tail_eq_one`),
so the five facts are `Integrable 1`, `Integrable 1`, `0 < 1`, `1 ≤ 2 * 1 ^ 2` and
`1 ≤ (1 + 8 / k) * 1 ^ 2`.

The five conjuncts are the binder text of
`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` at
`k := correctedRuntimeSamples m eps`, and are projected out one by one just below. -/
theorem slowCanonical_momentBinders_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    (∀ j, Integrable
      (fun omega ↦ streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, Integrable
      (fun omega ↦ (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, 0 < ∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, ∫ omega, (streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ j, ∫ omega,
        (slowClippedPositiveEmpiricalFamily m
          (correctedRuntimeSamples m eps) eps Q
          (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      (1 + 8 / (correctedRuntimeSamples m eps : Real)) *
        (∫ omega, slowClippedPositiveEmpiricalFamily m
            (correctedRuntimeSamples m eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) := by
  have hbase := slowCanonical_momentBinders hn m heps heps1 hK hKc hball hfin hKR
    hop htau hmixError hexact
  have hk : 0 < correctedRuntimeSamples m eps := correctedRuntimeSamples_pos m eps
  have htail : ∀ j, m < j →
      (fun omega ↦ streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
        =ᵐ[independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) :=
    fun j hj ↦ slowCanonical_streamAverage_tail_eq_one hn m
      (correctedRuntimeSamples m eps) hk hq4 hK hball scoreScale slack boundSq hQ
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) hj
  have htailSq : ∀ j, m < j →
      (fun omega ↦ (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
        =ᵐ[independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) := by
    intro j hj
    filter_upwards [htail j hj] with omega homega
    rw [homega]
    norm_num
  have hclip : ∀ j, m < j →
      (fun omega ↦ slowClippedPositiveEmpiricalFamily m
          (correctedRuntimeSamples m eps) eps Q (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega)
        =ᵐ[independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) :=
    fun j hj ↦ slowCanonical_clippedFamily_tail_eq_one hn m heps heps1 hq4 hK hball
      scoreScale slack boundSq hQ hj
  have hclipSq : ∀ j, m < j →
      (fun omega ↦ (slowClippedPositiveEmpiricalFamily m
          (correctedRuntimeSamples m eps) eps Q (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2)
        =ᵐ[independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) := by
    intro j hj
    filter_upwards [hclip j hj] with omega homega
    rw [homega]
    norm_num
  refine ⟨fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · rcases Nat.lt_or_ge m j with hj | hj
    · exact (integrable_const (1 : Real)).congr (htail j hj).symm
    · exact hbase.1 j hj
  · rcases Nat.lt_or_ge m j with hj | hj
    · exact (integrable_const (1 : Real)).congr (htailSq j hj).symm
    · exact hbase.2.1 j hj
  · rcases Nat.lt_or_ge m j with hj | hj
    · rw [integral_congr_ae (htail j hj)]
      simp
    · exact hbase.2.2.1 j hj
  · rcases Nat.lt_or_ge m j with hj | hj
    · rw [integral_congr_ae (htail j hj), integral_congr_ae (htailSq j hj)]
      simp
    · exact hbase.2.2.2.1 j hj
  · rcases Nat.lt_or_ge m j with hj | hj
    · rw [integral_congr_ae (hclip j hj), integral_congr_ae (hclipSq j hj)]
      have hk8 : (0 : Real) ≤ 8 / (correctedRuntimeSamples m eps : Real) := by positivity
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_pow]
      linarith
    · exact hbase.2.2.2.2.2.1 j hj

#print axioms slowCanonical_momentBinders_all

/-! ## Step 7 — the five binders as five separate theorems

`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` consumes them as five
separate arguments, so each conjunct is projected out under its own name. -/

/-- The frontier's `hWint` at **all** `j`. -/
theorem slowCanonical_hWint_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    ∀ j, Integrable
      (fun omega ↦ streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)) :=
  (slowCanonical_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR hq4
    scoreScale slack boundSq hQ hop htau hmixError hexact).1

/-- The frontier's `hW2int` at **all** `j`. -/
theorem slowCanonical_hW2int_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    ∀ j, Integrable
      (fun omega ↦ (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)) :=
  (slowCanonical_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR hq4
    scoreScale slack boundSq hQ hop htau hmixError hexact).2.1

/-- The frontier's `hWEpos` at **all** `j`. -/
theorem slowCanonical_hWEpos_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    ∀ j, 0 < ∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)) :=
  (slowCanonical_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR hq4
    scoreScale slack boundSq hQ hop htau hmixError hexact).2.2.1

/-- The frontier's `hrawSecond` at **all** `j`. -/
theorem slowCanonical_hrawSecond_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    ∀ j, ∫ omega, (streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2 :=
  (slowCanonical_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR hq4
    scoreScale slack boundSq hQ hop htau hmixError hexact).2.2.2.1

/-- The frontier's `hphaseMoment` at **all** `j`, at
`factor := fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)` in its beta-reduced
form.  This is the fifth tail binder; it is about the *clipped* family, and no ungated
clipped bundle existed before this file. -/
theorem slowCanonical_hphaseMoment_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    ∀ j, ∫ omega,
        (slowClippedPositiveEmpiricalFamily m
          (correctedRuntimeSamples m eps) eps Q
          (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      (1 + 8 / (correctedRuntimeSamples m eps : Real)) *
        (∫ omega, slowClippedPositiveEmpiricalFamily m
            (correctedRuntimeSamples m eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2 :=
  (slowCanonical_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR hq4
    scoreScale slack boundSq hQ hop htau hmixError hexact).2.2.2.2

#print axioms slowCanonical_hWint_all
#print axioms slowCanonical_hW2int_all
#print axioms slowCanonical_hWEpos_all
#print axioms slowCanonical_hrawSecond_all
#print axioms slowCanonical_hphaseMoment_all

end Ttc.CVSlowCanonicalTailPhases

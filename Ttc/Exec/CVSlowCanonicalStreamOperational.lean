import Ttc.Exec.CVSlowCanonicalRetainedReference

/-! # Operational stream package for the canonical slow schedule

This file instantiates the operational binders of the slow-canonical robust
certificate.  Two arithmetic parameters are separated:

* `shareEps` drives the *schedule* (`scoreAwareRetries` / `scoreAwareEta` /
  `scoreAwareZeta` / `scoreAwareMixError`);
* `eta` drives the *estimator* (`correctedAlpha` and the dependence target
  `correctedNu`).

The existing constructor
`Ttc.CVSlowRadiusQCanonicalOperational.seedProjectedOperational_slowRadiusQ_scoreAware`
uses a single `eps` for both roles.  We call it at `eps := shareEps` with a
throw-away zero statistic (the fields it supplies that we reuse — `pi`, `tau`,
`warmConst`, `mixError`, `last_seed_warm`, `distributional_mixing` — depend
neither on `V` nor on the estimator parameter), and rebuild the two
estimator-dependent fields `U_eq` and `dependence_budget` at `eta`.  The latter
uses monotonicity of `correctedNu` in its accuracy argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Ttc.CVSlowCanonicalStreamOperational

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence Ttc.CVIndependentStreamDependence
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowRadiusQReferencePhaseTV
open Ttc.CVSlowRadiusQCanonicalOperational Ttc.CVSlowRadiusQRecursiveOperational
open Ttc.CVSlowSourceReferenceCertificate Ttc.CVSlowCanonicalRetainedReference
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## Arithmetic helpers -/

/-- The accuracy recursion driven by the identically-zero statistic is the constant
family `1, 0, 0, …`; in particular it factors through any prefix. -/
theorem accuracyU_zeroFamily {Om : Type*} [MeasurableSpace Om] (mu : Measure Om)
    (alpha : Real) (i : Nat) :
    accuracyU mu (fun _ _ ↦ (0 : Real)) alpha i =
      fun _ ↦ (if i = 0 then (1 : Real) else 0) := by
  cases i with
  | zero => funext w; simp
  | succ j =>
      have hpre : prefixMean mu (fun _ _ ↦ (0 : Real)) (j + 1) = 0 := by
        unfold prefixMean
        refine Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos j)) ?_
        simp
      funext w
      rw [accuracyU_succ]
      simp [hpre]

/-- Closed form of the corrected dependence target. -/
theorem correctedNu_eq_pow (m : Nat) {e : Real} (he : 0 < e) :
    correctedNu m e = e ^ 10 / (100000 ^ 5 * ((m : Real) + 1) ^ 5) := by
  have hm : (0 : Real) < (m : Real) + 1 := by positivity
  unfold correctedNu correctedAlpha
  field_simp

/-- `correctedNu m ·` is monotone on the positive reals. -/
theorem correctedNu_mono (m : Nat) {a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    correctedNu m a ≤ correctedNu m b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [correctedNu_eq_pow m ha, correctedNu_eq_pow m hb]
  gcongr

/-- The dependence target computed at the schedule parameters `(m+1, eps/2)` is
below the one computed at the estimator parameters `(m, eps)`. -/
theorem correctedNu_succ_half_le (m : Nat) {eps : Real} (heps : 0 < eps) :
    correctedNu (m + 1) (eps / 2) ≤ correctedNu m eps := by
  have hhalf : (0 : Real) < eps / 2 := by positivity
  rw [correctedNu_eq_pow (m + 1) hhalf, correctedNu_eq_pow m heps]
  have hcast : (((m + 1 : Nat) : Real) + 1) = ((m : Real) + 1) + 1 := by push_cast; ring
  rw [hcast]
  have hm : (0 : Real) < (m : Real) + 1 := by positivity
  gcongr <;> linarith


#print axioms accuracyU_zeroFamily
#print axioms correctedNu_eq_pow
#print axioms correctedNu_mono
#print axioms correctedNu_succ_half_le

/-! ## The two-parameter seed-projected package -/

/-- Seed-projected operational package for the canonical slow schedule with the
schedule accuracy `shareEps` and the estimator accuracy `eta` decoupled.  The
warm-start and stationary-tail seed identities are discharged internally. -/
noncomputable def seedProjectedOperational_slowCanonical_split
    (hn : 21 ≤ n) (cutoff k : Nat) (hcut : 0 < cutoff) (hk : 1 ≤ k)
    {q shareEps eta : Real} (hq4 : 4 ≤ q)
    (hshare : 0 < shareEps) (hshare1 : shareEps ≤ 1) (hle : shareEps ≤ eta)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (scoreScale : Real) {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (V : Nat → (Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (inhomogeneousPathMeasure (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) cutoff k
          (q := q) (eps := shareEps) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq)) (slowInitialPair n))
      V (correctedAlpha cutoff eta) i = fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) cutoff k
          (q := q) (eps := shareEps) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq))
      (slowCanonicalActiveSchedule (by omega : 1 ≤ n) cutoff k
        (q := q) (eps := shareEps) (s0 := slowSourceInitialVariance n)
        (lt_of_lt_of_le (by norm_num) hq4)
        (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
        slowReferenceWarm slack boundSq)
      Prod.snd Prod.fst (slowInitialPair n) V cutoff eta := by
  have hn1 : 1 ≤ n := by omega
  have hq1 : (1 : Real) < q := lt_of_lt_of_le (by norm_num) hq4
  have hs0 : 0 < slowSourceInitialVariance n := by
    unfold slowSourceInitialVariance; positivity
  have hrad : ∀ i, 1 ≤ q *
      Real.sqrt (slowSourceSigmaSq n (slowSourceInitialVariance n) i) * Real.sqrt n :=
    fun i ↦ one_le_slow_radius hn1 hq4 (by rfl) i
  have hwarmOne : (1 : ENNReal) ≤ slowReferenceWarm := by
    unfold slowReferenceWarm
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Real.add_one_le_exp (1 : Real)
    linarith
  have hwarmTop : slowReferenceWarm ≠ ⊤ := by
    unfold slowReferenceWarm; exact ENNReal.ofReal_ne_top
  have hstart : IsWarm slowReferenceWarm (Measure.map Prod.snd (slowInitialPair n))
      (slowRadiusQSeedTarget n q (slowSourceInitialVariance n) K 0) := by
    rw [map_snd_slowInitialPair]
    exact isWarm_slowRetainedSeedTarget (m := cutoff) (by omega : 2 ≤ n) hq4 hK hKc
      hball hcut
  have base := seedProjectedOperational_slowRadiusQ_scoreAware (n := n) hn cutoff k hk
    hq1 hs0 hshare hshare1 hK hKc hball hfin hrad scoreScale hslack hbound
    (slowStationaryTail n q (slowSourceInitialVariance n) K) (slowInitialPair n)
    (fun _ _ ↦ (0 : Real)) slowReferenceWarm hwarmOne hwarmTop hstart
    (map_snd_slowStationaryTail n q (slowSourceInitialVariance n) K)
    (fun i _ ↦ if i = 0 then (1 : Real) else 0) (fun _ _ ↦ (0 : Real))
    (fun _ ↦ measurable_const) (fun _ ↦ measurable_const)
    (fun i ↦ accuracyU_zeroFamily _ _ i) (fun _ ↦ rfl)
  exact
    { measurable_seed := base.measurable_seed
      measurable_score := base.measurable_score
      factor := base.factor
      pi := base.pi
      tau := base.tau
      tau_prob := base.tau_prob
      warmConst := base.warmConst
      mixError := base.mixError
      mixError_ne_top := base.mixError_ne_top
      u := u
      v := v
      measurable_u := hu
      measurable_v := hv
      U_eq := hU
      V_eq := hV
      last_seed_warm := base.last_seed_warm
      distributional_mixing := base.distributional_mixing
      dependence_budget := fun i ↦
        (base.dependence_budget i).trans (correctedNu_mono cutoff hshare hle) }

#print axioms seedProjectedOperational_slowCanonical_split

/-! ## The block stream package -/

/-- The `hop` binder of the slow-canonical robust certificate: the schedule is built
at cutoff `m + 1` with share accuracy `eps / 2`, the estimator at length `m` with
accuracy `eps`. -/
noncomputable def slowCanonicalStreamOperational
    (hn : 21 ≤ n) (m k : Nat) (hk : 1 ≤ k)
    {q eps : Real} (hq4 : 4 ≤ q) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (scoreScale : Real) {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (Vscalar : Nat → (Nat → ScoreSeed n) → Real)
    (uscalar : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (vscalar : Nat → State n → Real)
    (huscalar : ∀ i, Measurable (uscalar i)) (hvscalar : ∀ i, Measurable (vscalar i))
    (hUscalar : ∀ i, accuracyU
      (inhomogeneousPathMeasure (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq)) (slowInitialPair n))
      Vscalar (correctedAlpha (m + 1) eps) i =
        fun omega ↦ uscalar i (Preorder.frestrictLe i omega))
    (hVscalar : ∀ i, Vscalar (i + 1) = fun omega ↦ vscalar i (omega (i + 1)).1)
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → (Fin k → ScoreSeed n) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (independentPathLaw k (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq)) (slowInitialPair n)) V
      (correctedAlpha m eps) i =
        fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1))) :
    IndependentStreamOperational k
      (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq))
      (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
        (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
        (lt_of_lt_of_le (by norm_num) hq4)
        (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
        slowReferenceWarm slack boundSq)
      Prod.snd (slowInitialPair n) V m eps := by
  refine independentStreamOperational_of_seedProjected_atLength
    (seedProjectedOperational_slowCanonical_split hn (m + 1) k (Nat.succ_pos m) hk hq4
      (by linarith) (by linarith) (by linarith) hK hKc hball hfin scoreScale hslack
      hbound Vscalar uscalar vscalar huscalar hvscalar hUscalar hVscalar)
    V u v hu hv hU hV ?_
  intro i
  show (k : Real) * (2 * (activeReferenceMixError (m + 1)
      (activeReferenceMixError (m + 1)
        (scoreAwareMixError (m + 1) k (eps / 2) slack boundSq)) i).toReal) ≤
    correctedNu m eps
  unfold activeReferenceMixError
  by_cases hi : i + 1 < m + 1
  · rw [if_pos hi, if_pos hi]
    exact (scoreAwareMixError_budget (m := m + 1) (k := k) (by linarith) (by linarith)
      hslack hbound i).trans (correctedNu_succ_half_le m heps)
  · rw [if_neg hi]
    simpa using correctedNu_nonneg (m := m) (ε := eps)

#print axioms slowCanonicalStreamOperational

/-- The `htau` discharge: on the estimator range the stream's phase targets are the
canonical local pair references at chain length `m + 1`. -/
theorem tau_slowCanonicalStreamOperational
    (hn : 21 ≤ n) (m k : Nat) (hk : 1 ≤ k)
    {q eps : Real} (hq4 : 4 ≤ q) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (scoreScale : Real) {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (Vscalar : Nat → (Nat → ScoreSeed n) → Real)
    (uscalar : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (vscalar : Nat → State n → Real)
    (huscalar : ∀ i, Measurable (uscalar i)) (hvscalar : ∀ i, Measurable (vscalar i))
    (hUscalar : ∀ i, accuracyU
      (inhomogeneousPathMeasure (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq)) (slowInitialPair n))
      Vscalar (correctedAlpha (m + 1) eps) i =
        fun omega ↦ uscalar i (Preorder.frestrictLe i omega))
    (hVscalar : ∀ i, Vscalar (i + 1) = fun omega ↦ vscalar i (omega (i + 1)).1)
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → (Fin k → ScoreSeed n) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (independentPathLaw k (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq)) (slowInitialPair n)) V
      (correctedAlpha m eps) i =
        fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1))) :
    ∀ i, i < m →
      (slowCanonicalStreamOperational hn m k hk hq4 heps heps1 hK hKc hball hfin
        scoreScale hslack hbound Vscalar uscalar vscalar huscalar hvscalar hUscalar
        hVscalar V u v hu hv hU hV).tau i =
        slowLocalPairReference (m + 1) n q (slowSourceInitialVariance n) K i := by
  intro i hi
  show activeReferenceTarget (m + 1)
      (slowLocalPairReference (m + 1) n q (slowSourceInitialVariance n) K)
      (slowStationaryTail n q (slowSourceInitialVariance n) K) i = _
  unfold activeReferenceTarget
  rw [if_pos (by omega : i + 1 < m + 1)]

#print axioms tau_slowCanonicalStreamOperational

/-- The `hmixError` discharge. -/
theorem mixError_slowCanonicalStreamOperational
    (hn : 21 ≤ n) (m k : Nat) (hk : 1 ≤ k)
    {q eps : Real} (hq4 : 4 ≤ q) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (scoreScale : Real) {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (Vscalar : Nat → (Nat → ScoreSeed n) → Real)
    (uscalar : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (vscalar : Nat → State n → Real)
    (huscalar : ∀ i, Measurable (uscalar i)) (hvscalar : ∀ i, Measurable (vscalar i))
    (hUscalar : ∀ i, accuracyU
      (inhomogeneousPathMeasure (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq)) (slowInitialPair n))
      Vscalar (correctedAlpha (m + 1) eps) i =
        fun omega ↦ uscalar i (Preorder.frestrictLe i omega))
    (hVscalar : ∀ i, Vscalar (i + 1) = fun omega ↦ vscalar i (omega (i + 1)).1)
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → (Fin k → ScoreSeed n) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (independentPathLaw k (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq)) (slowInitialPair n)) V
      (correctedAlpha m eps) i =
        fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1))) :
    ∀ j, (slowCanonicalStreamOperational hn m k hk hq4 heps heps1 hK hKc hball hfin
        scoreScale hslack hbound Vscalar uscalar vscalar huscalar hvscalar hUscalar
        hVscalar V u v hu hv hU hV).mixError j =
      activeReferenceMixError (m + 1)
        (scoreAwareMixError (m + 1) k (eps / 2) slack boundSq) j := by
  intro j
  show activeReferenceMixError (m + 1)
      (activeReferenceMixError (m + 1)
        (scoreAwareMixError (m + 1) k (eps / 2) slack boundSq)) j = _
  unfold activeReferenceMixError
  by_cases hj : j + 1 < m + 1 <;> simp [hj]

#print axioms mixError_slowCanonicalStreamOperational

/-! ## Repackaged in the frontier's `Q`-with-equation form -/

/-- Exactly the `hop` / `htau` / `hmixError` triple of
`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`,
bundled so that the abstract schedule variable `Q` and its defining equation `hQ`
may be used verbatim. -/
theorem exists_slowCanonicalStreamOperational
    (hn : 21 ≤ n) (m k : Nat) (hk : 1 ≤ k)
    {q eps : Real} (hq4 : 4 ≤ q) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (scoreScale : Real) {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (Vscalar : Nat → (Nat → ScoreSeed n) → Real)
    (uscalar : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (vscalar : Nat → State n → Real)
    (huscalar : ∀ i, Measurable (uscalar i)) (hvscalar : ∀ i, Measurable (vscalar i))
    (hUscalar : ∀ i, accuracyU
      (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n))
      Vscalar (correctedAlpha (m + 1) eps) i =
        fun omega ↦ uscalar i (Preorder.frestrictLe i omega))
    (hVscalar : ∀ i, Vscalar (i + 1) = fun omega ↦ vscalar i (omega (i + 1)).1)
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → (Fin k → ScoreSeed n) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)) V
      (correctedAlpha m eps) i =
        fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1))) :
    ∃ hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
        (slowInitialPair n) V m eps,
      (∀ i, i < m → hop.tau i =
        slowLocalPairReference (m + 1) n q (slowSourceInitialVariance n) K i) ∧
      (∀ j, hop.mixError j = activeReferenceMixError (m + 1)
        (scoreAwareMixError (m + 1) k (eps / 2) slack boundSq) j) := by
  subst hQ
  exact ⟨slowCanonicalStreamOperational hn m k hk hq4 heps heps1 hK hKc hball hfin
      scoreScale hslack hbound Vscalar uscalar vscalar huscalar hvscalar hUscalar
      hVscalar V u v hu hv hU hV,
    tau_slowCanonicalStreamOperational hn m k hk hq4 heps heps1 hK hKc hball hfin
      scoreScale hslack hbound Vscalar uscalar vscalar huscalar hvscalar hUscalar
      hVscalar V u v hu hv hU hV,
    mixError_slowCanonicalStreamOperational hn m k hk hq4 heps heps1 hK hKc hball hfin
      scoreScale hslack hbound Vscalar uscalar vscalar huscalar hvscalar hUscalar
      hVscalar V u v hu hv hU hV⟩

#print axioms exists_slowCanonicalStreamOperational

end Ttc.CVSlowCanonicalStreamOperational

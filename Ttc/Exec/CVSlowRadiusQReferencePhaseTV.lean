import Ttc.Exec.CVSlowRadiusQOperationalPair
import Ttc.Exec.CVAdaptiveRadiusQSmallRateWarm
import Ttc.Exec.CVHeterogeneousHistoryReference

/-! Retained seed targets and phase TV for the uniformly slow schedule. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVSlowRadiusQReferencePhaseTV

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVAdaptiveRadiusQCrossWarm
open Ttc.CVAdaptiveRadiusQSmallRateWarm
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowRadiusQFallbackSchedule
open Ttc.CVSlowRadiusQOperationalPair
open Ttc.CVGaussianScoreSeedPhaseKernel
open scoped ENNReal Classical BigOperators

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def slowRadiusQSeedTarget
    (n : Nat) (q s0 : Real) (K : Set (State n)) (i : Nat) : Measure (State n) :=
  ellGaussianProb (radiusQBody q K (slowSourceSigmaSq n s0 i))
    (radiusQDelta n q (slowSourceSigmaSq n s0 i))
    (slowSourceSigmaSq n s0 i)

noncomputable def slowRadiusQLocalGraphSeedTarget
    (m n : Nat) (q s0 : Real) (K : Set (State n)) (i : Nat) : Measure (State n) :=
  Measure.map (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
    (coolLaw m (slowSourceSigmaSq n s0)
      (radiusQBody q K (slowSourceSigmaSq n s0 i)) i)

theorem one_le_slow_radius
    (hn : 1 ≤ n) {q s0 : Real} (hq4 : 4 ≤ q)
    (hs0 : 1 / (16 * (n : Real)) ≤ s0) (i : Nat) :
    1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n := by
  have hs0pos : 0 < s0 := lt_of_lt_of_le (by positivity) hs0
  have hmono : s0 ≤ slowSourceSigmaSq n s0 i := by
    unfold slowSourceSigmaSq Arlib.GaussianCooling.geomSchedule
    have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    have hbase : 1 ≤ 1 + 1 / (n : Real) := by
      have : 0 ≤ 1 / (n : Real) := by positivity
      linarith
    have hp : 1 ≤ (1 + 1 / (n : Real)) ^ i := one_le_pow₀ hbase
    simpa using mul_le_mul_of_nonneg_left hp hs0pos.le
  have hnR : 0 < (n : Real) := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsqrt : 1 / (4 * Real.sqrt n) ≤
      Real.sqrt (slowSourceSigmaSq n s0 i) := by
    have hsq : (1 / (4 * Real.sqrt n)) ^ 2 ≤ slowSourceSigmaSq n s0 i := by
      calc
        (1 / (4 * Real.sqrt n)) ^ 2 = 1 / (16 * (n : Real)) := by
          rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hnR.le]
          ring
        _ ≤ s0 := hs0
        _ ≤ slowSourceSigmaSq n s0 i := hmono
    exact (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp (by
      simpa [Real.sq_sqrt (slowSourceSigmaSq_pos hn hs0pos i).le] using hsq)
  calc
    1 = 4 * (1 / (4 * Real.sqrt n)) * Real.sqrt n := by field_simp
    _ ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n := by gcongr

theorem isProbabilityMeasure_slowRadiusQSeedTarget
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (i : Nat)
    (hrad : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n) :
    IsProbabilityMeasure (slowRadiusQSeedTarget n q s0 K i) := by
  let body := radiusQBody q K (slowSourceSigmaSq n s0 i)
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball
      (by simpa only [body, radiusQBody] using hrad)
  have hbodyTop : volume body ≠ ⊤ := by
    dsimp only [body, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  have hs := slowSourceSigmaSq_pos hn hs0 i
  have hd := radiusQDelta_pos hn hq hs
  have hc0 : 0 < 1 - 1 / (2 * (n : Real)) := by
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : 1 - 1 / (2 * (n : Real)) < 1 := by
    have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hmass0 := ellGaussianMeasure_univ_ne_zero_of_ball
    (measurableSet_radiusQBody hK) (convex_radiusQBody hKc) hbodyBall
    hc0 hc1 hd (by simpa using radiusQDelta_le_n n q (slowSourceSigmaSq n s0 i)) hs
  have hmassTop := ellGaussianMeasure_univ_ne_top hs body
    (radiusQDelta n q (slowSourceSigmaSq n s0 i)) hbodyTop
  exact isProbabilityMeasure_ellGaussianProb hmass0 hmassTop

theorem isProbabilityMeasure_slowRadiusQLocalGraphSeedTarget
    (hn : 1 ≤ n) (m : Nat) {q s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hball : ball (0 : State n) 1 ⊆ K)
    (i : Nat) (hrad : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n) :
    IsProbabilityMeasure (slowRadiusQLocalGraphSeedTarget m n q s0 K i) := by
  let body := radiusQBody q K (slowSourceSigmaSq n s0 i)
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball
      (by simpa only [body, radiusQBody] using hrad)
  have hbodyTop : volume body ≠ ⊤ := by
    dsimp only [body, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  letI : IsProbabilityMeasure (coolLaw m (slowSourceSigmaSq n s0) body i) :=
    coolLaw_isProbabilityMeasure (slowSourceSigmaSq_pos hn hs0) hbodyBall hbodyTop i
  unfold slowRadiusQLocalGraphSeedTarget
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Every retained accepted seed is `2e`-warm for the following slow phase. -/
theorem isWarm_slowRadiusQLocalGraphSeedTarget_succ_two_exp
    (hn : 1 ≤ n) {m : Nat} {q s0 : Real} (hq : 0 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n) :
    IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (slowRadiusQLocalGraphSeedTarget m n q s0 K i)
      (slowRadiusQSeedTarget n q s0 K (i + 1)) := by
  have hraw := isWarm_standardScaledTruncated_ellGaussianProb_radiusQ_ratio
    (m := m) hn hq (slowSourceSigmaSq_pos hn hs0) hK hKc hball hi
    (show 1 ≤ 1 + 1 / (n : Real) by
      have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
      have : 0 ≤ 1 / (n : Real) := by positivity
      linarith)
    (by simpa [mul_comm] using slowSourceSigmaSq_succ n s0 i)
    hrad
    (radiusQDelta_pos hn hq (slowSourceSigmaSq_pos hn hs0 (i + 1)))
    (radiusQDelta_le_n n q _)
  exact hraw.mono (adaptiveRadiusQWarmFactor_one_add_le_two_exp hn
    (by positivity) le_rfl)

/-- Cost-erased seed form of the local graph-law phase theorem. -/
theorem tvLe_bind_radiusQWarmFallbackCostedKernelOfSigma_nextSeed
    (hn : 21 ≤ n) {q : Real} (hq : 1 < q)
    (sigmaSq : Nat → Real) (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    (i : Nat) (hi : i < m) (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb (radiusQBody q K (sigmaSq i))
        (radiusQDelta n q (sigmaSq i)) (sigmaSq i)))
    (L : Nat)
    (hsteps : steps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (radiusQDelta n q (sigmaSq i)) (sigmaSq i) (M / eta) zeta)
    (hretries : retries i = L) :
    TVLe
      (rho.bind (Kernel.map
        (radiusQWarmFallbackCostedKernelOfSigma (by omega : 1 ≤ n) q
          (zero_lt_one.trans hq) K hK sigmaSq hsigma steps retries fallback i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      (Measure.map (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq (radiusQBody q K (sigmaSq i)) i))
      (32 * zeta + (eta + Ttc.CVContinuingRetryParameters.continuingContraction ^ L)) := by
  have hpair :=
    tvLe_radiusQWarmFallbackKernelOfSigma_localPair_adjustable_zeroSafe_of_eq
      hn hq sigmaSq hsigma hK hKc hball steps retries fallback i hi rho
      hM1 hMtop heta0 hetatop heta1 hzeta0 hzetatop hzeta16 hrad hwarm
      L hsteps hretries
  have hseed := hpair.map measurable_snd
  rw [map_snd_scoreSeedReference] at hseed
  have herase : ∀ x : State n,
      Measure.map (fun y : ENNReal × ScoreSeed n ↦ y.2.2)
          (radiusQWarmFallbackCostedKernelOfSigma (by omega : 1 ≤ n) q
            (zero_lt_one.trans hq) K hK sigmaSq hsigma steps retries fallback i x) =
        Measure.map Prod.snd
          (radiusQWarmFallbackKernelOfSigma (by omega : 1 ≤ n) q
            (zero_lt_one.trans hq) K hK sigmaSq hsigma steps retries fallback i x) := by
    intro x
    have h := congrArg (Measure.map Prod.snd)
      (map_snd_radiusQWarmFallbackCostedKernelOfSigma (by omega : 1 ≤ n) q
        (zero_lt_one.trans hq) K hK sigmaSq hsigma steps retries fallback i x)
    rw [Measure.map_map measurable_snd measurable_snd] at h
    simpa only [Function.comp_def] using h
  have hleft :
      rho.bind (Kernel.map
        (radiusQWarmFallbackCostedKernelOfSigma (by omega : 1 ≤ n) q
          (zero_lt_one.trans hq) K hK sigmaSq hsigma steps retries fallback i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)) =
      Measure.map Prod.snd
        (sampleFromKernel
          (radiusQWarmFallbackKernelOfSigma (by omega : 1 ≤ n) q
            (zero_lt_one.trans hq) K hK sigmaSq hsigma steps retries fallback i) rho) := by
    unfold sampleFromKernel
    ext S hS
    rw [Measure.bind_apply hS (Kernel.aemeasurable _),
      Measure.map_apply measurable_snd hS,
      Measure.bind_apply (hS.preimage measurable_snd) (Kernel.aemeasurable _)]
    apply lintegral_congr
    intro x
    rw [Kernel.map_apply _ (by fun_prop), ← Measure.map_apply measurable_snd hS,
      herase x, Measure.map_apply measurable_snd hS]
  rw [hleft]
  exact hseed

#print axioms isWarm_slowRadiusQLocalGraphSeedTarget_succ_two_exp
#print axioms tvLe_bind_radiusQWarmFallbackCostedKernelOfSigma_nextSeed

end Ttc.CVSlowRadiusQReferencePhaseTV

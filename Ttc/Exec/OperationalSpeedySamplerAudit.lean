import Ttc.Exec.SpeedySamplerChain
import Ttc.Exec.LazyProperProposalCost
import Ttc.Exec.RawBallWalkQueryCost
import Ttc.Exec.KV97RoundedEndpointBridge
import Arlib.MarkovChains.Continuous.LambdaFromShrunken

/-!
# Operational audit of the polynomial speedy uniform sampler

The unconditional speedy sampler has a polynomial number of *abstract speedy-kernel*
steps.  This file connects its uniform (`s = 0`) kernel to the existing cost-recording
proper-proposal execution.  The connection is exact at the level of laws.

The resulting expected-query estimate retains the warmness multiplier `M`.  For the
single-inball start used by the unconditional theorem, the available value is
`M = (1 + D)^(2n)`.  Thus this operational bridge does not turn the polynomial abstract
step bound into a polynomial membership-query bound.  This is the first semantic mismatch
between `SamplerCost.drawOpCharge` and an actual query trace; no theorem here claims that
the arithmetic charge measures the execution below.
-/

namespace Ttc.OperationalSpeedySamplerAudit

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.LazyProperCost
open scoped ENNReal BigOperators Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- At zero variance the speedy Gaussian move mass is exactly the indicator of being a
non-stuck speedy-walk state. -/
theorem speedyMetropolisMove_variance_zero
    (K : Set (State n)) (delta : Real) (x : State n) :
    speedyMetropolisMove K delta 0 x =
      (StuckPoints K delta).indicator (fun _ => (0 : ENNReal)) x +
        (StuckPoints K delta)ᶜ.indicator (fun _ => (1 : ENNReal)) x := by
  rw [speedyMetropolisMove_apply]
  simp_rw [Ttc.RawBallWalkQueryCost.metropolisDensity_variance_zero]
  rw [setLIntegral_indicator measurableSet_ball]
  simp only [Pi.one_apply, setLIntegral_one]
  by_cases hx : x ∈ StuckPoints K delta
  · have hxc : x ∉ (StuckPoints K delta)ᶜ := by simp [hx]
    rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hxc,
      mem_stuckPoints_iff.1 hx]
    simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (Set.mem_compl hx), zero_add]
    exact ENNReal.div_self
      (fun h => hx (mem_stuckPoints_iff.2 h))
      (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left))

/-- At zero variance, the speedy Metropolis-Gaussian kernel is literally the speedy
uniform-walk kernel. -/
theorem speedyMetropolisGaussian_variance_zero_eq_speedyWalk
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) :
    speedyMetropolisGaussian K delta 0 = speedyWalk K delta := by
  ext x A hA
  rw [speedyMetropolisGaussian_apply_set hK delta 0 x hA,
    speedyWalk_apply_set hK delta x hA]
  simp_rw [Ttc.RawBallWalkQueryCost.metropolisDensity_variance_zero]
  rw [setLIntegral_indicator measurableSet_ball]
  simp only [Pi.one_apply, setLIntegral_one]
  have hinter : ball x delta ∩ (A ∩ K) = A ∩ (ball x delta ∩ K) := by
    ext y
    simp only [Set.mem_inter_iff]
    tauto
  rw [hinter, speedyMetropolisMove_variance_zero]
  by_cases hx : x ∈ StuckPoints K delta
  · have hxc : x ∉ (StuckPoints K delta)ᶜ := by simp [hx]
    rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hxc]
    simp [hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (Set.mem_compl hx)]
    simp [hx]

/-- Cost-recording execution of `t` lazy speedy uniform-walk steps. -/
noncomputable def costedLazySpeedyEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real)
    (mu : Measure (State n)) (t : Nat) : Measure (ENNReal × State n) :=
  Measure.map
    (fun omega => (Ttc.SequentialCost.totalCost t omega, (omega t).2))
    (lazyProperExecution K hK delta 0 mu)

theorem measurable_costedLazySpeedyEndpointMap (t : Nat) :
    Measurable (fun omega : Nat → ENNReal × State n =>
      (Ttc.SequentialCost.totalCost t omega, (omega t).2)) :=
  (Ttc.SequentialCost.measurable_totalCost t).prodMk
    (measurable_snd.comp (measurable_pi_apply t))

instance isProbabilityMeasure_costedLazySpeedyEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    IsProbabilityMeasure (costedLazySpeedyEndpointLaw hK delta mu t) := by
  unfold costedLazySpeedyEndpointLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_costedLazySpeedyEndpointMap t).aemeasurable

/-- Forgetting costs gives exactly the lazy speedy uniform-walk iterate used by the
unconditional mixing theorem. -/
theorem map_snd_costedLazySpeedyEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    Measure.map Prod.snd (costedLazySpeedyEndpointLaw hK delta mu t) =
      iterate (lazy (speedyWalk K delta)) mu t := by
  rw [costedLazySpeedyEndpointLaw,
    Measure.map_map measurable_snd (measurable_costedLazySpeedyEndpointMap t)]
  change Measure.map (fun omega => (omega t).2)
      (lazyProperExecution K hK delta 0 mu) = _
  rw [map_lazyProperExecution_output hK delta 0 mu t,
    speedyMetropolisGaussian_variance_zero_eq_speedyWalk hK delta]

/-- The actual expected membership-query trace is controlled by the same exit-time sum
that appears in the wasted-step analysis. -/
theorem lintegral_fst_costedLazySpeedyEndpointLaw_le_exitMeanSum
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    (∫⁻ z, z.1 ∂costedLazySpeedyEndpointLaw hK delta mu t) ≤
      (2 : ENNReal)⁻¹ * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x)⁻¹
          ∂iterate (lazy (speedyWalk K delta)) mu i := by
  rw [costedLazySpeedyEndpointLaw,
    lintegral_map measurable_fst (measurable_costedLazySpeedyEndpointMap t)]
  have h := lintegral_lazyProperTotalCost_le_half_exitMeanSum hK delta 0 mu t
  rw [speedyMetropolisGaussian_variance_zero_eq_speedyWalk hK delta] at h
  refine h.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply lintegral_congr
  intro x
  rw [speedyMetropolisMove_variance_zero]
  by_cases hx : x ∈ StuckPoints K delta
  · have hxc : x ∉ (StuckPoints K delta)ᶜ := by simp [hx]
    rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hxc]
    have hell : ell K delta x = 0 := by
      rw [ell_apply, mem_stuckPoints_iff.1 hx]
      simp
    simp [hell]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (Set.mem_compl hx)]
    simp

/-- The strongest currently available direct operational estimate.  Its right-hand side
contains the warmness multiplier `M`, unlike the abstract speedy mixing deadline, which
contains only `log M`. -/
theorem lintegral_fst_costedLazySpeedyEndpointLaw_le_warm
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {M : ENNReal} {mu : Measure (State n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellProb K delta)) (t : Nat) :
    (∫⁻ z, z.1 ∂costedLazySpeedyEndpointLaw hK delta mu t) ≤
      (t : ENNReal) * M := by
  let P := lazy (speedyWalk K delta)
  let pi := ellProb K delta
  let f : State n → ENNReal := fun x => (ell K delta x)⁻¹
  let sumCost : ENNReal := ∑ i ∈ Finset.range t, ∫⁻ x, f x ∂iterate P mu i
  have hcost := lintegral_fst_costedLazySpeedyEndpointLaw_le_exitMeanSum
    hK delta mu t
  have hinv : Kernel.Invariant P pi :=
    (isReversible_lazy (isReversible_speedyWalk_prob hK delta)).invariant
  have hsum : sumCost ≤ (t : ENNReal) * (M * ∫⁻ x, f x ∂pi) :=
    sum_lintegral_iterate_le_of_isWarm hwarm (step_invariant hinv) f t
  have hlam := half_le_avgLocalConductance hn hK hKc hball hdelta hdeltan hK0 hKtop
  have havg : (2 : ENNReal)⁻¹ * (∫⁻ x, f x ∂pi) ≤ 1 := by
    have h := mul_lintegral_inv_ell_ellProb_le_one_of_le_avg
      hK hdelta hK0 hKtop hlam
    rw [show ENNReal.ofReal (1 / 2 : Real) = (2 : ENNReal)⁻¹ by
      rw [show (1 : Real) / 2 = ((2 : ENNReal)⁻¹).toReal by simp]
      exact ENNReal.ofReal_toReal (by simp)] at h
    exact h
  calc
    (∫⁻ z, z.1 ∂costedLazySpeedyEndpointLaw hK delta mu t)
        ≤ (2 : ENNReal)⁻¹ * sumCost := by
          simpa only [sumCost, f, P] using hcost
    _ ≤ (2 : ENNReal)⁻¹ * ((t : ENNReal) * (M * ∫⁻ x, f x ∂pi)) := by gcongr
    _ = ((t : ENNReal) * M) * ((2 : ENNReal)⁻¹ * ∫⁻ x, f x ∂pi) := by ring
    _ ≤ ((t : ENNReal) * M) * 1 := by gcongr
    _ = (t : ENNReal) * M := mul_one _

/-- Concrete specialization to the unconditional sampler's samplable unit-ball start.
The factor that prevents a polynomial recorded-query conclusion is now visible in the
conclusion as `(1 + D)^(2*n)`. -/
theorem lintegral_fst_costedLazySpeedyEndpointLaw_unitBallStart_le
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {D delta : Real} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hdelta : 0 < delta) (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (t : Nat) :
    (∫⁻ z, z.1 ∂costedLazySpeedyEndpointLaw hK delta
      (Arlib.uniformOn volume (ball (0 : State n) 1)) t) ≤
      (t : ENNReal) * ENNReal.ofReal ((1 + D) ^ (2 * n)) := by
  let mu : Measure (State n) := Arlib.uniformOn volume (ball (0 : State n) 1)
  haveI : IsProbabilityMeasure mu := Arlib.isProbabilityMeasure_uniformOn volume
    volume_unitBall_ne_zero volume_unitBall_ne_top
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn1
  have h0K : (0 : State n) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hD0 : (0 : Real) ≤ D := by simpa using hD 0 h0K 0 h0K
  have hKR : ∀ x ∈ K, ‖x‖ ≤ D := by
    intro x hx
    simpa using hD x hx 0 h0K
  have hK0 : volume K ≠ 0 :=
    Arlib.MarkovChains.volume_ne_zero_of_ball_subset one_pos hball
  have hKtop : volume K ≠ ⊤ :=
    Arlib.MarkovChains.volume_ne_top_of_diam_bound h0K hD
  have hdelta1 : delta ≤ 1 := by
    calc
      delta ≤ 1 / (2 * (n : Real)) := hdeltan
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
  have hc : 1 ≤ (1 + D) ^ n := one_le_pow₀ (by linarith)
  have hwarm0 := isWarm_uniformOn_unitBall_ellProb hKc hball hD hc
    (volume_le_one_add_pow_mul_volume_unitBall hD0 hKR) hdelta hdelta1
  have hpow : (1 + D) ^ n * (1 + D) ^ n = (1 + D) ^ (2 * n) := by
    rw [two_mul, pow_add]
  rw [hpow] at hwarm0
  change (∫⁻ z, z.1 ∂costedLazySpeedyEndpointLaw hK delta mu t) ≤ _
  exact lintegral_fst_costedLazySpeedyEndpointLaw_le_warm hn1 hK hKc hball
    hdelta hdeltan hK0 hKtop hwarm0 t

/-- End-to-end continuous sampler audit at the exact polynomial speedy deadline: the
recorded execution has the desired TV law, but its proved query bound contains the
exponential single-inball warm factor. -/
theorem operational_speedyWalk_mixes_and_queryCost_unitBallStart
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {D rho : Real} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    let t := Ttc.speedyMixSteps n D rho
    let xi := costedLazySpeedyEndpointLaw hK (rho / (4 * (n : Real)))
      (Arlib.uniformOn volume (ball (0 : State n) 1)) t
    TVLe (Measure.map Prod.snd xi) (Arlib.uniformOn volume K) (ENNReal.ofReal rho) ∧
      (∫⁻ z, z.1 ∂xi) ≤
        (t : ENNReal) * ENNReal.ofReal ((1 + D) ^ (2 * n)) := by
  let t := Ttc.speedyMixSteps n D rho
  let mu : Measure (State n) := Arlib.uniformOn volume (ball (0 : State n) 1)
  haveI : IsProbabilityMeasure mu := Arlib.isProbabilityMeasure_uniformOn volume
    volume_unitBall_ne_zero volume_unitBall_ne_top
  have hdelta : 0 < rho / (4 * (n : Real)) := by
    have : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hdeltan : rho / (4 * (n : Real)) ≤ 1 / (2 * (n : Real)) := by
    have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    have heq : 1 / (2 * (n : Real)) = 2 / (4 * (n : Real)) := by
      field_simp
      norm_num
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  constructor
  · rw [map_snd_costedLazySpeedyEndpointLaw]
    have ht : Ttc.speedyMixSteps n (D / 1) rho ≤ t := by simp [t]
    simpa only [one_mul, div_one] using
      (Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_uncond hn hK hKc
        (cen := (0 : State n)) (γ := 1) one_pos hball hD hrho0 hrho1
        (m := t) ht)
  · exact lintegral_fst_costedLazySpeedyEndpointLaw_unitBallStart_le
      hn hK hKc hball hD hdelta hdeltan t

section Rounded

variable {A : Type*} {Dnf : Ttc.DNF A}

/-- The actual cost-traced speedy endpoint followed by the actual costed KV97
rounding/rejection bridge, packaged at the exact measure-valued TTC sampler law. -/
noncomputable def operationalExpectedQueryKV97Sampler
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat)
    (body : A → Set (State n)) (rho : Int)
    (law : {c : Ttc.Cube A // c ∈ Dnf} → Measure (State n))
    (i : {c : Ttc.Cube A // c ∈ Dnf})
    (hmarg : iterate (lazy (speedyWalk K delta)) mu t = law i)
    (hpos : 0 < Ttc.CostedKV97Rounding.roundedMeasure
      (law i) (Ttc.KV97RoundedEndpointBridge.integerAcceptance body rho i.val)) :
    Ttc.KV97RoundedEndpointBridge.ExpectedQueryFineSampler
      (Ttc.KV97RoundedEndpointBridge.kv97SampMeasure body rho law i) :=
  Ttc.KV97RoundedEndpointBridge.expectedQueryKV97Sampler
    (costedLazySpeedyEndpointLaw hK delta mu t) body rho law i
    ((map_snd_costedLazySpeedyEndpointLaw hK delta mu t).trans hmarg) hpos

/-- Honest query bound for the packaged sampler.  The KV97 acceptance overhead is a
constant, but the speedy execution still costs `t * M`; this is the unresolved
exponential factor for the currently available single-inball warm start. -/
theorem lintegral_operationalExpectedQueryKV97Sampler_le_warm
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {M : ENNReal} {mu : Measure (State n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellProb K delta)) (t : Nat)
    (body : A → Set (State n)) (rho : Int)
    (law : {c : Ttc.Cube A // c ∈ Dnf} → Measure (State n))
    (i : {c : Ttc.Cube A // c ∈ Dnf})
    (hmarg : iterate (lazy (speedyWalk K delta)) mu t = law i)
    (haccept : ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (law i) (Ttc.KV97RoundedEndpointBridge.integerAcceptance body rho i.val)) :
    (∫⁻ z, z.1 ∂Ttc.KV97RoundedEndpointBridge.costedFineEndpointLaw
      (costedLazySpeedyEndpointLaw hK delta mu t) body rho i.val) ≤
      (ENNReal.ofReal ((1 : Real) / 8))⁻¹ * ((t : ENNReal) * M + 1) := by
  apply Ttc.KV97RoundedEndpointBridge.lintegral_fst_costedFineEndpointLaw_le
  · rw [map_snd_costedLazySpeedyEndpointLaw hK delta mu t, hmarg]
    exact haccept
  · exact lintegral_fst_costedLazySpeedyEndpointLaw_le_warm
      hn hK hKc hball hdelta hdeltan hK0 hKtop hwarm t

end Rounded

#print axioms speedyMetropolisMove_variance_zero
#print axioms speedyMetropolisGaussian_variance_zero_eq_speedyWalk
#print axioms map_snd_costedLazySpeedyEndpointLaw
#print axioms lintegral_fst_costedLazySpeedyEndpointLaw_le_exitMeanSum
#print axioms lintegral_fst_costedLazySpeedyEndpointLaw_le_warm
#print axioms lintegral_fst_costedLazySpeedyEndpointLaw_unitBallStart_le
#print axioms operational_speedyWalk_mixes_and_queryCost_unitBallStart
#print axioms operationalExpectedQueryKV97Sampler
#print axioms lintegral_operationalExpectedQueryKV97Sampler_le_warm

end Ttc.OperationalSpeedySamplerAudit

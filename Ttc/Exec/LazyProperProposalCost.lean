/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.SequentialCostedKernel
import Arlib.MarkovChains.Continuous.ProperProposalCostedRestart

/-!
# Costed lazy proper-proposal Gaussian steps

The lazy speedy Gaussian walk flips a fair coin: on one branch it stays put, and on the
other it runs the independently restarted proper-proposal experiment.  This file attaches
the already-proved proposal count to that coin mixture and composes homogeneous lazy steps
with `Ttc.SequentialCost`.

The cost counts ordinary Gaussian proposals.  Interpreting every proposal as exactly one
membership query still requires the eventual executable membership-test semantics.
-/

namespace Ttc.LazyProperCost

open MeasureTheory ProbabilityTheory Function Set
open Arlib
open Arlib.MarkovChains
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- Fair coin mixture of a costed step and a zero-cost hold. -/
noncomputable def lazyCostedKernel (Q : Kernel S (ENNReal × S)) :
    Kernel S (ENNReal × S) where
  toFun x := ((2 : ENNReal)⁻¹ • Q x) +
    ((2 : ENNReal)⁻¹ • Measure.dirac (0, x))
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have hrw : ∀ x : S,
        ((((2 : ENNReal)⁻¹ • Q x) +
          ((2 : ENNReal)⁻¹ • Measure.dirac (0, x))) :
            Measure (ENNReal × S)) A =
          (2 : ENNReal)⁻¹ * Q x A +
            (2 : ENNReal)⁻¹ * A.indicator 1 (0, x) := by
      intro x
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
        smul_eq_mul, Measure.dirac_apply' _ hA]
    simp_rw [hrw]
    exact ((Kernel.measurable_coe Q hA).const_mul _).add
      (((measurable_one.indicator hA).comp
        (measurable_const.prodMk measurable_id)).const_mul _)

theorem lazyCostedKernel_apply (Q : Kernel S (ENNReal × S)) (x : S) :
    lazyCostedKernel Q x = ((2 : ENNReal)⁻¹ • Q x) +
      ((2 : ENNReal)⁻¹ • Measure.dirac (0, x)) := rfl

instance (Q : Kernel S (ENNReal × S)) [IsMarkovKernel Q] :
    IsMarkovKernel (lazyCostedKernel Q) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [lazyCostedKernel_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, measure_univ,
    Measure.dirac_apply' _ MeasurableSet.univ]
  simp only [Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- Forgetting costs turns the fair costed mixture into the ordinary lazy kernel. -/
theorem map_snd_lazyCostedKernel
    (Q : Kernel S (ENNReal × S)) [IsMarkovKernel Q]
    (P : Kernel S S) [IsMarkovKernel P]
    (hforget : ∀ x, Measure.map Prod.snd (Q x) = P x) (x : S) :
    Measure.map Prod.snd (lazyCostedKernel Q x) = lazy P x := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA, lazyCostedKernel_apply,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    lazy_apply_set P x hA]
  have hQ : Q x (Prod.snd ⁻¹' A) = P x A := by
    rw [← Measure.map_apply measurable_snd hA, hforget]
  rw [hQ, Measure.dirac_apply' _ (hA.preimage measurable_snd)]
  rfl

/-- Laziness halves the expected cost of one costed experiment. -/
theorem lintegral_fst_lazyCostedKernel
    (Q : Kernel S (ENNReal × S)) [IsMarkovKernel Q] (x : S) :
    ∫⁻ y, y.1 ∂lazyCostedKernel Q x =
      (2 : ENNReal)⁻¹ * ∫⁻ y, y.1 ∂Q x := by
  rw [lazyCostedKernel_apply, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac' (0, x) measurable_fst]
  simp

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- One lazy speedy Gaussian step carrying the realized ordinary-proposal count. -/
noncomputable def lazyProperProposalCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) :
    Kernel (State n) (ENNReal × State n) :=
  lazyCostedKernel (properProposalCostedKernel K hK delta s)

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) :
    IsMarkovKernel (lazyProperProposalCostedKernel K hK delta s) := by
  unfold lazyProperProposalCostedKernel
  infer_instance

/-- The cost-forgetting law is exactly the lazy speedy Metropolis--Gaussian kernel. -/
theorem map_snd_lazyProperProposalCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (x : State n) :
    Measure.map Prod.snd (lazyProperProposalCostedKernel K hK delta s x) =
      lazy (speedyMetropolisGaussian K delta s) x := by
  exact map_snd_lazyCostedKernel _ _
    (map_snd_properProposalCostedKernel_eq_speedy hK delta s) x

/-- The conditional mean proposal count of one lazy step is at most half the Gaussian
exit-time integrand. -/
theorem lintegral_fst_lazyProperProposalCostedKernel_le
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (x : State n) :
    ∫⁻ y, y.1 ∂lazyProperProposalCostedKernel K hK delta s x ≤
      (2 : ENNReal)⁻¹ * (ell K delta x * speedyMetropolisMove K delta s x)⁻¹ := by
  rw [lazyProperProposalCostedKernel, lintegral_fst_lazyCostedKernel]
  gcongr
  exact lintegral_fst_properProposalCostedKernel_le_exitMean hK delta s x

/-! ## Homogeneous sequential execution -/

/-- The constant schedule used to run `t` lazy proper-proposal steps. -/
noncomputable def lazyProperSchedule
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) :
    Nat -> Kernel (State n) (ENNReal × State n) :=
  fun _ => lazyProperProposalCostedKernel K hK delta s

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (i : Nat) :
    IsMarkovKernel (lazyProperSchedule K hK delta s i) := by
  unfold lazyProperSchedule
  infer_instance

/-- Ionescu--Tulcea execution of the homogeneous lazy costed walk. -/
noncomputable def lazyProperExecution
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (mu : Measure (State n)) : Measure (Nat -> ENNReal × State n) :=
  Ttc.SequentialCost.execution (lazyProperSchedule K hK delta s) mu

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (lazyProperExecution K hK delta s mu) := by
  unfold lazyProperExecution
  infer_instance

/-- After `t` costed lazy steps, the state output has exactly the usual lazy iterate law. -/
theorem map_lazyProperExecution_output
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    Measure.map (fun omega => (omega t).2) (lazyProperExecution K hK delta s mu) =
      iterate (lazy (speedyMetropolisGaussian K delta s)) mu t := by
  induction t with
  | zero =>
      exact Ttc.SequentialCost.map_execution_output_zero
        (lazyProperSchedule K hK delta s) mu
  | succ t ih =>
      change Measure.map (fun omega => (omega (t + 1)).2)
          (Ttc.SequentialCost.execution (lazyProperSchedule K hK delta s) mu) = _
      rw [Ttc.SequentialCost.map_execution_output_succ
          (lazyProperSchedule K hK delta s)
          (fun _ => lazy (speedyMetropolisGaussian K delta s))
          (fun i x => map_snd_lazyProperProposalCostedKernel hK delta s x)]
      rw [show Measure.map (fun omega => (omega t).2)
          (Ttc.SequentialCost.execution (lazyProperSchedule K hK delta s) mu) =
            iterate (lazy (speedyMetropolisGaussian K delta s)) mu t by
        simpa only [lazyProperExecution] using ih]
      rfl

/-- Expected realized proposal count is bounded by half the exit-time means along the
actual lazy-chain marginals. -/
theorem lintegral_lazyProperTotalCost_le_half_exitMeanSum
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    ∫⁻ omega, Ttc.SequentialCost.totalCost t omega
        ∂lazyProperExecution K hK delta s mu ≤
      (2 : ENNReal)⁻¹ * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x * speedyMetropolisMove K delta s x)⁻¹
          ∂iterate (lazy (speedyMetropolisGaussian K delta s)) mu i := by
  rw [lazyProperExecution,
    Ttc.SequentialCost.lintegral_totalCost_eq_sum_stateMeans]
  calc
    (∑ i ∈ Finset.range t,
        ∫⁻ x, Ttc.SequentialCost.stepMean (lazyProperSchedule K hK delta s) i x
          ∂Measure.map (fun omega => (omega i).2)
            (Ttc.SequentialCost.execution (lazyProperSchedule K hK delta s) mu))
      ≤ ∑ i ∈ Finset.range t,
          ∫⁻ x, (2 : ENNReal)⁻¹ *
              (ell K delta x * speedyMetropolisMove K delta s x)⁻¹
            ∂iterate (lazy (speedyMetropolisGaussian K delta s)) mu i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← map_lazyProperExecution_output hK delta s mu i]
        apply lintegral_mono
        exact lintegral_fst_lazyProperProposalCostedKernel_le hK delta s
    _ = (2 : ENNReal)⁻¹ * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x * speedyMetropolisMove K delta s x)⁻¹
          ∂iterate (lazy (speedyMetropolisGaussian K delta s)) mu i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_const_mul (2 : ENNReal)⁻¹
        (((measurable_ell hK delta).mul
          (measurable_speedyMetropolisMove hK delta s)).inv)

/-- Radius-four expected proposal-count bound for the honest lazy costed execution.

Compared with the non-lazy `10/3` bound, the fair lazy coin contributes the factor `1/2`:
the multiplicative statement is `6 * E[cost] <= 10 * t * M`.  The state marginals here are
the actual lazy iterates.  Their `M`-warmness follows from invariance of the lazy kernel, so
the radius-four stationary estimate can be applied without replacing lazy iterates by
non-lazy ones. -/
theorem six_mul_lintegral_lazyProperTotalCost_le_ten_mul_radius_four
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : Metric.ball (0 : State n) 1 ⊆ K)
    {delta sigma R : Real} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltasigma : delta ≤ sigma / (8 * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ 4 * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {M : ENNReal} {mu : Measure (State n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2))) (t : Nat) :
    6 * (∫⁻ omega, Ttc.SequentialCost.totalCost t omega
        ∂lazyProperExecution K hK delta (sigma ^ 2) mu) ≤
      10 * ((t : ENNReal) * M) := by
  let P := lazy (speedyMetropolisGaussian K delta (sigma ^ 2))
  let pi := ellGaussianProb K delta (sigma ^ 2)
  let f : State n -> ENNReal :=
    fun x => (ell K delta x * speedyMetropolisMove K delta (sigma ^ 2) x)⁻¹
  let sumCost : ENNReal := ∑ i ∈ Finset.range t, ∫⁻ x, f x ∂iterate P mu i
  have hcost := lintegral_lazyProperTotalCost_le_half_exitMeanSum
    hK delta (sigma ^ 2) mu t
  have hinv : Kernel.Invariant P pi := by
    exact (isReversible_lazy
      (isReversible_speedyMetropolisGaussian_prob hK delta (sigma ^ 2))).invariant
  have hsum : sumCost ≤ (t : ENNReal) * (M * ∫⁻ x, f x ∂pi) := by
    exact sum_lintegral_iterate_le_of_isWarm hwarm (step_invariant hinv) f t
  have hstationary : 3 * (∫⁻ x, f x ∂pi) ≤ 10 := by
    have h := three_mul_sum_lintegral_le_ten_mul_radius_four hn hK hKc hball
      hdelta hsigma hdeltan hdeltasigma hR hRsigma hKR
      (M := (1 : ENNReal)) (Q₀ := pi) (IsWarm.refl pi) 1
    simpa only [f, pi, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Arlib.MarkovChains.iterate_zero, Nat.cast_one, one_mul, mul_one] using h
  have hsixhalf : (6 : ENNReal) * (2 : ENNReal)⁻¹ = 3 := by
    rw [show (6 : ENNReal) = ENNReal.ofReal 6 by norm_num,
      show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 6)]
    norm_num
  calc
    6 * (∫⁻ omega, Ttc.SequentialCost.totalCost t omega
        ∂lazyProperExecution K hK delta (sigma ^ 2) mu)
      ≤ 6 * ((2 : ENNReal)⁻¹ * sumCost) := by
        exact mul_le_mul_right (by simpa only [sumCost, f, P] using hcost) 6
    _ = 3 * sumCost := by rw [← mul_assoc, hsixhalf]
    _ ≤ 3 * ((t : ENNReal) * (M * ∫⁻ x, f x ∂pi)) := by gcongr
    _ = ((t : ENNReal) * M) * (3 * ∫⁻ x, f x ∂pi) := by ring
    _ ≤ ((t : ENNReal) * M) * 10 := by gcongr
    _ = 10 * ((t : ENNReal) * M) := by ring

/-! ### Axiom audit -/

#print axioms map_snd_lazyProperProposalCostedKernel
#print axioms map_lazyProperExecution_output
#print axioms six_mul_lintegral_lazyProperTotalCost_le_ten_mul_radius_four

end Ttc.LazyProperCost

import Kr25Ssmxt.Analysis.FairThinningExpectation
import Kr25Ssmxt.Analysis.CostedMeasureMonad
import Mathlib.Probability.Distributions.Poisson.Basic

/-! The first moment of the Poisson count used by manuscript TTC. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

private theorem poisson_weight_succ (r : NNReal) (n : Nat) :
    (n + 1 : Real) * (Real.exp (-(r : Real)) * (r : Real) ^ (n + 1) /
      (n + 1).factorial) =
    (r : Real) * (Real.exp (-(r : Real)) * (r : Real) ^ n / n.factorial) := by
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hn : (n + 1 : Real) ≠ 0 := by positivity
  have hf : (n.factorial : Real) ≠ 0 := by positivity
  field_simp

private theorem poisson_weight_summable (r : NNReal) :
    Summable (fun n : Nat => (n : Real) *
      (Real.exp (-(r : Real)) * (r : Real) ^ n / n.factorial)) := by
  let w : Nat → Real := fun n => (n : Real) *
    (Real.exp (-(r : Real)) * (r : Real) ^ n / n.factorial)
  have hshift : Summable (fun n => w (n + 1)) := by
    have h : (fun n => w (n + 1)) = fun n =>
        (r : Real) * (Real.exp (-(r : Real)) * (r : Real) ^ n / n.factorial) := by
      funext n
      simpa only [w, Nat.cast_add, Nat.cast_one] using poisson_weight_succ r n
    rw [h]
    exact (hasSum_one_poissonMeasure r).summable.mul_left _
  exact (summable_nat_add_iff 1).1 hshift

theorem poissonMeasure_integral_count (r : NNReal) :
    ∫ n : Nat, (n : Real) ∂poissonMeasure r = (r : Real) := by
  let w : Nat → Real := fun n => (n : Real) *
    (Real.exp (-(r : Real)) * (r : Real) ^ n / n.factorial)
  have hw : Summable w := poisson_weight_summable r
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  have hfun : (fun n : Nat =>
      (Real.exp (-(r : Real)) * (r : Real) ^ n / n.factorial) * (n : Real)) = w := by
    funext n
    dsimp [w]
    ring
  rw [hfun]
  rw [← hw.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, w, Nat.cast_zero, zero_mul, zero_add]
  have h : (fun n : Nat => ((n + 1 : Nat) : Real) *
      (Real.exp (-(r : Real)) * (r : Real) ^ (n + 1) / (n + 1).factorial)) =
      fun n => (r : Real) *
        (Real.exp (-(r : Real)) * (r : Real) ^ n / n.factorial) := by
    funext n
    simpa only [Nat.cast_add, Nat.cast_one] using poisson_weight_succ r n
  rw [h, tsum_mul_left, (hasSum_one_poissonMeasure r).tsum_eq]
  ring

theorem poissonMeasure_integrable_count (r : NNReal) :
    Integrable (fun n : Nat => (n : Real)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := poisson_weight_summable r
  convert hs using 1
  funext n
  have hn : 0 ≤ (n : Real) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hn]
  ring

theorem poissonMeasure_lintegral_count (r : NNReal) :
    ∫⁻ n : Nat, (n : ENNReal) ∂poissonMeasure r = (r : ENNReal) := by
  have h := ofReal_integral_eq_lintegral_ofReal
    (poissonMeasure_integrable_count r)
    (Filter.Eventually.of_forall (fun n : Nat => Nat.cast_nonneg n))
  rw [poissonMeasure_integral_count r] at h
  have hfun : (fun n : Nat => ENNReal.ofReal (n : Real)) =
      (fun n : Nat => (n : ENNReal)) := by
    funext n
    simp
  rw [hfun] at h
  simpa using h.symm

/-- The Poisson-averaged expected number of second-loop rounds. -/
theorem poisson_averaged_firstExitRound_le {n : Nat} (s : TTCState n)
    (r : NNReal) (cutoff : Nat) (threshold : Real) (hcutoff : 0 < cutoff)
    (hthreshold : ∀ q : Nat, q < cutoff → (q : Real) ≤ threshold) :
    ∫⁻ pending : Nat, (∫⁻ coins,
        (firstExitRound s pending threshold coins : ENNReal)
          ∂fairCoinStreamLaw) ∂poissonMeasure r ≤
      2 * ((s.samples.card + (r : ENNReal)) / cutoff) := by
  have hpoint (pending : Nat) :=
    expected_firstExitRound_le s pending cutoff threshold hcutoff hthreshold
  calc
    (∫⁻ pending : Nat, (∫⁻ coins,
        (firstExitRound s pending threshold coins : ENNReal)
          ∂fairCoinStreamLaw) ∂poissonMeasure r) ≤
        ∫⁻ pending : Nat,
          2 * ((s.samples.card + pending : ENNReal) / cutoff)
            ∂poissonMeasure r := by
      exact lintegral_mono hpoint
    _ = 2 * ((s.samples.card + (r : ENNReal)) / cutoff) := by
      have hmeas : Measurable (fun pending : Nat =>
          ((s.samples.card + pending : ENNReal) / cutoff)) := by
        exact measurable_of_countable _
      rw [lintegral_const_mul _ hmeas]
      congr 1
      simp_rw [div_eq_mul_inv, add_mul]
      rw [lintegral_add_left (by fun_prop)]
      simp only [lintegral_const, measure_univ, mul_one]
      rw [lintegral_mul_const _ (measurable_of_countable (fun q : Nat => (q : ENNReal)))]
      rw [poissonMeasure_lintegral_count]

theorem poisson_averaged_countThinCost_le {n : Nat} (s : TTCState n)
    (r : NNReal) (cutoff : Nat) (threshold : Real) (hcutoff : 0 < cutoff)
    (hthreshold : ∀ q : Nat, q < cutoff → (q : Real) ≤ threshold) :
    ∫⁻ pending : Nat, (∫⁻ result, (result.2 : ENNReal) ∂
      manuscriptCountThinWithCost s pending threshold) ∂poissonMeasure r ≤
      (TTCRuntime.countThinningRoundOperations s.samples.card : ENNReal) *
        (2 * ((s.samples.card + (r : ENNReal)) / cutoff)) := by
  calc
    (∫⁻ pending : Nat, (∫⁻ result, (result.2 : ENNReal) ∂
      manuscriptCountThinWithCost s pending threshold) ∂poissonMeasure r) ≤
      ∫⁻ pending : Nat,
        (TTCRuntime.countThinningRoundOperations s.samples.card : ENNReal) *
          (∫⁻ coins, (firstExitRound s pending threshold coins : ENNReal)
            ∂fairCoinStreamLaw) ∂poissonMeasure r := by
      apply lintegral_mono
      intro pending
      exact le_of_eq (manuscriptCountThinWithCost_expected_eq s pending threshold)
    _ = (TTCRuntime.countThinningRoundOperations s.samples.card : ENNReal) *
        (∫⁻ pending : Nat, (∫⁻ coins,
          (firstExitRound s pending threshold coins : ENNReal)
            ∂fairCoinStreamLaw) ∂poissonMeasure r) := by
      rw [lintegral_const_mul _ (measurable_of_countable _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (poisson_averaged_firstExitRound_le s r cutoff threshold hcutoff hthreshold)
      (by positivity)

/-- Under the entry-population and Poisson-mean budget, the second loop has
at most four expected rounds. -/
theorem poisson_averaged_firstExitRound_le_four {n : Nat} (s : TTCState n)
    (r : NNReal) (cutoff : Nat) (threshold : Real) (hcutoff : 0 < cutoff)
    (hthreshold : ∀ q : Nat, q < cutoff → (q : Real) ≤ threshold)
    (hpopulation : (s.samples.card : ENNReal) + (r : ENNReal) ≤
      2 * (cutoff : ENNReal)) :
    ∫⁻ pending : Nat, (∫⁻ coins,
        (firstExitRound s pending threshold coins : ENNReal)
          ∂fairCoinStreamLaw) ∂poissonMeasure r ≤ 4 := by
  apply (poisson_averaged_firstExitRound_le s r cutoff threshold hcutoff
    hthreshold).trans
  have hcutoff0 : (cutoff : ENNReal) ≠ 0 := by exact_mod_cast hcutoff.ne'
  have hcutoffTop : (cutoff : ENNReal) ≠ ⊤ := by simp
  have hratio : ((s.samples.card : ENNReal) + (r : ENNReal)) / cutoff ≤ 2 :=
    (ENNReal.div_le_iff hcutoff0 hcutoffTop).2 (by simpa [mul_comm] using hpopulation)
  calc
    2 * (((s.samples.card : ENNReal) + (r : ENNReal)) / cutoff) ≤ 2 * 2 := by
      gcongr
    _ = 4 := by norm_num

theorem poisson_averaged_firstExitRound_le_four_of_guard {n : Nat}
    (s : TTCState n) (r : NNReal) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (hsamples : (s.samples.card : Real) ≤ threshold)
    (hrate : (r : Real) < threshold) :
    ∫⁻ pending : Nat, (∫⁻ coins,
        (firstExitRound s pending threshold coins : ENNReal)
          ∂fairCoinStreamLaw) ∂poissonMeasure r ≤ 4 := by
  have hpopulationReal : (s.samples.card : Real) + (r : Real) ≤
      2 * (Nat.floor threshold + 1 : Real) := by
    have hfloor := Nat.lt_floor_add_one threshold
    linarith
  have hpopulation : (s.samples.card : ENNReal) + (r : ENNReal) ≤
      2 * (Nat.floor threshold + 1 : ENNReal) := by
    exact_mod_cast hpopulationReal
  apply poisson_averaged_firstExitRound_le_four s r
    (Nat.floor threshold + 1) threshold (Nat.succ_pos _) (by
      intro q hq
      exact (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hq)).trans
        (Nat.floor_le hthreshold))
  simpa only [Nat.cast_add, Nat.cast_one] using hpopulation

/-- The charged count-thinning loop inherits the four-round expectation
after the manuscript's first rate guard. -/
theorem poisson_averaged_countThinCost_le_four_of_guard {n : Nat}
    (s : TTCState n) (r : NNReal) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (hsamples : (s.samples.card : Real) ≤ threshold)
    (hrate : (r : Real) < threshold) :
    ∫⁻ pending : Nat, (∫⁻ result, (result.2 : ENNReal) ∂
      manuscriptCountThinWithCost s pending threshold) ∂poissonMeasure r ≤
      4 * TTCRuntime.countThinningRoundOperations s.samples.card := by
  have hpopulationReal : (s.samples.card : Real) + (r : Real) ≤
      2 * (Nat.floor threshold + 1 : Real) := by
    have hfloor := Nat.lt_floor_add_one threshold
    linarith
  have hpopulation : (s.samples.card : ENNReal) + (r : ENNReal) ≤
      2 * (Nat.floor threshold + 1 : ENNReal) := by
    exact_mod_cast hpopulationReal
  have hbase := poisson_averaged_countThinCost_le s r
    (Nat.floor threshold + 1) threshold (Nat.succ_pos _) (by
      intro q hq
      exact (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hq)).trans
        (Nat.floor_le hthreshold))
  have hratio : ((s.samples.card : ENNReal) + (r : ENNReal)) /
      (Nat.floor threshold + 1 : ENNReal) ≤ 2 := by
    apply (ENNReal.div_le_iff (by exact_mod_cast (Nat.succ_pos (Nat.floor threshold)).ne')
      (by simp)).2
    simpa [mul_comm] using hpopulation
  calc
    _ ≤ (TTCRuntime.countThinningRoundOperations s.samples.card : ENNReal) *
        (2 * (((s.samples.card : ENNReal) + (r : ENNReal)) /
          (Nat.floor threshold + 1 : ENNReal))) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hbase
    _ ≤ (TTCRuntime.countThinningRoundOperations s.samples.card : ENNReal) *
        (2 * 2) := by gcongr
    _ = 4 * TTCRuntime.countThinningRoundOperations s.samples.card := by ring

/-- The actual charged Poisson draw followed by the second manuscript loop
has the requested constant expected overhead. -/
theorem manuscriptPoissonCountThin_expected_cost_le {n : Nat}
    (s : TTCState n) (r : NNReal) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (hsamples : (s.samples.card : Real) ≤ threshold)
    (hrate : (r : Real) < threshold) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind
        (costedCharge (poissonMeasure r) TTCRuntime.poissonDrawOperations)
        (fun pending => manuscriptCountThinWithCost s pending threshold) ≤
      TTCRuntime.poissonDrawOperations +
        4 * TTCRuntime.countThinningRoundOperations s.samples.card := by
  have hmass (pending : Nat) :
      (manuscriptCountThinWithCost s pending threshold) Set.univ ≤ 1 :=
    manuscriptCountThinWithCost_mass_le_one s pending threshold
  apply (costedBind_lintegral_cost_le _ _ (measurable_of_countable _) hmass).trans
  have hpair : Measurable (fun pending : Nat =>
      (pending, TTCRuntime.poissonDrawOperations)) := by fun_prop
  unfold costedCharge
  rw [lintegral_map (by fun_prop) hpair]
  simp only [TTCRuntime.poissonDrawOperations]
  rw [lintegral_add_left (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]
  simpa only [TTCRuntime.poissonDrawOperations, Nat.cast_one] using add_le_add_right
    (poisson_averaged_countThinCost_le_four_of_guard s r threshold
      hthreshold hsamples hrate) (1 : ENNReal)

end Kr25Ssmxt

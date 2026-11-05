import Kr25Ssmxt.Analysis.ManuscriptFixedLevelIntensity
import Kr25Ssmxt.Analysis.ManuscriptDyadicCutoff

/-! A one-sided Poisson tail at the dyadic cutoff. The scalar mean hypothesis
is the one supplied by the fixed-level point-intensity envelope. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem poisson_upper_tail_two_thirds (mean : NNReal) (threshold : Real)
    (hthreshold : 0 < threshold)
    (hmean : (mean : Real) ≤ 2 * threshold / 3) :
    (poissonMeasure mean).real {k : Nat | threshold ≤ (k : Real)} ≤
      Real.exp (-threshold / 15) := by
  let s : Real := Real.log (3 / 2)
  have hs : 0 < s := Real.log_pos (by norm_num : (1 : Real) < 3 / 2)
  have hexp : Real.exp s = 3 / 2 := by
    dsimp [s]
    rw [Real.exp_log (by norm_num : (0 : Real) < 3 / 2)]
  have hpad := manuscript_pade_log_bound
    (t := (3 / 2 : Real)) (by norm_num)
  have hs_lower : (2 / 5 : Real) ≤ s := by
    dsimp [s]
    nlinarith
  rw [poissonMeasure_real_eq_tsum_indicator]
  have htail := Arlib.Probability.poisson_upper_tail_tilt
    (mu := (mean : Real)) (a := threshold - (mean : Real))
    (s := s) (by positivity) hs
  have hbound :
      (mean : Real) * (Real.exp s - 1) - s *
        ((mean : Real) + (threshold - (mean : Real))) ≤
        -threshold / 15 := by
    rw [hexp]
    nlinarith [mul_nonneg hthreshold.le (sub_nonneg.mpr hs_lower)]
  have hexp_bound :
      Real.exp ((mean : Real) * (Real.exp s - 1) - s *
        ((mean : Real) + (threshold - (mean : Real)))) ≤
        Real.exp (-threshold / 15) := Real.exp_le_exp.mpr hbound
  have hsum : (mean : Real) + (threshold - (mean : Real)) = threshold := by
    ring
  calc
    (∑' k : Nat, if threshold ≤ (k : Real) then
        Arlib.Probability.poissonPMF (mean : Real) k else 0) ≤
      Real.exp ((mean : Real) * (Real.exp s - 1) - s *
        ((mean : Real) + (threshold - (mean : Real)))) := by
          simpa only [hsum] using htail
    _ ≤ Real.exp (-threshold / 15) := hexp_bound

theorem fixedLevelLaw_total_upper_cutoff
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) (threshold : Real)
    (hthreshold : 0 < threshold)
    (hmean :
      ((∑ i, fixedLevelRates steps (fun _ => 0) i : NNReal) : Real) ≤
        2 * threshold / 3) :
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : ι → Nat => ∑ i, counts i)).real
          {k : Nat | threshold ≤ (k : Real)} ≤
      Real.exp (-threshold / 15) := by
  rw [fixedLevelLaw_total_poisson]
  exact poisson_upper_tail_two_thirds
    (∑ i, fixedLevelRates steps (fun _ => 0) i)
    threshold hthreshold hmean

/-- At the manuscript's penultimate dyadic level, the uniform point-rate
envelope and the size of the union force the total Poisson mean below two
thirds of the threshold. -/
theorem fixedLevelLaw_dyadic_cutoff_upper_tail
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι))
    (count : Nat) (hcount : 0 < count)
    (hcovered : (fixedLevelCoverage steps ∅).card ≤ count)
    (threshold : Real) (hthreshold : 0 < threshold)
    (upper : NNReal)
    (hupper : (upper : Real) ≤
      (4 / 3) * threshold /
        (2 : Real) ^ (manuscriptDyadicCutoff count - 1))
    (hsteps : ∀ step ∈ steps, step.RateEnvelope 0 upper) :
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : ι → Nat => ∑ i, counts i)).real
          {k : Nat | threshold ≤ (k : Real)} ≤
      Real.exp (-threshold / 15) := by
  let mean : NNReal := ∑ i, fixedLevelRates steps (fun _ => 0) i
  let covered := fixedLevelCoverage steps ∅
  let d := manuscriptDyadicCutoff count - 1
  have hpow : 0 < (2 : Real) ^ d := by positivity
  have hhalf : 2 * (count : Real) < (2 : Real) ^ d := by
    exact_mod_cast manuscriptDyadicCutoff_half count hcount
  have hmeanNN : mean ≤ covered.card • upper :=
    (fixedLevelRates_total_mean_bounds ι steps 0 upper hsteps).2
  have hmeanR : (mean : Real) ≤ (covered.card : Real) * upper := by
    have hcast : (mean : Real) ≤ ((covered.card • upper : NNReal) : Real) := by
      exact_mod_cast hmeanNN
    simpa only [NNReal.coe_nsmul, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_natCast] using hcast
  have hcardR : (covered.card : Real) ≤ count := by
    exact_mod_cast hcovered
  have hupperTotal : (mean : Real) ≤
      (count : Real) * ((4 / 3) * threshold / (2 : Real) ^ d) := by
    calc
      (mean : Real) ≤ (covered.card : Real) * upper := hmeanR
      _ ≤ (count : Real) * upper :=
        mul_le_mul_of_nonneg_right hcardR upper.coe_nonneg
      _ ≤ (count : Real) * ((4 / 3) * threshold / (2 : Real) ^ d) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
  have hstrict : (count : Real) * ((4 / 3) * threshold /
      (2 : Real) ^ d) < 2 * threshold / 3 := by
    rw [show (count : Real) * ((4 / 3) * threshold / (2 : Real) ^ d) =
      ((count : Real) * ((4 / 3) * threshold)) / (2 : Real) ^ d by ring]
    apply (div_lt_iff₀ hpow).2
    nlinarith [mul_pos hthreshold (sub_pos.mpr hhalf)]
  apply fixedLevelLaw_total_upper_cutoff ι steps threshold hthreshold
  exact hupperTotal.trans_lt hstrict |>.le

end Kr25Ssmxt

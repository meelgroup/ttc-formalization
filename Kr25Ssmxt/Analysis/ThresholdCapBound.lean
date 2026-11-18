import Kr25Ssmxt.Analysis.RuntimeBudgets

/-! An explicit parameter bound for the paper's sample threshold. -/

namespace Kr25Ssmxt

open Real

theorem ApproxParams.epsilonPrime_le_one_div_twelve (p : ApproxParams) :
    p.ε' ≤ 1 / 12 := by
  unfold ApproxParams.ε'
  linarith [p.epsilon_le_one]

theorem ApproxParams.one_sub_epsilonPrime_ge_eleven_div_twelve
    (p : ApproxParams) :
    11 / 12 ≤ 1 - p.ε' := by
  linarith [p.epsilonPrime_le_one_div_twelve]

theorem ApproxParams.threshold_le_explicit_parameter_envelope
    (p : ApproxParams) (m : Nat) (hm : 1 ≤ m) :
    p.Thresh m ≤
      27 * Real.log (24 / p.delta) / p.ε' ^ 2 +
        15 * (Real.log (6 / p.delta) + Real.log m) := by
  have heps : 0 < p.ε' := by
    unfold ApproxParams.ε'
    positivity [p.epsilon_pos]
  have hone : 0 < 1 - p.ε' := by
    linarith [p.one_sub_epsilonPrime_ge_eleven_div_twelve]
  have hδ : 0 < p.delta := p.delta_pos
  have hlog24 : 0 ≤ Real.log (24 / p.delta) := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith [p.delta_le_one]
  have hlog6 : 0 ≤ Real.log (6 / p.delta) := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith [p.delta_le_one]
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hrecip : 24 / (1 - p.ε') ≤ 27 := by
    apply (div_le_iff₀ hone).2
    linarith [p.one_sub_epsilonPrime_ge_eleven_div_twelve]
  have hfirst :
      24 * Real.log (24 / p.delta) /
          ((1 - p.ε') * p.ε' ^ 2) ≤
        27 * Real.log (24 / p.delta) / p.ε' ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hrecip hlog24
    have hsq : 0 < p.ε' ^ 2 := sq_pos_of_pos heps
    calc
      _ = (24 / (1 - p.ε') * Real.log (24 / p.delta)) /
          p.ε' ^ 2 := by
            field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hmul hsq.le
  have hsecond : 0 ≤ 15 * (Real.log (6 / p.delta) + Real.log m) := by
    positivity
  unfold ApproxParams.Thresh
  exact max_le (le_add_of_le_of_nonneg hfirst hsecond)
    (le_add_of_nonneg_of_le (div_nonneg (by positivity) (by positivity)) le_rfl)

theorem TTCRuntime.sampleCap_le_explicit_parameter_envelope
    (p : ApproxParams) (m : Nat) (hm : 1 ≤ m) :
    TTCRuntime.ThresholdCap p m ≤
      Nat.ceil (27 * Real.log (24 / p.delta) / p.ε' ^ 2 +
        15 * (Real.log (6 / p.delta) + Real.log m)) := by
  unfold TTCRuntime.ThresholdCap
  exact Nat.ceil_mono (p.threshold_le_explicit_parameter_envelope m hm)

theorem TTCRuntime.sampleCap_cast_le_explicit_parameter_envelope
    (p : ApproxParams) (m : Nat) (hm : 1 ≤ m) :
    (TTCRuntime.ThresholdCap p m : Real) ≤
      1 + 27 * Real.log (24 / p.delta) / p.ε' ^ 2 +
        15 * (Real.log (6 / p.delta) + Real.log m) := by
  have hcap := TTCRuntime.sampleCap_le_explicit_parameter_envelope p m hm
  have heps : 0 < p.ε' := by
    dsimp [ApproxParams.ε']
    positivity [p.epsilon_pos]
  have hδ : 0 < p.delta := p.delta_pos
  have hlog24 : 0 ≤ Real.log (24 / p.delta) := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith [p.delta_le_one]
  have hlog6 : 0 ≤ Real.log (6 / p.delta) := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith [p.delta_le_one]
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have harg : 0 ≤
      27 * Real.log (24 / p.delta) / p.ε' ^ 2 +
        15 * (Real.log (6 / p.delta) + Real.log m) := by positivity
  have hcapR : (TTCRuntime.ThresholdCap p m : Real) ≤
      (Nat.ceil (27 * Real.log (24 / p.delta) / p.ε' ^ 2 +
        15 * (Real.log (6 / p.delta) + Real.log m)) : Real) := by
    exact_mod_cast hcap
  have hceil := (Nat.ceil_lt_add_one harg).le
  linarith

end Kr25Ssmxt

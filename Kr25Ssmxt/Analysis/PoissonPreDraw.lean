import Kr25Ssmxt.Analysis.AdaptiveTapeAppend

/-! Couple the paper's Poisson draw after deterministic rate halving
to a Poisson draw at the incoming rate followed by independent thinning. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem survivalProbability_toNNReal (rounds : Nat) :
    unitInterval.toNNReal (survivalProbability rounds) =
      (1 / 2 : NNReal) ^ rounds := by
  rfl

theorem poisson_predraw_after_rate_halving
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) :
    (poissonMeasure (intensity * s.p)).bind (fun baseCount =>
      fairCoinStreamLaw.map (fun coins => pendingAfter coins
        (ttcReference.firstLoopExit s intensity threshold) s.nextLabel baseCount)) =
      poissonMeasure
        (intensity * (ttcReference.firstLoopResult s intensity threshold
          (fun _ => true)).p) := by
  rw [poisson_pendingAfter_law]
  rw [survivalProbability_toNNReal]
  simp only [ttcReference.firstLoopResult]
  simp only [one_div, ← inv_pow, div_eq_mul_inv]
  ac_rfl

theorem poisson_predraw_at_fixed_rounds
    (mean : NNReal) (rounds firstLabel : Nat) :
    (poissonMeasure (mean * (2 : NNReal) ^ rounds)).bind (fun baseCount =>
      fairCoinStreamLaw.map (fun coins =>
        pendingAfter coins rounds firstLabel baseCount)) =
      poissonMeasure mean := by
  rw [poisson_pendingAfter_law, survivalProbability_toNNReal]
  simp only [one_div]
  have hfactor : (2 : NNReal)⁻¹ ^ rounds * (mean * 2 ^ rounds) =
      mean * ((2 : NNReal) ^ rounds)⁻¹ * 2 ^ rounds := by
    rw [← inv_pow]
    ac_rfl
  rw [hfactor, mul_assoc, inv_mul_cancel₀
    (pow_ne_zero rounds (by norm_num : (2 : NNReal) ≠ 0))]
  simp

/-- One Poisson population drawn at absolute dyadic level zero can supply
the pending count at any later fixed level by thinning its copy labels. -/
theorem poisson_absolute_level
    (mean : NNReal) (firstLabel level : Nat) :
    (poissonMeasure mean).bind (fun baseCount =>
      fairCoinStreamLaw.map (fun coins =>
        pendingAfter coins level firstLabel baseCount)) =
      poissonMeasure (mean / (2 : NNReal) ^ level) := by
  rw [poisson_pendingAfter_law, survivalProbability_toNNReal]
  simp only [one_div, ← inv_pow, div_eq_mul_inv]
  ac_rfl

end Kr25Ssmxt

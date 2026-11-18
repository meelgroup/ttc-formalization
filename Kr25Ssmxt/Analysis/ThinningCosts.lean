import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.MeasurableThinningResult
import Kr25Ssmxt.Analysis.MeasurableSamplesAfterFixed
import Kr25Ssmxt.Analysis.FairCoinStreamLawIsProbabilityMeasure

/-!
# Costed paper thinning loops

The two costed loop laws retain their number of rounds. Forgetting the charge
recovers exactly the corresponding program law. These lemmas do not yet bound
the expected number of second-loop rounds.
-/

namespace Kr25Ssmxt

open MeasureTheory

theorem ApproxParams.threshold_pos (p : ApproxParams) (m : Nat) :
    0 < p.Thresh m := by
  have hδ : 1 < 24 / p.delta := by
    rw [one_lt_div p.delta_pos]
    linarith [p.delta_le_one]
  have hε0 : 0 < p.ε' := div_pos p.epsilon_pos (by norm_num)
  have hε1 : p.ε' < 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have hfirst : 0 < 24 * Real.log (24 / p.delta) /
      ((1 - p.ε') * p.ε' ^ 2) := by
    apply div_pos
    · exact mul_pos (by norm_num) (Real.log_pos hδ)
    · exact mul_pos (by linarith) (sq_pos_of_pos hε0)
  exact hfirst.trans_le (le_max_left _ _)

theorem measurable_rateThinningResult {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    Measurable (ttcReference.firstLoopResult s intensity threshold) := by
  let rounds := ttcReference.firstLoopExit s intensity threshold
  have hsamples : Measurable (fun coins : Nat × Nat → Bool =>
      samplesAfter coins rounds s.X) :=
    measurable_samplesAfter_fixed rounds s.X
  change Measurable (fun coins : Nat × Nat → Bool =>
    { p := s.p / (2 : NNReal) ^ rounds
      X := samplesAfter coins rounds s.X
      nextLabel := s.nextLabel : TTCState n })
  rw [measurable_comap_iff]
  exact measurable_const.prodMk (hsamples.prodMk measurable_const)

/-- The paper's deterministic-rate loop preserves total probability. -/
theorem rateThinUntil_isProbabilityMeasure {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    IsProbabilityMeasure (ttcReference.firstLoop s intensity threshold) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_rateThinningResult s intensity threshold).aemeasurable

/-- The charged first loop has precisely the program's uncharged state law. -/
theorem rateThinWithCost_fst {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    (ttcReference.firstLoopWithCost s intensity threshold).map Prod.fst =
      ttcReference.firstLoop s intensity threshold := by
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (ttcReference.firstLoopResult s intensity threshold coins,
        ttcReference.firstLoopCost s intensity threshold)) :=
    (measurable_rateThinningResult s intensity threshold).prodMk
      measurable_const
  unfold ttcReference.firstLoopWithCost ttcReference.firstLoop
  rw [MeasureTheory.Measure.map_map measurable_fst hpair]
  rfl

theorem rateThinWithCost_isProbabilityMeasure {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real) :
    IsProbabilityMeasure (ttcReference.firstLoopWithCost s intensity threshold) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  unfold ttcReference.firstLoopWithCost
  apply Measure.isProbabilityMeasure_map
  exact ((measurable_rateThinningResult s intensity threshold).prodMk
    measurable_const).aemeasurable

/-- The first loop's charged cost is deterministic, even though its retained
copies are random. -/
theorem rateThinWithCost_expectedCost {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    ∫⁻ result, (result.2 : ENNReal) ∂ttcReference.firstLoopWithCost s intensity threshold =
      ttcReference.firstLoopCost s intensity threshold := by
  letI : MeasureTheory.IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (ttcReference.firstLoopResult s intensity threshold coins,
        ttcReference.firstLoopCost s intensity threshold)) :=
    (measurable_rateThinningResult s intensity threshold).prodMk
      measurable_const
  unfold ttcReference.firstLoopWithCost
  rw [MeasureTheory.lintegral_map (by fun_prop) hpair]
  simp only [MeasureTheory.lintegral_const, measure_univ, mul_one]

theorem rateThinWithCost_mass_le_one {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    (ttcReference.firstLoopWithCost s intensity threshold) Set.univ ≤ 1 := by
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (ttcReference.firstLoopResult s intensity threshold coins,
        ttcReference.firstLoopCost s intensity threshold)) :=
    (measurable_rateThinningResult s intensity threshold).prodMk
      measurable_const
  unfold ttcReference.firstLoopWithCost
  rw [Measure.map_apply hpair MeasurableSet.univ]
  simpa using (show fairCoinStreamLaw Set.univ ≤ 1 from by
    letI : IsProbabilityMeasure fairCoinStreamLaw :=
      fairCoinStreamLaw_isProbabilityMeasure
    simp)

/-- A positive threshold makes the deterministic rate check terminate. -/
theorem rateExit_exists {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold) :
    ∃ rounds : Nat,
      ((intensity * s.p / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ threshold := by
  let a : Real := (intensity * s.p : NNReal)
  obtain ⟨rounds, hrounds⟩ := exists_nat_gt (a / threshold)
  have hpowNat : rounds < 2 ^ rounds := Nat.lt_two_pow_self
  have hpow : (rounds : Real) < (2 : Real) ^ rounds := by
    exact_mod_cast hpowNat
  have hmul : a < threshold * (2 : Real) ^ rounds := by
    have hbase : a < threshold * rounds := by
      simpa only [mul_comm] using (div_lt_iff₀ hthreshold).mp hrounds
    nlinarith [mul_lt_mul_of_pos_left hpow hthreshold]
  refine ⟨rounds, ?_⟩
  have hdenom : 0 < (2 : Real) ^ rounds := pow_pos (by norm_num) _
  have hratio : a / (2 : Real) ^ rounds ≤ threshold :=
    ((div_lt_iff₀ hdenom).2 (by nlinarith)).le
  simpa only [a, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using hratio

/-- The rate check exits at a level satisfying its guard. -/
theorem rateExit_guard {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold) :
    ((intensity * s.p / (2 : NNReal) ^
      ttcReference.firstLoopExit s intensity threshold : NNReal) : Real) ≤ threshold := by
  unfold ttcReference.firstLoopExit
  exact Nat.sInf_mem (by
    obtain ⟨rounds, hrounds⟩ := rateExit_exists s intensity hthreshold
    exact ⟨rounds, hrounds⟩)

/-- Once the current scaled Poisson mean is at most the threshold, the rate check does
not halve the rate. -/
theorem rateExit_zero_of_le {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real)
    (hbelow : ((intensity * s.p : NNReal) : Real) ≤ threshold) :
    ttcReference.firstLoopExit s intensity threshold = 0 := by
  unfold ttcReference.firstLoopExit
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hmin : sInf {rounds : Nat |
      ((intensity * s.p / (2 : NNReal) ^ rounds : NNReal) : Real) ≤
        threshold} ≤ 0 := by
    apply Nat.sInf_le
    simpa using hbelow
  omega

theorem rateExit_zero_of_lt {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real)
    (hbelow : ((intensity * s.p : NNReal) : Real) < threshold) :
    ttcReference.firstLoopExit s intensity threshold = 0 :=
  rateExit_zero_of_le s intensity threshold hbelow.le

theorem rateThinningResult_of_le {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real)
    (hbelow : ((intensity * s.p : NNReal) : Real) ≤ threshold)
    (coins : Nat × Nat → Bool) :
    ttcReference.firstLoopResult s intensity threshold coins = s := by
  simp [ttcReference.firstLoopResult,
    rateExit_zero_of_le s intensity threshold hbelow,
    samplesAfter, survives]

theorem rateThinningResult_of_below {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real)
    (hbelow : ((intensity * s.p : NNReal) : Real) < threshold)
    (coins : Nat × Nat → Bool) :
    ttcReference.firstLoopResult s intensity threshold coins = s :=
  rateThinningResult_of_le s intensity threshold hbelow.le coins

/-- If the second while-loop passes a fixed dyadic level, the hypothetical
population at that level exceeds its threshold. -/
theorem second_loop_crossing_implies_large_population
    {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (coins : Nat × Nat → Bool) (rounds : Nat)
    (hcross : rounds < ttcPseudocode.secondLoopExitRound s pending threshold coins) :
    threshold <
      (samplesAfter coins rounds s.X).card +
        pendingAfter coins rounds s.nextLabel pending := by
  by_contra h
  have hexit : ttcPseudocode.secondLoopExit s pending threshold coins rounds := by
    dsimp [ttcPseudocode.secondLoopExit]
    exact le_of_not_gt h
  have hmin : ttcPseudocode.secondLoopExitRound s pending threshold coins ≤ rounds := by
    unfold ttcPseudocode.secondLoopExitRound
    exact Nat.sInf_le hexit
  omega

/-- Every rate-check result has a Poisson mean at most the threshold. -/
theorem rateThinningResult_guard {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold)
    (coins : Nat × Nat → Bool) :
    ((intensity * (ttcReference.firstLoopResult s intensity threshold coins).p :
      NNReal) : Real) ≤ threshold := by
  simpa only [ttcReference.firstLoopResult, mul_div_assoc] using
    rateExit_guard s intensity hthreshold

theorem rateExit_mono_intensity {n : Nat} (s : TTCState n)
    {small large : NNReal} (hsmall : small ≤ large)
    {threshold : Real} (hthreshold : 0 < threshold) :
    ttcReference.firstLoopExit s small threshold ≤
      ttcReference.firstLoopExit s large threshold := by
  have hlarge := rateExit_guard s large hthreshold
  have hbound : small * s.p /
      (2 : NNReal) ^ ttcReference.firstLoopExit s large threshold ≤
      large * s.p /
      (2 : NNReal) ^ ttcReference.firstLoopExit s large threshold := by
    gcongr
  have hboundReal :
      ((small * s.p /
        (2 : NNReal) ^ ttcReference.firstLoopExit s large threshold : NNReal) : Real) ≤
      ((large * s.p /
        (2 : NNReal) ^ ttcReference.firstLoopExit s large threshold : NNReal) : Real) := by
    exact_mod_cast hbound
  unfold ttcReference.firstLoopExit
  exact Nat.sInf_le (hboundReal.trans hlarge)

theorem rateThinningCost_mono_intensity {n : Nat} (s : TTCState n)
    {small large : NNReal} (hsmall : small ≤ large)
    {threshold : Real} (hthreshold : 0 < threshold) :
    ttcReference.firstLoopCost s small threshold ≤
      ttcReference.firstLoopCost s large threshold := by
  have hmono := rateExit_mono_intensity s hsmall hthreshold
  unfold ttcReference.firstLoopCost
  split_ifs with hs hl <;> omega

/-- The first loop's number of halvings is logarithmic in its initial mean
relative to the threshold. -/
theorem rateExit_le_clog {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold) :
    ttcReference.firstLoopExit s intensity threshold ≤
      Nat.clog 2 (Nat.ceil (((intensity * s.p : NNReal) : Real) / threshold) + 1) := by
  let a : Real := (intensity * s.p : NNReal)
  let N : Nat := Nat.ceil (a / threshold) + 1
  have hceil : a / threshold ≤ (Nat.ceil (a / threshold) : Real) := Nat.le_ceil _
  have hpowNat : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog (by norm_num) N
  have hpow : (N : Real) ≤ (2 : Real) ^ Nat.clog 2 N := by
    exact_mod_cast hpowNat
  have hlt : a / threshold < (2 : Real) ^ Nat.clog 2 N := by
    dsimp [N] at hpow
    push_cast at hpow
    linarith
  have hmul : a < threshold * (2 : Real) ^ Nat.clog 2 N := by
    rw [div_lt_iff₀ hthreshold] at hlt
    nlinarith
  have hdenom : 0 < (2 : Real) ^ Nat.clog 2 N := pow_pos (by norm_num) _
  have hexit :
      ((intensity * s.p / (2 : NNReal) ^ Nat.clog 2 N : NNReal) : Real) ≤
        threshold := by
    have hratio : a / (2 : Real) ^ Nat.clog 2 N ≤ threshold :=
      ((div_lt_iff₀ hdenom).2 (by nlinarith)).le
    simpa only [a, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using hratio
  unfold ttcReference.firstLoopExit
  exact Nat.sInf_le hexit

theorem rateThinningCost_le_clog {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold) :
    ttcReference.firstLoopCost s intensity threshold ≤
      Nat.clog 2 (Nat.ceil (((intensity * s.p : NNReal) : Real) / threshold) + 1) *
        TTCRuntime.rateThinningRoundOperations s.X.card := by
  have hle := rateExit_le_clog s intensity hthreshold
  unfold ttcReference.firstLoopCost
  split_ifs with h0
  · exact Nat.zero_le _
  · exact Nat.le_mul_of_pos_left _ (by omega)

/-- The charged second loop has precisely the program's uncharged state and
pending-count law. -/
theorem countThinWithCost_fst {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) :
    (ttcPseudocode.secondLoopWithCost s pending threshold).map Prod.fst =
      ttcPseudocode.secondLoop s pending threshold := by
  have hcost : Measurable (fun coins : Nat × Nat → Bool =>
      ttcPseudocode.secondLoopCost s pending threshold coins) := by
    unfold ttcPseudocode.secondLoopCost
    exact (measurable_of_countable
      (fun rounds : Nat => rounds *
        TTCRuntime.countThinningRoundOperations s.X.card)).comp
          (measurable_firstExitRound s pending threshold)
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (ttcPseudocode.secondLoopResult s pending threshold coins,
        ttcPseudocode.secondLoopCost s pending threshold coins)) :=
    (measurable_thinningResult s pending threshold).prodMk hcost
  unfold ttcPseudocode.secondLoopWithCost ttcPseudocode.secondLoop
  rw [MeasureTheory.Measure.map_map measurable_fst hpair]
  rfl

theorem countThinWithCost_mass_le_one {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) :
    (ttcPseudocode.secondLoopWithCost s pending threshold) Set.univ ≤ 1 := by
  have hcost : Measurable (fun coins : Nat × Nat → Bool =>
      ttcPseudocode.secondLoopCost s pending threshold coins) := by
    unfold ttcPseudocode.secondLoopCost
    exact (measurable_of_countable
      (fun rounds : Nat => rounds *
        TTCRuntime.countThinningRoundOperations s.X.card)).comp
          (measurable_firstExitRound s pending threshold)
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (ttcPseudocode.secondLoopResult s pending threshold coins,
        ttcPseudocode.secondLoopCost s pending threshold coins)) :=
    (measurable_thinningResult s pending threshold).prodMk hcost
  unfold ttcPseudocode.secondLoopWithCost
  rw [Measure.map_apply hpair MeasurableSet.univ]
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  simp

theorem countThinWithCost_isProbabilityMeasure {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real) :
    IsProbabilityMeasure (ttcPseudocode.secondLoopWithCost s pending threshold) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  unfold ttcPseudocode.secondLoopWithCost
  apply Measure.isProbabilityMeasure_map
  have hcost : Measurable (fun coins : Nat × Nat → Bool =>
      ttcPseudocode.secondLoopCost s pending threshold coins) := by
    unfold ttcPseudocode.secondLoopCost
    exact (measurable_of_countable
      (fun rounds : Nat => rounds *
        TTCRuntime.countThinningRoundOperations s.X.card)).comp
          (measurable_firstExitRound s pending threshold)
  exact ((measurable_thinningResult s pending threshold).prodMk hcost).aemeasurable

end Kr25Ssmxt

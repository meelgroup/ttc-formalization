import Kr25Ssmxt.Analysis.MeasurableThinningResult
import Kr25Ssmxt.Analysis.MeasurableSamplesAfterFixed
import Kr25Ssmxt.Analysis.FairCoinStreamLawIsProbabilityMeasure

/-!
# Costed manuscript thinning loops

The two costed loop laws retain their number of rounds. Forgetting the charge
recovers exactly the corresponding program law. These lemmas do not yet bound
the expected number of second-loop rounds.
-/

namespace Kr25Ssmxt

open MeasureTheory

theorem ApproxParams.threshold_pos (p : ApproxParams) (m : Nat) :
    0 < p.threshold m := by
  have hδ : 1 < 24 / p.delta := by
    rw [one_lt_div p.delta_pos]
    linarith [p.delta_le_one]
  have hε0 : 0 < p.epsilonPrime := div_pos p.epsilon_pos (by norm_num)
  have hε1 : p.epsilonPrime < 1 := by
    dsimp [ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  have hfirst : 0 < 24 * Real.log (24 / p.delta) /
      ((1 - p.epsilonPrime) * p.epsilonPrime ^ 2) := by
    apply div_pos
    · exact mul_pos (by norm_num) (Real.log_pos hδ)
    · exact mul_pos (by linarith) (sq_pos_of_pos hε0)
  exact hfirst.trans_le (le_max_left _ _)

theorem measurable_manuscriptRateThinningResult {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    Measurable (manuscriptRateThinningResult s intensity threshold) := by
  let rounds := manuscriptRateExit s intensity threshold
  have hsamples : Measurable (fun coins : Nat × Nat → Bool =>
      samplesAfter coins rounds s.samples) :=
    measurable_samplesAfter_fixed rounds s.samples
  change Measurable (fun coins : Nat × Nat → Bool =>
    { rate := s.rate / (2 : NNReal) ^ rounds
      samples := samplesAfter coins rounds s.samples
      nextLabel := s.nextLabel : TTCState n })
  rw [measurable_comap_iff]
  exact measurable_const.prodMk (hsamples.prodMk measurable_const)

/-- The manuscript's deterministic-rate loop preserves total probability. -/
theorem manuscriptRateThinUntil_isProbabilityMeasure {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    IsProbabilityMeasure (manuscriptRateThinUntil s intensity threshold) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_manuscriptRateThinningResult s intensity threshold).aemeasurable

/-- The charged first loop has precisely the program's uncharged state law. -/
theorem manuscriptRateThinWithCost_fst {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    (manuscriptRateThinWithCost s intensity threshold).map Prod.fst =
      manuscriptRateThinUntil s intensity threshold := by
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (manuscriptRateThinningResult s intensity threshold coins,
        manuscriptRateThinningCost s intensity threshold)) :=
    (measurable_manuscriptRateThinningResult s intensity threshold).prodMk
      measurable_const
  unfold manuscriptRateThinWithCost manuscriptRateThinUntil
  rw [MeasureTheory.Measure.map_map measurable_fst hpair]
  rfl

theorem manuscriptRateThinWithCost_isProbabilityMeasure {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real) :
    IsProbabilityMeasure (manuscriptRateThinWithCost s intensity threshold) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  unfold manuscriptRateThinWithCost
  apply Measure.isProbabilityMeasure_map
  exact ((measurable_manuscriptRateThinningResult s intensity threshold).prodMk
    measurable_const).aemeasurable

/-- The first loop's charged cost is deterministic, even though its retained
copies are random. -/
theorem manuscriptRateThinWithCost_expectedCost {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    ∫⁻ result, (result.2 : ENNReal) ∂manuscriptRateThinWithCost s intensity threshold =
      manuscriptRateThinningCost s intensity threshold := by
  letI : MeasureTheory.IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (manuscriptRateThinningResult s intensity threshold coins,
        manuscriptRateThinningCost s intensity threshold)) :=
    (measurable_manuscriptRateThinningResult s intensity threshold).prodMk
      measurable_const
  unfold manuscriptRateThinWithCost
  rw [MeasureTheory.lintegral_map (by fun_prop) hpair]
  simp only [MeasureTheory.lintegral_const, measure_univ, mul_one]

theorem manuscriptRateThinWithCost_mass_le_one {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) :
    (manuscriptRateThinWithCost s intensity threshold) Set.univ ≤ 1 := by
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (manuscriptRateThinningResult s intensity threshold coins,
        manuscriptRateThinningCost s intensity threshold)) :=
    (measurable_manuscriptRateThinningResult s intensity threshold).prodMk
      measurable_const
  unfold manuscriptRateThinWithCost
  rw [Measure.map_apply hpair MeasurableSet.univ]
  simpa using (show fairCoinStreamLaw Set.univ ≤ 1 from by
    letI : IsProbabilityMeasure fairCoinStreamLaw :=
      fairCoinStreamLaw_isProbabilityMeasure
    simp)

/-- Any explicit dyadic level below the guard threshold bounds the number of
first-loop rounds and hence its charged cost. The clipping bound must supply
such a level for the full runtime theorem. -/
theorem manuscriptRateThinningCost_le {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) (rounds : Nat)
    (hexit :
      ((intensity * s.rate / (2 : NNReal) ^ rounds : NNReal) : Real) < threshold) :
    manuscriptRateThinningCost s intensity threshold ≤
      rounds * TTCRuntime.rateThinningRoundOperations s.samples.card := by
  unfold manuscriptRateThinningCost manuscriptRateExit
  exact Nat.mul_le_mul_right _ (Nat.sInf_le hexit)

/-- A positive threshold makes the deterministic first rate loop terminate. -/
theorem manuscriptRateExit_exists {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold) :
    ∃ rounds : Nat,
      ((intensity * s.rate / (2 : NNReal) ^ rounds : NNReal) : Real) < threshold := by
  let a : Real := (intensity * s.rate : NNReal)
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
  have hratio : a / (2 : Real) ^ rounds < threshold :=
    (div_lt_iff₀ hdenom).2 (by nlinarith)
  simpa only [a, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using hratio

/-- The first rate loop exits at a level satisfying its strict guard. -/
theorem manuscriptRateExit_guard {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold) :
    ((intensity * s.rate / (2 : NNReal) ^
      manuscriptRateExit s intensity threshold : NNReal) : Real) < threshold := by
  unfold manuscriptRateExit
  exact Nat.sInf_mem (by
    obtain ⟨rounds, hrounds⟩ := manuscriptRateExit_exists s intensity hthreshold
    exact ⟨rounds, hrounds⟩)

/-- Once the current scaled Poisson mean is below the threshold, the first
while-loop does not halve the rate. -/
theorem manuscriptRateExit_zero_of_lt {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real)
    (hbelow : ((intensity * s.rate : NNReal) : Real) < threshold) :
    manuscriptRateExit s intensity threshold = 0 := by
  unfold manuscriptRateExit
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hmin : sInf {rounds : Nat |
      ((intensity * s.rate / (2 : NNReal) ^ rounds : NNReal) : Real) <
        threshold} ≤ 0 := by
    apply Nat.sInf_le
    simpa using hbelow
  omega

theorem manuscriptRateThinningResult_of_below {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real)
    (hbelow : ((intensity * s.rate : NNReal) : Real) < threshold)
    (coins : Nat × Nat → Bool) :
    manuscriptRateThinningResult s intensity threshold coins = s := by
  simp [manuscriptRateThinningResult,
    manuscriptRateExit_zero_of_lt s intensity threshold hbelow,
    samplesAfter, survives]

/-- If the second while-loop passes a fixed dyadic level, the hypothetical
population at that level exceeds its threshold. -/
theorem manuscript_second_loop_crossing_implies_large_population
    {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (coins : Nat × Nat → Bool) (rounds : Nat)
    (hcross : rounds < firstExitRound s pending threshold coins) :
    threshold <
      (samplesAfter coins rounds s.samples).card +
        pendingAfter coins rounds s.nextLabel pending := by
  by_contra h
  have hexit : thinningExit s pending threshold coins rounds := by
    dsimp [thinningExit]
    exact le_of_not_gt h
  have hmin : firstExitRound s pending threshold coins ≤ rounds := by
    unfold firstExitRound
    exact Nat.sInf_le hexit
  omega

/-- Every first-loop result has a Poisson mean below the threshold. -/
theorem manuscriptRateThinningResult_guard {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold)
    (coins : Nat × Nat → Bool) :
    ((intensity * (manuscriptRateThinningResult s intensity threshold coins).rate :
      NNReal) : Real) < threshold := by
  simpa only [manuscriptRateThinningResult, mul_div_assoc] using
    manuscriptRateExit_guard s intensity hthreshold

theorem manuscriptRateExit_mono_intensity {n : Nat} (s : TTCState n)
    {small large : NNReal} (hsmall : small ≤ large)
    {threshold : Real} (hthreshold : 0 < threshold) :
    manuscriptRateExit s small threshold ≤
      manuscriptRateExit s large threshold := by
  have hlarge := manuscriptRateExit_guard s large hthreshold
  have hbound : small * s.rate /
      (2 : NNReal) ^ manuscriptRateExit s large threshold ≤
      large * s.rate /
      (2 : NNReal) ^ manuscriptRateExit s large threshold := by
    gcongr
  have hboundReal :
      ((small * s.rate /
        (2 : NNReal) ^ manuscriptRateExit s large threshold : NNReal) : Real) ≤
      ((large * s.rate /
        (2 : NNReal) ^ manuscriptRateExit s large threshold : NNReal) : Real) := by
    exact_mod_cast hbound
  unfold manuscriptRateExit
  exact Nat.sInf_le (hboundReal.trans_lt hlarge)

theorem manuscriptRateThinningCost_mono_intensity {n : Nat} (s : TTCState n)
    {small large : NNReal} (hsmall : small ≤ large)
    {threshold : Real} (hthreshold : 0 < threshold) :
    manuscriptRateThinningCost s small threshold ≤
      manuscriptRateThinningCost s large threshold := by
  unfold manuscriptRateThinningCost
  exact Nat.mul_le_mul_right _
    (manuscriptRateExit_mono_intensity s hsmall hthreshold)

/-- The first loop's number of halvings is logarithmic in its initial mean
relative to the threshold. -/
theorem manuscriptRateExit_le_clog {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold) :
    manuscriptRateExit s intensity threshold ≤
      Nat.clog 2 (Nat.ceil (((intensity * s.rate : NNReal) : Real) / threshold) + 1) := by
  let a : Real := (intensity * s.rate : NNReal)
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
      ((intensity * s.rate / (2 : NNReal) ^ Nat.clog 2 N : NNReal) : Real) <
        threshold := by
    have hratio : a / (2 : Real) ^ Nat.clog 2 N < threshold :=
      (div_lt_iff₀ hdenom).2 (by nlinarith)
    simpa only [a, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using hratio
  unfold manuscriptRateExit
  exact Nat.sInf_le hexit

theorem manuscriptRateThinningCost_le_clog {n : Nat} (s : TTCState n)
    (intensity : NNReal) {threshold : Real} (hthreshold : 0 < threshold) :
    manuscriptRateThinningCost s intensity threshold ≤
      Nat.clog 2 (Nat.ceil (((intensity * s.rate : NNReal) : Real) / threshold) + 1) *
        TTCRuntime.rateThinningRoundOperations s.samples.card := by
  unfold manuscriptRateThinningCost
  exact Nat.mul_le_mul_right _ (manuscriptRateExit_le_clog s intensity hthreshold)

/-- The charged second loop has precisely the program's uncharged state and
pending-count law. -/
theorem manuscriptCountThinWithCost_fst {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) :
    (manuscriptCountThinWithCost s pending threshold).map Prod.fst =
      thinUntil s pending threshold := by
  have hcost : Measurable (fun coins : Nat × Nat → Bool =>
      manuscriptCountThinningCost s pending threshold coins) := by
    unfold manuscriptCountThinningCost
    exact (measurable_of_countable
      (fun rounds : Nat => rounds *
        TTCRuntime.countThinningRoundOperations s.samples.card)).comp
          (measurable_firstExitRound s pending threshold)
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (thinningResult s pending threshold coins,
        manuscriptCountThinningCost s pending threshold coins)) :=
    (measurable_thinningResult s pending threshold).prodMk hcost
  unfold manuscriptCountThinWithCost thinUntil
  rw [MeasureTheory.Measure.map_map measurable_fst hpair]
  rfl

theorem manuscriptCountThinWithCost_mass_le_one {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) :
    (manuscriptCountThinWithCost s pending threshold) Set.univ ≤ 1 := by
  have hcost : Measurable (fun coins : Nat × Nat → Bool =>
      manuscriptCountThinningCost s pending threshold coins) := by
    unfold manuscriptCountThinningCost
    exact (measurable_of_countable
      (fun rounds : Nat => rounds *
        TTCRuntime.countThinningRoundOperations s.samples.card)).comp
          (measurable_firstExitRound s pending threshold)
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (thinningResult s pending threshold coins,
        manuscriptCountThinningCost s pending threshold coins)) :=
    (measurable_thinningResult s pending threshold).prodMk hcost
  unfold manuscriptCountThinWithCost
  rw [Measure.map_apply hpair MeasurableSet.univ]
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  simp

theorem manuscriptCountThinWithCost_isProbabilityMeasure {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real) :
    IsProbabilityMeasure (manuscriptCountThinWithCost s pending threshold) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  unfold manuscriptCountThinWithCost
  apply Measure.isProbabilityMeasure_map
  have hcost : Measurable (fun coins : Nat × Nat → Bool =>
      manuscriptCountThinningCost s pending threshold coins) := by
    unfold manuscriptCountThinningCost
    exact (measurable_of_countable
      (fun rounds : Nat => rounds *
        TTCRuntime.countThinningRoundOperations s.samples.card)).comp
          (measurable_firstExitRound s pending threshold)
  exact ((measurable_thinningResult s pending threshold).prodMk hcost).aemeasurable

end Kr25Ssmxt

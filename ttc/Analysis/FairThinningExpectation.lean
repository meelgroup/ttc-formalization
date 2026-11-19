import ttc.Analysis.FairCoinStreamLawIsProbabilityMeasure
import ttc.Analysis.MeasurableSetSurvives
import ttc.Analysis.MeasurableSurvivorCount
import ttc.Analysis.MeasurableFirstExitRound
import ttc.Analysis.NatTailExpectation
import ttc.Analysis.ThinningCosts
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Survival probabilities in the paper thinning loop

Each labelled copy survives a fixed number of fair rounds with probability
`2⁻ʳ`. This is the input to the second-loop expectation bound.
-/

namespace ttc

open MeasureTheory ProbabilityTheory Set
open Classical

theorem fairCoinLaw_true : fairCoinLaw {true} = (1 / 2 : ENNReal) := by
  have hprob : (fairProbability : Real) = 1 / 2 := by
    unfold fairProbability
    rw [Set.projIcc_of_mem zero_le_one
      (show (1 / 2 : Real) ∈ Set.Icc 0 1 by norm_num)]
  unfold fairCoinLaw
  rw [bernoulliMeasure_apply_of_mem_of_notMem fairProbability
    (by measurability) (by simp) (by simp)]
  have hnn : unitInterval.toNNReal fairProbability = (1 / 2 : NNReal) := by
    apply Subtype.ext
    simpa using hprob
  rw [hnn]
  norm_num

theorem fairCoinStreamLaw_survives (rounds label : Nat) :
    fairCoinStreamLaw {coins | survives coins rounds label} =
      (1 / 2 : ENNReal) ^ rounds := by
  have hprobAll : ∀ _ : Nat × Nat, IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  let s : Finset (Nat × Nat) := (Finset.range rounds).image fun r => (r, label)
  have hs : {coins : Nat × Nat → Bool | survives coins rounds label} =
      Set.pi (s : Set (Nat × Nat)) (fun _ => {true}) := by
    ext coins
    simp [survives, s, Set.mem_pi]
  rw [hs, fairCoinStreamLaw]
  rw [Measure.infinitePi_pi (hμ := hprobAll) (μ := fun _ : Nat × Nat => fairCoinLaw)
    (s := s) (by intros; measurability)]
  simp only [fairCoinLaw_true, Finset.prod_const]
  have hcard : s.card = rounds := by
    unfold s
    rw [Finset.card_image_of_injective]
    · simp
    · intro x y h
      exact congrArg Prod.fst h
  simp [hcard]

/-- Linearity of expectation for finitely many labelled copies; labels need
not be distinct. -/
theorem expected_survivor_card {α : Type*} [DecidableEq α]
    (copies : Finset α) (label : α → Nat) (rounds : Nat) :
    ∫⁻ coins, (((copies.filter fun a => survives coins rounds (label a)).card : Nat) : ENNReal)
        ∂fairCoinStreamLaw =
      copies.card * (1 / 2 : ENNReal) ^ rounds := by
  classical
  induction copies using Finset.induction_on with
  | empty => simp
  | @insert a copies ha ih =>
      have hset : MeasurableSet
          {coins : Nat × Nat → Bool | survives coins rounds (label a)} :=
        measurableSet_survives rounds (label a)
      have hindicator :
          (∫⁻ coins, (if survives coins rounds (label a) then (1 : ENNReal) else 0)
              ∂fairCoinStreamLaw) = (1 / 2 : ENNReal) ^ rounds := by
        have hfun : (fun coins : Nat × Nat → Bool =>
            if survives coins rounds (label a) then (1 : ENNReal) else 0) =
            Set.indicator {coins | survives coins rounds (label a)} 1 := by
          funext coins
          by_cases h : survives coins rounds (label a) <;> simp [h, Set.indicator]
        rw [hfun, lintegral_indicator_one hset, fairCoinStreamLaw_survives]
      have hrewrite :
          (∫⁻ coins, (((((insert a copies).filter
            fun x => survives coins rounds (label x)).card : Nat) : ENNReal))
              ∂fairCoinStreamLaw) =
          (∫⁻ coins, ((if survives coins rounds (label a) then (1 : ENNReal) else 0) +
            ((((copies.filter fun x => survives coins rounds (label x)).card : Nat) :
              ENNReal))) ∂fairCoinStreamLaw) := by
        apply lintegral_congr
        intro coins
        rw [Finset.filter_insert]
        by_cases h : survives coins rounds (label a) <;>
          simp [h, ha, Finset.card_insert_of_notMem, add_comm]
      rw [hrewrite]
      rw [lintegral_add_left (Measurable.ite hset measurable_const measurable_const),
        hindicator, ih]
      simp only [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      ring

/-- Expected retained copies after a fixed number of thinning rounds. -/
theorem expected_samplesAfter_card {n : Nat}
    (samples : Finset (SampleCopy n)) (rounds : Nat) :
    ∫⁻ coins, ((samplesAfter coins rounds samples).card : ENNReal)
        ∂fairCoinStreamLaw =
      samples.card * (1 / 2 : ENNReal) ^ rounds := by
  classical
  simpa [samplesAfter] using expected_survivor_card samples Prod.fst rounds

/-- Expected pending copies after a fixed number of thinning rounds. -/
theorem expected_pendingAfter (firstLabel count rounds : Nat) :
    ∫⁻ coins, (pendingAfter coins rounds firstLabel count : ENNReal)
        ∂fairCoinStreamLaw =
      count * (1 / 2 : ENNReal) ^ rounds := by
  classical
  simpa [pendingAfter] using
    expected_survivor_card (Finset.range count) (fun i => firstLabel + i) rounds

/-- Expected combined retained and pending population at a fixed round. -/
theorem expected_thinning_population {n : Nat} (s : TTCState n)
    (pending rounds : Nat) :
    ∫⁻ coins, (((samplesAfter coins rounds s.X).card +
        pendingAfter coins rounds s.nextLabel pending : Nat) : ENNReal)
        ∂fairCoinStreamLaw =
      (s.X.card + pending : ENNReal) * (1 / 2 : ENNReal) ^ rounds := by
  have hmeas : Measurable (fun coins : Nat × Nat → Bool =>
      ((samplesAfter coins rounds s.X).card : ENNReal)) := by
    exact (measurable_of_countable (fun q : Nat => (q : ENNReal))).comp
      (by simpa [samplesAfter] using
        measurable_survivorCount s.X (fun copy => copy.1) rounds)
  simp only [Nat.cast_add]
  rw [lintegral_add_left hmeas, expected_samplesAfter_card,
    expected_pendingAfter]
  rw [← add_mul]

/-- A fixed-round tail bound for the population that controls the second
thinning guard. -/
theorem thinning_population_tail {n : Nat} (s : TTCState n)
    (pending rounds cutoff : Nat) (hcutoff : 0 < cutoff) :
    fairCoinStreamLaw {coins | cutoff ≤
      (samplesAfter coins rounds s.X).card +
        pendingAfter coins rounds s.nextLabel pending} ≤
      ((s.X.card + pending : ENNReal) * (1 / 2 : ENNReal) ^ rounds) /
        cutoff := by
  let f : (Nat × Nat → Bool) → ENNReal := fun coins =>
    (((samplesAfter coins rounds s.X).card +
      pendingAfter coins rounds s.nextLabel pending : Nat) : ENNReal)
  have hsample : Measurable (fun coins : Nat × Nat → Bool =>
      (samplesAfter coins rounds s.X).card) := by
    simpa [samplesAfter] using
      measurable_survivorCount s.X (fun copy => copy.1) rounds
  have hpending : Measurable (fun coins : Nat × Nat → Bool =>
      pendingAfter coins rounds s.nextLabel pending) := by
    simpa [pendingAfter] using
      measurable_survivorCount (Finset.range pending)
        (fun i => s.nextLabel + i) rounds
  have hf : Measurable f := by
    exact (measurable_of_countable (fun q : Nat => (q : ENNReal))).comp
      (hsample.add hpending)
  have hmarkov := meas_ge_le_lintegral_div (μ := fairCoinStreamLaw)
    hf.aemeasurable (show (cutoff : ENNReal) ≠ 0 by exact_mod_cast hcutoff.ne')
    (by simp : (cutoff : ENNReal) ≠ ⊤)
  change fairCoinStreamLaw {coins | (cutoff : ENNReal) ≤ f coins} ≤
    (∫⁻ coins, f coins ∂fairCoinStreamLaw) / cutoff at hmarkov
  rw [show (∫⁻ coins, f coins ∂fairCoinStreamLaw) =
      (s.X.card + pending : ENNReal) * (1 / 2 : ENNReal) ^ rounds from
    expected_thinning_population s pending rounds] at hmarkov
  have hset : {coins | cutoff ≤
      (samplesAfter coins rounds s.X).card +
        pendingAfter coins rounds s.nextLabel pending} =
      {coins | (cutoff : ENNReal) ≤ f coins} := by
    ext coins
    simp only [Set.mem_ofPred_eq, f]
    norm_cast
  rw [hset]
  exact hmarkov

/-- A tail bound for the actual first-exit round. Any integer cutoff strictly
above the real guard threshold may be used. -/
theorem firstExitRound_tail {n : Nat} (s : TTCState n)
    (pending rounds cutoff : Nat) (threshold : Real)
    (hcutoff : 0 < cutoff)
    (hthreshold : ∀ q : Nat, q < cutoff → (q : Real) ≤ threshold) :
    fairCoinStreamLaw {coins | rounds < ttcPseudocode.secondLoopExitRound s pending threshold coins} ≤
      ((s.X.card + pending : ENNReal) * (1 / 2 : ENNReal) ^ rounds) /
        cutoff := by
  have hsubset :
      {coins | rounds < ttcPseudocode.secondLoopExitRound s pending threshold coins} ⊆
      {coins | cutoff ≤ (samplesAfter coins rounds s.X).card +
        pendingAfter coins rounds s.nextLabel pending} := by
    intro coins hcoins
    by_contra hsmall
    have hsmall' : (samplesAfter coins rounds s.X).card +
        pendingAfter coins rounds s.nextLabel pending < cutoff :=
      Nat.lt_of_not_ge hsmall
    have hexit : ttcPseudocode.secondLoopExit s pending threshold coins rounds := by
      unfold ttcPseudocode.secondLoopExit
      simpa only [Nat.cast_add] using hthreshold _ hsmall'
    have hround : ttcPseudocode.secondLoopExitRound s pending threshold coins ≤ rounds := by
      unfold ttcPseudocode.secondLoopExitRound
      exact Nat.sInf_le hexit
    exact (not_le_of_gt hcoins) hround
  exact (measure_mono hsubset).trans
    (thinning_population_tail s pending rounds cutoff hcutoff)

/-- The cutoff in the exit-round tail can be selected directly from the
real paper threshold. -/
theorem firstExitRound_tail_floor {n : Nat} (s : TTCState n)
    (pending rounds : Nat) (threshold : Real) (hthreshold : 0 ≤ threshold) :
    fairCoinStreamLaw {coins | rounds < ttcPseudocode.secondLoopExitRound s pending threshold coins} ≤
      ((s.X.card + pending : ENNReal) * (1 / 2 : ENNReal) ^ rounds) /
        (Nat.floor threshold + 1) := by
  have htail := firstExitRound_tail s pending rounds (Nat.floor threshold + 1)
    threshold (Nat.succ_pos _) (by
      intro q hq
      have hle : q ≤ Nat.floor threshold := Nat.lt_succ_iff.mp hq
      exact (Nat.cast_le.mpr hle).trans (Nat.floor_le hthreshold))
  simpa only [Nat.cast_add, Nat.cast_one] using htail

/-- The second-loop exit counter has finite expectation, with a bound linear
in its entry population divided by the integer guard cutoff. -/
theorem expected_firstExitRound_le {n : Nat} (s : TTCState n)
    (pending cutoff : Nat) (threshold : Real) (hcutoff : 0 < cutoff)
    (hthreshold : ∀ q : Nat, q < cutoff → (q : Real) ≤ threshold) :
    ∫⁻ coins, (ttcPseudocode.secondLoopExitRound s pending threshold coins : ENNReal)
        ∂fairCoinStreamLaw ≤
      2 * ((s.X.card + pending : ENNReal) / cutoff) := by
  rw [lintegral_nat_eq_tsum_tail fairCoinStreamLaw
    (ttcPseudocode.secondLoopExitRound s pending threshold)
    (measurable_firstExitRound s pending threshold)]
  calc
    (∑' rounds : Nat, fairCoinStreamLaw
        {coins | rounds < ttcPseudocode.secondLoopExitRound s pending threshold coins}) ≤
        ∑' rounds : Nat,
          ((s.X.card + pending : ENNReal) *
            (1 / 2 : ENNReal) ^ rounds) / cutoff := by
      exact ENNReal.tsum_le_tsum (fun rounds =>
        firstExitRound_tail s pending rounds cutoff threshold hcutoff hthreshold)
    _ = ((s.X.card + pending : ENNReal) / cutoff) *
        (∑' rounds : Nat, (1 / 2 : ENNReal) ^ rounds) := by
      have hterm (rounds : Nat) :
          ((s.X.card + pending : ENNReal) *
            (1 / 2 : ENNReal) ^ rounds) / cutoff =
          ((s.X.card + pending : ENNReal) / cutoff) *
            (1 / 2 : ENNReal) ^ rounds := by
        simp only [div_eq_mul_inv]
        ac_rfl
      simp_rw [hterm]
      exact ENNReal.tsum_mul_left
    _ = 2 * ((s.X.card + pending : ENNReal) / cutoff) := by
      rw [ENNReal.tsum_geometric]
      norm_num
      ac_rfl

theorem expected_firstExitRound_le_floor {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (hthreshold : 0 ≤ threshold) :
    ∫⁻ coins, (ttcPseudocode.secondLoopExitRound s pending threshold coins : ENNReal)
        ∂fairCoinStreamLaw ≤
      2 * ((s.X.card + pending : ENNReal) / (Nat.floor threshold + 1)) := by
  have hbound := expected_firstExitRound_le s pending
    (Nat.floor threshold + 1) threshold (Nat.succ_pos _) (by
      intro q hq
      exact (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hq)).trans
        (Nat.floor_le hthreshold))
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

/-- Exact mean charge of the count-thinning law. -/
theorem countThinWithCost_expected_eq {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) :
    ∫⁻ result, (result.2 : ENNReal) ∂
        ttcPseudocode.secondLoopWithCost s pending threshold =
      (TTCRuntime.countThinningRoundOperations s.X.card : ENNReal) *
        (∫⁻ coins, (ttcPseudocode.secondLoopExitRound s pending threshold coins : ENNReal)
          ∂fairCoinStreamLaw) := by
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
  rw [lintegral_map (by fun_prop) hpair]
  simp only [ttcPseudocode.secondLoopCost, Nat.cast_mul]
  have hmeas : Measurable (fun coins : Nat × Nat → Bool =>
      (ttcPseudocode.secondLoopExitRound s pending threshold coins : ENNReal)) :=
    (measurable_of_countable (fun q : Nat => (q : ENNReal))).comp
      (measurable_firstExitRound s pending threshold)
  rw [lintegral_mul_const
    (TTCRuntime.countThinningRoundOperations s.X.card : ENNReal) hmeas]
  rw [mul_comm (∫⁻ coins, (ttcPseudocode.secondLoopExitRound s pending threshold coins : ENNReal)
    ∂fairCoinStreamLaw)]

/-- The charged count-thinning law inherits the finite first-exit mean. -/
theorem countThinWithCost_expected_le {n : Nat} (s : TTCState n)
    (pending cutoff : Nat) (threshold : Real) (hcutoff : 0 < cutoff)
    (hthreshold : ∀ q : Nat, q < cutoff → (q : Real) ≤ threshold) :
    ∫⁻ result, (result.2 : ENNReal) ∂
        ttcPseudocode.secondLoopWithCost s pending threshold ≤
      (TTCRuntime.countThinningRoundOperations s.X.card : ENNReal) *
        (2 * ((s.X.card + pending : ENNReal) / cutoff)) := by
  rw [countThinWithCost_expected_eq]
  exact mul_le_mul_of_nonneg_left
    (expected_firstExitRound_le s pending cutoff threshold hcutoff hthreshold)
    (by positivity)

/-- Every finite thinning population exits the paper guard almost
surely. This removes the `sInf ∅ = 0` totalization branch from analysis. -/
theorem never_thinningExit_null {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (hthreshold : 0 ≤ threshold) :
    fairCoinStreamLaw {coins | ∀ rounds,
      ¬ ttcPseudocode.secondLoopExit s pending threshold coins rounds} = 0 := by
  let never : Set (Nat × Nat → Bool) :=
    {coins | ∀ rounds, ¬ ttcPseudocode.secondLoopExit s pending threshold coins rounds}
  have hbound (rounds : Nat) : fairCoinStreamLaw never ≤
      ((s.X.card + pending : NNReal) : ENNReal) *
        (1 / 2 : ENNReal) ^ rounds := by
    have hsubset : never ⊆ {coins | 1 ≤
        (samplesAfter coins rounds s.X).card +
          pendingAfter coins rounds s.nextLabel pending} := by
      intro coins hcoins
      have hnot := hcoins rounds
      have hpos : 0 < (samplesAfter coins rounds s.X).card +
          pendingAfter coins rounds s.nextLabel pending := by
        by_contra h
        have hz : (samplesAfter coins rounds s.X).card +
            pendingAfter coins rounds s.nextLabel pending = 0 := Nat.eq_zero_of_not_pos h
        apply hnot
        unfold ttcPseudocode.secondLoopExit
        simpa only [← Nat.cast_add, hz, Nat.cast_zero] using hthreshold
      exact hpos
    have ht := (measure_mono hsubset).trans
      (thinning_population_tail s pending rounds 1 (by omega))
    simpa using ht
  change fairCoinStreamLaw never = 0
  exact ENNReal.eq_zero_of_le_mul_pow (by norm_num : (1 / 2 : ENNReal) < 1)
    hbound

/-- The totalized first-exit counter satisfies its guard almost surely. -/
theorem firstExitRound_guard_ae {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (hthreshold : 0 ≤ threshold) :
    ∀ᵐ coins ∂fairCoinStreamLaw,
      ttcPseudocode.secondLoopExit s pending threshold coins
        (ttcPseudocode.secondLoopExitRound s pending threshold coins) := by
  rw [ae_iff]
  apply measure_mono_null ?_ (never_thinningExit_null s pending threshold hthreshold)
  intro coins hbad
  intro rounds hexit
  have hs : ({r : Nat | ttcPseudocode.secondLoopExit s pending threshold coins r}).Nonempty :=
    ⟨rounds, hexit⟩
  have hleast : ttcPseudocode.secondLoopExit s pending threshold coins
      (ttcPseudocode.secondLoopExitRound s pending threshold coins) := by
    unfold ttcPseudocode.secondLoopExitRound
    exact Nat.sInf_mem hs
  exact hbad hleast

/-- Appending a batch cannot create more stored copies than its length. -/
theorem TTCState.addBatch_card_le {n count : Nat} (s : TTCState n)
    (points : Fin count → LatticePoint n) :
    (s.addBatch points).X.card ≤ s.X.card + count := by
  classical
  unfold TTCState.addBatch
  dsimp
  apply (Finset.card_union_le _ _).trans
  have hadded : (Finset.univ.image
      (fun i : Fin count => (s.nextLabel + i.val, points i))).card ≤ count := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin count)))
      (f := fun i => (s.nextLabel + i.val, points i)))
  exact Nat.add_le_add_left hadded _

/-- The uncharged thinning law exits with no more than the guard's population
almost surely. -/
theorem thinUntil_population_le_ae {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (hthreshold : 0 ≤ threshold) :
    ∀ᵐ result ∂ttcPseudocode.secondLoop s pending threshold,
      ((result.1.X.card + result.2 : Nat) : Real) ≤ threshold := by
  have hmap : Measurable (ttcPseudocode.secondLoopResult s pending threshold) :=
    measurable_thinningResult s pending threshold
  have hset : MeasurableSet {result : TTCState n × Nat |
      ((result.1.X.card + result.2 : Nat) : Real) ≤ threshold} := by
    have hcoords : Measurable (fun state : TTCState n =>
        (state.p, state.X, state.nextLabel)) := comap_measurable _
    have hsamples : Measurable (fun result : TTCState n × Nat =>
        result.1.X) :=
      ((measurable_fst.comp measurable_snd).comp hcoords).comp measurable_fst
    have hcard : Measurable (fun result : TTCState n × Nat =>
        result.1.X.card) :=
      (measurable_of_countable (fun copies : Finset (SampleCopy n) => copies.card)).comp
        hsamples
    have htotal : Measurable (fun result : TTCState n × Nat =>
        result.1.X.card + result.2) := hcard.add measurable_snd
    exact ((measurable_of_countable (fun q : Nat => (q : Real))).comp htotal)
      measurableSet_Iic
  unfold ttcPseudocode.secondLoop
  rw [ae_map_iff hmap.aemeasurable hset]
  filter_upwards [firstExitRound_guard_ae s pending threshold hthreshold] with coins hcoins
  simpa only [ttcPseudocode.secondLoopResult, Nat.cast_add, ttcPseudocode.secondLoopExit] using hcoins

/-- Forgetting the charged round count transports the same exit guard to the
result law used by the runtime program. -/
theorem countThinWithCost_population_le_ae {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (hthreshold : 0 ≤ threshold) :
    ∀ᵐ result ∂ttcPseudocode.secondLoopWithCost s pending threshold,
      ((result.1.1.X.card + result.1.2 : Nat) : Real) ≤ threshold := by
  have hset : MeasurableSet {result : TTCState n × Nat |
      ((result.1.X.card + result.2 : Nat) : Real) ≤ threshold} := by
    have hcoords : Measurable (fun state : TTCState n =>
        (state.p, state.X, state.nextLabel)) := comap_measurable _
    have hsamples : Measurable (fun result : TTCState n × Nat =>
        result.1.X) :=
      ((measurable_fst.comp measurable_snd).comp hcoords).comp measurable_fst
    have hcard : Measurable (fun result : TTCState n × Nat =>
        result.1.X.card) :=
      (measurable_of_countable (fun copies : Finset (SampleCopy n) => copies.card)).comp
        hsamples
    have htotal : Measurable (fun result : TTCState n × Nat =>
        result.1.X.card + result.2) := hcard.add measurable_snd
    exact ((measurable_of_countable (fun q : Nat => (q : Real))).comp htotal)
      measurableSet_Iic
  have hbase := thinUntil_population_le_ae s pending threshold hthreshold
  rw [← countThinWithCost_fst s pending threshold] at hbase
  exact (ae_map_iff measurable_fst.aemeasurable hset).mp hbase

/-- Any batch requested after a successful second-loop guard leaves the
stored population below the same threshold. -/
theorem thinningResult_addBatch_card_le {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (coins : Nat × Nat → Bool)
    (hguard : ttcPseudocode.secondLoopExit s pending threshold coins
      (ttcPseudocode.secondLoopExitRound s pending threshold coins))
    (points : Fin (ttcPseudocode.secondLoopResult s pending threshold coins).2 → LatticePoint n) :
    (((ttcPseudocode.secondLoopResult s pending threshold coins).1.addBatch points).X.card : Real) ≤
      threshold := by
  have hcard := TTCState.addBatch_card_le
    (ttcPseudocode.secondLoopResult s pending threshold coins).1 points
  have hguard' : ((ttcPseudocode.secondLoopResult s pending threshold coins).1.X.card +
      (ttcPseudocode.secondLoopResult s pending threshold coins).2 : Nat) ≤
      threshold := by
    simpa [ttcPseudocode.secondLoopResult, ttcPseudocode.secondLoopExit, Nat.cast_add] using hguard
  exact (Nat.cast_le.mpr hcard).trans hguard'

theorem TTCState.removeComponent_card_le {n : Nat} (s : TTCState n)
    (P : PolytopeData n) :
    (s.removeComponent P).X.card ≤ s.X.card := by
  classical
  unfold TTCState.removeComponent
  dsimp
  exact Finset.card_filter_le _ _

theorem deletionPassOperations_le {n : Nat} (s : TTCState n)
    (P : PolytopeData n) :
    TTCRuntime.deletionPassOperations n P.presentation.facetCount
      s.X.card (s.X.card - (s.removeComponent P).X.card) ≤
      s.X.card * (TTCRuntime.facetScanOperations n
        P.presentation.facetCount + 1) := by
  unfold TTCRuntime.deletionPassOperations TTCRuntime.deleteCopyOperations
  have hremove : s.X.card - (s.removeComponent P).X.card ≤
      s.X.card := Nat.sub_le _ _
  simp only [Nat.mul_add, mul_one]
  omega

theorem rateThinningResult_card_le {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) (coins : Nat × Nat → Bool) :
    (ttcReference.firstLoopResult s intensity threshold coins).X.card ≤
      s.X.card := by
  dsimp only [ttcReference.firstLoopResult]
  unfold samplesAfter
  exact Finset.card_filter_le _ _

end ttc

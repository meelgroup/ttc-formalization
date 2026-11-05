import Kr25Ssmxt.Analysis.ManuscriptCoinSpliceLaw

/-! The observed initial rounds and untouched future rounds of an IID fair
coin stream are independent. The prefix is padded by false coins. -/

namespace Kr25Ssmxt

open MeasureTheory

def coinPrefix (rounds : Nat) (coins : Nat × Nat → Bool) :
    Nat × Nat → Bool :=
  fun index => if index.1 < rounds then coins index else false

theorem measurable_coinPrefix (rounds : Nat) :
    Measurable (coinPrefix rounds) := by
  apply measurable_pi_lambda
  intro index
  by_cases h : index.1 < rounds
  · simpa only [coinPrefix, h, ite_true] using measurable_pi_apply index
  · simpa only [coinPrefix, h, ite_false] using
      (measurable_const : Measurable
        (fun _ : Nat × Nat → Bool => false))

theorem coinPrefix_spliceCoins (rounds : Nat)
    (first future : Nat × Nat → Bool) :
    coinPrefix rounds (spliceCoins first future rounds) =
      coinPrefix rounds first := by
  funext index
  by_cases h : index.1 < rounds <;>
    simp [coinPrefix, spliceCoins, h]

theorem survives_coinPrefix_iff (rounds upto label : Nat)
    (hupto : upto ≤ rounds) (coins : Nat × Nat → Bool) :
    survives (coinPrefix rounds coins) upto label ↔
      survives coins upto label := by
  unfold survives
  constructor
  · intro h r hr
    have hbound : r < rounds := lt_of_lt_of_le hr hupto
    simpa [coinPrefix, hbound] using h r hr
  · intro h r hr
    have hbound : r < rounds := lt_of_lt_of_le hr hupto
    simpa [coinPrefix, hbound] using h r hr

theorem samplesAfter_coinPrefix {n : Nat}
    (s : TTCState n) (rounds upto : Nat) (hupto : upto ≤ rounds)
    (coins : Nat × Nat → Bool) :
    samplesAfter (coinPrefix rounds coins) upto s.samples =
      samplesAfter coins upto s.samples := by
  classical
  ext copy
  simp only [samplesAfter, Finset.mem_filter]
  exact and_congr_right (fun _ =>
    survives_coinPrefix_iff rounds upto copy.1 hupto coins)

theorem pendingAfter_coinPrefix
    (rounds upto firstLabel count : Nat) (hupto : upto ≤ rounds)
    (coins : Nat × Nat → Bool) :
    pendingAfter (coinPrefix rounds coins) upto firstLabel count =
      pendingAfter coins upto firstLabel count := by
  classical
  unfold pendingAfter
  congr 1
  ext i
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ =>
    survives_coinPrefix_iff rounds upto (firstLabel + i) hupto coins)

theorem thinningExit_coinPrefix_iff {n : Nat}
    (s : TTCState n) (pending rounds upto : Nat)
    (hupto : upto ≤ rounds) (threshold : Real)
    (coins : Nat × Nat → Bool) :
    thinningExit s pending threshold (coinPrefix rounds coins) upto ↔
      thinningExit s pending threshold coins upto := by
  simp only [thinningExit,
    samplesAfter_coinPrefix s rounds upto hupto coins,
    pendingAfter_coinPrefix rounds upto s.nextLabel pending hupto coins]

/-- At a fixed absolute level, all already observed fair coins are
independent of the shifted future fair stream. -/
theorem fairCoinStreamLaw_prefix_shift (rounds : Nat) :
    fairCoinStreamLaw.map
      (fun coins => (coinPrefix rounds coins, shiftCoins rounds coins)) =
    (fairCoinStreamLaw.map (coinPrefix rounds)).prod fairCoinStreamLaw := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let split : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun coins => (coinPrefix rounds coins, shiftCoins rounds coins)
  have hsplit : Measurable split :=
    (measurable_coinPrefix rounds).prodMk
      (measurable_pi_lambda _ (fun index =>
        measurable_pi_apply (index.1 + rounds, index.2)))
  have hfun : split ∘
      (fun pair : (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
        spliceCoins pair.1 pair.2 rounds) =
      Prod.map (coinPrefix rounds) id := by
    funext pair
    exact Prod.ext
      (coinPrefix_spliceCoins rounds pair.1 pair.2)
      (shiftCoins_spliceCoins pair.1 pair.2 rounds)
  calc
    fairCoinStreamLaw.map split =
        ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
          (fun pair => spliceCoins pair.1 pair.2 rounds)).map split := by
            rw [fairCoinStreamLaw_splice rounds]
    _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (split ∘ (fun pair => spliceCoins pair.1 pair.2 rounds)) := by
          rw [Measure.map_map hsplit (measurable_spliceCoins_pair rounds)]
    _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (Prod.map (coinPrefix rounds) id) := by rw [hfun]
    _ = (fairCoinStreamLaw.map (coinPrefix rounds)).prod
        fairCoinStreamLaw := by
          simpa only [Measure.map_id] using
            (Measure.map_prod_map fairCoinStreamLaw fairCoinStreamLaw
              (measurable_coinPrefix rounds) measurable_id).symm

theorem fairCoinStreamLaw_prefix_shift_indep
    (rounds : Nat) (A B : Set (Nat × Nat → Bool))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    fairCoinStreamLaw
      ((coinPrefix rounds) ⁻¹' A ∩ (shiftCoins rounds) ⁻¹' B) =
    fairCoinStreamLaw ((coinPrefix rounds) ⁻¹' A) *
      fairCoinStreamLaw B := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let split : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun coins => (coinPrefix rounds coins, shiftCoins rounds coins)
  have hsplit : Measurable split :=
    (measurable_coinPrefix rounds).prodMk
      (measurable_pi_lambda _ (fun index =>
        measurable_pi_apply (index.1 + rounds, index.2)))
  have hpreimage : split ⁻¹' (A ×ˢ B) =
      (coinPrefix rounds) ⁻¹' A ∩ (shiftCoins rounds) ⁻¹' B := by
    ext coins
    rfl
  calc
    fairCoinStreamLaw
        ((coinPrefix rounds) ⁻¹' A ∩ (shiftCoins rounds) ⁻¹' B) =
      (fairCoinStreamLaw.map split) (A ×ˢ B) := by
        rw [← hpreimage, Measure.map_apply hsplit (hA.prod hB)]
    _ = ((fairCoinStreamLaw.map (coinPrefix rounds)).prod
        fairCoinStreamLaw) (A ×ˢ B) := by
          rw [fairCoinStreamLaw_prefix_shift rounds]
    _ = (fairCoinStreamLaw.map (coinPrefix rounds)) A *
        fairCoinStreamLaw B := Measure.prod_prod A B
    _ = fairCoinStreamLaw ((coinPrefix rounds) ⁻¹' A) *
        fairCoinStreamLaw B := by
          rw [Measure.map_apply (measurable_coinPrefix rounds) hA]

/-- Each event that a coin-driven stopping rule ends at round `r` must be
decidable from the first `r` rounds. This is the exact information needed to
reuse the untouched fair tail after stopping. -/
def CoinPrefixStoppingRule (stop : (Nat × Nat → Bool) → Nat) : Prop :=
  ∀ rounds, ∃ A : Set (Nat × Nat → Bool), MeasurableSet A ∧
    {coins | stop coins = rounds} = (coinPrefix rounds) ⁻¹' A

theorem CoinPrefixStoppingRule.event_shift_indep
    (stop : (Nat × Nat → Bool) → Nat)
    (hstop : CoinPrefixStoppingRule stop)
    (rounds : Nat) (B : Set (Nat × Nat → Bool))
    (hB : MeasurableSet B) :
    fairCoinStreamLaw
      ({coins | stop coins = rounds} ∩ (shiftCoins rounds) ⁻¹' B) =
    fairCoinStreamLaw {coins | stop coins = rounds} *
      fairCoinStreamLaw B := by
  obtain ⟨A, hA, hEq⟩ := hstop rounds
  rw [hEq]
  exact fairCoinStreamLaw_prefix_shift_indep rounds A B hA hB

end Kr25Ssmxt

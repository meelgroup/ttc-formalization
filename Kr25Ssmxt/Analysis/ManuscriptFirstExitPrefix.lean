import Kr25Ssmxt.Analysis.ManuscriptCoinPrefixLaw
import Kr25Ssmxt.Analysis.FairThinningExpectation

/-! The manuscript's first-exit round is determined by observed fair-coin
prefixes, except on the null nontermination event introduced by `sInf ∅`. -/

namespace Kr25Ssmxt

open MeasureTheory

def firstExitPrefixEvent {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) : Nat → Set (Nat × Nat → Bool)
  | 0 => {coins | thinningExit s pending threshold coins 0}
  | k + 1 => {coins | thinningExit s pending threshold coins (k + 1) ∧
      ¬ thinningExit s pending threshold coins k}

theorem measurableSet_firstExitPrefixEvent {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (rounds : Nat) :
    MeasurableSet (firstExitPrefixEvent s pending threshold rounds) := by
  cases rounds with
  | zero => exact measurableSet_thinningExit s pending threshold 0
  | succ k =>
      exact (measurableSet_thinningExit s pending threshold (k + 1)).inter
        (measurableSet_thinningExit s pending threshold k).compl

theorem firstExitPrefixEvent_preimage {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (rounds : Nat) :
    (coinPrefix rounds) ⁻¹'
      (firstExitPrefixEvent s pending threshold rounds) =
      firstExitPrefixEvent s pending threshold rounds := by
  ext coins
  cases rounds with
  | zero =>
      exact thinningExit_coinPrefix_iff s pending 0 0 (le_refl 0)
        threshold coins
  | succ k =>
      exact and_congr
        (thinningExit_coinPrefix_iff s pending (k + 1) (k + 1)
          (le_refl _) threshold coins)
        (not_congr (thinningExit_coinPrefix_iff s pending (k + 1) k
          (by omega) threshold coins))

theorem firstExitRound_eq_prefix_event_ae {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) (rounds : Nat) :
    ∀ᵐ coins ∂fairCoinStreamLaw,
      (firstExitRound s pending threshold coins = rounds ↔
        coins ∈ firstExitPrefixEvent s pending threshold rounds) := by
  filter_upwards [firstExitRound_guard_ae s pending threshold hthreshold]
    with coins hguard
  cases rounds with
  | zero =>
      change firstExitRound s pending threshold coins = 0 ↔
        thinningExit s pending threshold coins 0
      constructor
      · intro hzero
        simpa [hzero] using hguard
      · intro hexit
        unfold firstExitRound
        rw [Nat.sInf_eq_zero]
        exact Or.inl hexit
  | succ k =>
      change firstExitRound s pending threshold coins = k + 1 ↔
        thinningExit s pending threshold coins (k + 1) ∧
          ¬ thinningExit s pending threshold coins k
      have hup : ∀ r₁ r₂ : Nat, r₁ ≤ r₂ →
          r₁ ∈ {r | thinningExit s pending threshold coins r} →
          r₂ ∈ {r | thinningExit s pending threshold coins r} := by
        intro r₁ r₂ hr hexit
        exact thinningExit_mono_rounds s pending threshold coins hr hexit
      exact Nat.sInf_upward_closed_eq_succ_iff hup k

/-- At the actual first-exit round, the unused fair tail is independent of
the event that the loop stopped at that round. The exceptional nonterminating
streams have zero measure. -/
theorem firstExitRound_event_shift_indep {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) (rounds : Nat)
    (B : Set (Nat × Nat → Bool)) (hB : MeasurableSet B) :
    fairCoinStreamLaw
      ({coins | firstExitRound s pending threshold coins = rounds} ∩
        (shiftCoins rounds) ⁻¹' B) =
    fairCoinStreamLaw
      {coins | firstExitRound s pending threshold coins = rounds} *
      fairCoinStreamLaw B := by
  let A := firstExitPrefixEvent s pending threshold rounds
  have hA : MeasurableSet A :=
    measurableSet_firstExitPrefixEvent s pending threshold rounds
  have hae := firstExitRound_eq_prefix_event_ae s pending threshold
    hthreshold rounds
  have hmeasure : fairCoinStreamLaw
      {coins | firstExitRound s pending threshold coins = rounds} =
      fairCoinStreamLaw A := by
    apply measure_congr
    filter_upwards [hae] with coins hcoins
    exact propext hcoins
  calc
    fairCoinStreamLaw
        ({coins | firstExitRound s pending threshold coins = rounds} ∩
          (shiftCoins rounds) ⁻¹' B) =
      fairCoinStreamLaw (A ∩ (shiftCoins rounds) ⁻¹' B) := by
        apply measure_congr
        filter_upwards [hae] with coins hcoins
        exact propext (and_congr hcoins Iff.rfl)
    _ = fairCoinStreamLaw ((coinPrefix rounds) ⁻¹' A ∩
        (shiftCoins rounds) ⁻¹' B) := by
          rw [firstExitPrefixEvent_preimage]
    _ = fairCoinStreamLaw ((coinPrefix rounds) ⁻¹' A) *
        fairCoinStreamLaw B :=
          fairCoinStreamLaw_prefix_shift_indep rounds A B hA hB
    _ = fairCoinStreamLaw
        {coins | firstExitRound s pending threshold coins = rounds} *
          fairCoinStreamLaw B := by
            rw [firstExitPrefixEvent_preimage, ← hmeasure]

end Kr25Ssmxt

import Kr25Ssmxt.Analysis.ManuscriptAdvanceBatchObserved

/-! Pathwise reconstruction of the second-loop stopped observation from the
observation itself, and gluing of a global source prefix to its tail. -/

namespace Kr25Ssmxt

open MeasureTheory

/-- Use `pre` on the first `rounds` relative rounds and the shifted `post`
afterwards. -/
def manuscriptGlobalSourceGlue (rounds : Nat)
    (pre post : Nat × (Nat × Nat) → Bool) :
    Nat × (Nat × Nat) → Bool :=
  fun tag => if tag.2.1 < rounds then pre tag
    else post (tag.1, (tag.2.1 - rounds, tag.2.2))

theorem manuscriptGlobalSourcePrefix_glue (rounds : Nat)
    (pre post : Nat × (Nat × Nat) → Bool) :
    manuscriptGlobalSourcePrefix rounds
        (manuscriptGlobalSourceGlue rounds pre post) =
      manuscriptGlobalSourcePrefix rounds pre := by
  funext tag
  by_cases h : tag.2.1 < rounds <;>
    simp [manuscriptGlobalSourcePrefix, manuscriptGlobalSourceGlue, h]

theorem manuscriptGlobalSourceShift_glue (rounds : Nat)
    (pre post : Nat × (Nat × Nat) → Bool) :
    manuscriptGlobalSourceShift rounds
        (manuscriptGlobalSourceGlue rounds pre post) = post := by
  funext tag
  have hnot : ¬ tag.2.1 + rounds < rounds := by omega
  simp [manuscriptGlobalSourceShift, manuscriptGlobalSourceGlue, hnot]

theorem manuscriptGlobalSourceGlue_prefix_shift (rounds : Nat)
    (source : Nat × (Nat × Nat) → Bool) :
    manuscriptGlobalSourceGlue rounds
        (manuscriptGlobalSourcePrefix rounds source)
        (manuscriptGlobalSourceShift rounds source) = source := by
  funext tag
  by_cases h : tag.2.1 < rounds
  · simp [manuscriptGlobalSourcePrefix, manuscriptGlobalSourceGlue, h]
  · have hadd : tag.2.1 - rounds + rounds = tag.2.1 := by omega
    simp [manuscriptGlobalSourceShift, manuscriptGlobalSourceGlue, h, hadd]

theorem measurable_manuscriptGlobalSourceGlue (rounds : Nat) :
    Measurable (fun z : (Nat × (Nat × Nat) → Bool) ×
        (Nat × (Nat × Nat) → Bool) =>
      manuscriptGlobalSourceGlue rounds z.1 z.2) := by
  apply Measurable.of_eval
  intro tag
  by_cases h : tag.2.1 < rounds
  · simp only [manuscriptGlobalSourceGlue, h, if_true]
    exact (measurable_pi_apply tag).comp measurable_fst
  · simp only [manuscriptGlobalSourceGlue, h, if_false]
    exact (measurable_pi_apply (tag.1, (tag.2.1 - rounds, tag.2.2))).comp
        measurable_snd

theorem manuscriptGlobalSourcePrefix_idem (rounds : Nat)
    (source : Nat × (Nat × Nat) → Bool) :
    manuscriptGlobalSourcePrefix rounds
        (manuscriptGlobalSourcePrefix rounds source) =
      manuscriptGlobalSourcePrefix rounds source := by
  funext tag
  by_cases h : tag.2.1 < rounds <;>
    simp [manuscriptGlobalSourcePrefix, h]

theorem coinPrefix_idem (rounds : Nat) (coins : Nat × Nat → Bool) :
    coinPrefix rounds (coinPrefix rounds coins) = coinPrefix rounds coins := by
  funext pair
  by_cases h : pair.1 < rounds <;> simp [coinPrefix, h]

/-- On a terminating stream, the first exit round is determined by the coins
observed strictly before it. -/
theorem firstExitRound_eq_of_prefix_eq {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (coins other : Nat × Nat → Bool)
    (hexit : ttcPseudocode.secondLoopExit s pending threshold coins
      (ttcPseudocode.secondLoopExitRound s pending threshold coins))
    (hprefix : coinPrefix (ttcPseudocode.secondLoopExitRound s pending threshold coins) other =
      coinPrefix (ttcPseudocode.secondLoopExitRound s pending threshold coins) coins) :
    ttcPseudocode.secondLoopExitRound s pending threshold other =
      ttcPseudocode.secondLoopExitRound s pending threshold coins := by
  let k := ttcPseudocode.secondLoopExitRound s pending threshold coins
  have hiff : ∀ r ≤ k, ttcPseudocode.secondLoopExit s pending threshold other r ↔
      ttcPseudocode.secondLoopExit s pending threshold coins r := by
    intro r hr
    rw [← thinningExit_coinPrefix_iff s pending k r hr threshold other,
      ← thinningExit_coinPrefix_iff s pending k r hr threshold coins]
    rw [hprefix]
  have hexitOther : ttcPseudocode.secondLoopExit s pending threshold other k :=
    (hiff k le_rfl).2 hexit
  have hle : ttcPseudocode.secondLoopExitRound s pending threshold other ≤ k :=
    Nat.sInf_le hexitOther
  have hmem : ttcPseudocode.secondLoopExit s pending threshold other
      (ttcPseudocode.secondLoopExitRound s pending threshold other) :=
    Nat.sInf_mem (s := {r | ttcPseudocode.secondLoopExit s pending threshold other r})
      ⟨k, hexitOther⟩
  have hge : k ≤ ttcPseudocode.secondLoopExitRound s pending threshold other :=
    Nat.sInf_le ((hiff _ hle).1 hmem)
  exact le_antisymm hle hge

/-- The stopped observation, evaluated on its own observed prefixes, returns
itself whenever the loop terminated at the recorded round. -/
theorem manuscriptSurvivorPairFullObservation_reconstruct
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat)
    (y : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))
    (hexit : ttcPseudocode.secondLoopExit s
      (pendingAfter preCoins preRounds s.nextLabel basePending) threshold
      (manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
        basePending origin y)
      (manuscriptSurvivorPairStop s threshold preCoins preRounds
        basePending origin y)) :
    manuscriptSurvivorPairFullObservation s threshold preCoins preRounds
        basePending origin
        (manuscriptSurvivorPairFullObservation s threshold preCoins
          preRounds basePending origin y).2 =
      manuscriptSurvivorPairFullObservation s threshold preCoins preRounds
        basePending origin y := by
  let k := manuscriptSurvivorPairStop s threshold preCoins preRounds
    basePending origin y
  let o : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) :=
    (manuscriptGlobalSourcePrefix k y.1, coinPrefix k y.2)
  have ho : (manuscriptSurvivorPairFullObservation s threshold preCoins
      preRounds basePending origin y).2 = o := rfl
  have hread := manuscriptSurvivorPairRead_prefix_eq_of_fullPrefixes
    preCoins preRounds s.nextLabel basePending origin o y k
    (manuscriptGlobalSourcePrefix_idem k y.1) (coinPrefix_idem k y.2)
  have hstop : manuscriptSurvivorPairStop s threshold preCoins preRounds
      basePending origin o = k :=
    firstExitRound_eq_of_prefix_eq s
      (pendingAfter preCoins preRounds s.nextLabel basePending) threshold
      (manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
        basePending origin y)
      (manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
        basePending origin o) hexit hread
  rw [ho]
  change (manuscriptSurvivorPairStop s threshold preCoins preRounds
      basePending origin o,
    (manuscriptGlobalSourcePrefix
      (manuscriptSurvivorPairStop s threshold preCoins preRounds
        basePending origin o) o.1,
      coinPrefix (manuscriptSurvivorPairStop s threshold preCoins preRounds
        basePending origin o) o.2)) =
    (k, (manuscriptGlobalSourcePrefix k y.1, coinPrefix k y.2))
  rw [hstop]
  simp only [o, manuscriptGlobalSourcePrefix_idem, coinPrefix_idem]

end Kr25Ssmxt

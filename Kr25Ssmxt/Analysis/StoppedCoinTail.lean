import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.FirstExitPrefix
import Kr25Ssmxt.Analysis.CoinLabelMergeLaw

/-! A fair-coin tail after the paper's almost surely finite thinning
stopping round is independent of the stopped round itself. -/

namespace Kr25Ssmxt

open MeasureTheory Function

theorem measurable_stoppedCoinPair
    (stop : (Nat × Nat → Bool) → Nat) (hstop : Measurable stop) :
    Measurable (fun coins => (stop coins, shiftCoins (stop coins) coins)) := by
  have hshiftJoint : Measurable
      (fun z : Nat × (Nat × Nat → Bool) => shiftCoins z.1 z.2) := by
    apply Measurable.of_eval
    intro index
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_pi_apply (index.1 + rounds, index.2)
  exact hstop.prodMk (hshiftJoint.comp (hstop.prodMk measurable_id))

theorem fairCoinStreamLaw_stopped_shift
    (stop : (Nat × Nat → Bool) → Nat)
    (hstop : Measurable stop)
    (hindep : ∀ (rounds : Nat) (B : Set (Nat × Nat → Bool)),
      MeasurableSet B →
      fairCoinStreamLaw
        ({coins | stop coins = rounds} ∩ (shiftCoins rounds) ⁻¹' B) =
      fairCoinStreamLaw {coins | stop coins = rounds} *
        fairCoinStreamLaw B) :
    fairCoinStreamLaw.map
      (fun coins => (stop coins, shiftCoins (stop coins) coins)) =
    (fairCoinStreamLaw.map stop).prod fairCoinStreamLaw := by
  classical
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let shiftAt : (Nat × Nat → Bool) → Nat × Nat → Bool :=
    fun coins => shiftCoins (stop coins) coins
  let output : (Nat × Nat → Bool) →
      Nat × (Nat × Nat → Bool) := fun coins => (stop coins, shiftAt coins)
  have houtput : Measurable output :=
    measurable_stoppedCoinPair stop hstop
  letI : IsProbabilityMeasure (fairCoinStreamLaw.map output) :=
    Measure.isProbabilityMeasure_map houtput.aemeasurable
  apply Measure.ext_prod
  intro A B hA hB
  let fiber (rounds : Nat) : Set (Nat × Nat → Bool) :=
    {coins | stop coins = rounds}
  let F (rounds : Nat) : Set (Nat × Nat → Bool) :=
    if rounds ∈ A then fiber rounds else ∅
  let E (rounds : Nat) : Set (Nat × Nat → Bool) :=
    if rounds ∈ A then fiber rounds ∩ (shiftCoins rounds) ⁻¹' B else ∅
  have hshift (rounds : Nat) : Measurable (shiftCoins rounds) :=
    Measurable.of_eval (fun index =>
      measurable_pi_apply (index.1 + rounds, index.2))
  have hfiber (rounds : Nat) : MeasurableSet (fiber rounds) :=
    (measurableSet_singleton rounds).preimage hstop
  have hF (rounds : Nat) : MeasurableSet (F rounds) := by
    by_cases hr : rounds ∈ A <;> simp [F, hr, hfiber rounds]
  have hE (rounds : Nat) : MeasurableSet (E rounds) := by
    by_cases hr : rounds ∈ A
    · simpa [E, hr] using (hfiber rounds).inter
        (hB.preimage (hshift rounds))
    · simp [E, hr]
  have hdisjF : Pairwise (Disjoint on F) := by
    intro r q hrq
    apply Set.disjoint_left.mpr
    intro coins hfr hfq
    by_cases hra : r ∈ A <;> by_cases hqa : q ∈ A
    · have hr : stop coins = r := by simpa [F, hra, fiber] using hfr
      have hq : stop coins = q := by simpa [F, hqa, fiber] using hfq
      exact hrq (hr.symm.trans hq)
    all_goals simp [F, *] at hfr hfq
  have hdisjE : Pairwise (Disjoint on E) := by
    intro r q hrq
    apply Set.disjoint_left.mpr
    intro coins her heq
    have hfr : coins ∈ F r := by
      by_cases hra : r ∈ A <;> simp_all [E, F]
    have hfq : coins ∈ F q := by
      by_cases hqa : q ∈ A <;> simp_all [E, F]
    exact Set.disjoint_left.mp (hdisjF hrq) hfr hfq
  have hF_union : (⋃ rounds, F rounds) = stop ⁻¹' A := by
    ext coins
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨r, hr⟩
      by_cases hra : r ∈ A
      · have heq : stop coins = r := by simpa [F, hra, fiber] using hr
        exact heq ▸ hra
      · simp [F, hra] at hr
    · intro hAstop
      refine ⟨stop coins, ?_⟩
      simp [F, hAstop, fiber]
  have hE_union : (⋃ rounds, E rounds) = output ⁻¹' (A ×ˢ B) := by
    ext coins
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_prod]
    constructor
    · rintro ⟨r, hr⟩
      by_cases hra : r ∈ A
      · have hp : stop coins = r ∧ shiftCoins r coins ∈ B := by
          simpa [E, hra, fiber] using hr
        change stop coins ∈ A ∧
          shiftCoins (stop coins) coins ∈ B
        rw [hp.1]
        exact ⟨hra, hp.2⟩
      · simp [E, hra] at hr
    · rintro ⟨ha, hb⟩
      refine ⟨stop coins, ?_⟩
      simp [E, ha, fiber, output, shiftAt] at hb ⊢
      exact hb
  have hterm (rounds : Nat) :
      fairCoinStreamLaw (E rounds) =
        fairCoinStreamLaw (F rounds) * fairCoinStreamLaw B := by
    by_cases hr : rounds ∈ A
    · simp only [E, F, if_pos hr]
      exact hindep rounds B hB
    · simp [E, F, hr]
  have hF_measure : fairCoinStreamLaw (stop ⁻¹' A) =
      ∑' rounds, fairCoinStreamLaw (F rounds) := by
    rw [← hF_union]
    exact measure_iUnion hdisjF hF
  have hE_measure : fairCoinStreamLaw (output ⁻¹' (A ×ˢ B)) =
      ∑' rounds, fairCoinStreamLaw (E rounds) := by
    rw [← hE_union]
    exact measure_iUnion hdisjE hE
  rw [Measure.map_apply houtput (hA.prod hB), hE_measure]
  rw [Measure.prod_prod, Measure.map_apply hstop hA, hF_measure]
  simp_rw [hterm]
  simp only [mul_comm (fairCoinStreamLaw (F _)) (fairCoinStreamLaw B)]
  rw [ENNReal.tsum_mul_left, mul_comm]

/-- The unused coin stream after the actual first-exit thinning loop is
fair and independent of the number of rounds spent in the loop. -/
theorem firstExitRound_shift_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) :
    fairCoinStreamLaw.map
      (fun coins => (ttcPseudocode.secondLoopExitRound s pending threshold coins,
        shiftCoins (ttcPseudocode.secondLoopExitRound s pending threshold coins) coins)) =
    (fairCoinStreamLaw.map (ttcPseudocode.secondLoopExitRound s pending threshold)).prod
      fairCoinStreamLaw := by
  exact fairCoinStreamLaw_stopped_shift
    (ttcPseudocode.secondLoopExitRound s pending threshold)
    (measurable_firstExitRound s pending threshold)
    (fun rounds B hB => firstExitRound_event_shift_indep s pending
      threshold hthreshold rounds B hB)

theorem firstExitRoundSplit_merged_shift_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) (hfresh : s.LabelsFresh) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair =>
        let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
        (rounds, shiftCoins rounds
          (mergeCoinsAtLabel s.nextLabel pair.1 pair.2))) =
    ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair => firstExitRoundSplit s pending threshold pair.1 pair.2)).prod
      fairCoinStreamLaw := by
  let merge : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × Nat → Bool := fun pair =>
    mergeCoinsAtLabel s.nextLabel pair.1 pair.2
  have hmerge : Measurable merge :=
    measurable_mergeCoinsAtLabel_pair s.nextLabel
  have hstop : Measurable (ttcPseudocode.secondLoopExitRound s pending threshold) :=
    measurable_firstExitRound s pending threshold
  have hpath (pair : (Nat × Nat → Bool) × (Nat × Nat → Bool)) :
      firstExitRoundSplit s pending threshold pair.1 pair.2 =
      ttcPseudocode.secondLoopExitRound s pending threshold (merge pair) :=
    (firstExitRound_mergeCoinsAtLabel s pending threshold pair.1
      pair.2 hfresh).symm
  have hpair : Measurable (fun coins =>
      (ttcPseudocode.secondLoopExitRound s pending threshold coins,
        shiftCoins (ttcPseudocode.secondLoopExitRound s pending threshold coins) coins)) :=
    measurable_stoppedCoinPair _ hstop
  calc
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair =>
          let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
          (rounds, shiftCoins rounds (merge pair))) =
      (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        ((fun coins => (ttcPseudocode.secondLoopExitRound s pending threshold coins,
          shiftCoins (ttcPseudocode.secondLoopExitRound s pending threshold coins) coins)) ∘
            merge) := by
              congr 1
              funext pair
              simp only [Function.comp_apply]
              rw [← hpath pair]
    _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map merge).map
        (fun coins => (ttcPseudocode.secondLoopExitRound s pending threshold coins,
          shiftCoins (ttcPseudocode.secondLoopExitRound s pending threshold coins) coins)) := by
            rw [Measure.map_map hpair hmerge]
    _ = fairCoinStreamLaw.map
        (fun coins => (ttcPseudocode.secondLoopExitRound s pending threshold coins,
          shiftCoins (ttcPseudocode.secondLoopExitRound s pending threshold coins) coins)) := by
            rw [fairCoinStreamLaw_mergeLabels s.nextLabel]
    _ = (fairCoinStreamLaw.map
        (ttcPseudocode.secondLoopExitRound s pending threshold)).prod fairCoinStreamLaw :=
          firstExitRound_shift_law s pending threshold hthreshold
    _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => firstExitRoundSplit s pending threshold pair.1 pair.2)).prod
          fairCoinStreamLaw := by
            have hstopMap : (fairCoinStreamLaw.prod fairCoinStreamLaw).map
                (fun pair => firstExitRoundSplit s pending threshold pair.1
                  pair.2) =
                fairCoinStreamLaw.map
                  (ttcPseudocode.secondLoopExitRound s pending threshold) := by
              calc
                _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map
                    ((ttcPseudocode.secondLoopExitRound s pending threshold) ∘ merge) := by
                      congr 1
                      funext pair
                      exact hpath pair
                _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map merge).map
                    (ttcPseudocode.secondLoopExitRound s pending threshold) := by
                      rw [Measure.map_map hstop hmerge]
                _ = _ := by rw [fairCoinStreamLaw_mergeLabels s.nextLabel]
            rw [hstopMap]

end Kr25Ssmxt

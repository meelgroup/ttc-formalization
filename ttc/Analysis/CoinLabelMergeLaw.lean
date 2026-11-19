import ttc.Analysis.CoinSpliceLaw
import ttc.Analysis.TwoLoopCoinLaw
import ttc.Analysis.CoinRelabelLaw
import ttc.Analysis.AbsoluteCoinStream

/-! Independent first-round coin arrays for old and newly drawn copies can
be merged along the fresh-label boundary into one fair array. -/

namespace ttc

open MeasureTheory

def mergeCoinsAtLabel (boundary : Nat)
    (old fresh : Nat × Nat → Bool) : Nat × Nat → Bool :=
  fun pair => if pair.2 < boundary then old pair else fresh pair

def mergeCoinIndex (boundary : Nat) (pair : Nat × Nat) :
    Fin 2 × (Nat × Nat) :=
  (if pair.2 < boundary then 0 else 1, pair)

theorem mergeCoinIndex_injective (boundary : Nat) :
    Function.Injective (mergeCoinIndex boundary) := by
  intro a b hab
  exact congrArg (fun pair : Fin 2 × (Nat × Nat) => pair.2) hab

theorem measurable_mergeCoinsAtLabel_pair (boundary : Nat) :
    Measurable (fun pair : (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      mergeCoinsAtLabel boundary pair.1 pair.2) := by
  apply Measurable.of_eval
  intro index
  by_cases h : index.2 < boundary
  · simpa only [mergeCoinsAtLabel, h, ite_true, Function.comp_def] using
      (measurable_pi_apply index).comp measurable_fst
  · simpa only [mergeCoinsAtLabel, h, ite_false, Function.comp_def] using
      (measurable_pi_apply index).comp measurable_snd

theorem fairCoinStreamLaw_mergeLabels (boundary : Nat) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair => mergeCoinsAtLabel boundary pair.1 pair.2) =
    fairCoinStreamLaw := by
  let global : Measure (Fin 2 × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : ∀ _ : Fin 2 × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hpair : global.map (fun coins =>
      ((fun pair => coins (0, pair)), fun pair => coins (1, pair))) =
      fairCoinStreamLaw.prod fairCoinStreamLaw := by
    have hcurry := Measure.infinitePi_map_curry
      (μ := fun _ : Fin 2 => fun _ : Nat × Nat => fairCoinLaw)
      (hμ := fun _ _ => fairCoinLaw_isProbabilityMeasure)
    have hcurry' : global.map
        (MeasurableEquiv.curry (Fin 2) (Nat × Nat) Bool) =
        Measure.infinitePi (fun _ : Fin 2 => fairCoinStreamLaw) := by
      simpa [global, fairCoinStreamLaw] using hcurry
    have htwo :
        (Measure.infinitePi (fun _ : Fin 2 => fairCoinStreamLaw)).map
          MeasurableEquiv.finTwoArrow =
        fairCoinStreamLaw.prod fairCoinStreamLaw := by
      rw [Measure.infinitePi_eq_pi]
      exact (measurePreserving_finTwoArrow fairCoinStreamLaw).map_eq
    calc
      global.map (fun coins =>
          ((fun pair => coins (0, pair)), fun pair => coins (1, pair))) =
        (global.map (MeasurableEquiv.curry (Fin 2) (Nat × Nat) Bool)).map
          MeasurableEquiv.finTwoArrow := by
            rw [Measure.map_map
              (MeasurableEquiv.finTwoArrow.measurable)
              (MeasurableEquiv.curry (Fin 2) (Nat × Nat) Bool).measurable]
            congr 1
      _ = _ := by rw [hcurry', htwo]
  rw [← hpair]
  have hmeas : Measurable
      (fun coins : Fin 2 × (Nat × Nat) → Bool =>
        ((fun pair => coins (0, pair)), fun pair => coins (1, pair))) := by
    fun_prop
  rw [Measure.map_map (measurable_mergeCoinsAtLabel_pair boundary) hmeas]
  have hfun :
      ((fun pair : (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
        mergeCoinsAtLabel boundary pair.1 pair.2) ∘
        (fun coins : Fin 2 × (Nat × Nat) → Bool =>
          ((fun pair => coins (0, pair)), fun pair => coins (1, pair)))) =
      (fun coins pair => coins (mergeCoinIndex boundary pair)) := by
    funext coins pair
    by_cases h : pair.2 < boundary <;>
      simp [mergeCoinsAtLabel, mergeCoinIndex, h]
  rw [hfun]
  change global.map (fun coins pair => coins (mergeCoinIndex boundary pair)) =
    fairCoinStreamLaw
  exact @Measure.map_infinitePi_infinitePi_of_inj
    (Fin 2 × (Nat × Nat)) (Nat × Nat) (fun _ => Bool)
    (fun _ => inferInstance) (fun _ => fairCoinLaw)
    (fun _ => fairCoinLaw_isProbabilityMeasure)
    (mergeCoinIndex boundary) (mergeCoinIndex_injective boundary)

theorem survives_mergeCoins_old
    (boundary rounds label : Nat) (hlabel : label < boundary)
    (old fresh : Nat × Nat → Bool) :
    survives (mergeCoinsAtLabel boundary old fresh) rounds label ↔
      survives old rounds label := by
  simp [survives, mergeCoinsAtLabel, hlabel]

theorem survives_mergeCoins_fresh
    (boundary rounds label : Nat) (hlabel : boundary ≤ label)
    (old fresh : Nat × Nat → Bool) :
    survives (mergeCoinsAtLabel boundary old fresh) rounds label ↔
      survives fresh rounds label := by
  have hnot : ¬ label < boundary := by omega
  simp [survives, mergeCoinsAtLabel, hnot]

theorem samplesAfter_mergeCoins_old
    {n : Nat} (s : TTCState n) (rounds : Nat)
    (old fresh : Nat × Nat → Bool) (hfresh : s.LabelsFresh) :
    samplesAfter (mergeCoinsAtLabel s.nextLabel old fresh) rounds s.X =
      samplesAfter old rounds s.X := by
  classical
  ext copy
  by_cases hc : copy ∈ s.X
  · simp only [samplesAfter, Finset.mem_filter, hc, true_and]
    exact survives_mergeCoins_old s.nextLabel rounds copy.1
      (hfresh.1 copy hc) old fresh
  · simp [samplesAfter, hc]

theorem rateThinningResult_mergeCoinsAtLabel
    {n : Nat} (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (old fresh : Nat × Nat → Bool) (hfresh : s.LabelsFresh) :
    ttcReference.firstLoopResult s intensity threshold
      (mergeCoinsAtLabel s.nextLabel old fresh) =
    ttcReference.firstLoopResult s intensity threshold old := by
  simp only [ttcReference.firstLoopResult,
    samplesAfter_mergeCoins_old s _ old fresh hfresh]

theorem shiftCoins_mergeCoinsAtLabel (boundary rounds : Nat)
    (old fresh : Nat × Nat → Bool) :
    shiftCoins rounds (mergeCoinsAtLabel boundary old fresh) =
    mergeCoinsAtLabel boundary (shiftCoins rounds old)
      (shiftCoins rounds fresh) := by
  funext pair
  simp only [shiftCoins, mergeCoinsAtLabel]

theorem pendingAfter_mergeCoins_fresh
    (boundary firstLabel pending rounds : Nat)
    (hfirst : boundary ≤ firstLabel)
    (old fresh : Nat × Nat → Bool) :
    pendingAfter (mergeCoinsAtLabel boundary old fresh)
      rounds firstLabel pending =
      pendingAfter fresh rounds firstLabel pending := by
  classical
  unfold pendingAfter
  congr 1
  ext i
  by_cases hi : i ∈ Finset.range pending
  · simp only [Finset.mem_filter, hi, true_and]
    exact survives_mergeCoins_fresh boundary rounds (firstLabel + i)
      (by omega) old fresh
  · simp [hi]

theorem pendingAfter_fresh_coins_congr
    (firstLabel pending rounds : Nat)
    (fresh fresh' : Nat × Nat → Bool)
    (hcoins : ∀ r i, i < pending →
      fresh (r, firstLabel + i) = fresh' (r, firstLabel + i)) :
    pendingAfter fresh rounds firstLabel pending =
      pendingAfter fresh' rounds firstLabel pending := by
  classical
  unfold pendingAfter
  congr 1
  ext i
  by_cases hi : i < pending
  · simp only [Finset.mem_filter, Finset.mem_range, hi, true_and]
    unfold survives
    constructor
    · intro h r hr
      rw [← hcoins r i hi]
      exact h r hr
    · intro h r hr
      rw [hcoins r i hi]
      exact h r hr
  · simp [hi]

def pendingCoinRestriction (firstLabel pending : Nat)
    (coins : Nat × Nat → Bool) : Nat × Fin pending → Bool :=
  fun pair => coins (pair.1, firstLabel + pair.2.val)

theorem measurable_pendingCoinRestriction (firstLabel pending : Nat) :
    Measurable (pendingCoinRestriction firstLabel pending) := by
  apply Measurable.of_eval
  intro pair
  exact measurable_pi_apply (pair.1, firstLabel + pair.2.val)

theorem fairCoinStreamLaw_pendingCoinRestriction
    (firstLabel pending : Nat) :
    fairCoinStreamLaw.map (pendingCoinRestriction firstLabel pending) =
      Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw) := by
  have hinj : Function.Injective (fun i : Fin pending => firstLabel + i.val) := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel hij)
  exact fairCoinStreamLaw_reindex_labels
    (fun i : Fin pending => firstLabel + i.val) hinj

theorem fairCoinStreamLaw_shift_pendingCoinRestriction
    (firstLabel pending rounds : Nat) :
    fairCoinStreamLaw.map
      (fun coins => pendingCoinRestriction firstLabel pending
        (shiftCoins rounds coins)) =
      Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw) := by
  calc
    fairCoinStreamLaw.map
        (fun coins => pendingCoinRestriction firstLabel pending
          (shiftCoins rounds coins)) =
      (fairCoinStreamLaw.map (shiftCoins rounds)).map
        (pendingCoinRestriction firstLabel pending) := by
          exact (Measure.map_map
            (measurable_pendingCoinRestriction firstLabel pending)
            (measurable_shiftCoins rounds)).symm
    _ = _ := by
      rw [fairCoinStreamLaw_shift rounds,
        fairCoinStreamLaw_pendingCoinRestriction firstLabel pending]

theorem fairCoinStreamLaw_pair_pendingCoinRestriction
    (firstLabel pending : Nat) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair => (pair.1,
        pendingCoinRestriction firstLabel pending pair.2)) =
    fairCoinStreamLaw.prod
      (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  calc
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => (pair.1,
          pendingCoinRestriction firstLabel pending pair.2)) =
      (fairCoinStreamLaw.map id).prod
        (fairCoinStreamLaw.map (pendingCoinRestriction firstLabel pending)) := by
          exact (Measure.map_prod_map fairCoinStreamLaw fairCoinStreamLaw
            measurable_id (measurable_pendingCoinRestriction firstLabel pending)).symm
    _ = _ := by
      rw [Measure.map_id,
        fairCoinStreamLaw_pendingCoinRestriction firstLabel pending]

theorem fairCoinStreamLaw_pair_shift_pendingCoinRestriction
    (firstLabel pending rounds : Nat) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair => (pair.1,
        pendingCoinRestriction firstLabel pending
          (shiftCoins rounds pair.2))) =
    fairCoinStreamLaw.prod
      (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  calc
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => (pair.1,
          pendingCoinRestriction firstLabel pending
            (shiftCoins rounds pair.2))) =
      (fairCoinStreamLaw.map id).prod
        (fairCoinStreamLaw.map (fun coins =>
          pendingCoinRestriction firstLabel pending
            (shiftCoins rounds coins))) := by
          exact (Measure.map_prod_map fairCoinStreamLaw fairCoinStreamLaw
            measurable_id
            ((measurable_pendingCoinRestriction firstLabel pending).comp
              (measurable_shiftCoins rounds))).symm
    _ = _ := by
      rw [Measure.map_id,
        fairCoinStreamLaw_shift_pendingCoinRestriction firstLabel pending rounds]

def pendingCoinExtension (firstLabel pending : Nat)
    (coins : Nat × Fin pending → Bool) : Nat × Nat → Bool :=
  fun pair => if h : firstLabel ≤ pair.2 ∧ pair.2 < firstLabel + pending then
    coins (pair.1, ⟨pair.2 - firstLabel, by omega⟩)
  else true

theorem measurable_pendingCoinExtension (firstLabel pending : Nat) :
    Measurable (pendingCoinExtension firstLabel pending) := by
  apply Measurable.of_eval
  intro pair
  by_cases h : firstLabel ≤ pair.2 ∧ pair.2 < firstLabel + pending
  · simpa [pendingCoinExtension, h] using
      (measurable_pi_apply
        (pair.1, (⟨pair.2 - firstLabel, by omega⟩ : Fin pending)))
  · simp only [pendingCoinExtension, h, dite_false]
    exact measurable_const

theorem pendingCoinExtension_at (firstLabel pending r i : Nat)
    (hi : i < pending) (coins : Nat × Fin pending → Bool) :
    pendingCoinExtension firstLabel pending coins (r, firstLabel + i) =
      coins (r, ⟨i, hi⟩) := by
  simp [pendingCoinExtension, hi]

theorem pendingCoinExtension_restriction (firstLabel pending : Nat)
    (coins : Nat × Nat → Bool) (r i : Nat) (hi : i < pending) :
    pendingCoinExtension firstLabel pending
      (pendingCoinRestriction firstLabel pending coins)
      (r, firstLabel + i) = coins (r, firstLabel + i) := by
  rw [pendingCoinExtension_at firstLabel pending r i hi]
  rfl

/-- The thinning loop with separated coin arrays for stored and pending copies. -/
noncomputable def firstExitRoundSplit {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (old fresh : Nat × Nat → Bool) : Nat :=
  sInf {rounds | (samplesAfter old rounds s.X).card +
    pendingAfter fresh rounds s.nextLabel pending ≤ threshold}

theorem firstExitRoundSplit_fresh_coins_congr {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (old fresh fresh' : Nat × Nat → Bool)
    (hcoins : ∀ r i, i < pending →
      fresh (r, s.nextLabel + i) = fresh' (r, s.nextLabel + i)) :
    firstExitRoundSplit s pending threshold old fresh =
      firstExitRoundSplit s pending threshold old fresh' := by
  simp only [firstExitRoundSplit,
    pendingAfter_fresh_coins_congr s.nextLabel pending _ fresh fresh' hcoins]

theorem firstExitRound_mergeCoinsAtLabel {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (old fresh : Nat × Nat → Bool)
    (hfresh : s.LabelsFresh) :
    ttcPseudocode.secondLoopExitRound s pending threshold
      (mergeCoinsAtLabel s.nextLabel old fresh) =
    firstExitRoundSplit s pending threshold old fresh := by
  simp only [ttcPseudocode.secondLoopExitRound, firstExitRoundSplit, ttcPseudocode.secondLoopExit,
    samplesAfter_mergeCoins_old s _ old fresh hfresh,
    pendingAfter_mergeCoins_fresh s.nextLabel s.nextLabel pending _
      (le_refl _) old fresh]

/-- The result of a thinning loop, using the two separated coin arrays. -/
noncomputable def thinningResultSplit {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (old fresh : Nat × Nat → Bool) : TTCState n × Nat :=
  let rounds := firstExitRoundSplit s pending threshold old fresh
  ({ p := s.p / (2 : NNReal) ^ rounds
     X := samplesAfter old rounds s.X
     nextLabel := s.nextLabel },
   pendingAfter fresh rounds s.nextLabel pending)

theorem thinningResultSplit_fresh_coins_congr {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (old fresh fresh' : Nat × Nat → Bool)
    (hcoins : ∀ r i, i < pending →
      fresh (r, s.nextLabel + i) = fresh' (r, s.nextLabel + i)) :
    thinningResultSplit s pending threshold old fresh =
      thinningResultSplit s pending threshold old fresh' := by
  simp only [thinningResultSplit,
    firstExitRoundSplit_fresh_coins_congr s pending threshold old fresh fresh'
      hcoins,
    pendingAfter_fresh_coins_congr s.nextLabel pending _ fresh fresh' hcoins]

/-- The finite pending label block is the entire fresh-coin input to the
second loop. -/
noncomputable def thinningResultSplitFinite {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (old : Nat × Nat → Bool) (fresh : Nat × Fin pending → Bool) :
    TTCState n × Nat :=
  thinningResultSplit s pending threshold old
    (pendingCoinExtension s.nextLabel pending fresh)

theorem thinningResultSplit_eq_finite {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (old fresh : Nat × Nat → Bool) :
    thinningResultSplit s pending threshold old fresh =
    thinningResultSplitFinite s pending threshold old
      (pendingCoinRestriction s.nextLabel pending fresh) := by
  unfold thinningResultSplitFinite
  apply thinningResultSplit_fresh_coins_congr
  intro r i hi
  exact (pendingCoinExtension_restriction s.nextLabel pending fresh r i hi).symm

theorem measurable_thinningResultSplitFinite_pair {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hfresh : s.LabelsFresh) :
    Measurable (fun pair : (Nat × Nat → Bool) ×
        (Nat × Fin pending → Bool) =>
      thinningResultSplitFinite s pending threshold pair.1 pair.2) := by
  have hmerge : Measurable (fun pair : (Nat × Nat → Bool) ×
      (Nat × Fin pending → Bool) =>
      mergeCoinsAtLabel s.nextLabel pair.1
        (pendingCoinExtension s.nextLabel pending pair.2)) :=
    (measurable_mergeCoinsAtLabel_pair s.nextLabel).comp
      (measurable_fst.prodMk
        ((measurable_pendingCoinExtension s.nextLabel pending).comp
          measurable_snd))
  have heq : (fun pair : (Nat × Nat → Bool) ×
      (Nat × Fin pending → Bool) =>
      thinningResultSplitFinite s pending threshold pair.1 pair.2) =
      (fun pair => ttcPseudocode.secondLoopResult s pending threshold
        (mergeCoinsAtLabel s.nextLabel pair.1
          (pendingCoinExtension s.nextLabel pending pair.2))) := by
    funext pair
    simp only [thinningResultSplitFinite, thinningResultSplit,
      ttcPseudocode.secondLoopResult, firstExitRound_mergeCoinsAtLabel s pending threshold
        pair.1 (pendingCoinExtension s.nextLabel pending pair.2) hfresh,
      samplesAfter_mergeCoins_old s _ pair.1
        (pendingCoinExtension s.nextLabel pending pair.2) hfresh,
      pendingAfter_mergeCoins_fresh s.nextLabel s.nextLabel pending _
        (le_refl _) pair.1
        (pendingCoinExtension s.nextLabel pending pair.2)]
  rw [heq]
  exact (measurable_thinningResult s pending threshold).comp hmerge

/-- The loop's new-copy randomness is exactly a finite-label fair array. -/
theorem thinUntil_split_finite_coin_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hfresh : s.LabelsFresh) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair => thinningResultSplit s pending threshold pair.1 pair.2) =
    (fairCoinStreamLaw.prod
      (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).map
        (fun pair => thinningResultSplitFinite s pending threshold
          pair.1 pair.2) := by
  let project : (Nat × Nat → Bool) × (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Fin pending → Bool) :=
    fun pair => (pair.1,
      pendingCoinRestriction s.nextLabel pending pair.2)
  let result : (Nat × Nat → Bool) × (Nat × Fin pending → Bool) →
      TTCState n × Nat :=
    fun pair => thinningResultSplitFinite s pending threshold pair.1 pair.2
  have hproject : Measurable project :=
    measurable_fst.prodMk
      ((measurable_pendingCoinRestriction s.nextLabel pending).comp
        measurable_snd)
  have hresult : Measurable result :=
    measurable_thinningResultSplitFinite_pair s pending threshold hfresh
  calc
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => thinningResultSplit s pending threshold pair.1 pair.2) =
      (fairCoinStreamLaw.prod fairCoinStreamLaw).map (result ∘ project) := by
        congr 1
        funext pair
        exact thinningResultSplit_eq_finite s pending threshold pair.1 pair.2
    _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map project).map
        result := (Measure.map_map hresult hproject).symm
    _ = _ := by
      rw [fairCoinStreamLaw_pair_pendingCoinRestriction s.nextLabel pending]

theorem thinningResult_mergeCoinsAtLabel {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (old fresh : Nat × Nat → Bool)
    (hfresh : s.LabelsFresh) :
    ttcPseudocode.secondLoopResult s pending threshold
      (mergeCoinsAtLabel s.nextLabel old fresh) =
    thinningResultSplit s pending threshold old fresh := by
  simp only [ttcPseudocode.secondLoopResult, thinningResultSplit,
    firstExitRound_mergeCoinsAtLabel s pending threshold old fresh hfresh,
    samplesAfter_mergeCoins_old s _ old fresh hfresh,
    pendingAfter_mergeCoins_fresh s.nextLabel s.nextLabel pending _
      (le_refl _) old fresh]

theorem thinningResultSplitFinite_labelsFresh {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (old : Nat × Nat → Bool) (fresh : Nat × Fin pending → Bool)
    (hfresh : s.LabelsFresh) :
    (thinningResultSplitFinite s pending threshold old fresh).1.LabelsFresh := by
  unfold thinningResultSplitFinite
  rw [← thinningResult_mergeCoinsAtLabel s pending threshold old
    (pendingCoinExtension s.nextLabel pending fresh) hfresh]
  exact thinningResult_labelsFresh s pending threshold
    (mergeCoinsAtLabel s.nextLabel old
      (pendingCoinExtension s.nextLabel pending fresh)) hfresh

theorem absolute_active_split_path
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (pending : Nat) (old fresh : Nat × Nat → Bool)
    (hfresh : s.LabelsFresh) :
    let rounds := ttcReference.firstLoopExit s intensity threshold
    ttcPseudocode.secondLoopResult
      (ttcReference.firstLoopResult s intensity threshold
        (mergeCoinsAtLabel s.nextLabel old fresh))
      pending threshold
      (shiftCoins rounds (mergeCoinsAtLabel s.nextLabel old fresh)) =
    thinningResultSplit
      (ttcReference.firstLoopResult s intensity threshold old)
      pending threshold (shiftCoins rounds old)
      (shiftCoins rounds fresh) := by
  dsimp only
  rw [rateThinningResult_mergeCoinsAtLabel s intensity threshold
    old fresh hfresh]
  rw [shiftCoins_mergeCoinsAtLabel s.nextLabel
    (ttcReference.firstLoopExit s intensity threshold) old fresh]
  exact thinningResult_mergeCoinsAtLabel
    (ttcReference.firstLoopResult s intensity threshold old)
    pending threshold (shiftCoins (ttcReference.firstLoopExit s intensity threshold) old)
    (shiftCoins (ttcReference.firstLoopExit s intensity threshold) fresh)
    (rateThinningResult_labelsFresh s intensity threshold old hfresh)

/-- A full active thinning stream can be replaced by independent old-copy and
fresh-copy streams, including the rate loop and the later count loop. -/
theorem absolute_active_split_law
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (pending : Nat) (hfresh : s.LabelsFresh) :
    fairCoinStreamLaw.map (fun coins =>
      ttcPseudocode.secondLoopResult
        (ttcReference.firstLoopResult s intensity threshold coins)
        pending threshold
        (shiftCoins (ttcReference.firstLoopExit s intensity threshold) coins)) =
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map (fun pair =>
      thinningResultSplit
        (ttcReference.firstLoopResult s intensity threshold pair.1)
        pending threshold
        (shiftCoins (ttcReference.firstLoopExit s intensity threshold) pair.1)
        (shiftCoins (ttcReference.firstLoopExit s intensity threshold) pair.2)) := by
  let rounds := ttcReference.firstLoopExit s intensity threshold
  let result : (Nat × Nat → Bool) → TTCState n × Nat :=
    fun coins => ttcPseudocode.secondLoopResult
      (ttcReference.firstLoopResult s intensity threshold coins)
      pending threshold (shiftCoins rounds coins)
  have hresult : Measurable result := by
    exact (measurable_thinningResult_joint threshold).comp
      (((measurable_rateThinningResult s intensity threshold).prodMk
          measurable_const).prodMk (measurable_shiftCoins rounds))
  let merge : (Nat × Nat → Bool) × (Nat × Nat → Bool) →
      (Nat × Nat → Bool) :=
    fun pair => mergeCoinsAtLabel s.nextLabel pair.1 pair.2
  have hmerge : Measurable merge :=
    measurable_mergeCoinsAtLabel_pair s.nextLabel
  have hpath (pair : (Nat × Nat → Bool) × (Nat × Nat → Bool)) :
      result (merge pair) =
      thinningResultSplit
        (ttcReference.firstLoopResult s intensity threshold pair.1)
        pending threshold (shiftCoins rounds pair.1)
        (shiftCoins rounds pair.2) :=
    absolute_active_split_path s intensity threshold pending
      pair.1 pair.2 hfresh
  change fairCoinStreamLaw.map result = _
  calc
    fairCoinStreamLaw.map result =
        ((fairCoinStreamLaw.prod fairCoinStreamLaw).map merge).map result := by
          rw [fairCoinStreamLaw_mergeLabels s.nextLabel]
    _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map
          (result ∘ merge) := Measure.map_map hresult hmerge
    _ = _ := by
          congr 1
          funext pair
          exact hpath pair

theorem thinUntil_split_coin_law {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (hfresh : s.LabelsFresh) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair => thinningResultSplit s pending threshold pair.1 pair.2) =
    ttcPseudocode.secondLoop s pending threshold := by
  calc
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => thinningResultSplit s pending threshold pair.1 pair.2) =
      (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => ttcPseudocode.secondLoopResult s pending threshold
          (mergeCoinsAtLabel s.nextLabel pair.1 pair.2)) := by
            congr 1
            funext pair
            exact (thinningResult_mergeCoinsAtLabel s pending threshold
              pair.1 pair.2 hfresh).symm
    _ = fairCoinStreamLaw.map (ttcPseudocode.secondLoopResult s pending threshold) := by
      have hmap :
          ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
            (fun pair => mergeCoinsAtLabel s.nextLabel pair.1 pair.2)).map
              (ttcPseudocode.secondLoopResult s pending threshold) =
          (fairCoinStreamLaw.prod fairCoinStreamLaw).map
            (fun pair => ttcPseudocode.secondLoopResult s pending threshold
              (mergeCoinsAtLabel s.nextLabel pair.1 pair.2)) := by
        exact Measure.map_map
          (measurable_thinningResult s pending threshold)
          (measurable_mergeCoinsAtLabel_pair s.nextLabel)
      calc
        _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
            (fun pair => mergeCoinsAtLabel s.nextLabel pair.1 pair.2)).map
              (ttcPseudocode.secondLoopResult s pending threshold) := hmap.symm
        _ = _ := by rw [fairCoinStreamLaw_mergeLabels]
    _ = ttcPseudocode.secondLoop s pending threshold := rfl

/-- The separated coin representation can be substituted inside an adaptive
state distribution, provided reachable states have fresh labels. -/
theorem thinUntil_bind_split_coin_law {n : Nat}
    (μ : Measure (TTCState n × Nat)) (threshold : Real)
    (hfresh : ∀ᵐ pair ∂μ, pair.1.LabelsFresh) :
    μ.bind (fun pair => ttcPseudocode.secondLoop pair.1 pair.2 threshold) =
    μ.bind (fun pair => (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun coins => thinningResultSplit pair.1 pair.2 threshold
        coins.1 coins.2)) := by
  apply Measure.bind_congr_right
  filter_upwards [hfresh] with pair hp
  exact (thinUntil_split_coin_law pair.1 pair.2 threshold hp).symm

end ttc

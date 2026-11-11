import Kr25Ssmxt.Analysis.ManuscriptCoinLabelMergeLaw

/-! The active two-loop kernel needs a fair fresh-coin array only on its
finite pending population. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_manuscript_active_finite_result
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (pending : Nat) (hfresh : s.LabelsFresh) :
    Measurable (fun pair : (Nat × Nat → Bool) ×
        (Nat × Fin pending → Bool) =>
      thinningResultSplitFinite
        (ttcPseudocode.firstLoopResult s intensity threshold pair.1)
        pending threshold
        (shiftCoins (ttcPseudocode.firstLoopExit s intensity threshold) pair.1)
        pair.2) := by
  let rounds := ttcPseudocode.firstLoopExit s intensity threshold
  let first : (Nat × Nat → Bool) → TTCState n :=
    ttcPseudocode.firstLoopResult s intensity threshold
  have hfirst : Measurable first :=
    measurable_manuscriptRateThinningResult s intensity threshold
  have hmerge : Measurable
      (fun pair : (Nat × Nat → Bool) × (Nat × Fin pending → Bool) =>
        mergeCoinsAtLabel s.nextLabel (shiftCoins rounds pair.1)
          (pendingCoinExtension s.nextLabel pending pair.2)) :=
    (measurable_mergeCoinsAtLabel_pair s.nextLabel).comp
      (((measurable_shiftCoins rounds).comp measurable_fst).prodMk
        ((measurable_pendingCoinExtension s.nextLabel pending).comp
          measurable_snd))
  have heq : (fun pair : (Nat × Nat → Bool) ×
      (Nat × Fin pending → Bool) =>
      thinningResultSplitFinite (first pair.1) pending threshold
        (shiftCoins rounds pair.1) pair.2) =
      (fun pair => ttcPseudocode.secondLoopResult (first pair.1) pending threshold
        (mergeCoinsAtLabel s.nextLabel (shiftCoins rounds pair.1)
          (pendingCoinExtension s.nextLabel pending pair.2))) := by
    funext pair
    exact (thinningResult_mergeCoinsAtLabel (first pair.1)
      pending threshold (shiftCoins rounds pair.1)
      (pendingCoinExtension s.nextLabel pending pair.2)
      (manuscriptRateThinningResult_labelsFresh s intensity threshold
        pair.1 hfresh)).symm
  rw [heq]
  exact (measurable_thinningResult_joint threshold).comp
    (((hfirst.comp measurable_fst).prodMk measurable_const).prodMk hmerge)

theorem manuscript_absolute_active_finite_coin_law
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (pending : Nat) (hfresh : s.LabelsFresh) :
    let rounds := ttcPseudocode.firstLoopExit s intensity threshold
    fairCoinStreamLaw.map (fun coins =>
      ttcPseudocode.secondLoopResult
        (ttcPseudocode.firstLoopResult s intensity threshold coins)
        pending threshold (shiftCoins rounds coins)) =
    (fairCoinStreamLaw.prod
      (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).map
      (fun pair => thinningResultSplitFinite
        (ttcPseudocode.firstLoopResult s intensity threshold pair.1)
        pending threshold (shiftCoins rounds pair.1) pair.2) := by
  dsimp only
  let rounds := ttcPseudocode.firstLoopExit s intensity threshold
  let first : (Nat × Nat → Bool) → TTCState n :=
    ttcPseudocode.firstLoopResult s intensity threshold
  let project : (Nat × Nat → Bool) × (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Fin pending → Bool) :=
    fun pair => (pair.1,
      pendingCoinRestriction s.nextLabel pending
        (shiftCoins rounds pair.2))
  let result : (Nat × Nat → Bool) × (Nat × Fin pending → Bool) →
      TTCState n × Nat :=
    fun pair => thinningResultSplitFinite (first pair.1) pending threshold
      (shiftCoins rounds pair.1) pair.2
  have hfirst : Measurable first :=
    measurable_manuscriptRateThinningResult s intensity threshold
  have hmerge : Measurable
      (fun pair : (Nat × Nat → Bool) × (Nat × Fin pending → Bool) =>
        mergeCoinsAtLabel s.nextLabel (shiftCoins rounds pair.1)
          (pendingCoinExtension s.nextLabel pending pair.2)) :=
    (measurable_mergeCoinsAtLabel_pair s.nextLabel).comp
      (((measurable_shiftCoins rounds).comp measurable_fst).prodMk
        ((measurable_pendingCoinExtension s.nextLabel pending).comp
          measurable_snd))
  have hresult : Measurable result := by
    have heq : result = fun pair =>
        ttcPseudocode.secondLoopResult (first pair.1) pending threshold
          (mergeCoinsAtLabel s.nextLabel (shiftCoins rounds pair.1)
            (pendingCoinExtension s.nextLabel pending pair.2)) := by
      funext pair
      exact (thinningResult_mergeCoinsAtLabel (first pair.1)
        pending threshold (shiftCoins rounds pair.1)
        (pendingCoinExtension s.nextLabel pending pair.2)
        (manuscriptRateThinningResult_labelsFresh s intensity threshold
          pair.1 hfresh)).symm
    rw [heq]
    exact (measurable_thinningResult_joint threshold).comp
      ((((hfirst.comp measurable_fst).prodMk measurable_const)).prodMk
        hmerge)
  have hproject : Measurable project :=
    measurable_fst.prodMk
      (((measurable_pendingCoinRestriction s.nextLabel pending).comp
        (measurable_shiftCoins rounds)).comp measurable_snd)
  have hpath (pair : (Nat × Nat → Bool) × (Nat × Nat → Bool)) :
      thinningResultSplit (first pair.1) pending threshold
        (shiftCoins rounds pair.1) (shiftCoins rounds pair.2) =
      result (project pair) := by
    exact thinningResultSplit_eq_finite (first pair.1) pending threshold
      (shiftCoins rounds pair.1) (shiftCoins rounds pair.2)
  calc
    fairCoinStreamLaw.map (fun coins =>
        ttcPseudocode.secondLoopResult (first coins) pending threshold
          (shiftCoins rounds coins)) =
      (fairCoinStreamLaw.prod fairCoinStreamLaw).map (fun pair =>
        thinningResultSplit (first pair.1) pending threshold
          (shiftCoins rounds pair.1) (shiftCoins rounds pair.2)) :=
        manuscript_absolute_active_split_law s intensity threshold pending
          hfresh
    _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (result ∘ project) := by
          congr 1
          funext pair
          exact hpath pair
    _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map project).map
        result := (Measure.map_map hresult hproject).symm
    _ = _ := by
      rw [fairCoinStreamLaw_pair_shift_pendingCoinRestriction
        s.nextLabel pending rounds]

end Kr25Ssmxt

import Kr25Ssmxt.Analysis.TwoStageSurvivorLabels

/-! Conditional on the initial Poisson draw and pre-thinning coins, the
component can attach permanent point marks at surviving original labels. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem community_active_finite_origin_tape
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal) (hfresh : s.LabelsFresh)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let rounds := ttcPseudocode.firstLoopExit s intensity threshold
    let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    let coinLaw := fairCoinStreamLaw.prod
      (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))
    let result := fun pair : (Nat × Nat → Bool) ×
        (Nat × Fin pending → Bool) =>
      thinningResultSplitFinite
        (ttcPseudocode.firstLoopResult s intensity threshold pair.1)
        pending threshold (shiftCoins rounds pair.1) pair.2
    (coinLaw.map result).bind (fun second =>
      ((ttcSubroutines hn prep).GenerateSamples P second.2
        b eta delta).map fun batch => second.1.addBatch batch) =
    coinLaw.bind fun pair =>
      let second := result pair
      let activeRounds := firstExitRoundSplit
        (ttcPseudocode.firstLoopResult s intensity threshold pair.1)
        pending threshold (shiftCoins rounds pair.1)
        (pendingCoinExtension s.nextLabel pending pair.2)
      (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
        second.1.addBatch (fun i : Fin second.2 =>
          tape (twoStageSurvivorLabel preCoins preRounds s.nextLabel
            basePending pair.2 activeRounds i)) := by
  dsimp only
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let rounds := ttcPseudocode.firstLoopExit s intensity threshold
  let coinLaw := fairCoinStreamLaw.prod
    (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))
  let result : (Nat × Nat → Bool) × (Nat × Fin pending → Bool) →
      TTCState n × Nat := fun pair =>
    thinningResultSplitFinite
      (ttcPseudocode.firstLoopResult s intensity threshold pair.1)
      pending threshold (shiftCoins rounds pair.1) pair.2
  let K : TTCState n × Nat → Measure (TTCState n) := fun second =>
    ((ttcSubroutines hn prep).GenerateSamples P second.2
      b eta delta).map fun batch => second.1.addBatch batch
  have hresult : Measurable result :=
    measurable_active_finite_result s intensity threshold pending
      hfresh
  have hK : Measurable K :=
    measurable_community_sampleAppend_kernel hn prep P b eta delta
  change (coinLaw.map result).bind K = _
  rw [bind_mapped_measure coinLaw result hresult K hK]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pair
  exact community_twoStage_sampler_tape hn prep P b eta delta
    threshold hroute s intensity preCoins preRounds basePending pair.1 pair.2

noncomputable def communityOriginTapeKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (pair : (Nat × Nat → Bool) ×
      (Nat × Fin (pendingAfter preCoins preRounds s.nextLabel basePending) →
        Bool)) : Measure (TTCState n) :=
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let rounds := ttcPseudocode.firstLoopExit s intensity threshold
  let first := ttcPseudocode.firstLoopResult s intensity threshold pair.1
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds pair.1) pair.2
  let activeRounds := firstExitRoundSplit first pending threshold
    (shiftCoins rounds pair.1)
    (pendingCoinExtension s.nextLabel pending pair.2)
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
    second.1.addBatch (fun i : Fin second.2 =>
      tape (twoStageSurvivorLabel preCoins preRounds s.nextLabel
        basePending pair.2 activeRounds i))

theorem measurable_communityOriginTapeKernel
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal) (hfresh : s.LabelsFresh)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat) :
    Measurable (communityOriginTapeKernel hn P b eta threshold
      hroute s intensity preCoins preRounds basePending) := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let result : (Nat × Nat → Bool) × (Nat × Fin pending → Bool) →
      TTCState n × Nat := fun pair =>
    thinningResultSplitFinite
      (ttcPseudocode.firstLoopResult s intensity threshold pair.1)
      pending threshold
      (shiftCoins (ttcPseudocode.firstLoopExit s intensity threshold) pair.1) pair.2
  let K : TTCState n × Nat → Measure (TTCState n) := fun second =>
    ((ttcSubroutines hn prep).GenerateSamples P second.2
      b eta delta).map fun batch => second.1.addBatch batch
  have hresult : Measurable result :=
    measurable_active_finite_result s intensity threshold pending
      hfresh
  have hK : Measurable K :=
    measurable_community_sampleAppend_kernel hn prep P b eta delta
  have heq : communityOriginTapeKernel hn P b eta threshold hroute
      s intensity preCoins preRounds basePending = K ∘ result := by
    funext pair
    exact (community_twoStage_sampler_tape hn prep P b eta delta
      threshold hroute s intensity preCoins preRounds basePending
      pair.1 pair.2).symm
  rw [heq]
  exact hK.comp hresult

/-- The finite fresh coins can be read from an independent future stream at
the pre-surviving original Poisson labels, with the permanent mark tape
attached to those same original labels. -/
theorem community_originTape_futureCoins
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal) (hfresh : s.LabelsFresh)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let K := communityOriginTapeKernel hn P b eta threshold
      hroute s intensity preCoins preRounds basePending
    (fairCoinStreamLaw.prod
      (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).bind K =
    (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun pair =>
      K (pair.1, originalSurvivorCoinRestriction preCoins preRounds
        s.nextLabel basePending pair.2) := by
  dsimp only
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let K := communityOriginTapeKernel hn P b eta threshold hroute
    s intensity preCoins preRounds basePending
  let project : (Nat × Nat → Bool) × (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Fin pending → Bool) :=
    fun pair => (pair.1, originalSurvivorCoinRestriction preCoins preRounds
      s.nextLabel basePending pair.2)
  have hproject : Measurable project :=
    measurable_fst.prodMk
      ((measurable_originalSurvivorCoinRestriction preCoins preRounds
        s.nextLabel basePending).comp measurable_snd)
  have hK : Measurable K :=
    measurable_communityOriginTapeKernel hn prep P b eta delta
      threshold hroute s intensity hfresh preCoins preRounds basePending
  change (fairCoinStreamLaw.prod
    (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).bind K =
      (fairCoinStreamLaw.prod fairCoinStreamLaw).bind (K ∘ project)
  calc
    (fairCoinStreamLaw.prod
        (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).bind K =
      ((fairCoinStreamLaw.prod fairCoinStreamLaw).map project).bind K := by
        rw [fairCoinStreamLaw_pair_originalSurvivorCoinRestriction]
    _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).bind (K ∘ project) :=
      bind_mapped_measure _ project hproject K hK

/-- The component's source-driven kernel: Poisson copies and marks are drawn
at their original labels, while stored copies use an independent old-copy
coin stream. -/
noncomputable def communityOriginSourceKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n) (level : Nat) :
    Measure (TTCState n) :=
  let intensity := ttcPseudocode.t b n threshold outcome.2
  let deleted := state.removeComponent P
  let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
    fairCoinStreamLaw.bind fun preCoins =>
      let preRounds := level + rounds
      let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
      (fairCoinStreamLaw.prod
        (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).bind
        fun pair =>
          let first := ttcPseudocode.firstLoopResult deleted intensity threshold
            pair.1
          let second := thinningResultSplitFinite first pending threshold
            (shiftCoins rounds pair.1) pair.2
          let activeRounds := firstExitRoundSplit first pending threshold
            (shiftCoins rounds pair.1)
            (pendingCoinExtension deleted.nextLabel pending pair.2)
          (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
            second.1.addBatch (fun i : Fin second.2 =>
              tape (twoStageSurvivorLabel preCoins preRounds
                deleted.nextLabel basePending pair.2 activeRounds i))

/-- The executable component has exactly the source-driven law with marks
at original Poisson labels. -/
theorem communityComponentGivenVolume_eq_originSourceKernel
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n)
    (level : Nat) (hrate : state.p = 1 / (2 : NNReal) ^ level)
    (hfresh : state.LabelsFresh) :
    communityComponentGivenVolume hn prep P b eta delta threshold
      outcome state =
    communityOriginSourceKernel hn P b eta threshold hroute
      outcome state level := by
  let intensity := ttcPseudocode.t b n threshold outcome.2
  let deleted := state.removeComponent P
  let K : TTCState n × Nat → Measure (TTCState n) := fun second =>
    ((ttcSubroutines hn prep).GenerateSamples P second.2
      b eta delta).map fun batch => second.1.addBatch batch
  have hK : Measurable K :=
    measurable_community_sampleAppend_kernel hn prep P b eta delta
  let source : Measure (TTCState n × Nat) :=
    (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        fairCoinStreamLaw.map fun activeCoins =>
          ttcPseudocode.secondLoopResult
            (ttcPseudocode.firstLoopResult deleted intensity threshold activeCoins)
            (pendingAfter preCoins
              (level + ttcPseudocode.firstLoopExit deleted intensity threshold)
              deleted.nextLabel basePending)
            threshold
            (shiftCoins (ttcPseudocode.firstLoopExit deleted intensity threshold)
              activeCoins)
  let finiteSource : Measure (TTCState n × Nat) :=
    (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind
        (absoluteFinitePreKernel deleted intensity threshold
          level basePending)
  have hbase : communityComponentGivenVolume hn prep P b eta delta
      threshold outcome state = source.bind K := by
    exact communityComponentGivenVolume_absolute_predraw
      hn prep P b eta delta threshold outcome state level hrate
  have hsource : source = finiteSource :=
    poisson_twoLoops_absolute_finite deleted intensity threshold
      level (state.labelsFresh_removeComponent P hfresh)
  calc
    communityComponentGivenVolume hn prep P b eta delta threshold
        outcome state = source.bind K := hbase
    _ = finiteSource.bind K := by rw [hsource]
    _ = (ProbabilityTheory.poissonMeasure intensity).bind
        (fun basePending => fairCoinStreamLaw.bind fun preCoins =>
          (absoluteFinitePreKernel deleted intensity threshold
            level basePending preCoins).bind K) := by
            exact absoluteFiniteSource_bind deleted intensity
              threshold level (state.labelsFresh_removeComponent P hfresh) K hK
    _ = communityOriginSourceKernel hn P b eta threshold hroute
          outcome state level := by
      unfold communityOriginSourceKernel
      apply Measure.bind_congr_right
      apply Filter.Eventually.of_forall
      intro basePending
      apply Measure.bind_congr_right
      apply Filter.Eventually.of_forall
      intro preCoins
      exact community_active_finite_origin_tape
        hn prep P b eta delta threshold hroute deleted intensity
        (state.labelsFresh_removeComponent P hfresh) preCoins
        (level + ttcPseudocode.firstLoopExit deleted intensity threshold) basePending

/-- The same source law with a full future fair-coin stream in place of the
finite survivor-indexed coin block. -/
noncomputable def communityFutureSourceKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n) (level : Nat) :
    Measure (TTCState n) :=
  let intensity := ttcPseudocode.t b n threshold outcome.2
  let deleted := state.removeComponent P
  let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
  (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
    fairCoinStreamLaw.bind fun preCoins =>
      (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun pair =>
        communityOriginTapeKernel hn P b eta threshold hroute
          deleted intensity preCoins (level + rounds) basePending
          (pair.1, originalSurvivorCoinRestriction preCoins
            (level + rounds) deleted.nextLabel basePending pair.2)

theorem communityComponentGivenVolume_eq_futureSourceKernel
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n)
    (level : Nat) (hrate : state.p = 1 / (2 : NNReal) ^ level)
    (hfresh : state.LabelsFresh) :
    communityComponentGivenVolume hn prep P b eta delta threshold
      outcome state =
    communityFutureSourceKernel hn P b eta threshold hroute
      outcome state level := by
  rw [communityComponentGivenVolume_eq_originSourceKernel
    hn prep P b eta delta threshold hroute outcome state level hrate hfresh]
  unfold communityOriginSourceKernel
    communityFutureSourceKernel
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  exact community_originTape_futureCoins
    hn prep P b eta delta threshold hroute (state.removeComponent P)
    (ttcPseudocode.t b n threshold outcome.2)
    (state.labelsFresh_removeComponent P hfresh) preCoins
    (level + ttcPseudocode.firstLoopExit (state.removeComponent P)
      (ttcPseudocode.t b n threshold outcome.2) threshold) basePending

end Kr25Ssmxt

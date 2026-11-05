import Kr25Ssmxt.Analysis.ManuscriptOldCoinRestriction
import Kr25Ssmxt.Analysis.ManuscriptOriginMarkedComponent

/-! The source-labelled one-component kernel reads old-copy coins only at
labels already allocated by its incoming state. -/

namespace Kr25Ssmxt

open MeasureTheory

private noncomputable def tapeAppend {n : Nat}
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (fresh : Nat × Fin (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (second : TTCState n × Nat) (activeRounds : Nat)
    (hcount : second.2 = pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending) fresh)
      activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))
    (tape : Nat → LatticePoint n) : TTCState n :=
  second.1.addBatch (fun i : Fin second.2 =>
    tape (twoStageSurvivorLabel preCoins preRounds firstLabel basePending
      fresh activeRounds (Fin.cast hcount i)))

private theorem tapeAppend_congr {n : Nat}
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (fresh : Nat × Fin (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (second second' : TTCState n × Nat) (rounds rounds' : Nat)
    (hcount : second.2 = pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending) fresh)
      rounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))
    (hcount' : second'.2 = pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending) fresh)
      rounds' firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))
    (hsecond : second = second') (hrounds : rounds = rounds')
    (tape : Nat → LatticePoint n) :
    tapeAppend preCoins preRounds firstLabel basePending fresh second rounds hcount tape =
      tapeAppend preCoins preRounds firstLabel basePending fresh second' rounds' hcount' tape := by
  subst second'
  subst rounds'
  rfl

theorem communityManuscriptOriginTapeKernel_congr_allocated
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (old other : Nat × Nat → Bool)
    (fresh : Nat × Fin (pendingAfter preCoins preRounds s.nextLabel basePending) → Bool)
    (hfresh : s.LabelsFresh)
    (hagrees : ∀ round label, label < s.nextLabel →
      old (round, label) = other (round, label)) :
    communityManuscriptOriginTapeKernel hn P b eta threshold hroute s intensity
      preCoins preRounds basePending (old, fresh) =
    communityManuscriptOriginTapeKernel hn P b eta threshold hroute s intensity
      preCoins preRounds basePending (other, fresh) := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let rounds := manuscriptRateExit s intensity threshold
  have hfirst : manuscriptRateThinningResult s intensity threshold old =
      manuscriptRateThinningResult s intensity threshold other :=
    manuscriptRateThinningResult_congr_allocated s intensity threshold
      hfresh old other hagrees
  have hfirstFresh : (manuscriptRateThinningResult s intensity threshold old).LabelsFresh :=
    manuscriptRateThinningResult_labelsFresh s intensity threshold old hfresh
  have hshift : ∀ round label, label <
      (manuscriptRateThinningResult s intensity threshold old).nextLabel →
      shiftCoins rounds old (round, label) =
        shiftCoins rounds other (round, label) := by
    intro round label hlabel
    simpa [shiftCoins, Nat.add_comm] using
      hagrees (round + rounds) label
        (by simpa [manuscriptRateThinningResult] using hlabel)
  have hactive : firstExitRoundSplit
      (manuscriptRateThinningResult s intensity threshold old) pending threshold
      (shiftCoins rounds old) (pendingCoinExtension s.nextLabel pending fresh) =
      firstExitRoundSplit
        (manuscriptRateThinningResult s intensity threshold other) pending threshold
        (shiftCoins rounds other) (pendingCoinExtension s.nextLabel pending fresh) := by
    rw [← hfirst]
    exact firstExitRoundSplit_congr_old_allocated _ _ _ hfirstFresh _ _ _ hshift
  have hsecond : thinningResultSplitFinite
      (manuscriptRateThinningResult s intensity threshold old) pending threshold
      (shiftCoins rounds old) fresh =
      thinningResultSplitFinite
        (manuscriptRateThinningResult s intensity threshold other) pending threshold
        (shiftCoins rounds other) fresh := by
    rw [← hfirst]
    exact thinningResultSplitFinite_congr_old_allocated _ _ _ hfirstFresh _ _ _ hshift
  dsimp only [communityManuscriptOriginTapeKernel]
  congr 1
  funext tape
  change tapeAppend preCoins preRounds s.nextLabel basePending fresh
    (thinningResultSplitFinite
      (manuscriptRateThinningResult s intensity threshold old) pending threshold
      (shiftCoins rounds old) fresh)
    (firstExitRoundSplit
      (manuscriptRateThinningResult s intensity threshold old) pending threshold
      (shiftCoins rounds old) (pendingCoinExtension s.nextLabel pending fresh))
    (by rfl) tape =
    tapeAppend preCoins preRounds s.nextLabel basePending fresh
      (thinningResultSplitFinite
        (manuscriptRateThinningResult s intensity threshold other) pending threshold
        (shiftCoins rounds other) fresh)
      (firstExitRoundSplit
        (manuscriptRateThinningResult s intensity threshold other) pending threshold
        (shiftCoins rounds other) (pendingCoinExtension s.nextLabel pending fresh))
      (by rfl) tape
  exact tapeAppend_congr preCoins preRounds s.nextLabel basePending fresh
    _ _ _ _ (by rfl) (by rfl) hsecond hactive tape

theorem communityManuscriptOriginTapeKernel_eq_allocated_extension
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (old : Nat × Nat → Bool)
    (fresh : Nat × Fin (pendingAfter preCoins preRounds s.nextLabel basePending) → Bool)
    (hfresh : s.LabelsFresh) :
    communityManuscriptOriginTapeKernel hn P b eta threshold hroute s intensity
      preCoins preRounds basePending (old, fresh) =
    communityManuscriptOriginTapeKernel hn P b eta threshold hroute s intensity
      preCoins preRounds basePending
      (allocatedCoinExtension s.nextLabel
        (allocatedCoinRestriction s.nextLabel old), fresh) := by
  apply communityManuscriptOriginTapeKernel_congr_allocated
    hn P b eta threshold hroute s intensity preCoins preRounds basePending
    old _ fresh hfresh
  intro round label hlabel
  exact (allocatedCoinExtension_restriction_at s.nextLabel old round label hlabel).symm

theorem communityManuscriptFutureSourceKernel_eq_allocated_extension
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n) (level : Nat)
    (hfresh : state.LabelsFresh) :
    communityManuscriptFutureSourceKernel hn P b eta threshold hroute
      outcome state level =
    let intensity := manuscriptIntensity b n threshold outcome.2
    let deleted := state.removeComponent P
    let rounds := manuscriptRateExit deleted intensity threshold
    (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun pair =>
          communityManuscriptOriginTapeKernel hn P b eta threshold hroute
            deleted intensity preCoins (level + rounds) basePending
            (allocatedCoinExtension deleted.nextLabel
              (allocatedCoinRestriction deleted.nextLabel pair.1),
              originalSurvivorCoinRestriction preCoins
                (level + rounds) deleted.nextLabel basePending pair.2) := by
  unfold communityManuscriptFutureSourceKernel
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pair
  exact communityManuscriptOriginTapeKernel_eq_allocated_extension
    hn P b eta threshold hroute _ _ preCoins _ basePending pair.1 _
    (state.labelsFresh_removeComponent P hfresh)

/-- Both coin families in a source-labelled component step can be drawn on
their finite allocated label blocks. -/
theorem communityManuscript_originTape_finiteOldCoins
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal) (hfresh : s.LabelsFresh)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let K := communityManuscriptOriginTapeKernel hn P b eta threshold
      hroute s intensity preCoins preRounds basePending
    (fairCoinStreamLaw.prod
      (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).bind K =
    ((Measure.infinitePi
        (fun _ : Nat × Fin s.nextLabel => fairCoinLaw)).prod
      (Measure.infinitePi
        (fun _ : Nat × Fin pending => fairCoinLaw))).bind fun pair =>
      K (allocatedCoinExtension s.nextLabel pair.1, pair.2) := by
  dsimp only
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let freshLaw : Measure (Nat × Fin pending → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let oldLaw : Measure (Nat × Fin s.nextLabel → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let K := communityManuscriptOriginTapeKernel hn P b eta threshold
    hroute s intensity preCoins preRounds basePending
  let project : ((Nat × Nat → Bool) × (Nat × Fin pending → Bool)) →
      (Nat × Fin s.nextLabel → Bool) × (Nat × Fin pending → Bool) :=
    Prod.map (allocatedCoinRestriction s.nextLabel) id
  have hproject : Measurable project :=
    (measurable_allocatedCoinRestriction s.nextLabel).comp measurable_fst
      |>.prodMk measurable_snd
  let K' : (Nat × Fin s.nextLabel → Bool) × (Nat × Fin pending → Bool) →
      Measure (TTCState n) := fun pair =>
    K (allocatedCoinExtension s.nextLabel pair.1, pair.2)
  have hK' : Measurable K' := by
    exact (measurable_communityManuscriptOriginTapeKernel hn prep P b eta
      delta threshold hroute s intensity hfresh preCoins preRounds
      basePending).comp
        (((measurable_allocatedCoinExtension s.nextLabel).comp measurable_fst).prodMk
          measurable_snd)
  have hpoint : ∀ pair, K pair = K' (project pair) := by
    intro pair
    exact communityManuscriptOriginTapeKernel_eq_allocated_extension
      hn P b eta threshold hroute s intensity preCoins preRounds
      basePending pair.1 pair.2 hfresh
  have hmap : (fairCoinStreamLaw.prod freshLaw).map project =
      oldLaw.prod freshLaw := by
    letI : IsProbabilityMeasure fairCoinStreamLaw :=
      fairCoinStreamLaw_isProbabilityMeasure
    letI : IsProbabilityMeasure freshLaw := by
      dsimp [freshLaw]
      letI : ∀ _ : Nat × Fin pending, IsProbabilityMeasure fairCoinLaw :=
        fun _ => fairCoinLaw_isProbabilityMeasure
      infer_instance
    simpa [project, oldLaw, freshLaw, fairCoinStreamLaw_allocatedCoinRestriction]
      using (Measure.map_prod_map fairCoinStreamLaw freshLaw
        (measurable_allocatedCoinRestriction s.nextLabel) measurable_id).symm
  change (fairCoinStreamLaw.prod freshLaw).bind K =
    (oldLaw.prod freshLaw).bind K'
  rw [← hmap, bind_mapped_measure _ project hproject K' hK']
  exact Measure.bind_congr_right (Filter.Eventually.of_forall hpoint)

theorem communityManuscript_originTape_finiteCoinBlocks
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal) (hfresh : s.LabelsFresh)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let K := communityManuscriptOriginTapeKernel hn P b eta threshold
      hroute s intensity preCoins preRounds basePending
    (fairCoinStreamLaw.prod fairCoinStreamLaw).bind (fun pair =>
      K (pair.1, originalSurvivorCoinRestriction preCoins preRounds
        s.nextLabel basePending pair.2)) =
    ((Measure.infinitePi
        (fun _ : Nat × Fin s.nextLabel => fairCoinLaw)).prod
      (Measure.infinitePi
        (fun _ : Nat × Fin pending => fairCoinLaw))).bind fun pair =>
      K (allocatedCoinExtension s.nextLabel pair.1, pair.2) := by
  dsimp only
  rw [← communityManuscript_originTape_futureCoins hn prep P b eta delta
    threshold hroute s intensity hfresh preCoins preRounds basePending]
  exact communityManuscript_originTape_finiteOldCoins hn prep P b eta delta
    threshold hroute s intensity hfresh preCoins preRounds basePending

/-- The same one-component source program, with only the finite old and new
coin blocks used by its state transition. -/
noncomputable def communityManuscriptFiniteCoinSourceKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n) (level : Nat) :
    Measure (TTCState n) :=
  let intensity := manuscriptIntensity b n threshold outcome.2
  let deleted := state.removeComponent P
  let rounds := manuscriptRateExit deleted intensity threshold
  (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
    fairCoinStreamLaw.bind fun preCoins =>
      let pending := pendingAfter preCoins (level + rounds)
        deleted.nextLabel basePending
      ((Measure.infinitePi
          (fun _ : Nat × Fin deleted.nextLabel => fairCoinLaw)).prod
        (Measure.infinitePi
          (fun _ : Nat × Fin pending => fairCoinLaw))).bind fun pair =>
        communityManuscriptOriginTapeKernel hn P b eta threshold hroute
          deleted intensity preCoins (level + rounds) basePending
          (allocatedCoinExtension deleted.nextLabel pair.1, pair.2)

theorem communityManuscriptFutureSourceKernel_eq_finiteCoinSourceKernel
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n) (level : Nat)
    (hfresh : state.LabelsFresh) :
    communityManuscriptFutureSourceKernel hn P b eta threshold hroute
      outcome state level =
    communityManuscriptFiniteCoinSourceKernel hn P b eta threshold hroute
      outcome state level := by
  unfold communityManuscriptFutureSourceKernel
    communityManuscriptFiniteCoinSourceKernel
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  exact communityManuscript_originTape_finiteCoinBlocks
    hn prep P b eta delta threshold hroute (state.removeComponent P)
    (manuscriptIntensity b n threshold outcome.2)
    (state.labelsFresh_removeComponent P hfresh) preCoins
    (level + manuscriptRateExit (state.removeComponent P)
      (manuscriptIntensity b n threshold outcome.2) threshold) basePending

theorem communityManuscriptComponentGivenVolume_eq_finiteCoinSourceKernel
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n)
    (level : Nat) (hrate : state.rate = 1 / (2 : NNReal) ^ level)
    (hfresh : state.LabelsFresh) :
    communityManuscriptComponentGivenVolume hn prep P b eta delta threshold
      outcome state =
    communityManuscriptFiniteCoinSourceKernel hn P b eta threshold hroute
      outcome state level := by
  rw [communityManuscriptComponentGivenVolume_eq_futureSourceKernel
    hn prep P b eta delta threshold hroute outcome state level hrate hfresh]
  exact communityManuscriptFutureSourceKernel_eq_finiteCoinSourceKernel
    hn prep P b eta delta threshold hroute outcome state level hfresh

end Kr25Ssmxt

import Kr25Ssmxt.Analysis.ManuscriptOriginMarksIn

/-! If one refreshed component step moves the dyadic level past `level0`
while its deterministic first loop stops at or before `level0`, then the
output source population at `level0` already exceeds the threshold. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

/-- With every valid mark in `S`, the total point count over `S` is the
number of valid tags surviving the level. -/
theorem manuscriptOriginSourceState_sum_pointCounts_eq_card
    {n : Nat} (g : ManuscriptOriginSourceState n) (level : Nat)
    (S : Finset (LatticePoint n)) (h : ∀ tag ∈ g.valid, g.marks tag ∈ S) :
    (∑ x : S, g.pointCounts level S x) =
      (g.valid.filter fun tag => survives (g.coins tag.1) level tag.2).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := g.marks) (t := S)
    (fun tag htag => h tag (Finset.mem_filter.mp htag).1)]
  rw [← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro x _
  change (g.valid.filter fun tag =>
    survives (g.coins tag.1) level tag.2 ∧ g.marks tag = x.1).card = _
  rw [Finset.filter_filter]

/-- Before the split loop's first exit, its guard population exceeds the
threshold. -/
theorem lt_population_of_lt_firstExitRoundSplit {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (old fresh : Nat × Nat → Bool) (r : Nat)
    (h : r < firstExitRoundSplit s pending threshold old fresh) :
    threshold < (samplesAfter old r s.samples).card +
      pendingAfter fresh r s.nextLabel pending := by
  by_contra hle
  have hmem : r ∈ {rounds | (samplesAfter old rounds s.samples).card +
      pendingAfter fresh rounds s.nextLabel pending ≤ threshold} :=
    le_of_not_gt hle
  have hinf := Nat.sInf_le hmem
  unfold firstExitRoundSplit at h
  omega

/-- The second-loop population at relative round `r0` injects into the
valid output source tags surviving the absolute level `preRounds + r0`. -/
theorem ManuscriptOriginConfiguration.split_population_le_survivors
    {n : Nat} (d : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins fresh : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) (r0 level0 : Nat)
    (hlevel : level0 = d.level + manuscriptRateExit (d.state.removeComponent P)
      intensity threshold + r0) :
    (samplesAfter (shiftCoins (manuscriptRateExit (d.state.removeComponent P)
        intensity threshold)
        (manuscriptSourceOldCoins d.origin d.source.coins d.level)) r0
      (manuscriptRateThinningResult (d.state.removeComponent P) intensity
        threshold
        (manuscriptSourceOldCoins d.origin d.source.coins d.level)).samples).card +
      pendingAfter
        (pendingCoinExtension d.state.nextLabel
          (pendingAfter preCoins (d.level + manuscriptRateExit
            (d.state.removeComponent P) intensity threshold)
            d.state.nextLabel basePending)
          (originalSurvivorCoinRestriction preCoins
            (d.level + manuscriptRateExit (d.state.removeComponent P)
              intensity threshold) d.state.nextLabel basePending fresh))
        r0 d.state.nextLabel
        (pendingAfter preCoins (d.level + manuscriptRateExit
            (d.state.removeComponent P) intensity threshold)
            d.state.nextLabel basePending) ≤
    ((d.source.step
        { component := P
          firstLabel := d.state.nextLabel
          basePending := basePending
          preRounds := d.level + manuscriptRateExit
            (d.state.removeComponent P) intensity threshold
          preCoins := preCoins
          futureCoins := fresh
          tape := tape }).valid.filter fun tag =>
      Kr25Ssmxt.survives ((d.source.step
        { component := P
          firstLabel := d.state.nextLabel
          basePending := basePending
          preRounds := d.level + manuscriptRateExit
            (d.state.removeComponent P) intensity threshold
          preCoins := preCoins
          futureCoins := fresh
          tape := tape }).coins tag.1) level0 tag.2).card := by
  classical
  set deleted := d.state.removeComponent P with hdeleted
  set rounds := manuscriptRateExit deleted intensity threshold with hrounds
  set preRounds := d.level + rounds with hpreRounds
  set oldCoins := manuscriptSourceOldCoins d.origin d.source.coins d.level
    with holdCoins
  set first := manuscriptRateThinningResult deleted intensity threshold
    oldCoins with hfirst
  set step : ManuscriptOriginSourceStep n :=
    { component := P
      firstLabel := d.state.nextLabel
      basePending := basePending
      preRounds := preRounds
      preCoins := preCoins
      futureCoins := fresh
      tape := tape } with hstep
  set O := samplesAfter (shiftCoins rounds oldCoins) r0 first.samples with hO
  set N := ((Finset.range basePending).filter (fun k =>
      Kr25Ssmxt.survives (spliceCoins preCoins fresh preRounds)
        (preRounds + r0) (d.state.nextLabel + k))) with hN
  have hB := twoStageSurvivorCount_eq_absoluteSurvivorCount preCoins fresh
    preRounds d.state.nextLabel basePending r0
  rw [hB]
  let f : SampleCopy n → Nat × Nat := fun copy => d.origin copy.1
  let g : Nat → Nat × Nat := fun k => (d.source.processed, d.state.nextLabel + k)
  -- facts about old copies
  have hOsub : ∀ copy ∈ O, copy ∈ d.state.samples ∧
      copy.2.toPoint ∉ P.carrier := by
    intro copy hcopy
    have h1 : copy ∈ first.samples := (Finset.mem_filter.mp hcopy).1
    have h2 : copy ∈ deleted.samples := (Finset.mem_filter.mp h1).1
    exact Finset.mem_filter.mp h2
  have hdeletedSurv : ManuscriptOriginSurvives deleted d.origin
      d.source.coins d.level :=
    manuscriptOriginSurvives_removeComponent d.state P d.origin
      d.source.coins d.level d.survives
  have hfirstSurv : ManuscriptOriginSurvives first d.origin d.source.coins
      (d.level + rounds) :=
    manuscriptOriginSurvives_thin_of_samples deleted first d.origin
      d.source.coins d.level rounds rfl hdeletedSurv
  have hOSurv : ManuscriptOriginSurvives
      ({ rate := first.rate, samples := O, nextLabel := first.nextLabel } :
        TTCState n) d.origin d.source.coins (d.level + rounds + r0) := by
    apply manuscriptOriginSurvives_thin_of_samples first _ d.origin
      d.source.coins (d.level + rounds) r0 _ hfirstSurv
    change O = _
    rw [hO, shiftCoins_sourceOldCoins]
  have hinj : Set.InjOn f O := by
    intro a ha b hb hab
    have ha' := (hOsub a ha).1
    have hb' := (hOsub b hb).1
    have hlab : a.1 = b.1 :=
      d.history.2 a.1 b.1 (d.fresh.1 a ha') (d.fresh.1 b hb') hab
    exact d.fresh.2 a ha' b hb' hlab
  have hginj : Function.Injective g := by
    intro a b hab
    exact Nat.add_left_cancel (congrArg Prod.snd hab)
  have hdisj : Disjoint (O.image f) (N.image g) := by
    apply Finset.disjoint_left.mpr
    intro tag hold hnew
    obtain ⟨copy, hcopy, rfl⟩ := Finset.mem_image.mp hold
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hnew
    have hlt := d.bound _ (d.valid copy (hOsub copy hcopy).1)
    have h1 := congrArg Prod.fst hk
    change d.source.processed = (d.origin copy.1).1 at h1
    omega
  have hsub : O.image f ∪ N.image g ⊆
      (d.source.step step).valid.filter fun tag =>
        Kr25Ssmxt.survives ((d.source.step step).coins tag.1) level0 tag.2 := by
    intro tag htag
    rcases Finset.mem_union.mp htag with hold | hnew
    · obtain ⟨copy, hcopy, rfl⟩ := Finset.mem_image.mp hold
      obtain ⟨hmem, hout⟩ := hOsub copy hcopy
      have hvalid := d.valid copy hmem
      have hlt := d.bound _ hvalid
      apply Finset.mem_filter.mpr
      constructor
      · change f copy ∈ manuscriptValidUpdate d.source.valid d.source.marks P
          d.source.processed d.state.nextLabel basePending
        apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨hvalid, ?_⟩
        change (d.source.marks (d.origin copy.1)).toPoint ∉ P.carrier
        rw [← d.marked copy hmem]
        exact hout
      · change Kr25Ssmxt.survives (manuscriptCoinsAppend d.source.coins
          d.source.processed preCoins fresh preRounds (f copy).1) level0
          (f copy).2
        rw [manuscriptCoinsAppend_old d.source.coins d.source.processed
          (f copy).1 preCoins fresh preRounds hlt, hlevel]
        exact hOSurv copy hcopy
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hnew
      have hk' := Finset.mem_filter.mp hk
      apply Finset.mem_filter.mpr
      constructor
      · change g k ∈ manuscriptValidUpdate d.source.valid d.source.marks P
          d.source.processed d.state.nextLabel basePending
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨k, hk'.1, rfl⟩
      · change Kr25Ssmxt.survives (manuscriptCoinsAppend d.source.coins
          d.source.processed preCoins fresh preRounds (g k).1) level0
          (g k).2
        change Kr25Ssmxt.survives (manuscriptCoinsAppend d.source.coins
          d.source.processed preCoins fresh preRounds d.source.processed)
          level0 (d.state.nextLabel + k)
        rw [manuscriptCoinsAppend_new, hlevel]
        exact hk'.2
  calc O.card + N.card = (O.image f).card + (N.image g).card := by
        rw [Finset.card_image_of_injOn hinj,
          Finset.card_image_of_injective _ hginj]
    _ = (O.image f ∪ N.image g).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem ManuscriptOriginConfiguration.refreshed_advance_crossing
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins fresh : Nat × Nat → Bool)
    (oldFuture : Nat × (Nat × Nat) → Bool)
    (tape : Nat → LatticePoint n) (level0 : Nat)
    (hfirst : c.level + manuscriptRateExit (c.state.removeComponent P)
      intensity threshold ≤ level0)
    (hcross : level0 < ((c.refreshFuture oldFuture).advance P intensity
      threshold basePending preCoins fresh tape).level)
    (S : Finset (LatticePoint n))
    (hmarks : ((c.refreshFuture oldFuture).advance P intensity threshold
      basePending preCoins fresh tape).MarksIn S) :
    threshold < ((∑ x : S, ((c.refreshFuture oldFuture).advance P intensity
      threshold basePending preCoins fresh tape).source.pointCounts
        level0 S x : Nat) : Real) := by
  classical
  set d := c.refreshFuture oldFuture with hd
  have hfirst' : d.level + manuscriptRateExit (d.state.removeComponent P)
      intensity threshold ≤ level0 := hfirst
  clear_value d
  have hm := hmarks
  unfold ManuscriptOriginConfiguration.MarksIn at hm
  rw [ManuscriptOriginConfiguration.advance_source] at hm
  rw [ManuscriptOriginConfiguration.advance_level] at hcross
  dsimp only at hcross
  rw [ManuscriptOriginConfiguration.advance_source,
    manuscriptOriginSourceState_sum_pointCounts_eq_card _ _ _ hm]
  set r0 := level0 - (d.level + manuscriptRateExit (d.state.removeComponent P)
    intensity threshold) with hr0def
  have hlevel : level0 = d.level + manuscriptRateExit
      (d.state.removeComponent P) intensity threshold + r0 := by omega
  have hr0 : r0 < firstExitRoundSplit
      (manuscriptRateThinningResult (d.state.removeComponent P) intensity
        threshold (manuscriptSourceOldCoins d.origin d.source.coins d.level))
      (pendingAfter preCoins (d.level + manuscriptRateExit
        (d.state.removeComponent P) intensity threshold)
        (d.state.removeComponent P).nextLabel basePending) threshold
      (shiftCoins (manuscriptRateExit (d.state.removeComponent P) intensity
        threshold) (manuscriptSourceOldCoins d.origin d.source.coins d.level))
      (pendingCoinExtension (d.state.removeComponent P).nextLabel
        (pendingAfter preCoins (d.level + manuscriptRateExit
          (d.state.removeComponent P) intensity threshold)
          (d.state.removeComponent P).nextLabel basePending)
        (originalSurvivorCoinRestriction preCoins
          (d.level + manuscriptRateExit (d.state.removeComponent P)
            intensity threshold)
          (d.state.removeComponent P).nextLabel basePending fresh)) := by
    omega
  have hpop := lt_population_of_lt_firstExitRoundSplit _ _ _ _ _ r0 hr0
  have hcore := d.split_population_le_survivors P intensity threshold
    basePending preCoins fresh tape r0 level0 hlevel
  have hcore' := (Nat.cast_le (α := Real)).mpr hcore
  push_cast at hcore'
  exact lt_of_lt_of_le hpop hcore'

end Kr25Ssmxt

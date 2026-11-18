import Kr25Ssmxt.Analysis.OriginKernelAdvance
import Kr25Ssmxt.Analysis.OldCoinKernel

/-! Refresh the unobserved absolute-time source tails without changing the
current executable state or any of its ghost invariants. -/

namespace Kr25Ssmxt

open MeasureTheory

def refreshedSourceCoins
    (sources : Nat → Nat × Nat → Bool) (level : Nat)
    (future : Nat × (Nat × Nat) → Bool) :
    Nat → Nat × Nat → Bool :=
  fun component => spliceCoins (sources component)
    (fun pair => future (component, (pair.1, pair.2))) level

def originCoinPrefix (rounds : Nat)
    (sources : Nat → Nat × Nat → Bool) :
    Nat → Nat × Nat → Bool :=
  fun component => coinPrefix rounds (sources component)

theorem refreshedSourceCoins_prefix
    (sources : Nat → Nat × Nat → Bool) (level : Nat)
    (future : Nat × (Nat × Nat) → Bool)
    (component round label : Nat) (hround : round < level) :
    refreshedSourceCoins sources level future component
      (round, label) = sources component (round, label) := by
  simp [refreshedSourceCoins, spliceCoins, hround]

/-- A second refresh at the same level overwrites the first unobserved tail. -/
theorem refreshedSourceCoins_twice
    (sources : Nat → Nat × Nat → Bool) (level : Nat)
    (first second : Nat × (Nat × Nat) → Bool) :
    refreshedSourceCoins
      (refreshedSourceCoins sources level first) level second =
    refreshedSourceCoins sources level second := by
  funext component pair
  by_cases hround : pair.1 < level
  · simp [refreshedSourceCoins, spliceCoins, hround]
  · simp [refreshedSourceCoins, spliceCoins, hround]

theorem originCoinPrefix_refreshed
    (sources : Nat → Nat × Nat → Bool) (level observedLevel : Nat)
    (future : Nat × (Nat × Nat) → Bool)
    (hle : observedLevel ≤ level) :
    originCoinPrefix observedLevel
      (refreshedSourceCoins sources level future) =
    originCoinPrefix observedLevel sources := by
  funext component pair
  by_cases hround : pair.1 < observedLevel
  · simp only [originCoinPrefix, coinPrefix, hround, ite_true]
    exact refreshedSourceCoins_prefix sources level future
      component pair.1 pair.2 (by omega)
  · simp [originCoinPrefix, coinPrefix, hround]

theorem survives_refreshedSourceCoins_iff_le
    (sources : Nat → Nat × Nat → Bool) (level : Nat)
    (future : Nat × (Nat × Nat) → Bool)
    (component label observedLevel : Nat) (hle : observedLevel ≤ level) :
    survives (refreshedSourceCoins sources level future component)
      observedLevel label ↔
    survives (sources component) observedLevel label := by
  constructor
  · intro h round hround
    rw [← refreshedSourceCoins_prefix sources level future
      component round label (by omega)]
    exact h round hround
  · intro h round hround
    rw [refreshedSourceCoins_prefix sources level future
      component round label (by omega)]
    exact h round hround

theorem survives_refreshedSourceCoins_iff
    (sources : Nat → Nat × Nat → Bool) (level : Nat)
    (future : Nat × (Nat × Nat) → Bool)
    (component label : Nat) :
    survives (refreshedSourceCoins sources level future component)
      level label ↔
    survives (sources component) level label := by
  change survives
      (spliceCoins (sources component)
        (fun pair => future (component, (pair.1, pair.2))) level)
      level label ↔ _
  have hzero : survives
      (fun pair : Nat × Nat => future (component, (pair.1, pair.2)))
      0 label := by
    intro r hr
    omega
  simpa only [Nat.add_zero, hzero, and_true] using
    (survives_spliceCoins (sources component)
      (fun pair => future (component, (pair.1, pair.2))) level 0 label)

/-- At a later absolute level, survival splits into the already observed
prefix and the independent newly refreshed tail. -/
theorem survives_refreshedSourceCoins_future
    (sources : Nat → Nat × Nat → Bool) (level : Nat)
    (future : Nat × (Nat × Nat) → Bool)
    (component label observedLevel : Nat)
    (hle : level ≤ observedLevel) :
    survives (refreshedSourceCoins sources level future component)
      observedLevel label ↔
    survives (sources component) level label ∧
      survives (fun pair : Nat × Nat =>
        future (component, pair))
        (observedLevel - level) label := by
  have hcoins :
      refreshedSourceCoins sources level future component =
        spliceCoins (sources component)
          (fun pair : Nat × Nat => future (component, pair)) level := rfl
  rw [hcoins]
  simpa only [Nat.add_sub_of_le hle] using
    (survives_spliceCoins (sources component)
      (fun pair : Nat × Nat => future (component, pair)) level
      (observedLevel - level) label)

noncomputable def OriginConfiguration.refreshFuture
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) :
    OriginConfiguration n where
  state := c.state
  source := { c.source with
    coins := refreshedSourceCoins c.source.coins c.level future }
  origin := c.origin
  level := c.level
  p := c.p
  fresh := c.fresh
  history := c.history
  valid := c.valid
  marked := c.marked
  survives := by
    intro copy hcopy
    exact (survives_refreshedSourceCoins_iff c.source.coins
      c.level future (c.origin copy.1).1 (c.origin copy.1).2).2
        (c.survives copy hcopy)
  complete := by
    intro tag htag hsurv
    exact c.complete tag htag
      ((survives_refreshedSourceCoins_iff c.source.coins
        c.level future tag.1 tag.2).1 hsurv)
  bound := c.bound

theorem OriginSourceState.ext_data
    {n : Nat} {a b : OriginSourceState n}
    (hprocessed : a.processed = b.processed)
    (hvalid : a.valid = b.valid) (hmarks : a.marks = b.marks)
    (hcoins : a.coins = b.coins) : a = b := by
  cases a
  cases b
  cases hprocessed
  cases hvalid
  cases hmarks
  cases hcoins
  rfl

theorem OriginConfiguration.ext_data
    {n : Nat} {a b : OriginConfiguration n}
    (hstate : a.state = b.state) (hsource : a.source = b.source)
    (horigin : a.origin = b.origin) (hlevel : a.level = b.level) :
    a = b := by
  cases a
  cases b
  cases hstate
  cases hsource
  cases horigin
  cases hlevel
  rfl

theorem OriginConfiguration.refreshFuture_twice
    {n : Nat} (c : OriginConfiguration n)
    (first second : Nat × (Nat × Nat) → Bool) :
    (c.refreshFuture first).refreshFuture second =
      c.refreshFuture second := by
  apply OriginConfiguration.ext_data
  · rfl
  · apply OriginSourceState.ext_data
    · rfl
    · rfl
    · rfl
    · exact refreshedSourceCoins_twice
        c.source.coins c.level first second
  · rfl
  · rfl

/-- A canonical representative retaining the observed prefix and replacing
all unobserved source coins by false. -/
noncomputable def OriginConfiguration.observedRepresentative
    {n : Nat} (c : OriginConfiguration n) :
    OriginConfiguration n :=
  c.refreshFuture (fun _ => false)

/-- Read unused source coins relative to the current absolute level. -/
def OriginConfiguration.unusedTail
    {n : Nat} (c : OriginConfiguration n) :
    Nat × (Nat × Nat) → Bool :=
  fun index => c.source.coins index.1
    (c.level + index.2.1, index.2.2)

theorem OriginConfiguration.refreshFuture_unusedTail
    {n : Nat} (c : OriginConfiguration n) :
    c.refreshFuture c.unusedTail = c := by
  apply OriginConfiguration.ext_data
  · rfl
  · apply OriginSourceState.ext_data
    · rfl
    · rfl
    · rfl
    · funext component pair
      change refreshedSourceCoins c.source.coins c.level
          c.unusedTail component pair = c.source.coins component pair
      by_cases hround : pair.1 < c.level
      · simp [OriginConfiguration.unusedTail,
          refreshedSourceCoins, spliceCoins, hround]
      · have hadd : c.level + (pair.1 - c.level) = pair.1 := by omega
        simp [OriginConfiguration.unusedTail,
          refreshedSourceCoins, spliceCoins, hround, hadd]
  · rfl
  · rfl

theorem OriginConfiguration.unusedTail_refreshFuture
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) :
    (c.refreshFuture future).unusedTail = future := by
  funext index
  have hnot : ¬ c.level + index.2.1 < c.level := by omega
  change refreshedSourceCoins c.source.coins c.level future
      index.1 (c.level + index.2.1, index.2.2) = future index
  simp [refreshedSourceCoins, spliceCoins, hnot]

theorem OriginConfiguration.observedRepresentative_refresh
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) :
    (c.refreshFuture future).observedRepresentative =
      c.observedRepresentative := by
  exact c.refreshFuture_twice future (fun _ => false)

theorem OriginConfiguration.observedRepresentative_refreshFuture
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) :
    (c.observedRepresentative).refreshFuture future =
      c.refreshFuture future := by
  exact c.refreshFuture_twice (fun _ => false) future

theorem OriginConfiguration.observedRepresentative_refreshFuture_fun
    {n : Nat} (c : OriginConfiguration n) :
    (c.observedRepresentative).refreshFuture = c.refreshFuture := by
  funext future
  exact c.observedRepresentative_refreshFuture future

theorem OriginConfiguration.refreshFuture_state
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) :
    (c.refreshFuture future).state = c.state := rfl

theorem OriginConfiguration.refreshFuture_past_coinPrefix
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool)
    (observedLevel : Nat) (hle : observedLevel ≤ c.level) :
    originCoinPrefix observedLevel
      (c.refreshFuture future).source.coins =
    originCoinPrefix observedLevel c.source.coins := by
  exact originCoinPrefix_refreshed c.source.coins c.level
    observedLevel future hle

/-- Refreshing source tails does not change point counts at any absolute
level already reached by the ghost configuration. -/
theorem OriginConfiguration.refreshFuture_past_pointCounts
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) (observedLevel : Nat)
    (hle : observedLevel ≤ c.level)
    (S : Finset (LatticePoint n)) :
    (c.refreshFuture future).source.pointCounts observedLevel S =
      c.source.pointCounts observedLevel S := by
  classical
  funext x
  change (c.source.valid.filter fun tag : Nat × Nat =>
      Kr25Ssmxt.survives
        (refreshedSourceCoins c.source.coins c.level future tag.1)
        observedLevel tag.2 ∧ c.source.marks tag = x.1).card =
    (c.source.valid.filter fun tag : Nat × Nat =>
      Kr25Ssmxt.survives (c.source.coins tag.1) observedLevel tag.2 ∧
        c.source.marks tag = x.1).card
  congr 1
  ext tag
  simp only [Finset.mem_filter]
  rw [survives_refreshedSourceCoins_iff_le
    c.source.coins c.level future tag.1 tag.2 observedLevel hle]

noncomputable def refreshedFuturePointCounts
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) (observedLevel : Nat)
    (S : Finset (LatticePoint n)) : S → Nat := by
  classical
  exact fun x : S =>
    (c.source.valid.filter fun (tag : Nat × Nat) =>
      Kr25Ssmxt.survives (c.source.coins tag.1) c.level tag.2 ∧
      Kr25Ssmxt.survives (fun pair => future (tag.1, pair))
        (observedLevel - c.level) tag.2 ∧
      c.source.marks tag = x.1).card

/-- At a future level, the refreshed old point count is a finite count of
copies surviving the observed prefix and an independent fair tail. -/
theorem OriginConfiguration.refreshFuture_future_pointCounts
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) (observedLevel : Nat)
    (hle : c.level ≤ observedLevel)
    (S : Finset (LatticePoint n)) :
    (c.refreshFuture future).source.pointCounts observedLevel S =
      refreshedFuturePointCounts c future observedLevel S := by
  classical
  funext x
  change (c.source.valid.filter fun tag : Nat × Nat =>
      Kr25Ssmxt.survives
        (refreshedSourceCoins c.source.coins c.level future tag.1)
        observedLevel tag.2 ∧ c.source.marks tag = x.1).card =
      (c.source.valid.filter fun tag : Nat × Nat =>
        Kr25Ssmxt.survives (c.source.coins tag.1) c.level tag.2 ∧
        Kr25Ssmxt.survives (fun pair => future (tag.1, pair))
          (observedLevel - c.level) tag.2 ∧
        c.source.marks tag = x.1).card
  apply congrArg Finset.card
  ext tag
  simp only [Finset.mem_filter]
  rw [survives_refreshedSourceCoins_future
    c.source.coins c.level future tag.1 tag.2 observedLevel hle]
  tauto

theorem OriginConfiguration.refreshFuture_oldCoins
    {n : Nat} (c : OriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) :
    sourceOldCoins (c.refreshFuture future).origin
      (c.refreshFuture future).source.coins (c.refreshFuture future).level =
    fun pair => future ((c.origin pair.2).1,
      (pair.1, (c.origin pair.2).2)) := by
  funext pair
  simp [OriginConfiguration.refreshFuture,
    sourceOldCoins, refreshedSourceCoins,
    spliceCoins]

/-- Refreshing with a global independent fair source gives exactly the
allocated old-copy fair block required by the executable component kernel. -/
theorem OriginConfiguration.refreshFuture_allocatedOldCoinLaw
    {n : Nat} (c : OriginConfiguration n) :
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
        (fun future => allocatedCoinRestriction c.state.nextLabel
          (sourceOldCoins (c.refreshFuture future).origin
            (c.refreshFuture future).source.coins
            (c.refreshFuture future).level)) =
    Measure.infinitePi
      (fun _ : Nat × Fin c.state.nextLabel => fairCoinLaw) := by
  have hmap := origin_coins_on_allocated_labels
    c.state.nextLabel c.source.processed c.origin c.history
  have hfunctions :
      (fun future => allocatedCoinRestriction c.state.nextLabel
        (sourceOldCoins (c.refreshFuture future).origin
          (c.refreshFuture future).source.coins
          (c.refreshFuture future).level)) =
      (fun future pair => future
        (originCoinIndex c.state.nextLabel c.origin pair)) := by
    funext future pair
    change sourceOldCoins (c.refreshFuture future).origin
        (c.refreshFuture future).source.coins
        (c.refreshFuture future).level (pair.1, pair.2.val) =
      future ((c.origin pair.2.val).1,
        (pair.1, (c.origin pair.2.val).2))
    exact congrFun (c.refreshFuture_oldCoins future)
      (pair.1, pair.2.val)
  rw [hfunctions]
  exact hmap

/-- After refreshing the unused source tail, the old-copy decisions seen by
one executable component step have the same law as a fresh fair block.  The
statement keeps the new-copy decisions fixed, so it can be used inside the
later independent new-coin and point-tape draws. -/
theorem OriginConfiguration.refreshFuture_oldKernelLaw
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) (intensity : NNReal)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (fresh : Nat × Fin (pendingAfter preCoins preRounds
      (c.state.removeComponent P).nextLabel basePending) → Bool) :
    let s := c.state.removeComponent P
    let K := communityOriginTapeKernel hn P b eta threshold hroute
      s intensity preCoins preRounds basePending
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).bind (fun future =>
        K (sourceOldCoins (c.refreshFuture future).origin
          (c.refreshFuture future).source.coins
          (c.refreshFuture future).level, fresh)) =
    (Measure.infinitePi
      (fun _ : Nat × Fin s.nextLabel => fairCoinLaw)).bind (fun old =>
        K (allocatedCoinExtension s.nextLabel old, fresh)) := by
  dsimp only
  let s := c.state.removeComponent P
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let oldLaw : Measure (Nat × Fin s.nextLabel → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let oldOf : (Nat × (Nat × Nat) → Bool) →
      Nat × Fin s.nextLabel → Bool := fun future =>
    allocatedCoinRestriction s.nextLabel
      (sourceOldCoins (c.refreshFuture future).origin
        (c.refreshFuture future).source.coins
        (c.refreshFuture future).level)
  have hmap : sourceLaw.map oldOf = oldLaw := by
    dsimp only [sourceLaw, oldLaw, oldOf, s]
    exact c.refreshFuture_allocatedOldCoinLaw
  have holdOf : Measurable oldOf := by
    have hfun : oldOf = fun future pair =>
        future (originCoinIndex c.state.nextLabel c.origin pair) := by
      funext future pair
      exact congrFun (c.refreshFuture_oldCoins future) (pair.1, pair.2.val)
    rw [hfun]
    exact Measurable.of_eval (fun pair =>
      measurable_pi_apply (originCoinIndex
        c.state.nextLabel c.origin pair))
  let K := communityOriginTapeKernel hn P b eta threshold hroute
    s intensity preCoins preRounds basePending
  let K' : (Nat × Fin s.nextLabel → Bool) → Measure (TTCState n) :=
    fun old => K (allocatedCoinExtension s.nextLabel old, fresh)
  have hK' : Measurable K' := by
    exact (measurable_communityOriginTapeKernel hn prep P b eta
      delta threshold hroute s intensity
      (c.state.labelsFresh_removeComponent P c.fresh)
      preCoins preRounds basePending).comp
        (((measurable_allocatedCoinExtension s.nextLabel).prodMk
          measurable_const))
  have hpoint : ∀ future, K
      (sourceOldCoins (c.refreshFuture future).origin
        (c.refreshFuture future).source.coins
        (c.refreshFuture future).level, fresh) = K' (oldOf future) := by
    intro future
    exact communityOriginTapeKernel_eq_allocated_extension
      hn P b eta threshold hroute s intensity preCoins preRounds
      basePending _ fresh (c.state.labelsFresh_removeComponent P c.fresh)
  change sourceLaw.bind (fun future => K
    (sourceOldCoins (c.refreshFuture future).origin
      (c.refreshFuture future).source.coins
      (c.refreshFuture future).level, fresh)) = oldLaw.bind K'
  rw [← hmap, bind_mapped_measure sourceLaw oldOf holdOf K' hK']
  exact Measure.bind_congr_right (Filter.Eventually.of_forall hpoint)

/-- Refreshing the old source and drawing the fresh source independently
reproduces both finite coin blocks consumed by one component transition. -/
theorem OriginConfiguration.refreshFuture_jointCoinKernelLaw
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) (intensity : NNReal)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat) :
    let s := c.state.removeComponent P
    let K := communityOriginTapeKernel hn P b eta threshold hroute
      s intensity preCoins preRounds basePending
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).bind (fun pair =>
        K (sourceOldCoins (c.refreshFuture pair.1).origin
          (c.refreshFuture pair.1).source.coins
          (c.refreshFuture pair.1).level,
          originalSurvivorCoinRestriction preCoins preRounds s.nextLabel
            basePending pair.2)) =
    ((Measure.infinitePi
      (fun _ : Nat × Fin s.nextLabel => fairCoinLaw)).prod
      (Measure.infinitePi (fun _ : Nat × Fin
        (pendingAfter preCoins preRounds s.nextLabel basePending) =>
          fairCoinLaw))).bind (fun pair =>
        K (allocatedCoinExtension s.nextLabel pair.1, pair.2)) := by
  dsimp only
  let s := c.state.removeComponent P
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let oldLaw : Measure (Nat × Fin s.nextLabel → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let freshLaw : Measure (Nat × Fin pending → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let oldOf : (Nat × (Nat × Nat) → Bool) →
      Nat × Fin s.nextLabel → Bool := fun future =>
    allocatedCoinRestriction s.nextLabel
      (sourceOldCoins (c.refreshFuture future).origin
        (c.refreshFuture future).source.coins
        (c.refreshFuture future).level)
  let freshOf := originalSurvivorCoinRestriction preCoins preRounds
    s.nextLabel basePending
  have hmapOld : sourceLaw.map oldOf = oldLaw := by
    dsimp only [sourceLaw, oldLaw, oldOf, s]
    exact c.refreshFuture_allocatedOldCoinLaw
  have hmapFresh : fairCoinStreamLaw.map freshOf = freshLaw := by
    exact fairCoinStreamLaw_originalSurvivorCoinRestriction
      preCoins preRounds s.nextLabel basePending
  have holdOf : Measurable oldOf := by
    have hfun : oldOf = fun future pair =>
        future (originCoinIndex c.state.nextLabel c.origin pair) := by
      funext future pair
      exact congrFun (c.refreshFuture_oldCoins future) (pair.1, pair.2.val)
    rw [hfun]
    exact Measurable.of_eval (fun pair =>
      measurable_pi_apply (originCoinIndex
        c.state.nextLabel c.origin pair))
  have hfreshOf : Measurable freshOf :=
    measurable_originalSurvivorCoinRestriction preCoins preRounds
      s.nextLabel basePending
  let project : ((Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool)) →
      (Nat × Fin s.nextLabel → Bool) ×
      (Nat × Fin pending → Bool) :=
    fun pair => (oldOf pair.1, freshOf pair.2)
  have hproject : Measurable project :=
    (holdOf.comp measurable_fst).prodMk
      (hfreshOf.comp measurable_snd)
  have hjoint : (sourceLaw.prod fairCoinStreamLaw).map project =
      oldLaw.prod freshLaw := by
    letI : IsProbabilityMeasure sourceLaw := by
      dsimp [sourceLaw]
      letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
        fun _ => fairCoinLaw_isProbabilityMeasure
      infer_instance
    letI : IsProbabilityMeasure fairCoinStreamLaw :=
      fairCoinStreamLaw_isProbabilityMeasure
    change (sourceLaw.prod fairCoinStreamLaw).map
      (Prod.map oldOf freshOf) = oldLaw.prod freshLaw
    calc
      _ = (sourceLaw.map oldOf).prod
          (fairCoinStreamLaw.map freshOf) :=
        (Measure.map_prod_map sourceLaw fairCoinStreamLaw
          holdOf hfreshOf).symm
      _ = oldLaw.prod freshLaw := by rw [hmapOld, hmapFresh]
  let K := communityOriginTapeKernel hn P b eta threshold hroute
    s intensity preCoins preRounds basePending
  let K' : (Nat × Fin s.nextLabel → Bool) ×
      (Nat × Fin pending → Bool) → Measure (TTCState n) :=
    fun pair => K (allocatedCoinExtension s.nextLabel pair.1, pair.2)
  have hK' : Measurable K' := by
    exact (measurable_communityOriginTapeKernel hn prep P b eta
      delta threshold hroute s intensity
      (c.state.labelsFresh_removeComponent P c.fresh)
      preCoins preRounds basePending).comp
        (((measurable_allocatedCoinExtension s.nextLabel).comp
          measurable_fst).prodMk measurable_snd)
  have hpoint : ∀ pair : (Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool),
      K (sourceOldCoins (c.refreshFuture pair.1).origin
        (c.refreshFuture pair.1).source.coins
        (c.refreshFuture pair.1).level, freshOf pair.2) =
      K' (project pair) := by
    intro pair
    exact communityOriginTapeKernel_eq_allocated_extension
      hn P b eta threshold hroute s intensity preCoins preRounds
      basePending _ _ (c.state.labelsFresh_removeComponent P c.fresh)
  change (sourceLaw.prod fairCoinStreamLaw).bind
    (fun pair => K
      (sourceOldCoins (c.refreshFuture pair.1).origin
        (c.refreshFuture pair.1).source.coins
        (c.refreshFuture pair.1).level, freshOf pair.2)) =
    (oldLaw.prod freshLaw).bind K'
  rw [← hjoint, bind_mapped_measure _ project hproject K' hK']
  exact Measure.bind_congr_right (Filter.Eventually.of_forall hpoint)

/-- The executable state projection of one refreshed ghost transition is the
finite old/new coin source kernel, conditional on the Poisson draw and the
first-loop coin stream. -/
theorem OriginConfiguration.refreshFuture_advance_state_law
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) (intensity : NNReal)
    (basePending : Nat) (preCoins : Nat × Nat → Bool) :
    let s := c.state.removeComponent P
    let preRounds := c.level + ttcReference.firstLoopExit s intensity threshold
    let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).bind (fun pair =>
        (Measure.infinitePi (fun _ : Nat => pointLaw)).map (fun tape =>
          ((c.refreshFuture pair.1).advance P intensity threshold
            basePending preCoins pair.2 tape).state)) =
    ((Measure.infinitePi
      (fun _ : Nat × Fin s.nextLabel => fairCoinLaw)).prod
      (Measure.infinitePi (fun _ : Nat × Fin
        (pendingAfter preCoins preRounds s.nextLabel basePending) =>
          fairCoinLaw))).bind (fun pair =>
        communityOriginTapeKernel hn P b eta threshold hroute
          s intensity preCoins preRounds basePending
          (allocatedCoinExtension s.nextLabel pair.1, pair.2)) := by
  dsimp only
  let s := c.state.removeComponent P
  let preRounds := c.level + ttcReference.firstLoopExit s intensity threshold
  let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let K := communityOriginTapeKernel hn P b eta threshold hroute
    s intensity preCoins preRounds basePending
  calc
    (sourceLaw.prod fairCoinStreamLaw).bind (fun pair =>
        (Measure.infinitePi (fun _ : Nat => pointLaw)).map (fun tape =>
          ((c.refreshFuture pair.1).advance P intensity threshold
            basePending preCoins pair.2 tape).state)) =
      (sourceLaw.prod fairCoinStreamLaw).bind (fun pair =>
        K (sourceOldCoins (c.refreshFuture pair.1).origin
          (c.refreshFuture pair.1).source.coins
          (c.refreshFuture pair.1).level,
          originalSurvivorCoinRestriction preCoins preRounds s.nextLabel
            basePending pair.2)) := by
        apply Measure.bind_congr_right
        apply Filter.Eventually.of_forall
        intro pair
        exact (c.refreshFuture pair.1).advance_state_tapeLaw hn P b eta
          threshold hroute intensity basePending preCoins pair.2
    _ = _ := c.refreshFuture_jointCoinKernelLaw hn prep P b eta delta
      threshold hroute intensity preCoins preRounds basePending

/-- The state marginal of the complete refreshed ghost step agrees with the
actual paper component program after its CV18 volume outcome is fixed. -/
theorem OriginConfiguration.refreshFuture_component_state_law
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) (outcome : VolumeOutcome) :
    let intensity := ttcReference.t b n threshold outcome.2
    let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    (ProbabilityTheory.poissonMeasure intensity).bind (fun basePending =>
      fairCoinStreamLaw.bind (fun preCoins =>
        ((Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw).bind (fun pair =>
            (Measure.infinitePi (fun _ : Nat => pointLaw)).map (fun tape =>
              ((c.refreshFuture pair.1).advance P intensity threshold
                basePending preCoins pair.2 tape).state)))) =
      communityComponentGivenVolume hn prep P b eta delta
        threshold outcome c.state := by
  dsimp only
  let intensity := ttcReference.t b n threshold outcome.2
  have hgiven := communityComponentGivenVolume_eq_finiteCoinSourceKernel
    hn prep P b eta delta threshold hroute outcome c.state c.level
      c.p c.fresh
  rw [hgiven]
  unfold communityFiniteCoinSourceKernel
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  exact c.refreshFuture_advance_state_law hn prep P b eta delta
    threshold hroute intensity basePending preCoins

/-- Including the CV18 draw, the refreshed source transition has precisely
the state law of `ttcReference.step`. -/
theorem OriginConfiguration.refreshFuture_programComponent_law
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) :
    ((ttcSubroutines hn prep).ComputeVolume P eta delta).bind
      (fun outcome =>
        let intensity := ttcReference.t b n threshold outcome.2
        let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
          hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
        (ProbabilityTheory.poissonMeasure intensity).bind
          (fun basePending =>
            fairCoinStreamLaw.bind (fun preCoins =>
              ((Measure.infinitePi
                (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
                fairCoinStreamLaw).bind (fun pair =>
                  (Measure.infinitePi (fun _ : Nat => pointLaw)).map
                    (fun tape =>
                      ((c.refreshFuture pair.1).advance P intensity threshold
                        basePending preCoins pair.2 tape).state))))) =
      ttcReference.step (ttcSubroutines hn prep)
        b eta delta threshold P c.state := by
  unfold ttcReference.step
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro outcome
  exact c.refreshFuture_component_state_law hn prep P b eta delta
    threshold hroute outcome

end Kr25Ssmxt

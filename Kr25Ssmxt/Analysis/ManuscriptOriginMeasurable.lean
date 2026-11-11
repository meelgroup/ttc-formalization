import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ManuscriptSourceRefresh

/-! Product measurable structures for the source and ghost configuration.
Proof fields carry no extra observations. -/

namespace Kr25Ssmxt

open MeasureTheory

instance ManuscriptOriginSourceState.instMeasurableSpace (n : Nat) :
    MeasurableSpace (ManuscriptOriginSourceState n) :=
  MeasurableSpace.comap
    (fun g => (g.processed, g.valid, g.marks, g.coins)) inferInstance

theorem measurable_manuscriptOriginSourceState_data {n : Nat} :
    Measurable (fun g : ManuscriptOriginSourceState n =>
      (g.processed, g.valid, g.marks, g.coins)) :=
  comap_measurable _

instance ManuscriptOriginConfiguration.instMeasurableSpace (n : Nat) :
    MeasurableSpace (ManuscriptOriginConfiguration n) :=
  MeasurableSpace.comap
    (fun c => (c.state, c.source, c.origin, c.level)) inferInstance

theorem measurable_manuscriptOriginConfiguration_data {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      (c.state, c.source, c.origin, c.level)) :=
  comap_measurable _

theorem measurable_manuscriptOriginConfiguration_state {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n => c.state) :=
  measurable_fst.comp measurable_manuscriptOriginConfiguration_data

theorem measurable_manuscriptOriginConfiguration_source {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n => c.source) :=
  measurable_fst.comp
    (measurable_snd.comp measurable_manuscriptOriginConfiguration_data)

theorem measurable_manuscriptOriginConfiguration_origin {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n => c.origin) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp measurable_manuscriptOriginConfiguration_data))

theorem measurable_manuscriptOriginConfiguration_level {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n => c.level) :=
  measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_manuscriptOriginConfiguration_data))

theorem measurable_manuscriptOriginSourceState_coins {n : Nat} :
    Measurable (fun g : ManuscriptOriginSourceState n => g.coins) :=
  measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_manuscriptOriginSourceState_data))

theorem measurable_manuscriptOriginCoinPrefix (rounds : Nat) :
    Measurable (manuscriptOriginCoinPrefix rounds) := by
  apply Measurable.of_eval
  intro component
  exact (measurable_coinPrefix rounds).comp
    (measurable_pi_apply component)

theorem measurable_coinPrefix_joint :
    Measurable (fun z : Nat × (Nat × Nat → Bool) =>
      coinPrefix z.1 z.2) := by
  apply Measurable.of_eval
  intro index
  have hcond : MeasurableSet
      {z : Nat × (Nat × Nat → Bool) | index.1 < z.1} :=
    measurableSet_lt measurable_const measurable_fst
  change Measurable (fun z : Nat × (Nat × Nat → Bool) =>
    if index.1 < z.1 then z.2 index else false)
  exact Measurable.ite hcond
    ((measurable_pi_apply index).comp measurable_snd)
    measurable_const

theorem measurable_manuscriptOriginCoinPrefix_joint :
    Measurable (fun z : Nat × (Nat → Nat × Nat → Bool) =>
      manuscriptOriginCoinPrefix z.1 z.2) := by
  apply Measurable.of_eval
  intro component
  exact measurable_coinPrefix_joint.comp
    (measurable_fst.prodMk
      ((measurable_pi_apply component).comp measurable_snd))

theorem measurable_manuscriptOriginSourceState_valid {n : Nat} :
    Measurable (fun g : ManuscriptOriginSourceState n => g.valid) :=
  measurable_fst.comp
    (measurable_snd.comp measurable_manuscriptOriginSourceState_data)

theorem measurable_manuscriptOriginSourceState_processed {n : Nat} :
    Measurable (fun g : ManuscriptOriginSourceState n => g.processed) :=
  measurable_fst.comp measurable_manuscriptOriginSourceState_data

theorem measurable_manuscriptOriginSourceState_marks {n : Nat} :
    Measurable (fun g : ManuscriptOriginSourceState n => g.marks) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp measurable_manuscriptOriginSourceState_data))

theorem measurable_manuscriptOriginSourceState_pointCounts
    {n : Nat} (level : Nat) (S : Finset (LatticePoint n)) :
    Measurable (fun g : ManuscriptOriginSourceState n =>
      g.pointCounts level S) := by
  classical
  apply Measurable.of_eval
  intro x
  let filtered : ManuscriptOriginSourceState n → Finset (Nat × Nat) :=
    fun g => g.valid.filter fun tag =>
      Kr25Ssmxt.survives (g.coins tag.1) level tag.2 ∧
        g.marks tag = x.1
  have hfiltered : Measurable filtered := by
    rw [measurable_finset_iff]
    intro tag
    have hvalid : Measurable (fun g : ManuscriptOriginSourceState n =>
        tag ∈ g.valid) :=
      (measurable_finset_mem tag).comp
        measurable_manuscriptOriginSourceState_valid
    have hsurv : Measurable (fun g : ManuscriptOriginSourceState n =>
        Kr25Ssmxt.survives (g.coins tag.1) level tag.2) := by
      apply measurableSet_setOfPred.mp
      exact (measurableSet_survives level tag.2).preimage
        ((measurable_pi_apply tag.1).comp
          measurable_manuscriptOriginSourceState_coins)
    have hmarks : Measurable (fun g : ManuscriptOriginSourceState n =>
        g.marks tag) :=
      (measurable_pi_apply tag).comp
        measurable_manuscriptOriginSourceState_marks
    change Measurable (fun g : ManuscriptOriginSourceState n =>
      tag ∈ g.valid.filter fun t =>
        Kr25Ssmxt.survives (g.coins t.1) level t.2 ∧
          g.marks t = x.1)
    simpa only [Finset.mem_filter] using
      hvalid.and (hsurv.and (hmarks.eq_const x.1))
  change Measurable (fun g : ManuscriptOriginSourceState n =>
    (filtered g).card)
  exact (measurable_of_countable (fun F : Finset (Nat × Nat) =>
    F.card)).comp hfiltered

theorem measurable_manuscriptRefreshedSourceCoins
    (sources : Nat → Nat × Nat → Bool) (level : Nat) :
    Measurable (manuscriptRefreshedSourceCoins sources level) := by
  apply Measurable.of_eval
  intro component
  apply Measurable.of_eval
  intro pair
  by_cases hround : pair.1 < level
  · simpa [manuscriptRefreshedSourceCoins, spliceCoins, hround] using
      (measurable_const : Measurable
        (fun _ : Nat × (Nat × Nat) → Bool => sources component pair))
  · simpa [manuscriptRefreshedSourceCoins, spliceCoins, hround] using
      (measurable_pi_apply (component, (pair.1 - level, pair.2)) :
        Measurable (fun future : Nat × (Nat × Nat) → Bool =>
          future (component, (pair.1 - level, pair.2))))

theorem ManuscriptOriginConfiguration.measurable_refreshFuture
    {n : Nat} (c : ManuscriptOriginConfiguration n) :
    Measurable c.refreshFuture := by
  rw [measurable_comap_iff]
  change Measurable (fun future : Nat × (Nat × Nat) → Bool =>
    (c.state,
      ({ c.source with
        coins := manuscriptRefreshedSourceCoins c.source.coins c.level future } :
          ManuscriptOriginSourceState n),
      c.origin, c.level))
  have hsource : Measurable (fun future : Nat × (Nat × Nat) → Bool =>
      ({ c.source with
        coins := manuscriptRefreshedSourceCoins c.source.coins c.level future } :
        ManuscriptOriginSourceState n)) := by
    rw [measurable_comap_iff]
    change Measurable (fun future : Nat × (Nat × Nat) → Bool =>
      (c.source.processed, c.source.valid, c.source.marks,
        manuscriptRefreshedSourceCoins c.source.coins c.level future))
    exact measurable_const.prodMk
      (measurable_const.prodMk
        (measurable_const.prodMk
          (measurable_manuscriptRefreshedSourceCoins c.source.coins c.level)))
  exact measurable_const.prodMk
    (hsource.prodMk (measurable_const.prodMk measurable_const))

/-- The refresh also varies measurably with a random incoming ghost state. -/
theorem ManuscriptOriginConfiguration.measurable_refreshFuture_joint
    {n : Nat} :
    Measurable (fun z : ManuscriptOriginConfiguration n ×
        (Nat × (Nat × Nat) → Bool) => z.1.refreshFuture z.2) := by
  let source : ManuscriptOriginConfiguration n ×
      (Nat × (Nat × Nat) → Bool) → ManuscriptOriginSourceState n :=
    fun z => z.1.source
  let level : ManuscriptOriginConfiguration n ×
      (Nat × (Nat × Nat) → Bool) → Nat := fun z => z.1.level
  have hsource : Measurable source :=
    measurable_manuscriptOriginConfiguration_source.comp measurable_fst
  have hlevel : Measurable level :=
    measurable_manuscriptOriginConfiguration_level.comp measurable_fst
  have hcoins : Measurable (fun z : ManuscriptOriginConfiguration n ×
      (Nat × (Nat × Nat) → Bool) => z.1.source.coins) :=
    measurable_manuscriptOriginSourceState_coins.comp hsource
  have heval : Measurable (fun z :
      (Nat × (Nat × Nat) → Bool) × (Nat × (Nat × Nat)) => z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro index
    exact measurable_pi_apply index
  have hrefreshed : Measurable (fun z : ManuscriptOriginConfiguration n ×
      (Nat × (Nat × Nat) → Bool) =>
      manuscriptRefreshedSourceCoins z.1.source.coins z.1.level z.2) := by
    apply Measurable.of_eval
    intro component
    apply Measurable.of_eval
    intro pair
    have hold : Measurable (fun z : ManuscriptOriginConfiguration n ×
        (Nat × (Nat × Nat) → Bool) =>
        z.1.source.coins component pair) :=
      (measurable_pi_apply pair).comp
        ((measurable_pi_apply component).comp hcoins)
    have hindex : Measurable (fun z : ManuscriptOriginConfiguration n ×
        (Nat × (Nat × Nat) → Bool) =>
        (component, (pair.1 - level z, pair.2))) := by
      exact measurable_const.prodMk
        (((measurable_of_countable
          (fun r : Nat => pair.1 - r)).comp hlevel).prodMk
            measurable_const)
    have hfuture : Measurable (fun z : ManuscriptOriginConfiguration n ×
        (Nat × (Nat × Nat) → Bool) =>
        z.2 (component, (pair.1 - level z, pair.2))) :=
      heval.comp (measurable_snd.prodMk hindex)
    have hcond : MeasurableSet {z : ManuscriptOriginConfiguration n ×
        (Nat × (Nat × Nat) → Bool) | pair.1 < level z} := by
      exact measurableSet_lt measurable_const hlevel
    simpa only [manuscriptRefreshedSourceCoins, spliceCoins] using
      Measurable.ite hcond hold hfuture
  rw [measurable_comap_iff]
  have hsourceData : Measurable (fun z : ManuscriptOriginConfiguration n ×
      (Nat × (Nat × Nat) → Bool) =>
      ((source z).processed, (source z).valid,
        (source z).marks, (source z).coins)) :=
    measurable_manuscriptOriginSourceState_data.comp hsource
  have hsourceNext : Measurable (fun z : ManuscriptOriginConfiguration n ×
      (Nat × (Nat × Nat) → Bool) =>
      ({ z.1.source with
        coins := manuscriptRefreshedSourceCoins z.1.source.coins
          z.1.level z.2 } : ManuscriptOriginSourceState n)) := by
    rw [measurable_comap_iff]
    change Measurable (fun z : ManuscriptOriginConfiguration n ×
      (Nat × (Nat × Nat) → Bool) =>
      ((source z).processed, (source z).valid,
        (source z).marks,
        manuscriptRefreshedSourceCoins z.1.source.coins z.1.level z.2))
    exact (measurable_fst.comp hsourceData).prodMk
      ((measurable_fst.comp (measurable_snd.comp hsourceData)).prodMk
        ((measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp hsourceData))).prodMk
          hrefreshed))
  change Measurable (fun z : ManuscriptOriginConfiguration n ×
    (Nat × (Nat × Nat) → Bool) =>
      (z.1.state,
        ({ z.1.source with
          coins := manuscriptRefreshedSourceCoins z.1.source.coins
            z.1.level z.2 } : ManuscriptOriginSourceState n),
        z.1.origin, z.1.level))
  exact (measurable_manuscriptOriginConfiguration_state.comp measurable_fst).prodMk
    (hsourceNext.prodMk
      ((measurable_manuscriptOriginConfiguration_origin.comp measurable_fst).prodMk
        hlevel))

/-- A Markov kernel on ghost configurations that resamples exactly the
unobserved future coin source. -/
noncomputable def ManuscriptOriginConfiguration.refreshLaw
    {n : Nat} (c : ManuscriptOriginConfiguration n) :
    Measure (ManuscriptOriginConfiguration n) :=
  (Measure.infinitePi
    (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map c.refreshFuture

theorem ManuscriptOriginConfiguration.refreshLaw_isProbabilityMeasure
    {n : Nat} (c : ManuscriptOriginConfiguration n) :
    IsProbabilityMeasure c.refreshLaw := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  change IsProbabilityMeasure (sourceLaw.map c.refreshFuture)
  exact Measure.isProbabilityMeasure_map c.measurable_refreshFuture.aemeasurable

theorem measurable_manuscriptOriginConfiguration_refreshLaw
    {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n => c.refreshLaw) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  have hprob : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  have hnext : Measurable
      (fun z : ManuscriptOriginConfiguration n ×
          (Nat × (Nat × Nat) → Bool) =>
        Measure.dirac (z.1.refreshFuture z.2)) :=
    Measure.measurable_dirac.comp
      ManuscriptOriginConfiguration.measurable_refreshFuture_joint
  have hbind := measurable_parametric_probability_bind
    (fun _ : ManuscriptOriginConfiguration n => sourceLaw)
    measurable_const (fun _ => hprob)
    (fun z : ManuscriptOriginConfiguration n ×
      (Nat × (Nat × Nat) → Bool) =>
      Measure.dirac (z.1.refreshFuture z.2)) hnext
  convert hbind using 1
  funext c
  exact (Measure.bind_dirac_eq_map sourceLaw
    c.measurable_refreshFuture).symm

theorem measurable_manuscriptOriginObservedRepresentative {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.observedRepresentative) := by
  exact ManuscriptOriginConfiguration.measurable_refreshFuture_joint.comp
    (measurable_id.prodMk measurable_const)

theorem measurable_manuscriptOriginUnusedTail {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.unusedTail) := by
  apply Measurable.of_eval
  intro index
  have hcoin : Measurable
      (fun z : Nat × (Nat → Nat × Nat → Bool) =>
        z.2 index.1 (z.1 + index.2.1, index.2.2)) := by
    apply measurable_from_prod_countable_right
    intro level
    exact (measurable_pi_apply (level + index.2.1, index.2.2)).comp
      (measurable_pi_apply index.1)
  exact hcoin.comp
    (measurable_manuscriptOriginConfiguration_level.prodMk
      (measurable_manuscriptOriginSourceState_coins.comp
        measurable_manuscriptOriginConfiguration_source))

theorem ManuscriptOriginConfiguration.refreshLaw_map_state
    {n : Nat} (c : ManuscriptOriginConfiguration n) :
    c.refreshLaw.map (fun next => next.state) =
      Measure.dirac c.state := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  change (sourceLaw.map c.refreshFuture).map
    (fun next => next.state) = Measure.dirac c.state
  rw [Measure.map_map measurable_manuscriptOriginConfiguration_state
    c.measurable_refreshFuture]
  have hfun : (fun future => (c.refreshFuture future).state) =
      (fun _ => c.state) := by
    funext future
    rfl
  change sourceLaw.map (fun future => (c.refreshFuture future).state) =
    Measure.dirac c.state
  rw [hfun]
  simp

theorem ManuscriptOriginConfiguration.refreshLaw_map_past_pointCounts
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (observedLevel : Nat) (hle : observedLevel ≤ c.level)
    (S : Finset (LatticePoint n)) :
    c.refreshLaw.map
      (fun next => next.source.pointCounts observedLevel S) =
      Measure.dirac (c.source.pointCounts observedLevel S) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  have hcounts : Measurable (fun next : ManuscriptOriginConfiguration n =>
      next.source.pointCounts observedLevel S) :=
    (measurable_manuscriptOriginSourceState_pointCounts observedLevel S).comp
      measurable_manuscriptOriginConfiguration_source
  change (sourceLaw.map c.refreshFuture).map
    (fun next => next.source.pointCounts observedLevel S) =
    Measure.dirac (c.source.pointCounts observedLevel S)
  rw [Measure.map_map hcounts c.measurable_refreshFuture]
  have hfun : (fun future =>
      (c.refreshFuture future).source.pointCounts observedLevel S) =
      (fun _ => c.source.pointCounts observedLevel S) := by
    funext future
    exact c.refreshFuture_past_pointCounts future observedLevel hle S
  change sourceLaw.map (fun future =>
      (c.refreshFuture future).source.pointCounts observedLevel S) = _
  rw [hfun]
  simp

/-- The law of old counts at a future level is exactly the law of thinning
the observed surviving tags by the fresh global fair source. -/
theorem ManuscriptOriginConfiguration.refreshLaw_map_future_pointCounts
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (observedLevel : Nat) (hle : c.level ≤ observedLevel)
    (S : Finset (LatticePoint n)) :
    c.refreshLaw.map
      (fun next => next.source.pointCounts observedLevel S) =
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
        (fun future =>
          manuscriptRefreshedFuturePointCounts c future observedLevel S) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  have hcounts : Measurable (fun next : ManuscriptOriginConfiguration n =>
      next.source.pointCounts observedLevel S) :=
    (measurable_manuscriptOriginSourceState_pointCounts observedLevel S).comp
      measurable_manuscriptOriginConfiguration_source
  change (sourceLaw.map c.refreshFuture).map
    (fun next => next.source.pointCounts observedLevel S) = _
  rw [Measure.map_map hcounts c.measurable_refreshFuture]
  congr 1
  funext future
  exact c.refreshFuture_future_pointCounts future observedLevel hle S

theorem ManuscriptOriginConfiguration.refreshLaw_map_past_coinPrefix
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (observedLevel : Nat) (hle : observedLevel ≤ c.level) :
    c.refreshLaw.map (fun next =>
      manuscriptOriginCoinPrefix observedLevel next.source.coins) =
    Measure.dirac
      (manuscriptOriginCoinPrefix observedLevel c.source.coins) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  have hprefix : Measurable (fun next : ManuscriptOriginConfiguration n =>
      manuscriptOriginCoinPrefix observedLevel next.source.coins) :=
    (measurable_manuscriptOriginCoinPrefix observedLevel).comp
      (measurable_manuscriptOriginSourceState_coins.comp
        measurable_manuscriptOriginConfiguration_source)
  change (sourceLaw.map c.refreshFuture).map (fun next =>
    manuscriptOriginCoinPrefix observedLevel next.source.coins) = _
  rw [Measure.map_map hprefix c.measurable_refreshFuture]
  change sourceLaw.map (fun future =>
    manuscriptOriginCoinPrefix observedLevel
      (c.refreshFuture future).source.coins) = _
  have hfun : (fun future =>
      manuscriptOriginCoinPrefix observedLevel
        (c.refreshFuture future).source.coins) =
      (fun _ => manuscriptOriginCoinPrefix observedLevel c.source.coins) := by
    funext future
    exact c.refreshFuture_past_coinPrefix future observedLevel hle
  rw [hfun]
  simp

/-- All source data already observed by a run at a fixed absolute level. -/
def manuscriptOriginObservedPrefix {n : Nat} (observedLevel : Nat)
    (c : ManuscriptOriginConfiguration n) :=
  (c.state, c.source.processed, c.source.valid, c.source.marks,
    c.origin, c.level,
    manuscriptOriginCoinPrefix observedLevel c.source.coins)

theorem measurable_manuscriptOriginObservedPrefix
    {n : Nat} (observedLevel : Nat) :
    Measurable (manuscriptOriginObservedPrefix (n := n) observedLevel) := by
  have hsource := measurable_manuscriptOriginConfiguration_source (n := n)
  exact measurable_manuscriptOriginConfiguration_state.prodMk
    ((measurable_manuscriptOriginSourceState_processed.comp hsource).prodMk
      ((measurable_manuscriptOriginSourceState_valid.comp hsource).prodMk
        ((measurable_manuscriptOriginSourceState_marks.comp hsource).prodMk
          (measurable_manuscriptOriginConfiguration_origin.prodMk
            (measurable_manuscriptOriginConfiguration_level.prodMk
              ((measurable_manuscriptOriginCoinPrefix observedLevel).comp
                (measurable_manuscriptOriginSourceState_coins.comp
                  hsource)))))))

theorem measurable_manuscriptOriginCurrentObservedPrefix
    {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      manuscriptOriginObservedPrefix c.level c) := by
  have hsource := measurable_manuscriptOriginConfiguration_source (n := n)
  have hlevel := measurable_manuscriptOriginConfiguration_level (n := n)
  have hcoin : Measurable (fun c : ManuscriptOriginConfiguration n =>
      manuscriptOriginCoinPrefix c.level c.source.coins) :=
    measurable_manuscriptOriginCoinPrefix_joint.comp
      (hlevel.prodMk
        (measurable_manuscriptOriginSourceState_coins.comp hsource))
  exact measurable_manuscriptOriginConfiguration_state.prodMk
    ((measurable_manuscriptOriginSourceState_processed.comp hsource).prodMk
      ((measurable_manuscriptOriginSourceState_valid.comp hsource).prodMk
        ((measurable_manuscriptOriginSourceState_marks.comp hsource).prodMk
          (measurable_manuscriptOriginConfiguration_origin.prodMk
            (hlevel.prodMk hcoin)))))

theorem ManuscriptOriginConfiguration.refreshFuture_observedPrefix
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool)
    (observedLevel : Nat) (hle : observedLevel ≤ c.level) :
    manuscriptOriginObservedPrefix observedLevel (c.refreshFuture future) =
      manuscriptOriginObservedPrefix observedLevel c := by
  unfold manuscriptOriginObservedPrefix
  rw [c.refreshFuture_past_coinPrefix future observedLevel hle]
  rfl

theorem ManuscriptOriginConfiguration.refreshFuture_currentObservedPrefix
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) :
    manuscriptOriginObservedPrefix (c.refreshFuture future).level
      (c.refreshFuture future) =
    manuscriptOriginObservedPrefix c.level c := by
  exact c.refreshFuture_observedPrefix future c.level (le_refl _)

theorem ManuscriptOriginConfiguration.refreshLaw_map_observedPrefix
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (observedLevel : Nat) (hle : observedLevel ≤ c.level) :
    c.refreshLaw.map (manuscriptOriginObservedPrefix observedLevel) =
      Measure.dirac (manuscriptOriginObservedPrefix observedLevel c) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  change (sourceLaw.map c.refreshFuture).map
    (manuscriptOriginObservedPrefix observedLevel) = _
  rw [Measure.map_map
    (measurable_manuscriptOriginObservedPrefix observedLevel)
    c.measurable_refreshFuture]
  change sourceLaw.map (fun future =>
    manuscriptOriginObservedPrefix observedLevel (c.refreshFuture future)) = _
  have hfun : (fun future =>
      manuscriptOriginObservedPrefix observedLevel (c.refreshFuture future)) =
      (fun _ => manuscriptOriginObservedPrefix observedLevel c) := by
    funext future
    exact c.refreshFuture_observedPrefix future observedLevel hle
  rw [hfun]
  simp

theorem ManuscriptOriginConfiguration.refreshLaw_map_currentObservedPrefix
    {n : Nat} (c : ManuscriptOriginConfiguration n) :
    c.refreshLaw.map
      (fun next => manuscriptOriginObservedPrefix next.level next) =
    Measure.dirac (manuscriptOriginObservedPrefix c.level c) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  change (sourceLaw.map c.refreshFuture).map
    (fun next => manuscriptOriginObservedPrefix next.level next) = _
  rw [Measure.map_map
    measurable_manuscriptOriginCurrentObservedPrefix
    c.measurable_refreshFuture]
  change sourceLaw.map (fun future =>
    manuscriptOriginObservedPrefix (c.refreshFuture future).level
      (c.refreshFuture future)) = _
  have hfun : (fun future =>
      manuscriptOriginObservedPrefix (c.refreshFuture future).level
        (c.refreshFuture future)) =
      (fun _ => manuscriptOriginObservedPrefix c.level c) := by
    funext future
    exact c.refreshFuture_currentObservedPrefix future
  rw [hfun]
  simp

/-- Conditional on a fixed incoming ghost configuration, the current
observed history and the newly drawn future source form a product law. -/
theorem ManuscriptOriginConfiguration.refreshFuture_observed_future_product
    {n : Nat} (c : ManuscriptOriginConfiguration n) :
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
        (fun future =>
          (manuscriptOriginObservedPrefix (c.refreshFuture future).level
            (c.refreshFuture future), future)) =
      (Measure.dirac (manuscriptOriginObservedPrefix c.level c)).prod
        (Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  have hfun : (fun future : Nat × (Nat × Nat) → Bool =>
      (manuscriptOriginObservedPrefix (c.refreshFuture future).level
        (c.refreshFuture future), future)) =
      (fun future => (manuscriptOriginObservedPrefix c.level c, future)) := by
    funext future
    rw [c.refreshFuture_currentObservedPrefix future]
  change sourceLaw.map _ = (Measure.dirac _).prod sourceLaw
  rw [hfun]
  exact (Measure.dirac_prod (manuscriptOriginObservedPrefix c.level c)).symm

theorem manuscriptOrigin_refreshFuture_random_observed_product
    {n : Nat} (μ : Measure (ManuscriptOriginConfiguration n))
    [IsProbabilityMeasure μ] :
    (μ.prod (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw))).map
      (fun pair =>
        (manuscriptOriginObservedPrefix
          (pair.1.refreshFuture pair.2).level
          (pair.1.refreshFuture pair.2), pair.2)) =
    (μ.map (fun c => manuscriptOriginObservedPrefix c.level c)).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  let obs : ManuscriptOriginConfiguration n → _ :=
    fun c => manuscriptOriginObservedPrefix c.level c
  have hobs : Measurable obs :=
    measurable_manuscriptOriginCurrentObservedPrefix
  have heq : (fun pair : ManuscriptOriginConfiguration n ×
      (Nat × (Nat × Nat) → Bool) =>
        (manuscriptOriginObservedPrefix
          (pair.1.refreshFuture pair.2).level
          (pair.1.refreshFuture pair.2), pair.2)) =
      Prod.map obs id := by
    funext pair
    exact congrArg (fun a => (a, pair.2))
      (pair.1.refreshFuture_currentObservedPrefix pair.2)
  change (μ.prod sourceLaw).map _ = (μ.map obs).prod sourceLaw
  rw [heq]
  calc
    (μ.prod sourceLaw).map (Prod.map obs id) =
        (μ.map obs).prod (sourceLaw.map id) :=
      (Measure.map_prod_map μ sourceLaw hobs measurable_id).symm
    _ = (μ.map obs).prod sourceLaw := by rw [Measure.map_id]

/-- The independent refreshed source supplies a fair old-copy block even
when the incoming ghost configuration was selected adaptively. -/
theorem manuscriptOriginConfiguration_futureCoins_adaptive_bind
    {n : Nat} {β : Type*} [MeasurableSpace β]
    (μ : Measure (ManuscriptOriginConfiguration n))
    (K : (c : ManuscriptOriginConfiguration n) →
      (Nat × Fin c.state.nextLabel → Bool) → Measure β)
    (hK : ∀ c, Measurable (K c)) :
    μ.bind (fun c =>
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).bind
          (fun future =>
            K c (fun pair => future
              (manuscriptOriginCoinIndex c.state.nextLabel
                c.origin pair)))) =
    μ.bind (fun c =>
      (Measure.infinitePi
        (fun _ : Nat × Fin c.state.nextLabel => fairCoinLaw)).bind
          (K c)) := by
  exact manuscript_origin_futureCoins_adaptive_bind μ
    (fun c => c.state.nextLabel) (fun c => c.source.processed)
    (fun c => c.origin)
    (Filter.Eventually.of_forall (fun c => c.history)) K hK

noncomputable def manuscriptOriginRefreshKernel (n : Nat) :
    ProbabilityTheory.Kernel
      (ManuscriptOriginConfiguration n)
      (ManuscriptOriginConfiguration n) :=
  ⟨ManuscriptOriginConfiguration.refreshLaw,
    measurable_manuscriptOriginConfiguration_refreshLaw⟩

instance manuscriptOriginRefreshKernel_isMarkov (n : Nat) :
    ProbabilityTheory.IsMarkovKernel (manuscriptOriginRefreshKernel n) :=
  ⟨fun c => c.refreshLaw_isProbabilityMeasure⟩

theorem measurable_manuscriptMarksAppend
    {n : Nat} (marks : Nat × Nat → LatticePoint n)
    (component : Nat) :
    Measurable (fun tape : Nat → LatticePoint n =>
      manuscriptMarksAppend marks component tape) := by
  apply Measurable.of_eval
  intro tag
  by_cases htag : tag.1 = component
  · simpa [manuscriptMarksAppend, htag] using
      (measurable_pi_apply tag.2 :
        Measurable (fun tape : Nat → LatticePoint n => tape tag.2))
  · simpa [manuscriptMarksAppend, htag] using
      (measurable_const : Measurable
        (fun _ : Nat → LatticePoint n => marks tag))

theorem ManuscriptOriginSourceState.measurable_step_tape
    {n : Nat} (g : ManuscriptOriginSourceState n)
    (P : PolytopeData n) (firstLabel basePending preRounds : Nat)
    (preCoins future : Nat × Nat → Bool) :
    Measurable (fun tape : Nat → LatticePoint n =>
      g.step
        { component := P
          firstLabel := firstLabel
          basePending := basePending
          preRounds := preRounds
          preCoins := preCoins
          futureCoins := future
          tape := tape }) := by
  rw [measurable_comap_iff]
  change Measurable (fun tape : Nat → LatticePoint n =>
    (g.processed + 1,
      manuscriptValidUpdate g.valid g.marks P g.processed firstLabel
        basePending,
      manuscriptMarksAppend g.marks g.processed tape,
      manuscriptCoinsAppend g.coins g.processed preCoins future preRounds))
  exact measurable_const.prodMk
    (measurable_const.prodMk
      ((measurable_manuscriptMarksAppend g.marks g.processed).prodMk
        measurable_const))

theorem measurable_firstExitRoundSplitFinite_pair
    {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (hfresh : s.LabelsFresh) :
    Measurable (fun pair : (Nat × Nat → Bool) ×
        (Nat × Fin pending → Bool) =>
      firstExitRoundSplit s pending threshold pair.1
        (pendingCoinExtension s.nextLabel pending pair.2)) := by
  have hmerge : Measurable (fun pair : (Nat × Nat → Bool) ×
      (Nat × Fin pending → Bool) =>
      mergeCoinsAtLabel s.nextLabel pair.1
        (pendingCoinExtension s.nextLabel pending pair.2)) :=
    (measurable_mergeCoinsAtLabel_pair s.nextLabel).comp
      (measurable_fst.prodMk
        ((measurable_pendingCoinExtension s.nextLabel pending).comp
          measurable_snd))
  have hround : Measurable (fun pair : (Nat × Nat → Bool) ×
      (Nat × Fin pending → Bool) =>
      ttcPseudocode.secondLoopExitRound s pending threshold
        (mergeCoinsAtLabel s.nextLabel pair.1
          (pendingCoinExtension s.nextLabel pending pair.2))) :=
    (measurable_firstExitRound s pending threshold).comp hmerge
  convert hround using 1
  funext pair
  exact (firstExitRound_mergeCoinsAtLabel s pending threshold pair.1
    (pendingCoinExtension s.nextLabel pending pair.2) hfresh).symm

theorem ManuscriptOriginConfiguration.measurable_advance_tape
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun tape : Nat → LatticePoint n =>
      c.advance P intensity threshold basePending preCoins future tape) := by
  rw [measurable_comap_iff]
  let deleted := c.state.removeComponent P
  let preRounds := c.level + ttcPseudocode.firstLoopExit deleted intensity threshold
  let fresh := originalSurvivorCoinRestriction preCoins preRounds
    deleted.nextLabel basePending future
  have hstate : Measurable (fun tape : Nat → LatticePoint n =>
      (c.advance P intensity threshold basePending preCoins future tape).state) := by
    change Measurable (communityManuscriptOriginTapeResult deleted intensity
      threshold preCoins preRounds basePending
      (manuscriptSourceOldCoins c.origin c.source.coins c.level, fresh))
    exact measurable_communityManuscriptOriginTapeResult deleted intensity
      threshold preCoins preRounds basePending _
  have hsource : Measurable (fun tape : Nat → LatticePoint n =>
      (c.advance P intensity threshold basePending preCoins future tape).source) := by
    change Measurable (fun tape : Nat → LatticePoint n =>
      c.source.step
        { component := P
          firstLabel := c.state.nextLabel
          basePending := basePending
          preRounds := preRounds
          preCoins := preCoins
          futureCoins := future
          tape := tape })
    exact c.source.measurable_step_tape P c.state.nextLabel
      basePending preRounds preCoins future
  have horigin : Measurable (fun tape : Nat → LatticePoint n =>
      (c.advance P intensity threshold basePending preCoins future tape).origin) := by
    convert (measurable_const : Measurable (fun _ : Nat → LatticePoint n =>
      (c.advance P intensity threshold basePending preCoins future
        (fun _ => 0)).origin)) using 1
    funext tape
    rfl
  have hlevel : Measurable (fun tape : Nat → LatticePoint n =>
      (c.advance P intensity threshold basePending preCoins future tape).level) := by
    convert (measurable_const : Measurable (fun _ : Nat → LatticePoint n =>
      (c.advance P intensity threshold basePending preCoins future
        (fun _ => 0)).level)) using 1
    funext tape
    rfl
  exact hstate.prodMk (hsource.prodMk (horigin.prodMk hlevel))

/-- A ghost transition after the Poisson and coin choices, retaining its
source history and attaching the independent normalized sampler tape. -/
noncomputable def ManuscriptOriginConfiguration.tapeAdvanceLaw
    {n : Nat} (hn : 21 ≤ n) (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    Measure (ManuscriptOriginConfiguration n) :=
  (Measure.infinitePi (fun _ : Nat =>
    normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)).map
    (fun tape => c.advance P intensity threshold basePending
      preCoins future tape)

theorem ManuscriptOriginConfiguration.tapeAdvanceLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    IsProbabilityMeasure (c.tapeAdvanceLaw hn P b eta threshold hroute
      intensity basePending preCoins future) := by
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  letI : IsProbabilityMeasure pointLaw :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  letI : ∀ _ : Nat, IsProbabilityMeasure pointLaw := fun _ => inferInstance
  letI : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : Nat => pointLaw)) := inferInstance
  unfold ManuscriptOriginConfiguration.tapeAdvanceLaw
  exact Measure.isProbabilityMeasure_map
    (c.measurable_advance_tape P intensity threshold basePending
      preCoins future).aemeasurable

theorem ManuscriptOriginConfiguration.tapeAdvanceLaw_map_state
    {n : Nat} (hn : 21 ≤ n) (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    (c.tapeAdvanceLaw hn P b eta threshold hroute intensity basePending
      preCoins future).map (fun next => next.state) =
    communityManuscriptOriginTapeKernel hn P b eta threshold hroute
      (c.state.removeComponent P) intensity preCoins
      (c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
        intensity threshold) basePending
      (manuscriptSourceOldCoins c.origin c.source.coins c.level,
        originalSurvivorCoinRestriction preCoins
          (c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
            intensity threshold)
          (c.state.removeComponent P).nextLabel basePending future) := by
  unfold ManuscriptOriginConfiguration.tapeAdvanceLaw
  rw [Measure.map_map measurable_manuscriptOriginConfiguration_state
    (c.measurable_advance_tape P intensity threshold basePending
      preCoins future)]
  exact c.advance_state_tapeLaw hn P b eta threshold hroute intensity
    basePending preCoins future

end Kr25Ssmxt

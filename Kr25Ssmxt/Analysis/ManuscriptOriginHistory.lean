import Kr25Ssmxt.Analysis.ManuscriptOriginMarkedComponent

/-! Ghost bookkeeping for the source coupling. Every executable copy label
records a unique component and original Poisson-copy index. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

def manuscriptOriginAppend (origin : Nat → Nat × Nat)
    (component firstLabel count : Nat) (index : Fin count → Nat) :
    Nat → Nat × Nat :=
  fun label => if h : firstLabel ≤ label ∧ label < firstLabel + count then
    (component, index ⟨label - firstLabel, by omega⟩)
  else origin label

theorem manuscriptOriginAppend_old (origin : Nat → Nat × Nat)
    (component firstLabel count : Nat) (index : Fin count → Nat)
    (label : Nat) (hlabel : label < firstLabel) :
    manuscriptOriginAppend origin component firstLabel count index label =
      origin label := by
  have hnot : ¬ (firstLabel ≤ label ∧ label < firstLabel + count) := by omega
  simp [manuscriptOriginAppend, hnot]

theorem manuscriptOriginAppend_new (origin : Nat → Nat × Nat)
    (component firstLabel count : Nat) (index : Fin count → Nat)
    (i : Fin count) :
    manuscriptOriginAppend origin component firstLabel count index
      (firstLabel + i.val) = (component, index i) := by
  have h : firstLabel ≤ firstLabel + i.val ∧
      firstLabel + i.val < firstLabel + count := by omega
  simp [manuscriptOriginAppend, h]

def ManuscriptOriginHistory (nextLabel processed : Nat)
    (origin : Nat → Nat × Nat) : Prop :=
  (∀ label < nextLabel, (origin label).1 < processed) ∧
    (∀ a b, a < nextLabel → b < nextLabel →
      origin a = origin b → a = b)

theorem manuscriptOriginHistory_initial (origin : Nat → Nat × Nat) :
    ManuscriptOriginHistory 0 0 origin := by
  constructor
  · intro label hlabel
    omega
  · intro a b ha
    omega

theorem manuscriptOriginHistory_append
    (origin : Nat → Nat × Nat) (processed firstLabel count : Nat)
    (index : Fin count → Nat) (hindex : Function.Injective index)
    (h : ManuscriptOriginHistory firstLabel processed origin) :
    ManuscriptOriginHistory (firstLabel + count) (processed + 1)
      (manuscriptOriginAppend origin processed firstLabel count index) := by
  constructor
  · intro label hlabel
    by_cases hbefore : label < firstLabel
    · rw [manuscriptOriginAppend_old origin processed firstLabel count index
        label hbefore]
      exact Nat.lt_succ_of_lt (h.1 label hbefore)
    · have hrange : firstLabel ≤ label ∧
          label < firstLabel + count := by omega
      simp [manuscriptOriginAppend, hrange]
  · intro a b ha hb hab
    by_cases haold : a < firstLabel <;> by_cases hbold : b < firstLabel
    · rw [manuscriptOriginAppend_old origin processed firstLabel count index
        a haold, manuscriptOriginAppend_old origin processed firstLabel count
        index b hbold] at hab
      exact h.2 a b haold hbold hab
    · have hbrange : firstLabel ≤ b ∧ b < firstLabel + count := by omega
      have ha' := manuscriptOriginAppend_old origin processed firstLabel count
        index a haold
      have hb' : manuscriptOriginAppend origin processed firstLabel count index
          b = (processed,
            index ⟨b - firstLabel, by omega⟩) := by
        simp [manuscriptOriginAppend, hbrange]
      rw [ha', hb'] at hab
      have hcomponent := congrArg Prod.fst hab
      have hlt := h.1 a haold
      omega
    · have harange : firstLabel ≤ a ∧ a < firstLabel + count := by omega
      have ha' : manuscriptOriginAppend origin processed firstLabel count index
          a = (processed,
            index ⟨a - firstLabel, by omega⟩) := by
        simp [manuscriptOriginAppend, harange]
      have hb' := manuscriptOriginAppend_old origin processed firstLabel count
        index b hbold
      rw [ha', hb'] at hab
      have hcomponent := congrArg Prod.fst hab
      have hlt := h.1 b hbold
      omega
    · have harange : firstLabel ≤ a ∧ a < firstLabel + count := by omega
      have hbrange : firstLabel ≤ b ∧ b < firstLabel + count := by omega
      have ha' : manuscriptOriginAppend origin processed firstLabel count index
          a = (processed,
            index ⟨a - firstLabel, by omega⟩) := by
        simp [manuscriptOriginAppend, harange]
      have hb' : manuscriptOriginAppend origin processed firstLabel count index
          b = (processed,
            index ⟨b - firstLabel, by omega⟩) := by
        simp [manuscriptOriginAppend, hbrange]
      rw [ha', hb'] at hab
      have hind : (⟨a - firstLabel, by omega⟩ : Fin count) =
          ⟨b - firstLabel, by omega⟩ :=
        hindex (congrArg Prod.snd hab)
      have hval : a - firstLabel = b - firstLabel :=
        congrArg Fin.val hind
      omega

/-- The original Poisson index carried by each newly appended sample. -/
noncomputable def twoStageSurvivorIndex
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (activeCoins : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (activeRounds : Nat)
    (i : Fin (pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        activeCoins)
      activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))) : Nat :=
  (pendingSurvivorFin preCoins preRounds firstLabel basePending
    (pendingSurvivorFin
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending) activeCoins)
      activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) i)).val

theorem twoStageSurvivorLabel_eq_add_index
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (activeCoins : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (activeRounds : Nat)
    (i : Fin (pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        activeCoins)
      activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))) :
    twoStageSurvivorLabel preCoins preRounds firstLabel basePending
      activeCoins activeRounds i =
    firstLabel + twoStageSurvivorIndex preCoins preRounds firstLabel
      basePending activeCoins activeRounds i := rfl

theorem twoStageSurvivorIndex_injective
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (activeCoins : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (activeRounds : Nat) :
    Function.Injective (twoStageSurvivorIndex preCoins preRounds firstLabel
      basePending activeCoins activeRounds) := by
  intro i j hij
  apply twoStageSurvivorLabel_injective preCoins preRounds firstLabel
    basePending activeCoins activeRounds
  rw [twoStageSurvivorLabel_eq_add_index,
    twoStageSurvivorLabel_eq_add_index, hij]

/-- Appending one component's origin-labelled survivors preserves globally
unique source tags for every allocated executable label. -/
theorem manuscriptOriginHistory_append_twoStage
    (origin : Nat → Nat × Nat) (processed firstLabel : Nat)
    (h : ManuscriptOriginHistory firstLabel processed origin)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (activeCoins : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (activeRounds : Nat) :
    let index := twoStageSurvivorLabel preCoins preRounds firstLabel
      basePending activeCoins activeRounds
    ManuscriptOriginHistory (firstLabel +
      pendingAfter
        (pendingCoinExtension firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending)
          activeCoins)
        activeRounds firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending))
      (processed + 1)
      (manuscriptOriginAppend origin processed firstLabel _ index) := by
  dsimp only
  exact manuscriptOriginHistory_append origin processed firstLabel _ _
    (twoStageSurvivorLabel_injective preCoins preRounds firstLabel
      basePending activeCoins activeRounds) h

noncomputable def manuscriptSourceTags
    (component firstLabel basePending : Nat) : Finset (Nat × Nat) := by
  classical
  exact (Finset.range basePending).image
    (fun i => (component, firstLabel + i))

theorem twoStageSurvivorLabel_mem_sourceTags
    (component : Nat) (preCoins : Nat × Nat → Bool)
    (preRounds firstLabel basePending : Nat)
    (activeCoins : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (activeRounds : Nat)
    (i : Fin (pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        activeCoins)
      activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))) :
    (component, twoStageSurvivorLabel preCoins preRounds firstLabel
      basePending activeCoins activeRounds i) ∈
    manuscriptSourceTags component firstLabel basePending := by
  classical
  let j := pendingSurvivorFin
    (pendingCoinExtension firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) activeCoins)
    activeRounds firstLabel
    (pendingAfter preCoins preRounds firstLabel basePending) i
  let k := pendingSurvivorFin preCoins preRounds firstLabel basePending j
  apply Finset.mem_image.mpr
  exact ⟨k.val, Finset.mem_range.mpr k.isLt, rfl⟩

/-- Read a future fair coin for an executable label from its unique source
component and original Poisson-copy index. -/
def manuscriptOriginCoinIndex (nextLabel : Nat)
    (origin : Nat → Nat × Nat) :
    Nat × Fin nextLabel → Nat × (Nat × Nat) :=
  fun pair => ((origin pair.2.val).1, (pair.1, (origin pair.2.val).2))

theorem manuscriptOriginCoinIndex_injective
    (nextLabel processed : Nat) (origin : Nat → Nat × Nat)
    (h : ManuscriptOriginHistory nextLabel processed origin) :
    Function.Injective (manuscriptOriginCoinIndex nextLabel origin) := by
  intro a b hab
  have hround : a.1 = b.1 :=
    congrArg (fun p : Nat × (Nat × Nat) => p.2.1) hab
  have hcomponent : (origin a.2.val).1 = (origin b.2.val).1 :=
    congrArg (fun p : Nat × (Nat × Nat) => p.1) hab
  have hindex : (origin a.2.val).2 = (origin b.2.val).2 :=
    congrArg (fun p : Nat × (Nat × Nat) => p.2.2) hab
  have horigin : origin a.2.val = origin b.2.val :=
    Prod.ext hcomponent hindex
  have hlabel : a.2.val = b.2.val :=
    h.2 a.2.val b.2.val a.2.isLt b.2.isLt horigin
  exact Prod.ext hround (Fin.ext hlabel)

/-- Globally independent component-source coins, reindexed by the ghost
origin map, are fair on every allocated executable label. -/
theorem manuscript_origin_coins_on_allocated_labels
    (nextLabel processed : Nat) (origin : Nat → Nat × Nat)
    (h : ManuscriptOriginHistory nextLabel processed origin) :
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
        (fun sourceCoins pair => sourceCoins
          (manuscriptOriginCoinIndex nextLabel origin pair)) =
    Measure.infinitePi (fun _ : Nat × Fin nextLabel => fairCoinLaw) := by
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  exact @Measure.map_infinitePi_infinitePi_of_inj
    (Nat × (Nat × Nat)) (Nat × Fin nextLabel) (fun _ => Bool)
    (fun _ => inferInstance) (fun _ => fairCoinLaw)
    (fun _ => fairCoinLaw_isProbabilityMeasure)
    (manuscriptOriginCoinIndex nextLabel origin)
    (manuscriptOriginCoinIndex_injective nextLabel processed origin h)

/-- Every retained executable copy carries the permanent point mark of its
component and original Poisson-copy index. -/
def ManuscriptOriginMarked {n : Nat} (s : TTCState n)
    (origin : Nat → Nat × Nat)
    (marks : Nat × Nat → LatticePoint n) : Prop :=
  ∀ copy ∈ s.X, copy.2 = marks (origin copy.1)

theorem manuscriptOriginMarked_initial {n : Nat}
    (origin : Nat → Nat × Nat)
    (marks : Nat × Nat → LatticePoint n) :
    ManuscriptOriginMarked (TTCState.initial n) origin marks := by
  intro copy hcopy
  simp [TTCState.initial] at hcopy

theorem manuscriptOriginMarked_removeComponent {n : Nat}
    (s : TTCState n) (P : PolytopeData n)
    (origin : Nat → Nat × Nat)
    (marks : Nat × Nat → LatticePoint n)
    (h : ManuscriptOriginMarked s origin marks) :
    ManuscriptOriginMarked (s.removeComponent P) origin marks := by
  classical
  intro copy hcopy
  exact h copy (Finset.mem_filter.mp hcopy).1

theorem manuscriptOriginMarked_samplesAfter {n : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (marks : Nat × Nat → LatticePoint n)
    (h : ManuscriptOriginMarked s origin marks)
    (coins : Nat × Nat → Bool) (rounds : Nat) :
    ManuscriptOriginMarked
      {s with X := samplesAfter coins rounds s.X}
      origin marks := by
  classical
  intro copy hcopy
  exact h copy (Finset.mem_filter.mp hcopy).1

theorem manuscriptOriginMarked_rateThinningResult {n : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (marks : Nat × Nat → LatticePoint n)
    (h : ManuscriptOriginMarked s origin marks)
    (intensity : NNReal) (threshold : Real)
    (coins : Nat × Nat → Bool) :
    ManuscriptOriginMarked
      (ttcPseudocode.firstLoopResult s intensity threshold coins)
      origin marks := by
  classical
  intro copy hcopy
  exact h copy (Finset.mem_filter.mp hcopy).1

theorem manuscriptOriginMarked_splitThinningResult {n : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (marks : Nat × Nat → LatticePoint n)
    (h : ManuscriptOriginMarked s origin marks)
    (pending : Nat) (threshold : Real)
    (old : Nat × Nat → Bool) (fresh : Nat × Fin pending → Bool) :
    ManuscriptOriginMarked
      (thinningResultSplitFinite s pending threshold old fresh).1
      origin marks := by
  classical
  intro copy hcopy
  exact h copy (Finset.mem_filter.mp hcopy).1

theorem manuscriptOriginMarked_addBatch {n count : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (marks : Nat × Nat → LatticePoint n)
    (component : Nat) (index : Fin count → Nat)
    (hfresh : s.LabelsFresh)
    (hmarked : ManuscriptOriginMarked s origin marks) :
    ManuscriptOriginMarked
      (s.addBatch (fun i => marks (component, index i)))
      (manuscriptOriginAppend origin component s.nextLabel count index)
      marks := by
  classical
  intro copy hcopy
  change copy ∈ s.X ∪
    (Finset.univ.image fun i : Fin count =>
      (s.nextLabel + i.val, marks (component, index i))) at hcopy
  rcases Finset.mem_union.mp hcopy with hold | hnew
  · rw [manuscriptOriginAppend_old origin component s.nextLabel count index
      copy.1 (hfresh.1 copy hold)]
    exact hmarked copy hold
  · obtain ⟨i, -, hcopy'⟩ := Finset.mem_image.mp hnew
    rw [← hcopy']
    simp [manuscriptOriginAppend_new]

def manuscriptMarksAppend {n : Nat}
    (marks : Nat × Nat → LatticePoint n)
    (component : Nat) (tape : Nat → LatticePoint n) :
    Nat × Nat → LatticePoint n :=
  fun tag => if tag.1 = component then tape tag.2
    else marks tag

theorem manuscriptMarksAppend_old {n : Nat}
    (marks : Nat × Nat → LatticePoint n)
    (component : Nat) (tape : Nat → LatticePoint n)
    (tag : Nat × Nat) (hcomponent : tag.1 < component) :
    manuscriptMarksAppend marks component tape tag = marks tag := by
  have hne : tag.1 ≠ component := by omega
  simp [manuscriptMarksAppend, hne]

theorem manuscriptMarksAppend_new {n : Nat}
    (marks : Nat × Nat → LatticePoint n)
    (component : Nat) (tape : Nat → LatticePoint n)
    (index : Nat) :
    manuscriptMarksAppend marks component tape
      (component, index) = tape index := by
  simp [manuscriptMarksAppend]

theorem manuscriptOriginMarked_appendSource {n count : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (marks : Nat × Nat → LatticePoint n)
    (component : Nat) (index : Fin count → Nat)
    (tape : Nat → LatticePoint n)
    (hfresh : s.LabelsFresh)
    (hhistory : ManuscriptOriginHistory s.nextLabel component origin)
    (hmarked : ManuscriptOriginMarked s origin marks) :
    ManuscriptOriginMarked
      (s.addBatch (fun i => tape (index i)))
      (manuscriptOriginAppend origin component s.nextLabel count index)
      (manuscriptMarksAppend marks component tape) := by
  let marksNew := manuscriptMarksAppend marks component tape
  have hOld : ManuscriptOriginMarked s origin marksNew := by
    intro copy hcopy
    change copy.2 = manuscriptMarksAppend marks component tape
      (origin copy.1)
    rw [manuscriptMarksAppend_old marks component tape
      (origin copy.1) (hhistory.1 copy.1 (hfresh.1 copy hcopy))]
    exact hmarked copy hcopy
  have hbatch : (fun i : Fin count => tape (index i)) =
      (fun i => marksNew (component, index i)) := by
    funext i
    exact (manuscriptMarksAppend_new marks component tape
      (index i)).symm
  rw [hbatch]
  exact manuscriptOriginMarked_addBatch s origin marksNew component index
    hfresh hOld

theorem spliceCoins_self_shift (coins : Nat × Nat → Bool) (rounds : Nat) :
    spliceCoins coins (shiftCoins rounds coins) rounds = coins := by
  funext pair
  by_cases h : pair.1 < rounds
  · simp [spliceCoins, h]
  · have hle : rounds ≤ pair.1 := Nat.le_of_not_lt h
    have hsum : pair.1 - rounds + rounds = pair.1 := Nat.sub_add_cancel hle
    simp [spliceCoins, shiftCoins, h, hsum]

theorem survives_add_iff (coins : Nat × Nat → Bool)
    (firstRounds secondRounds label : Nat) :
    survives coins (firstRounds + secondRounds) label ↔
      survives coins firstRounds label ∧
        survives (shiftCoins firstRounds coins) secondRounds label := by
  simpa only [spliceCoins_self_shift] using
    (survives_spliceCoins coins (shiftCoins firstRounds coins)
      firstRounds secondRounds label)

def manuscriptSourceOldCoins (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool) (level : Nat) :
    Nat × Nat → Bool :=
  fun pair => sources (origin pair.2).1
    (level + pair.1, (origin pair.2).2)

theorem shiftCoins_sourceOldCoins (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool) (level rounds : Nat) :
    shiftCoins rounds (manuscriptSourceOldCoins origin sources level) =
    manuscriptSourceOldCoins origin sources (level + rounds) := by
  funext pair
  simp [shiftCoins, manuscriptSourceOldCoins, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

/-- Every retained copy has survived its source's absolute coins through the
current dyadic level. -/
def ManuscriptOriginSurvives {n : Nat} (s : TTCState n)
    (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool) (level : Nat) : Prop :=
  ∀ copy ∈ s.X,
    survives (sources (origin copy.1).1) level (origin copy.1).2

theorem manuscriptOriginSurvives_initial {n : Nat}
    (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool) :
    ManuscriptOriginSurvives (TTCState.initial n) origin sources 0 := by
  intro copy hcopy
  simp [TTCState.initial] at hcopy

theorem manuscriptOriginSurvives_removeComponent {n : Nat}
    (s : TTCState n) (P : PolytopeData n)
    (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool) (level : Nat)
    (h : ManuscriptOriginSurvives s origin sources level) :
    ManuscriptOriginSurvives (s.removeComponent P) origin sources level := by
  classical
  intro copy hcopy
  exact h copy (Finset.mem_filter.mp hcopy).1

theorem manuscriptOriginSurvives_thin {n : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool) (level rounds : Nat)
    (h : ManuscriptOriginSurvives s origin sources level) :
    ManuscriptOriginSurvives
      ({ p := s.p
         X := samplesAfter
           (manuscriptSourceOldCoins origin sources level) rounds s.X
         nextLabel := s.nextLabel } : TTCState n)
      origin sources (level + rounds) := by
  classical
  intro copy hcopy
  have hold : copy ∈ s.X := (Finset.mem_filter.mp hcopy).1
  have hfuture : survives
      (shiftCoins level (sources (origin copy.1).1)) rounds
      (origin copy.1).2 := by
    intro r hr
    simpa [manuscriptSourceOldCoins, shiftCoins, Nat.add_comm] using
      (Finset.mem_filter.mp hcopy).2 r hr
  exact (survives_add_iff (sources (origin copy.1).1) level rounds
    (origin copy.1).2).2 ⟨h copy hold, hfuture⟩

theorem manuscriptOriginSurvives_thin_of_samples {n : Nat}
    (s t : TTCState n) (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool) (level rounds : Nat)
    (hsamples : t.X = samplesAfter
      (manuscriptSourceOldCoins origin sources level) rounds s.X)
    (h : ManuscriptOriginSurvives s origin sources level) :
    ManuscriptOriginSurvives t origin sources (level + rounds) := by
  classical
  intro copy hcopy
  rw [hsamples] at hcopy
  have hold : copy ∈ s.X := (Finset.mem_filter.mp hcopy).1
  have hfuture : survives
      (shiftCoins level (sources (origin copy.1).1)) rounds
      (origin copy.1).2 := by
    intro r hr
    simpa [manuscriptSourceOldCoins, shiftCoins, Nat.add_comm] using
      (Finset.mem_filter.mp hcopy).2 r hr
  exact (survives_add_iff (sources (origin copy.1).1) level rounds
    (origin copy.1).2).2 ⟨h copy hold, hfuture⟩

theorem manuscriptOriginSurvives_twoLoops {n : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool) (level : Nat)
    (intensity : NNReal) (threshold : Real) (pending : Nat)
    (activeCoins : Nat × Fin pending → Bool)
    (h : ManuscriptOriginSurvives s origin sources level) :
    let oldCoins := manuscriptSourceOldCoins origin sources level
    let rounds := ttcPseudocode.firstLoopExit s intensity threshold
    let first := ttcPseudocode.firstLoopResult s intensity threshold oldCoins
    let activeRounds := firstExitRoundSplit first pending threshold
      (shiftCoins rounds oldCoins)
      (pendingCoinExtension s.nextLabel pending activeCoins)
    let second := thinningResultSplitFinite first pending threshold
      (shiftCoins rounds oldCoins) activeCoins
    ManuscriptOriginSurvives second.1 origin sources
      (level + rounds + activeRounds) := by
  dsimp only
  let oldCoins := manuscriptSourceOldCoins origin sources level
  let rounds := ttcPseudocode.firstLoopExit s intensity threshold
  let first := ttcPseudocode.firstLoopResult s intensity threshold oldCoins
  let activeRounds := firstExitRoundSplit first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension s.nextLabel pending activeCoins)
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds oldCoins) activeCoins
  have hfirst : ManuscriptOriginSurvives first origin sources
      (level + rounds) := by
    exact manuscriptOriginSurvives_thin_of_samples s first origin sources
      level rounds rfl h
  have hshift : shiftCoins rounds oldCoins =
      manuscriptSourceOldCoins origin sources (level + rounds) :=
    shiftCoins_sourceOldCoins origin sources level rounds
  have hsamples : second.1.X = samplesAfter
      (manuscriptSourceOldCoins origin sources (level + rounds))
      activeRounds first.X := by
    rw [← hshift]
    rfl
  exact manuscriptOriginSurvives_thin_of_samples first second.1 origin
    sources (level + rounds) activeRounds hsamples hfirst

def manuscriptCoinsAppend (sources : Nat → Nat × Nat → Bool)
    (component : Nat) (preCoins future : Nat × Nat → Bool)
    (preRounds : Nat) : Nat → Nat × Nat → Bool :=
  fun c => if c = component then spliceCoins preCoins future preRounds
    else sources c

theorem manuscriptCoinsAppend_old
    (sources : Nat → Nat × Nat → Bool) (component c : Nat)
    (preCoins future : Nat × Nat → Bool) (preRounds : Nat)
    (hc : c < component) :
    manuscriptCoinsAppend sources component preCoins future preRounds c =
      sources c := by
  have hne : c ≠ component := by omega
  simp [manuscriptCoinsAppend, hne]

theorem manuscriptCoinsAppend_new
    (sources : Nat → Nat × Nat → Bool) (component : Nat)
    (preCoins future : Nat × Nat → Bool) (preRounds : Nat) :
    manuscriptCoinsAppend sources component preCoins future preRounds
      component = spliceCoins preCoins future preRounds := by
  simp [manuscriptCoinsAppend]

theorem manuscriptOriginSurvives_appendSource {n count : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool)
    (component level : Nat)
    (index : Fin count → Nat) (points : Fin count → LatticePoint n)
    (preCoins future : Nat × Nat → Bool) (preRounds : Nat)
    (hfresh : s.LabelsFresh)
    (hhistory : ManuscriptOriginHistory s.nextLabel component origin)
    (hold : ManuscriptOriginSurvives s origin sources level)
    (hnew : ∀ i : Fin count,
      survives (spliceCoins preCoins future preRounds) level
        (index i)) :
    ManuscriptOriginSurvives (s.addBatch points)
      (manuscriptOriginAppend origin component s.nextLabel count index)
      (manuscriptCoinsAppend sources component preCoins future preRounds)
      level := by
  classical
  intro copy hcopy
  change copy ∈ s.X ∪
    (Finset.univ.image fun i : Fin count =>
      (s.nextLabel + i.val, points i)) at hcopy
  rcases Finset.mem_union.mp hcopy with hstored | hadded
  · have hlabel := hfresh.1 copy hstored
    rw [manuscriptOriginAppend_old origin component s.nextLabel count
      index copy.1 hlabel]
    rw [manuscriptCoinsAppend_old sources component (origin copy.1).1
      preCoins future preRounds (hhistory.1 copy.1 hlabel)]
    exact hold copy hstored
  · obtain ⟨i, -, hcopy'⟩ := Finset.mem_image.mp hadded
    rw [← hcopy']
    rw [manuscriptOriginAppend_new]
    rw [manuscriptCoinsAppend_new]
    exact hnew i

def ManuscriptOriginValid {n : Nat} (s : TTCState n)
    (origin : Nat → Nat × Nat) (valid : Finset (Nat × Nat)) : Prop :=
  ∀ copy ∈ s.X, origin copy.1 ∈ valid

theorem manuscriptOriginValid_initial {n : Nat}
    (origin : Nat → Nat × Nat) :
    ManuscriptOriginValid (TTCState.initial n) origin ∅ := by
  intro copy hcopy
  simp [TTCState.initial] at hcopy

theorem manuscriptOriginValid_removeComponent {n : Nat}
    (s : TTCState n) (P : PolytopeData n)
    (origin : Nat → Nat × Nat) (valid : Finset (Nat × Nat))
    (h : ManuscriptOriginValid s origin valid) :
    ManuscriptOriginValid (s.removeComponent P) origin valid := by
  classical
  intro copy hcopy
  exact h copy (Finset.mem_filter.mp hcopy).1

theorem manuscriptOriginValid_rateThinningResult {n : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (valid : Finset (Nat × Nat))
    (h : ManuscriptOriginValid s origin valid)
    (intensity : NNReal) (threshold : Real)
    (coins : Nat × Nat → Bool) :
    ManuscriptOriginValid
      (ttcPseudocode.firstLoopResult s intensity threshold coins)
      origin valid := by
  classical
  intro copy hcopy
  exact h copy (Finset.mem_filter.mp hcopy).1

theorem manuscriptOriginValid_splitThinningResult {n : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (valid : Finset (Nat × Nat))
    (h : ManuscriptOriginValid s origin valid)
    (pending : Nat) (threshold : Real)
    (old : Nat × Nat → Bool) (fresh : Nat × Fin pending → Bool) :
    ManuscriptOriginValid
      (thinningResultSplitFinite s pending threshold old fresh).1
      origin valid := by
  classical
  intro copy hcopy
  exact h copy (Finset.mem_filter.mp hcopy).1

theorem manuscriptOriginValid_appendSource {n count : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (valid newTags : Finset (Nat × Nat))
    (component : Nat) (index : Fin count → Nat)
    (points : Fin count → LatticePoint n)
    (hfresh : s.LabelsFresh)
    (hold : ManuscriptOriginValid s origin valid)
    (hnew : ∀ i : Fin count, (component, index i) ∈ newTags) :
    ManuscriptOriginValid (s.addBatch points)
      (manuscriptOriginAppend origin component s.nextLabel count index)
      (valid ∪ newTags) := by
  classical
  intro copy hcopy
  change copy ∈ s.X ∪
    (Finset.univ.image fun i : Fin count =>
      (s.nextLabel + i.val, points i)) at hcopy
  rcases Finset.mem_union.mp hcopy with hstored | hadded
  · rw [manuscriptOriginAppend_old origin component s.nextLabel count
      index copy.1 (hfresh.1 copy hstored)]
    exact Finset.mem_union_left _ (hold copy hstored)
  · obtain ⟨i, -, hcopy'⟩ := Finset.mem_image.mp hadded
    rw [← hcopy']
    rw [manuscriptOriginAppend_new]
    exact Finset.mem_union_right _ (hnew i)

/-- Every eligible source copy that survives the absolute level occurs in
the executable state. -/
def ManuscriptOriginComplete {n : Nat} (s : TTCState n)
    (origin : Nat → Nat × Nat) (valid : Finset (Nat × Nat))
    (sources : Nat → Nat × Nat → Bool) (level : Nat) : Prop :=
  ∀ tag ∈ valid, survives (sources tag.1) level tag.2 →
    ∃ copy ∈ s.X, origin copy.1 = tag

theorem manuscriptOriginComplete_initial {n : Nat}
    (origin : Nat → Nat × Nat)
    (sources : Nat → Nat × Nat → Bool) :
    ManuscriptOriginComplete (TTCState.initial n) origin ∅ sources 0 := by
  intro tag htag
  simp at htag

theorem manuscriptOriginComplete_removeComponent {n : Nat}
    (s : TTCState n) (P : PolytopeData n)
    (origin : Nat → Nat × Nat)
    (marks : Nat × Nat → LatticePoint n)
    (valid : Finset (Nat × Nat))
    (sources : Nat → Nat × Nat → Bool) (level : Nat)
    (hmarked : ManuscriptOriginMarked s origin marks)
    (hcomplete : ManuscriptOriginComplete s origin valid sources level) :
    ManuscriptOriginComplete (s.removeComponent P) origin
      (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier)
      sources level := by
  classical
  intro tag htag hsurv
  have hvalid : tag ∈ valid := (Finset.mem_filter.mp htag).1
  have hout : (marks tag).toPoint ∉ P.carrier :=
    (Finset.mem_filter.mp htag).2
  obtain ⟨copy, hcopy, horigin⟩ := hcomplete tag hvalid hsurv
  refine ⟨copy, ?_, horigin⟩
  apply Finset.mem_filter.mpr
  refine ⟨hcopy, ?_⟩
  have hpoint := hmarked copy hcopy
  rw [horigin] at hpoint
  rw [hpoint]
  exact hout

theorem manuscriptOriginComplete_thin_of_samples {n : Nat}
    (s t : TTCState n) (origin : Nat → Nat × Nat)
    (valid : Finset (Nat × Nat))
    (sources : Nat → Nat × Nat → Bool) (level rounds : Nat)
    (hsamples : t.X = samplesAfter
      (manuscriptSourceOldCoins origin sources level) rounds s.X)
    (hcomplete : ManuscriptOriginComplete s origin valid sources level) :
    ManuscriptOriginComplete t origin valid sources (level + rounds) := by
  classical
  intro tag htag hsurv
  have hparts := (survives_add_iff (sources tag.1) level rounds tag.2).mp
    hsurv
  obtain ⟨copy, hcopy, horigin⟩ := hcomplete tag htag hparts.1
  refine ⟨copy, ?_, horigin⟩
  rw [hsamples]
  apply Finset.mem_filter.mpr
  refine ⟨hcopy, ?_⟩
  intro r hr
  simpa [manuscriptSourceOldCoins, shiftCoins, horigin, Nat.add_comm]
    using hparts.2 r hr

def ManuscriptValidBound (valid : Finset (Nat × Nat))
    (processed : Nat) : Prop :=
  ∀ tag ∈ valid, tag.1 < processed

theorem manuscriptValidBound_initial : ManuscriptValidBound ∅ 0 := by
  intro tag htag
  simp at htag

theorem manuscriptValidBound_filter
    (valid : Finset (Nat × Nat)) (processed : Nat)
    (P : Nat × Nat → Prop) [DecidablePred P]
    (h : ManuscriptValidBound valid processed) :
    ManuscriptValidBound (valid.filter P) processed := by
  intro tag htag
  exact h tag (Finset.mem_filter.mp htag).1

theorem manuscriptValidBound_append
    (valid : Finset (Nat × Nat)) (component firstLabel basePending : Nat)
    (h : ManuscriptValidBound valid component) :
    ManuscriptValidBound
      (valid ∪ manuscriptSourceTags component firstLabel basePending)
      (component + 1) := by
  intro tag htag
  rcases Finset.mem_union.mp htag with hold | hnew
  · exact Nat.lt_succ_of_lt (h tag hold)
  · obtain ⟨i, -, htag'⟩ := Finset.mem_image.mp hnew
    have hcomponent := congrArg Prod.fst htag'
    omega

/-- A source append preserves coverage when its injected sample labels cover
every surviving original Poisson label. -/
theorem manuscriptOriginComplete_appendSource {n count : Nat}
    (s : TTCState n) (origin : Nat → Nat × Nat)
    (valid : Finset (Nat × Nat))
    (sources : Nat → Nat × Nat → Bool)
    (component : Nat) (preCoins future : Nat × Nat → Bool)
    (preRounds basePending activeRounds : Nat)
    (index : Fin count → Nat) (points : Fin count → LatticePoint n)
    (hfresh : s.LabelsFresh)
    (hbound : ManuscriptValidBound valid component)
    (hcomplete : ManuscriptOriginComplete s origin valid sources
      (preRounds + activeRounds))
    (hcover : ∀ k < basePending,
      survives (spliceCoins preCoins future preRounds)
        (preRounds + activeRounds) (s.nextLabel + k) →
      ∃ i : Fin count, index i = s.nextLabel + k) :
    ManuscriptOriginComplete (s.addBatch points)
      (manuscriptOriginAppend origin component s.nextLabel count index)
      (valid ∪ manuscriptSourceTags component s.nextLabel basePending)
      (manuscriptCoinsAppend sources component preCoins future preRounds)
      (preRounds + activeRounds) := by
  intro tag htag hsurv
  rcases Finset.mem_union.mp htag with hold | hnew
  · have hlt : tag.1 < component := hbound tag hold
    have hsurvOld : survives (sources tag.1)
        (preRounds + activeRounds) tag.2 := by
      simpa [manuscriptCoinsAppend, Nat.ne_of_lt hlt] using hsurv
    obtain ⟨copy, hcopy, horigin⟩ := hcomplete tag hold hsurvOld
    refine ⟨copy, ?_, ?_⟩
    · change copy ∈ s.X ∪
        (Finset.univ.image fun i => (s.nextLabel + i.val, points i))
      exact Finset.mem_union_left _ hcopy
    · rw [manuscriptOriginAppend_old origin component s.nextLabel count index
        copy.1 (hfresh.1 copy hcopy)]
      exact horigin
  · obtain ⟨k, hk, hkTag⟩ := Finset.mem_image.mp hnew
    have hkBound : k < basePending := Finset.mem_range.mp hk
    have htagEq : tag = (component, s.nextLabel + k) := hkTag.symm
    subst tag
    have hsurvNew : survives (spliceCoins preCoins future preRounds)
        (preRounds + activeRounds) (s.nextLabel + k) := by
      simpa [manuscriptCoinsAppend] using hsurv
    obtain ⟨i, hi⟩ := hcover k hkBound hsurvNew
    let copy : SampleCopy n := (s.nextLabel + i.val, points i)
    have hcopy : copy ∈ (s.addBatch points).X := by
      change copy ∈ s.X ∪
        (Finset.univ.image fun j => (s.nextLabel + j.val, points j))
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    refine ⟨copy, hcopy, ?_⟩
    change manuscriptOriginAppend origin component s.nextLabel count index
      (s.nextLabel + i.val) = (component, s.nextLabel + k)
    rw [manuscriptOriginAppend_new]
    exact congrArg (Prod.mk component) hi

end Kr25Ssmxt

import ttc.Analysis.ComponentAbsoluteFiniteTape
import ttc.Analysis.AbsolutePoissonTape

/-! A surviving newly drawn copy has an injective original Poisson label,
through both the absolute pre-thinning and the adaptive count loop. -/

namespace ttc

open Classical MeasureTheory
open Arlib.Probability

noncomputable def pendingSurvivorFin
    (coins : Nat × Nat → Bool) (rounds firstLabel pending : Nat)
    (i : Fin (pendingAfter coins rounds firstLabel pending)) : Fin pending := by
  classical
  let T := pendingSurvivorIndices coins rounds firstLabel pending
  have hmem : T.orderEmbOfFin
      (pendingSurvivorIndices_card coins rounds firstLabel pending) i ∈ T :=
    Finset.orderEmbOfFin_mem T
      (pendingSurvivorIndices_card coins rounds firstLabel pending) i
  have hlt : T.orderEmbOfFin
      (pendingSurvivorIndices_card coins rounds firstLabel pending) i < pending := by
    have hrange : T.orderEmbOfFin
        (pendingSurvivorIndices_card coins rounds firstLabel pending) i ∈
        Finset.range pending := by
      exact (Finset.mem_filter.mp hmem).1
    exact Finset.mem_range.mp hrange
  exact ⟨T.orderEmbOfFin
    (pendingSurvivorIndices_card coins rounds firstLabel pending) i, hlt⟩

theorem pendingSurvivorFin_injective
    (coins : Nat × Nat → Bool) (rounds firstLabel pending : Nat) :
    Function.Injective (pendingSurvivorFin coins rounds firstLabel pending) := by
  intro i j hij
  apply (pendingSurvivorIndices coins rounds firstLabel pending).orderEmbOfFin
    (pendingSurvivorIndices_card coins rounds firstLabel pending) |>.injective
  exact congrArg Fin.val hij

theorem pendingSurvivorFin_survives
    (coins : Nat × Nat → Bool) (rounds firstLabel pending : Nat)
    (i : Fin (pendingAfter coins rounds firstLabel pending)) :
    survives coins rounds
      (firstLabel + (pendingSurvivorFin coins rounds firstLabel pending i).val) := by
  classical
  have hmem := Finset.orderEmbOfFin_mem
    (pendingSurvivorIndices coins rounds firstLabel pending)
    (pendingSurvivorIndices_card coins rounds firstLabel pending) i
  exact (Finset.mem_filter.mp hmem).2

/-- Future absolute coins restricted to the pre-surviving original labels. -/
noncomputable def originalSurvivorCoinRestriction
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (future : Nat × Nat → Bool) :
    Nat × Fin (pendingAfter preCoins preRounds firstLabel basePending) → Bool :=
  fun pair => future (pair.1,
    firstLabel +
      (pendingSurvivorFin preCoins preRounds firstLabel basePending pair.2).val)

theorem measurable_originalSurvivorCoinRestriction
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat) :
    Measurable (originalSurvivorCoinRestriction preCoins preRounds
      firstLabel basePending) := by
  apply Measurable.of_eval
  intro pair
  exact measurable_pi_apply (pair.1,
    firstLabel +
      (pendingSurvivorFin preCoins preRounds firstLabel basePending pair.2).val)

theorem fairCoinStreamLaw_originalSurvivorCoinRestriction
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat) :
    fairCoinStreamLaw.map
      (originalSurvivorCoinRestriction preCoins preRounds
        firstLabel basePending) =
    Measure.infinitePi (fun _ : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) => fairCoinLaw) := by
  let labels : Fin (pendingAfter preCoins preRounds firstLabel basePending) →
      Nat := fun i => firstLabel +
        (pendingSurvivorFin preCoins preRounds firstLabel basePending i).val
  have hlabels : Function.Injective labels := by
    intro i j hij
    exact (pendingSurvivorFin_injective preCoins preRounds firstLabel
      basePending) (Fin.ext (Nat.add_left_cancel hij))
  exact fairCoinStreamLaw_reindex_labels labels hlabels

theorem fairCoinStreamLaw_pair_originalSurvivorCoinRestriction
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair => (pair.1,
        originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending pair.2)) =
    fairCoinStreamLaw.prod
      (Measure.infinitePi (fun _ : Nat × Fin
        (pendingAfter preCoins preRounds firstLabel basePending) =>
          fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  calc
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => (pair.1,
          originalSurvivorCoinRestriction preCoins preRounds
            firstLabel basePending pair.2)) =
      (fairCoinStreamLaw.map id).prod
        (fairCoinStreamLaw.map
          (originalSurvivorCoinRestriction preCoins preRounds
            firstLabel basePending)) := by
          exact (Measure.map_prod_map fairCoinStreamLaw fairCoinStreamLaw
            measurable_id
            (measurable_originalSurvivorCoinRestriction preCoins preRounds
              firstLabel basePending)).symm
    _ = _ := by
      rw [Measure.map_id,
        fairCoinStreamLaw_originalSurvivorCoinRestriction]

theorem survives_originalSurvivorCoinExtension
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (future : Nat × Nat → Bool) (activeRounds : Nat)
    (i : Fin (pendingAfter preCoins preRounds firstLabel basePending)) :
    survives
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending future))
      activeRounds (firstLabel + i.val) ↔
    survives future activeRounds
      (firstLabel +
        (pendingSurvivorFin preCoins preRounds firstLabel basePending i).val) := by
  simp only [survives]
  constructor
  · intro h r hr
    have hcoin := h r hr
    rw [pendingCoinExtension_at firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) r i.val i.isLt]
      at hcoin
    exact hcoin
  · intro h r hr
    rw [pendingCoinExtension_at firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) r i.val i.isLt]
    exact h r hr

noncomputable def twoStageSurvivorLabel
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
  firstLabel +
    (pendingSurvivorFin preCoins preRounds firstLabel basePending
      (pendingSurvivorFin
        (pendingCoinExtension firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending)
          activeCoins)
        activeRounds firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending) i)).val

theorem twoStageSurvivorLabel_injective
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (activeCoins : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (activeRounds : Nat) :
    Function.Injective (twoStageSurvivorLabel preCoins preRounds
      firstLabel basePending activeCoins activeRounds) := by
  intro i j hij
  have houter := Nat.add_left_cancel hij
  have hpre :
      pendingSurvivorFin preCoins preRounds firstLabel basePending
        (pendingSurvivorFin
          (pendingCoinExtension firstLabel
            (pendingAfter preCoins preRounds firstLabel basePending)
            activeCoins)
          activeRounds firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending) i) =
      pendingSurvivorFin preCoins preRounds firstLabel basePending
        (pendingSurvivorFin
          (pendingCoinExtension firstLabel
            (pendingAfter preCoins preRounds firstLabel basePending)
            activeCoins)
          activeRounds firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending) j) :=
    Fin.ext houter
  have hactive := (pendingSurvivorFin_injective preCoins preRounds
    firstLabel basePending) hpre
  exact (pendingSurvivorFin_injective
    (pendingCoinExtension firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) activeCoins)
    activeRounds firstLabel
    (pendingAfter preCoins preRounds firstLabel basePending)) hactive

theorem twoStageSurvivorLabel_survives_splice
    (preCoins future : Nat × Nat → Bool)
    (preRounds firstLabel basePending activeRounds : Nat)
    (i : Fin (pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending future))
      activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))) :
    survives (spliceCoins preCoins future preRounds)
      (preRounds + activeRounds)
      (twoStageSurvivorLabel preCoins preRounds firstLabel basePending
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending future) activeRounds i) := by
  let pending := pendingAfter preCoins preRounds firstLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    firstLabel basePending future
  let j : Fin pending := pendingSurvivorFin
    (pendingCoinExtension firstLabel pending activeCoins)
    activeRounds firstLabel pending i
  have hpre : survives preCoins preRounds
      (firstLabel +
        (pendingSurvivorFin preCoins preRounds firstLabel basePending j).val) :=
    pendingSurvivorFin_survives preCoins preRounds firstLabel basePending j
  have hactive : survives
      (pendingCoinExtension firstLabel pending activeCoins)
      activeRounds (firstLabel + j.val) :=
    pendingSurvivorFin_survives
      (pendingCoinExtension firstLabel pending activeCoins)
      activeRounds firstLabel pending i
  have hfuture : survives future activeRounds
      (firstLabel +
        (pendingSurvivorFin preCoins preRounds firstLabel basePending j).val) :=
    (survives_originalSurvivorCoinExtension preCoins preRounds firstLabel
      basePending future activeRounds j).mp hactive
  exact (survives_spliceCoins preCoins future preRounds activeRounds _).2
    ⟨hpre, hfuture⟩

theorem exists_twoStageSurvivorLabel_of_survives_splice
    (preCoins future : Nat × Nat → Bool)
    (preRounds firstLabel basePending activeRounds k : Nat)
    (hk : k < basePending)
    (hsurv : survives (spliceCoins preCoins future preRounds)
      (preRounds + activeRounds) (firstLabel + k)) :
    ∃ i : Fin (pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending future))
      activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending)),
      twoStageSurvivorLabel preCoins preRounds firstLabel basePending
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending future) activeRounds i = firstLabel + k := by
  classical
  let pending := pendingAfter preCoins preRounds firstLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    firstLabel basePending future
  let Tpre := pendingSurvivorIndices preCoins preRounds firstLabel basePending
  have hpreCard : Tpre.card = pending :=
    pendingSurvivorIndices_card preCoins preRounds firstLabel basePending
  obtain ⟨hpre, hfuture⟩ :=
    (survives_spliceCoins preCoins future preRounds activeRounds
      (firstLabel + k)).mp hsurv
  have hpreMem : k ∈ Tpre := by
    simp [Tpre, pendingSurvivorIndices, hk, hpre]
  have hpreImage : k ∈ Finset.univ.image (Tpre.orderEmbOfFin hpreCard) := by
    simpa only [Finset.image_orderEmbOfFin_univ] using hpreMem
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hpreImage
  have hjval : (pendingSurvivorFin preCoins preRounds firstLabel
      basePending j).val = k := by
    simpa [pendingSurvivorFin, Tpre] using hj
  have hactive : survives
      (pendingCoinExtension firstLabel pending activeCoins)
      activeRounds (firstLabel + j.val) := by
    apply (survives_originalSurvivorCoinExtension preCoins preRounds
      firstLabel basePending future activeRounds j).mpr
    simpa [hjval] using hfuture
  let Tactive := pendingSurvivorIndices
    (pendingCoinExtension firstLabel pending activeCoins)
    activeRounds firstLabel pending
  have hactiveMem : j.val ∈ Tactive := by
    simp [Tactive, pendingSurvivorIndices, j.isLt, hactive]
  have hactiveCard : Tactive.card =
      pendingAfter (pendingCoinExtension firstLabel pending activeCoins)
        activeRounds firstLabel pending :=
    pendingSurvivorIndices_card
      (pendingCoinExtension firstLabel pending activeCoins)
      activeRounds firstLabel pending
  have hactiveImage : j.val ∈
      Finset.univ.image (Tactive.orderEmbOfFin hactiveCard) := by
    simpa only [Finset.image_orderEmbOfFin_univ] using hactiveMem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hactiveImage
  have hival : pendingSurvivorFin
      (pendingCoinExtension firstLabel pending activeCoins)
      activeRounds firstLabel pending i = j := by
    apply Fin.ext
    simpa [pendingSurvivorFin, Tactive] using hi
  refine ⟨i, ?_⟩
  unfold twoStageSurvivorLabel
  rw [hival, hjval]

/-- The original labels of the two-stage survivors are exactly the labels
surviving the spliced absolute coin stream. -/
theorem twoStageSurvivorLabels_eq_absoluteSurvivors
    (preCoins future : Nat × Nat → Bool)
    (preRounds firstLabel basePending activeRounds : Nat) :
    (Finset.univ.image
      (twoStageSurvivorLabel preCoins preRounds firstLabel basePending
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending future) activeRounds)) =
    ((Finset.range basePending).filter (fun k =>
      survives (spliceCoins preCoins future preRounds)
        (preRounds + activeRounds) (firstLabel + k))).image
          (fun k => firstLabel + k) := by
  classical
  ext label
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
      firstLabel basePending future
    let pending := pendingAfter preCoins preRounds firstLabel basePending
    let j := pendingSurvivorFin
      (pendingCoinExtension firstLabel pending activeCoins)
      activeRounds firstLabel pending i
    let k := (pendingSurvivorFin preCoins preRounds firstLabel basePending j).val
    have hk : k < basePending :=
      (pendingSurvivorFin preCoins preRounds firstLabel basePending j).isLt
    have hsurv : survives (spliceCoins preCoins future preRounds)
        (preRounds + activeRounds) (firstLabel + k) := by
      simpa [twoStageSurvivorLabel, j, k, activeCoins, pending] using
        twoStageSurvivorLabel_survives_splice preCoins future preRounds
          firstLabel basePending activeRounds i
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, ?_⟩
    · simp [hk, hsurv]
    · exact (show firstLabel + k =
        twoStageSurvivorLabel preCoins preRounds firstLabel basePending
          activeCoins activeRounds i by rfl).trans hi
  · intro h
    obtain ⟨k, hk, hlabel⟩ := Finset.mem_image.mp h
    have hk' : k < basePending := by
      exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hsurv : survives (spliceCoins preCoins future preRounds)
        (preRounds + activeRounds) (firstLabel + k) :=
      (Finset.mem_filter.mp hk).2
    obtain ⟨i, hi⟩ := exists_twoStageSurvivorLabel_of_survives_splice
      preCoins future preRounds firstLabel basePending activeRounds k hk' hsurv
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact hi.trans hlabel

theorem twoStageSurvivorCount_eq_absoluteSurvivorCount
    (preCoins future : Nat × Nat → Bool)
    (preRounds firstLabel basePending activeRounds : Nat) :
    pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending future))
      activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) =
    ((Finset.range basePending).filter (fun k =>
      survives (spliceCoins preCoins future preRounds)
        (preRounds + activeRounds) (firstLabel + k))).card := by
  classical
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    firstLabel basePending future
  let count := pendingAfter
    (pendingCoinExtension firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) activeCoins)
    activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending)
  let labels : Fin count → Nat :=
    twoStageSurvivorLabel preCoins preRounds firstLabel basePending
      activeCoins activeRounds
  have hlabels : Function.Injective labels :=
    twoStageSurvivorLabel_injective preCoins preRounds firstLabel basePending
      activeCoins activeRounds
  calc
    count = (Finset.univ.image labels).card := by
      rw [Finset.card_image_of_injective _ hlabels]
      simp
    _ = (((Finset.range basePending).filter (fun k =>
        survives (spliceCoins preCoins future preRounds)
          (preRounds + activeRounds) (firstLabel + k))).image
            (fun k => firstLabel + k)).card := by
      rw [twoStageSurvivorLabels_eq_absoluteSurvivors]
    _ = _ := by
      rw [Finset.card_image_of_injective]
      intro a b h
      exact Nat.add_left_cancel h

theorem colourCount_injective_labels
    {n count : Nat} (labels : Fin count → Nat)
    (hlabels : Function.Injective labels)
    (tape : Nat → LatticePoint n) (x : LatticePoint n) :
    colourCount (fun i => tape (labels i)) x =
      ((Finset.univ.image labels).filter fun label => tape label = x).card := by
  classical
  rw [Finset.filter_image, Finset.card_image_of_injective _ hlabels]
  rfl

/-- The newly appended batch has exactly the fixed-level marked Poisson
source's point counts at the absolute level reached by the count loop. -/
theorem twoStageSampler_pointCount_eq_absoluteTape
    {n : Nat} (S : Finset (LatticePoint n))
    (preCoins future : Nat × Nat → Bool)
    (preRounds firstLabel basePending activeRounds : Nat)
    (tape : Nat → LatticePoint n) (x : S) :
    let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
      firstLabel basePending future
    colourCount
      (fun i => tape (twoStageSurvivorLabel preCoins preRounds firstLabel
        basePending activeCoins activeRounds i)) x.1 =
    poissonTapePointCounts S firstLabel
      (preRounds + activeRounds)
      (basePending, spliceCoins preCoins future preRounds, tape) x := by
  dsimp only
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    firstLabel basePending future
  let count := pendingAfter
    (pendingCoinExtension firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) activeCoins)
    activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending)
  let labels : Fin count → Nat :=
    twoStageSurvivorLabel preCoins preRounds firstLabel basePending
      activeCoins activeRounds
  let T := (Finset.range basePending).filter (fun k =>
    survives (spliceCoins preCoins future preRounds)
      (preRounds + activeRounds) (firstLabel + k))
  have hlabels : Function.Injective labels :=
    twoStageSurvivorLabel_injective preCoins preRounds firstLabel basePending
      activeCoins activeRounds
  calc
    colourCount (fun i => tape (labels i)) x.1 =
      ((Finset.univ.image labels).filter fun label =>
        tape label = x.1).card :=
      colourCount_injective_labels labels hlabels tape x.1
    _ = ((T.image (fun k => firstLabel + k)).filter fun label =>
        tape label = x.1).card := by
          rw [twoStageSurvivorLabels_eq_absoluteSurvivors]
    _ = ((T.filter fun k => tape (firstLabel + k) = x.1).image
        (fun k => firstLabel + k)).card := by
          rw [Finset.filter_image]
    _ = (T.filter fun k => tape (firstLabel + k) = x.1).card := by
          rw [Finset.card_image_of_injective]
          intro a b h
          exact Nat.add_left_cancel h
    _ = poissonTapePointCounts S firstLabel
        (preRounds + activeRounds)
        (basePending, spliceCoins preCoins future preRounds, tape) x := by
          simp [T, poissonTapePointCounts, Finset.filter_filter,
            and_comm, and_left_comm]

/-- The full component output count vector is the retained old-copy vector
plus the absolute source's marked Poisson vector at the reached level. -/
theorem twoStageComponent_pointCounts_eq_absoluteTape
    {n : Nat} (s : TTCState n) (hfresh : s.LabelsFresh)
    (intensity : NNReal) (threshold : Real)
    (preCoins future oldCoins : Nat × Nat → Bool)
    (preRounds basePending : Nat)
    (tape : Nat → LatticePoint n) (S : Finset (LatticePoint n)) :
    let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
      s.nextLabel basePending future
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let rounds := ttcReference.firstLoopExit s intensity threshold
    let first := ttcReference.firstLoopResult s intensity threshold oldCoins
    let second := thinningResultSplitFinite first pending threshold
      (shiftCoins rounds oldCoins) activeCoins
    let activeRounds := firstExitRoundSplit first pending threshold
      (shiftCoins rounds oldCoins)
      (pendingCoinExtension s.nextLabel pending activeCoins)
    let batch := fun i : Fin second.2 =>
      tape (twoStageSurvivorLabel preCoins preRounds s.nextLabel
        basePending activeCoins activeRounds i)
    (second.1.addBatch batch).pointCounts S =
      fun x : S => second.1.pointCounts S x +
        poissonTapePointCounts S s.nextLabel
          (preRounds + activeRounds)
          (basePending, spliceCoins preCoins future preRounds, tape) x := by
  dsimp only
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    s.nextLabel basePending future
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let rounds := ttcReference.firstLoopExit s intensity threshold
  let first := ttcReference.firstLoopResult s intensity threshold oldCoins
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds oldCoins) activeCoins
  let activeRounds := firstExitRoundSplit first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension s.nextLabel pending activeCoins)
  let batch : Fin second.2 → LatticePoint n := fun i =>
    tape (twoStageSurvivorLabel preCoins preRounds s.nextLabel
      basePending activeCoins activeRounds i)
  have hfirst : first.LabelsFresh :=
    rateThinningResult_labelsFresh s intensity threshold oldCoins
      hfresh
  have hsecond : second.1.LabelsFresh :=
    thinningResultSplitFinite_labelsFresh first pending threshold
      (shiftCoins rounds oldCoins) activeCoins hfirst
  rw [TTCState.pointCounts_addBatch second.1 batch S hsecond]
  funext x
  change second.1.pointCounts S x + colourCount batch x.1 =
    second.1.pointCounts S x +
      poissonTapePointCounts S s.nextLabel
        (preRounds + activeRounds)
        (basePending, spliceCoins preCoins future preRounds, tape) x
  congr 1
  exact twoStageSampler_pointCount_eq_absoluteTape S preCoins future
    preRounds s.nextLabel basePending activeRounds tape x

/-- With the two-stage survivor history fixed, the executable sampler may
draw its IID marks from the original Poisson-copy labels. -/
theorem community_twoStage_sampler_tape
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (oldCoins : Nat × Nat → Bool)
    (activeCoins : Nat × Fin
      (pendingAfter preCoins preRounds s.nextLabel basePending) → Bool) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let rounds := ttcReference.firstLoopExit s intensity threshold
    let first := ttcReference.firstLoopResult s intensity threshold oldCoins
    let second := thinningResultSplitFinite first pending threshold
      (shiftCoins rounds oldCoins) activeCoins
    let activeRounds := firstExitRoundSplit first pending threshold
      (shiftCoins rounds oldCoins)
      (pendingCoinExtension s.nextLabel pending activeCoins)
    let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    ((ttcSubroutines hn prep).GenerateSamples P second.2
      b eta).map (fun batch => second.1.addBatch batch) =
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape => second.1.addBatch
        (fun i : Fin second.2 => tape
          (twoStageSurvivorLabel preCoins preRounds s.nextLabel basePending
            activeCoins activeRounds i))) := by
  dsimp only
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let rounds := ttcReference.firstLoopExit s intensity threshold
  let first := ttcReference.firstLoopResult s intensity threshold oldCoins
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds oldCoins) activeCoins
  let activeRounds := firstExitRoundSplit first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension s.nextLabel pending activeCoins)
  let labels : Fin second.2 → Nat :=
    twoStageSurvivorLabel preCoins preRounds s.nextLabel basePending
      activeCoins activeRounds
  have hlabels : Function.Injective labels :=
    twoStageSurvivorLabel_injective preCoins preRounds s.nextLabel basePending
      activeCoins activeRounds
  exact community_sampleAppend_from_iidTape_at_labels
    hn prep P b eta delta hroute second labels hlabels

end ttc

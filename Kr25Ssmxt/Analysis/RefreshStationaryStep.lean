import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.AdvanceObservedRep
import Kr25Ssmxt.Analysis.ProductSplitBind
import Kr25Ssmxt.Analysis.SourceFreshCriterion
import Kr25Ssmxt.Analysis.OriginRefreshedStateMarginal
import Kr25Ssmxt.Analysis.OriginIntensityMeasurable

/-! The strong Markov property of one refreshed component step: after the
step, the observed prefix is independent of a globally fair unused tail.
Consequently every refreshed component law is fixed by the refresh kernel. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem OriginConfiguration.measurable_refreshFuture_advance_pair
    {n : Nat} {α : Type*} [MeasurableSpace α]
    (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins : Nat × Nat → Bool)
    (g : α → Nat × (Nat × Nat) → Bool)
    (f : α → Nat × Nat → Bool) (t : α → Nat → LatticePoint n)
    (hg : Measurable g) (hf : Measurable f) (ht : Measurable t) :
    Measurable (fun y : α =>
      (c.refreshFuture (g y)).advance P intensity threshold basePending
        preCoins (f y) (t y)) := by
  have hjoint := OriginConfiguration.measurable_advance_coinPair_intensity
    P threshold hthreshold basePending
  have h1 : Measurable (fun y : α => c.refreshFuture (g y)) :=
    c.measurable_refreshFuture.comp hg
  have h2 : Measurable (fun y : α => (c.refreshFuture (g y), intensity)) :=
    h1.prodMk measurable_const
  have h3 : Measurable (fun y : α =>
      ((c.refreshFuture (g y), intensity), (preCoins, f y))) :=
    h2.prodMk (measurable_const.prodMk hf)
  have h4 : Measurable (fun y : α =>
      (((c.refreshFuture (g y), intensity), (preCoins, f y)), t y)) :=
    h3.prodMk ht
  have h5 := hjoint.comp h4
  rw [Function.comp_def] at h5
  exact h5

/-- The product split used by refresh stationarity. -/
abbrev OriginTailFair {n : Nat}
    (ρ : Measure (OriginConfiguration n)) : Prop :=
  ProductSplit (fun c : OriginConfiguration n =>
      c.observedRepresentative)
    (fun c : OriginConfiguration n => c.unusedTail)
    (Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) ρ

theorem OriginTailFair.bind {n : Nat} {α : Type*}
    [MeasurableSpace α] (M : Measure α)
    (K : α → Measure (OriginConfiguration n)) (hK : Measurable K)
    (hsplit : ∀ a, OriginTailFair (K a)) :
    OriginTailFair (M.bind K) := by
  let : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  exact ProductSplit.bind measurable_originObservedRepresentative
    measurable_originUnusedTail M K hK hsplit

set_option maxHeartbeats 400000 in
/-- One fixed first-loop prefix, Poisson count, pre-thinning coins, and point
tape: the refreshed step is tail-fair over the remaining old/new sources. -/
theorem OriginConfiguration.refreshed_advance_tailFair_of_prefix
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) (pre : Nat × (Nat × Nat) → Bool) :
    let rounds := ttcReference.firstLoopExit (c.state.removeComponent P)
      intensity threshold
    OriginTailFair
      (((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw).map
        (fun y => (c.refreshFuture
          (globalSourceGlue rounds pre y.1)).advance P intensity
            threshold basePending preCoins y.2 tape)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let μ := sourceLaw.prod fairCoinStreamLaw
  let : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  let : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  let : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let deleted := c.state.removeComponent P
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let glue := globalSourceGlue rounds pre
  let firstOf : (Nat × (Nat × Nat) → Bool) → TTCState n := fun old =>
    ttcReference.firstLoopResult deleted intensity threshold
      (sourceOldCoins c.origin
        (c.refreshFuture old).source.coins c.level)
  let first := firstOf (glue (fun _ => false))
  have hfirstOf (q : Nat × (Nat × Nat) → Bool) : firstOf (glue q) = first :=
    c.refreshed_rateThinningResult_eq_of_prefix_eq P intensity threshold
      (glue q) (glue (fun _ => false))
      ((globalSourcePrefix_glue rounds pre q).trans
        (globalSourcePrefix_glue rounds pre _).symm)
  let pending := pendingAfter preCoins preRounds first.nextLabel basePending
  let obs := survivorPairFullObservation first threshold preCoins
    preRounds basePending c.origin
  let rem := survivorPairRemaining first threshold preCoins
    preRounds basePending c.origin
  let read := survivorPairRead preCoins preRounds first.nextLabel
    basePending c.origin
  let adv : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) →
      OriginConfiguration n := fun y =>
    (c.refreshFuture (glue y.1)).advance P intensity threshold basePending
      preCoins y.2 tape
  let Ψ : Nat × ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) →
      OriginConfiguration n := fun o =>
    (adv o.2).observedRepresentative
  have hhistory : OriginHistory first.nextLabel c.source.processed
      c.origin := by
    change OriginHistory c.state.nextLabel c.source.processed
      c.origin
    exact c.history
  -- measurability
  have hglue : Measurable glue :=
    (measurable_globalSourceGlue rounds).comp
      (measurable_const.prodMk measurable_id)
  have hadv : Measurable adv := by
    have h := c.measurable_refreshFuture_advance_pair
      (α := (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) P intensity
      threshold hthreshold basePending preCoins (fun y => glue y.1)
      (fun y => y.2) (fun _ => tape) (hglue.comp measurable_fst)
      measurable_snd measurable_const
    beta_reduce at h
    exact h
  have hΨ : Measurable Ψ :=
    measurable_originObservedRepresentative.comp
      (hadv.comp measurable_snd)
  have hobs : Measurable obs :=
    measurable_survivorPairFullObservation first threshold
      preCoins preRounds basePending c.origin
  have hrem : Measurable rem :=
    measurable_survivorPairRemaining first threshold preCoins
      preRounds basePending c.origin
  have hread : Measurable read :=
    measurable_survivorPairRead preCoins preRounds
      first.nextLabel basePending c.origin
  -- the product law of observation and remaining sources
  have hab : μ.map (fun y => (obs y, rem y)) = (μ.map obs).prod μ :=
    survivorPair_fullPrefix_tail_product first threshold
      hthreshold.le preCoins preRounds basePending c.source.processed
      c.origin hhistory
  -- the read stream is fair, so the loop terminates almost surely
  have hreadLaw : μ.map read = fairCoinStreamLaw := by
    have hjointLaw := fairCoinStreamLaw_jointRead
    change fairCoinStreamLaw.map _ = μ at hjointLaw
    rw [← hjointLaw, Measure.map_map hread measurable_jointRead]
    have hcomp : read ∘ (fun coins => (jointOldRead coins,
        jointFreshRead coins)) =
        jointSurvivorRead preCoins preRounds first.nextLabel
          basePending c.origin := by
      funext coins
      exact survivorPairRead_jointRead preCoins preRounds
        first.nextLabel basePending c.origin coins
    rw [hcomp]
    exact fairCoinStreamLaw_jointSurvivorRead preCoins preRounds
      first.nextLabel basePending c.source.processed c.origin hhistory
  have hguard : ∀ᵐ y ∂μ, ttcPseudocode.secondLoopExit first pending threshold (read y)
      (survivorPairStop first threshold preCoins preRounds
        basePending c.origin y) := by
    have h := firstExitRound_guard_ae first pending threshold hthreshold.le
    rw [← hreadLaw] at h
    exact ae_of_ae_map hread.aemeasurable h
  -- the pathwise identities
  have hobsEq : ∀ᵐ y ∂μ, (adv y).observedRepresentative = Ψ (obs y) := by
    filter_upwards [hguard] with y hy
    have hrec := survivorPairFullObservation_reconstruct first
      threshold preCoins preRounds basePending c.origin y hy
    apply c.refreshed_advance_observedRepresentative_eq P intensity
      threshold basePending preCoins y.2 (obs y).2.2 (glue y.1)
      (glue (obs y).2.1) tape
    · exact (globalSourcePrefix_glue rounds pre _).trans
        (globalSourcePrefix_glue rounds pre _).symm
    · change survivorPairFullObservation (firstOf (glue y.1))
          threshold preCoins preRounds basePending c.origin
          (globalSourceShift rounds (glue y.1), y.2) =
        survivorPairFullObservation (firstOf (glue y.1))
          threshold preCoins preRounds basePending c.origin
          (globalSourceShift rounds (glue (obs y).2.1),
            (obs y).2.2)
      rw [hfirstOf]
      simp only [glue, globalSourceShift_glue]
      exact hrec.symm
  have htailEq : ∀ y, (adv y).unusedTail =
      combinedTail c.source.processed (rem y) := by
    intro y
    have h := c.refreshed_advance_unusedTail_eq_combined P intensity
      threshold basePending preCoins y.2 (glue y.1) tape
    change (adv y).unusedTail = combinedTail c.source.processed
      (survivorPairRemaining (firstOf (glue y.1)) threshold
        preCoins preRounds basePending c.origin
        (globalSourceShift rounds (glue y.1), y.2)) at h
    rw [h, hfirstOf]
    simp only [glue, globalSourceShift_glue]
    rfl
  have hsplit := ProductSplit.of_map_factor μ μ obs rem hobs hrem hab adv
    (fun c : OriginConfiguration n => c.observedRepresentative)
    (fun c : OriginConfiguration n => c.unusedTail) Ψ
    (combinedTail c.source.processed) hΨ
    (measurable_combinedTail c.source.processed)
    measurable_originObservedRepresentative
    measurable_originUnusedTail hadv hobsEq htailEq
  rw [combinedTail_law] at hsplit
  exact hsplit

/-- Fixed Poisson count, pre-thinning coins, and point tape: averaging the
first-loop prefix keeps the refreshed step tail-fair. -/
theorem OriginConfiguration.refreshed_advance_tailFair
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    OriginTailFair
      (((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw).map
        (fun pair => (c.refreshFuture pair.1).advance P intensity
            threshold basePending preCoins pair.2 tape)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let μ := sourceLaw.prod fairCoinStreamLaw
  let _ : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  let _ : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  let _ : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let _ : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let rounds := ttcReference.firstLoopExit (c.state.removeComponent P)
    intensity threshold
  let lam := sourceLaw.map (globalSourcePrefix rounds)
  let split : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) →
      (Nat × (Nat × Nat) → Bool) ×
        ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) := fun z =>
    (globalSourcePrefix rounds z.1,
      (globalSourceShift rounds z.1, z.2))
  let unsplit : (Nat × (Nat × Nat) → Bool) ×
      ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) →
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) := fun w =>
    (globalSourceGlue rounds w.1 w.2.1, w.2.2)
  have hsplit : Measurable split :=
    ((measurable_globalSourcePrefix rounds).comp
      measurable_fst).prodMk
      (((measurable_globalSourceShift rounds).comp
        measurable_fst).prodMk measurable_snd)
  have hunsplit : Measurable unsplit :=
    ((measurable_globalSourceGlue rounds).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hround : unsplit ∘ split = id := by
    funext z
    exact Prod.ext (globalSourceGlue_prefix_shift rounds z.1) rfl
  have hlaw : μ.map split = lam.prod μ :=
    globalSource_prefix_with_fresh_law rounds
  have hμ : μ = (lam.prod μ).map unsplit := by
    rw [← hlaw, Measure.map_map hunsplit hsplit, hround, Measure.map_id]
  let H : (Nat × (Nat × Nat) → Bool) ×
      ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) →
      OriginConfiguration n := fun w =>
    (c.refreshFuture (globalSourceGlue rounds w.1 w.2.1)).advance
      P intensity threshold basePending preCoins w.2.2 tape
  have hH : Measurable H :=
    c.measurable_refreshFuture_advance_pair
      (α := (Nat × (Nat × Nat) → Bool) ×
        ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)))
      P intensity threshold hthreshold basePending preCoins
      (fun w => globalSourceGlue rounds w.1 w.2.1)
      (fun w => w.2.2) (fun _ => tape)
      ((measurable_globalSourceGlue rounds).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
      (measurable_snd.comp measurable_snd) measurable_const
  have hadv : Measurable (fun pair : (Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool) => (c.refreshFuture pair.1).advance P intensity
        threshold basePending preCoins pair.2 tape) :=
    c.measurable_refreshFuture_advance_pair
      (α := (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))
      P intensity threshold hthreshold basePending preCoins
      (fun pair => pair.1) (fun pair => pair.2)
      (fun _ => tape) measurable_fst measurable_snd measurable_const
  have hcomp : (fun pair : (Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool) => (c.refreshFuture pair.1).advance P intensity
        threshold basePending preCoins pair.2 tape) ∘ unsplit = H := rfl
  have hK : Measurable (fun p : Nat × (Nat × Nat) → Bool =>
      μ.map (fun y => H (p, y))) := by
    have h := (Measure.measurable_map H hH).comp
      (Measurable.map_prodMk_left (ν := μ))
    have heq : (fun p : Nat × (Nat × Nat) → Bool => μ.map (fun y => H (p, y))) =
        (Measure.map H) ∘ (fun p => μ.map (Prod.mk p)) := by
      funext p
      simp only [Function.comp_apply]
      rw [Measure.map_map hH measurable_prodMk_left]
      rfl
    rw [heq]
    exact h
  have hbind : (lam.prod μ).map H = lam.bind (fun p => μ.map (fun y => H (p, y))) := by
    rw [Measure.prod_eq_bind_map, map_bind_measure lam _ H
      Measurable.map_prodMk_left.aemeasurable hH]
    congr 1
    funext p
    rw [Measure.map_map hH measurable_prodMk_left]
    rfl
  change OriginTailFair (μ.map _)
  rw [hμ, Measure.map_map hadv hunsplit, hcomp, hbind]
  apply OriginTailFair.bind lam _ hK
  intro p
  exact c.refreshed_advance_tailFair_of_prefix P intensity threshold
    hthreshold basePending preCoins tape p

end Kr25Ssmxt

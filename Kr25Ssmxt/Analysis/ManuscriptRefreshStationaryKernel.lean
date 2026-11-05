import Kr25Ssmxt.Analysis.ManuscriptRefreshStationaryStep
import Kr25Ssmxt.Analysis.ManuscriptOriginOrderedMarginal

/-! Every refreshed component law, and every mixture of them, is fixed by
the source-tail refresh kernel. -/

namespace Kr25Ssmxt

open MeasureTheory

set_option maxHeartbeats 1000000 in
/-- For fixed Poisson count and pre-thinning coins, averaging the old/new
fair sources and the independent point tape keeps the step tail-fair. -/
theorem manuscriptOriginOrderedInnerLaw_tailFair
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : ManuscriptOriginConfiguration n)
    (preCoins : Nat × Nat → Bool) :
    ManuscriptOriginTailFair
      (manuscriptOriginOrderedInnerLaw hn P b eta threshold hroute
        intensity basePending c preCoins) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let _ : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  let _ : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  let _ : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let pairLaw := sourceLaw.prod fairCoinStreamLaw
  let _ : IsProbabilityMeasure pairLaw := by
    dsimp [pairLaw]
    infer_instance
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  let _ : IsProbabilityMeasure pointLaw :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  let tapeLaw : Measure (Nat → LatticePoint n) :=
    Measure.infinitePi (fun _ : Nat => pointLaw)
  let _ : IsProbabilityMeasure tapeLaw := by
    dsimp [tapeLaw]
    infer_instance
  let adv2 : ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) ×
      (Nat → LatticePoint n) → ManuscriptOriginConfiguration n := fun z =>
    (c.refreshFuture z.1.1).advance P intensity threshold basePending
      preCoins z.1.2 z.2
  have hadv2 : Measurable adv2 := by
    have h := c.measurable_refreshFuture_advance_pair
      (α := ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) ×
        (Nat → LatticePoint n))
      P intensity threshold hthreshold basePending preCoins
      (fun z => z.1.1) (fun z => z.1.2) (fun z => z.2)
      (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst) measurable_snd
    beta_reduce at h
    exact h
  have hdirac : Measurable (fun z => Measure.dirac (adv2 z)) :=
    Measure.measurable_dirac.comp hadv2
  have hinner : manuscriptOriginOrderedInnerLaw hn P b eta threshold hroute
      intensity basePending c preCoins =
      pairLaw.bind (fun pair => tapeLaw.bind
        (fun tape => Measure.dirac (adv2 (pair, tape)))) := by
    unfold manuscriptOriginOrderedInnerLaw
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro pair
    unfold manuscriptOriginCoinPairTapeLaw
    exact (Measure.bind_dirac_eq_map tapeLaw
      (hadv2.comp measurable_prodMk_left)).symm
  rw [hinner, measure_independent_bind_comm pairLaw tapeLaw
    (fun z => Measure.dirac (adv2 z)) hdirac]
  have hK : Measurable (fun tape : Nat → LatticePoint n =>
      pairLaw.bind (fun pair => Measure.dirac (adv2 (pair, tape)))) := by
    have h := measurable_parametric_probability_bind
      (fun _ : Nat → LatticePoint n => pairLaw) measurable_const
      (fun _ => inferInstance)
      (fun z : (Nat → LatticePoint n) ×
          ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) =>
        Measure.dirac (adv2 (z.2, z.1)))
      (hdirac.comp measurable_swap)
    exact h
  apply ManuscriptOriginTailFair.bind tapeLaw _ hK
  intro tape
  have hmap := Measure.bind_dirac_eq_map pairLaw
    (hadv2.comp (measurable_prodMk_right (y := tape)))
  change ManuscriptOriginTailFair
    (pairLaw.bind fun pair => Measure.dirac ((adv2 ∘ fun x => (x, tape)) pair))
  rw [hmap]
  exact c.refreshed_advance_tailFair P intensity threshold hthreshold
    basePending preCoins tape

set_option maxHeartbeats 1000000 in
/-- The refreshed one-component ghost law is tail-fair. -/
theorem manuscriptOriginRefreshedComponentLaw_tailFair
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    ManuscriptOriginTailFair
      (manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
        intensity c) := by
  rw [manuscriptOriginRefreshedComponentLaw_eq_ordered hn P b eta threshold
    hthreshold hroute intensity c]
  unfold manuscriptOriginOrderedComponentLaw
  apply ManuscriptOriginTailFair.bind _ _ (measurable_of_countable _)
  intro basePending
  exact ManuscriptOriginTailFair.bind fairCoinStreamLaw
    (manuscriptOriginOrderedInnerLaw hn P b eta threshold hroute intensity
      basePending c)
    (measurable_manuscriptOriginOrderedInnerLaw_preCoins hn P b eta
      threshold hthreshold hroute intensity basePending c)
    (fun preCoins => manuscriptOriginOrderedInnerLaw_tailFair hn P b eta
      threshold hthreshold hroute intensity basePending c preCoins)

/-- **Refresh stationarity is created by every refreshed component step.**
For any incoming ghost law, the output law of one refreshed component is
fixed by the source-tail refresh kernel. -/
theorem manuscriptOriginRefreshedComponentLaw_bind_stationary
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (μ : Measure (ManuscriptOriginConfiguration n)) :
    (μ.bind (manuscriptOriginRefreshedComponentLaw hn P b eta threshold
        hroute intensity)).bind (fun c => c.refreshLaw) =
      μ.bind (manuscriptOriginRefreshedComponentLaw hn P b eta threshold
        hroute intensity) := by
  apply manuscriptOrigin_refresh_stationary_of_prefix_tail_product
  exact ManuscriptOriginTailFair.bind μ _
    (measurable_manuscriptOriginRefreshedComponentLaw hn P b eta threshold
      hthreshold hroute intensity)
    (fun c => manuscriptOriginRefreshedComponentLaw_tailFair hn P b eta
      threshold hthreshold hroute intensity c)

end Kr25Ssmxt

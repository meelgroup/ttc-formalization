import Kr25Ssmxt.Analysis.OriginGivenVolumesFold

/-! Almost surely every valid source tag carries a mark in the finite
lattice set `S`; consequently the stored population is the total of the
source point counts on `S`. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

/-- Every valid source tag is marked by a point of `S`. -/
def OriginConfiguration.MarksIn {n : Nat}
    (S : Finset (LatticePoint n)) (c : OriginConfiguration n) : Prop :=
  ∀ tag ∈ c.source.valid, c.source.marks tag ∈ S

theorem measurableSet_originMarksIn {n : Nat}
    (S : Finset (LatticePoint n)) :
    MeasurableSet {c : OriginConfiguration n | c.MarksIn S} := by
  have h : {c : OriginConfiguration n | c.MarksIn S} =
      {c | ∀ tag, tag ∈ c.source.valid → c.source.marks tag ∈ S} := rfl
  rw [h]
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro tag
  apply Measurable.imp
  · exact (measurable_finset_mem tag).comp
      (measurable_originSourceState_valid.comp
        measurable_originConfiguration_source)
  · exact measurableSet_setOfPred.mp (S.measurableSet.preimage
      ((measurable_pi_apply tag).comp
        (measurable_originSourceState_marks.comp
          measurable_originConfiguration_source)))

/-- With all valid marks in `S`, the stored population equals the total of
the source point counts on `S` at the current level. -/
theorem OriginConfiguration.samples_card_eq_sum_pointCounts
    {n : Nat} (c : OriginConfiguration n)
    (S : Finset (LatticePoint n)) (hmarks : c.MarksIn S) :
    c.state.X.card = ∑ x : S, c.source.pointCounts c.level S x := by
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := c.state.X) (t := S) (f := fun copy => copy.2)
    (fun copy hcopy => by
      have hm := c.marked copy hcopy
      have hv := c.valid copy hcopy
      simp only
      rw [hm]
      exact hmarks _ hv)
  rw [hfib, ← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro x _
  have := congrFun (c.pointCounts_eq_source S) x
  rw [← this]
  rfl

theorem ae_bind_of_ae_ae_marksIn {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {m : Measure α} {f : α → Measure β}
    (hf : AEMeasurable f m)
    {p : β → Prop} (hp : MeasurableSet {b | p b})
    (h : ∀ᵐ a ∂m, ∀ᵐ b ∂f a, p b) : ∀ᵐ b ∂m.bind f, p b := by
  rw [ae_iff]
  apply nonpos_iff_eq_zero.mp
  calc m.bind f {b | ¬p b} ≤ ∫⁻ a, f a {b | ¬p b} ∂m :=
        Measure.bind_apply_le hf hp.compl
    _ = ∫⁻ _, 0 ∂m := by
        apply lintegral_congr_ae
        filter_upwards [h] with a ha
        exact ae_iff.mp ha
    _ = 0 := lintegral_zero

theorem ae_map_of_ae_marksIn {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {ν : Measure α} {f : α → β}
    (hf : AEMeasurable f ν)
    {p : β → Prop} (hp : MeasurableSet {b | p b})
    (h : ∀ᵐ a ∂ν, p (f a)) : ∀ᵐ b ∂ν.map f, p b :=
  (ae_map_iff hf hp).mpr h

theorem OriginConfiguration.advance_marksIn {n : Nat}
    (S : Finset (LatticePoint n)) (c : OriginConfiguration n)
    (hc : c.MarksIn S)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) (htape : ∀ j, tape j ∈ S) :
    (c.advance P intensity threshold basePending preCoins future tape).MarksIn
      S := by
  unfold OriginConfiguration.MarksIn
  rw [c.advance_source P intensity threshold basePending preCoins future tape]
  intro tag htag
  change tag ∈ validUpdate c.source.valid c.source.marks P
    c.source.processed c.state.nextLabel basePending at htag
  change marksAppend c.source.marks c.source.processed tape tag ∈ S
  unfold validUpdate at htag
  unfold marksAppend
  rcases Finset.mem_union.mp htag with hold | hnew
  · have hvalid := (Finset.mem_filter.mp hold).1
    have hlt := c.bound tag hvalid
    rw [if_neg (Nat.ne_of_lt hlt)]
    exact hc tag hvalid
  · unfold originSourceTags at hnew
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hnew
    rw [if_pos rfl]
    exact htape _

theorem OriginConfiguration.refreshFuture_marksIn {n : Nat}
    (S : Finset (LatticePoint n)) (c : OriginConfiguration n)
    (hc : c.MarksIn S) (future : Nat × (Nat × Nat) → Bool) :
    (c.refreshFuture future).MarksIn S := hc

theorem ae_tape_mem_marksIn {n : Nat} (μ : Measure (LatticePoint n))
    [IsProbabilityMeasure μ] (S : Finset (LatticePoint n))
    (hsupport : μ (S : Set (LatticePoint n))ᶜ = 0) :
    ∀ᵐ tape ∂(Measure.infinitePi (fun _ : Nat => μ)), ∀ j, tape j ∈ S := by
  rw [ae_all_iff]
  intro j
  have hmap := Measure.infinitePi_map_eval (fun _ : Nat => μ) j
  have hS : MeasurableSet (S : Set (LatticePoint n)) := S.measurableSet
  have : ∀ᵐ x ∂((Measure.infinitePi (fun _ : Nat => μ)).map
      (fun tape => tape j)), x ∈ S := by
    rw [hmap]
    exact measure_eq_zero_iff_ae_notMem.mp hsupport |>.mono
      (fun x hx => by simpa using hx)
  exact ae_of_ae_map (measurable_pi_apply j).aemeasurable this

set_option linter.unusedVariables false in
theorem originRefreshedComponentLaw_ae_marksIn
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (S : Finset (LatticePoint n))
    (hsupport : (normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0)
    (c : OriginConfiguration n) (hc : c.MarksIn S) :
    ∀ᵐ c' ∂(originRefreshedComponentLaw hn P b eta threshold
      hroute intensity c), c'.MarksIn S := by
  have hmeas := measurableSet_originMarksIn (n := n) S
  let _ : IsProbabilityMeasure (normalizedHitAndRunPointLaw hn P b eta
      hroute.1 hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2) :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  have htape := ae_tape_mem_marksIn _ S hsupport
  have hrefresh : ∀ᵐ c1 ∂c.refreshLaw, c1.MarksIn S := by
    unfold OriginConfiguration.refreshLaw
    exact ae_map_of_ae_marksIn c.measurable_refreshFuture.aemeasurable hmeas
      (ae_of_all _ (fun f =>
      OriginConfiguration.refreshFuture_marksIn S c hc f))
  unfold originRefreshedComponentLaw
  apply ae_bind_of_ae_ae_marksIn
    (measurable_originPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity).aemeasurable hmeas
  filter_upwards [hrefresh] with c1 hc1
  unfold originPoissonCoinTapeLaw
  apply ae_bind_of_ae_ae_marksIn (measurable_of_countable _).aemeasurable hmeas
  refine ae_of_all _ (fun basePending => ?_)
  unfold originFairCoinTapeLaw
  apply ae_bind_of_ae_ae_marksIn
    ((measurable_originCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (measurable_const.prodMk measurable_id)).aemeasurable hmeas
  refine ae_of_all _ (fun coins => ?_)
  unfold originCoinPairTapeLaw
  apply ae_map_of_ae_marksIn
    (c1.measurable_advance_tape P intensity threshold basePending
      coins.1 coins.2).aemeasurable hmeas
  filter_upwards [htape] with tape ht
  exact OriginConfiguration.advance_marksIn S c1 hc1 P intensity
    threshold basePending _ _ tape ht

theorem originGivenVolumesLaw_ae_marksIn
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (S : Finset (LatticePoint n))
    (components : List
      (OriginCertifiedComponent n k hn prep b eta delta))
    (hsupport : ∀ d ∈ components,
      (normalizedHitAndRunPointLaw hn d.polytope b eta d.route.1
        d.route.2.1 d.route.2.2.1 d.route.2.2.2.1 d.route.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0)
    (outcomes : Fin components.length → VolumeOutcome)
    (μ : Measure (OriginConfiguration n))
    (hμ : ∀ᵐ c ∂μ, c.MarksIn S) :
    ∀ᵐ c ∂(μ.bind (originGivenVolumesLaw hn prep b eta delta
      threshold components outcomes)), c.MarksIn S := by
  induction components generalizing μ with
  | nil =>
      apply ae_bind_of_ae_ae_marksIn Measure.measurable_dirac.aemeasurable
        (measurableSet_originMarksIn S)
      filter_upwards [hμ] with c hc
      change ∀ᵐ c' ∂(Measure.dirac c), c'.MarksIn S
      exact (ae_dirac_iff (measurableSet_originMarksIn S)).mpr hc
  | cons d rest ih =>
      apply ae_bind_of_ae_ae_marksIn
        (measurable_originGivenVolumesLaw hn prep b eta delta
          threshold hthreshold (d :: rest) outcomes).aemeasurable
        (measurableSet_originMarksIn S)
      filter_upwards [hμ] with c hc
      exact ih (fun d' hd' => hsupport d' (List.mem_cons_of_mem d hd'))
        (fun i => outcomes i.succ) _
        (originRefreshedComponentLaw_ae_marksIn hn d.polytope b eta
          threshold hthreshold d.route _ S (hsupport d List.mem_cons_self) c hc)

end Kr25Ssmxt

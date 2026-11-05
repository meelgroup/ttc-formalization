import Kr25Ssmxt.Analysis.ManuscriptOriginAdvanceStateCoinPairMeasurable

/-! The ghost transition after independent fair coin arrays and point tape
are drawn, conditional on a fixed Poisson count and volume outcome. -/

namespace Kr25Ssmxt

open MeasureTheory

private abbrev ManuscriptGhostCoinInput'' (n : Nat) :=
  ManuscriptOriginConfiguration n ×
    ((Nat × Nat → Bool) × (Nat × Nat → Bool))

noncomputable def manuscriptOriginCoinPairTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (z : ManuscriptGhostCoinInput'' n) :
    Measure (ManuscriptOriginConfiguration n) :=
  (Measure.infinitePi (fun _ : Nat =>
    normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)).map
    (fun tape => z.1.advance P intensity threshold basePending
      z.2.1 z.2.2 tape)

theorem measurable_manuscriptOriginCoinPairTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat) :
    Measurable (manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hroute intensity basePending) := by
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  letI : IsProbabilityMeasure pointLaw :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  let tapeLaw : Measure (Nat → LatticePoint n) :=
    Measure.infinitePi (fun _ : Nat => pointLaw)
  letI : ∀ _ : Nat, IsProbabilityMeasure pointLaw := fun _ => inferInstance
  letI : IsProbabilityMeasure tapeLaw := by
    dsimp [tapeLaw]
    infer_instance
  have hdirac : Measurable (fun z : ManuscriptGhostCoinInput'' n ×
      (Nat → LatticePoint n) =>
      Measure.dirac (z.1.1.advance P intensity threshold basePending
        z.1.2.1 z.1.2.2 z.2)) :=
    Measure.measurable_dirac.comp
      (ManuscriptOriginConfiguration.measurable_advance_coinPair
        P intensity threshold hthreshold basePending)
  have hbind := measurable_parametric_probability_bind
    (fun _ : ManuscriptGhostCoinInput'' n => tapeLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : ManuscriptGhostCoinInput'' n × (Nat → LatticePoint n) =>
      Measure.dirac (z.1.1.advance P intensity threshold basePending
        z.1.2.1 z.1.2.2 z.2)) hdirac
  convert hbind using 1
  funext z
  exact (Measure.bind_dirac_eq_map tapeLaw
    (z.1.measurable_advance_tape P intensity threshold basePending
      z.2.1 z.2.2)).symm

noncomputable def manuscriptOriginFairCoinTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : ManuscriptOriginConfiguration n) :
    Measure (ManuscriptOriginConfiguration n) :=
  (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun coins =>
    manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute intensity
      basePending (c, coins)

theorem measurable_manuscriptOriginFairCoinTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat) :
    Measurable (manuscriptOriginFairCoinTapeLaw hn P b eta threshold
      hroute intensity basePending) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let coinLaw := fairCoinStreamLaw.prod fairCoinStreamLaw
  letI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    infer_instance
  have hbind := measurable_parametric_probability_bind
    (fun _ : ManuscriptOriginConfiguration n => coinLaw)
    measurable_const (fun _ => inferInstance)
    (manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
      intensity basePending)
    (measurable_manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending)
  exact hbind

theorem manuscriptOriginCoinPairTapeLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (z : ManuscriptGhostCoinInput'' n) :
    IsProbabilityMeasure (manuscriptOriginCoinPairTapeLaw hn P b eta
      threshold hroute intensity basePending z) := by
  exact z.1.tapeAdvanceLaw_isProbabilityMeasure hn P b eta threshold
    hroute intensity basePending z.2.1 z.2.2

theorem manuscriptOriginFairCoinTapeLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : ManuscriptOriginConfiguration n) :
    IsProbabilityMeasure (manuscriptOriginFairCoinTapeLaw hn P b eta
      threshold hroute intensity basePending c) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let coinLaw := fairCoinStreamLaw.prod fairCoinStreamLaw
  letI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    infer_instance
  unfold manuscriptOriginFairCoinTapeLaw
  exact isProbabilityMeasure_bind
    ((measurable_manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (measurable_const.prodMk measurable_id)).aemeasurable
    (Filter.Eventually.of_forall (fun coins =>
      manuscriptOriginCoinPairTapeLaw_isProbabilityMeasure hn P b eta
        threshold hroute intensity basePending (c, coins)))

noncomputable def manuscriptOriginPoissonCoinTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    Measure (ManuscriptOriginConfiguration n) :=
  (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
    manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
      intensity basePending c

theorem measurable_manuscriptOriginPoissonCoinTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    Measurable (manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold
      hroute intensity) := by
  let countLaw := ProbabilityTheory.poissonMeasure intensity
  have hnext : Measurable (fun z : ManuscriptOriginConfiguration n × Nat =>
      manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        intensity z.2 z.1) := by
    apply measurable_from_prod_countable_left
    intro basePending
    exact measurable_manuscriptOriginFairCoinTapeLaw hn P b eta
      threshold hthreshold hroute intensity basePending
  have hbind := measurable_parametric_probability_bind
    (fun _ : ManuscriptOriginConfiguration n => countLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : ManuscriptOriginConfiguration n × Nat =>
      manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        intensity z.2 z.1) hnext
  exact hbind

theorem manuscriptOriginPoissonCoinTapeLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    IsProbabilityMeasure
      (manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold
        hroute intensity c) := by
  unfold manuscriptOriginPoissonCoinTapeLaw
  exact isProbabilityMeasure_bind
    (measurable_of_countable
      (fun count : Nat => manuscriptOriginFairCoinTapeLaw hn P b eta
        threshold hroute intensity count c)).aemeasurable
    (Filter.Eventually.of_forall (fun count =>
      manuscriptOriginFairCoinTapeLaw_isProbabilityMeasure hn P b eta
        threshold hthreshold hroute intensity count c))

noncomputable def manuscriptOriginPoissonCoinTapeKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    ProbabilityTheory.Kernel (ManuscriptOriginConfiguration n)
      (ManuscriptOriginConfiguration n) :=
  ⟨manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute intensity,
    measurable_manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity⟩

instance manuscriptOriginPoissonCoinTapeKernel_isMarkov
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    ProbabilityTheory.IsMarkovKernel
      (manuscriptOriginPoissonCoinTapeKernel hn P b eta threshold
        hthreshold hroute intensity) :=
  ⟨fun c => manuscriptOriginPoissonCoinTapeLaw_isProbabilityMeasure hn P b
    eta threshold hthreshold hroute intensity c⟩

end Kr25Ssmxt

import Kr25Ssmxt.Analysis.OriginAdvanceStateCoinPairMeasurable

/-! The ghost transition after independent fair coin arrays and point tape
are drawn, conditional on a fixed Poisson count and volume outcome. -/

namespace Kr25Ssmxt

open MeasureTheory

private abbrev GhostCoinInput'' (n : Nat) :=
  OriginConfiguration n ×
    ((Nat × Nat → Bool) × (Nat × Nat → Bool))

noncomputable def originCoinPairTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (z : GhostCoinInput'' n) :
    Measure (OriginConfiguration n) :=
  (Measure.infinitePi (fun _ : Nat =>
    normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)).map
    (fun tape => z.1.advance P intensity threshold basePending
      z.2.1 z.2.2 tape)

theorem measurable_originCoinPairTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat) :
    Measurable (originCoinPairTapeLaw hn P b eta threshold
      hroute intensity basePending) := by
  let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
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
  have hdirac : Measurable (fun z : GhostCoinInput'' n ×
      (Nat → LatticePoint n) =>
      Measure.dirac (z.1.1.advance P intensity threshold basePending
        z.1.2.1 z.1.2.2 z.2)) :=
    Measure.measurable_dirac.comp
      (OriginConfiguration.measurable_advance_coinPair
        P intensity threshold hthreshold basePending)
  have hbind := measurable_parametric_probability_bind
    (fun _ : GhostCoinInput'' n => tapeLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : GhostCoinInput'' n × (Nat → LatticePoint n) =>
      Measure.dirac (z.1.1.advance P intensity threshold basePending
        z.1.2.1 z.1.2.2 z.2)) hdirac
  convert hbind using 1
  funext z
  exact (Measure.bind_dirac_eq_map tapeLaw
    (z.1.measurable_advance_tape P intensity threshold basePending
      z.2.1 z.2.2)).symm

noncomputable def originFairCoinTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : OriginConfiguration n) :
    Measure (OriginConfiguration n) :=
  (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun coins =>
    originCoinPairTapeLaw hn P b eta threshold hroute intensity
      basePending (c, coins)

theorem measurable_originFairCoinTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat) :
    Measurable (originFairCoinTapeLaw hn P b eta threshold
      hroute intensity basePending) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let coinLaw := fairCoinStreamLaw.prod fairCoinStreamLaw
  letI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    infer_instance
  have hbind := measurable_parametric_probability_bind
    (fun _ : OriginConfiguration n => coinLaw)
    measurable_const (fun _ => inferInstance)
    (originCoinPairTapeLaw hn P b eta threshold hroute
      intensity basePending)
    (measurable_originCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending)
  exact hbind

theorem originCoinPairTapeLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (z : GhostCoinInput'' n) :
    IsProbabilityMeasure (originCoinPairTapeLaw hn P b eta
      threshold hroute intensity basePending z) := by
  exact z.1.tapeAdvanceLaw_isProbabilityMeasure hn P b eta threshold
    hroute intensity basePending z.2.1 z.2.2

theorem originFairCoinTapeLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : OriginConfiguration n) :
    IsProbabilityMeasure (originFairCoinTapeLaw hn P b eta
      threshold hroute intensity basePending c) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let coinLaw := fairCoinStreamLaw.prod fairCoinStreamLaw
  letI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    infer_instance
  unfold originFairCoinTapeLaw
  exact isProbabilityMeasure_bind
    ((measurable_originCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (measurable_const.prodMk measurable_id)).aemeasurable
    (Filter.Eventually.of_forall (fun coins =>
      originCoinPairTapeLaw_isProbabilityMeasure hn P b eta
        threshold hroute intensity basePending (c, coins)))

noncomputable def originPoissonCoinTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : OriginConfiguration n) :
    Measure (OriginConfiguration n) :=
  (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
    originFairCoinTapeLaw hn P b eta threshold hroute
      intensity basePending c

theorem measurable_originPoissonCoinTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    Measurable (originPoissonCoinTapeLaw hn P b eta threshold
      hroute intensity) := by
  let countLaw := ProbabilityTheory.poissonMeasure intensity
  have hnext : Measurable (fun z : OriginConfiguration n × Nat =>
      originFairCoinTapeLaw hn P b eta threshold hroute
        intensity z.2 z.1) := by
    apply measurable_from_prod_countable_left
    intro basePending
    exact measurable_originFairCoinTapeLaw hn P b eta
      threshold hthreshold hroute intensity basePending
  have hbind := measurable_parametric_probability_bind
    (fun _ : OriginConfiguration n => countLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : OriginConfiguration n × Nat =>
      originFairCoinTapeLaw hn P b eta threshold hroute
        intensity z.2 z.1) hnext
  exact hbind

theorem originPoissonCoinTapeLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : OriginConfiguration n) :
    IsProbabilityMeasure
      (originPoissonCoinTapeLaw hn P b eta threshold
        hroute intensity c) := by
  unfold originPoissonCoinTapeLaw
  exact isProbabilityMeasure_bind
    (measurable_of_countable
      (fun count : Nat => originFairCoinTapeLaw hn P b eta
        threshold hroute intensity count c)).aemeasurable
    (Filter.Eventually.of_forall (fun count =>
      originFairCoinTapeLaw_isProbabilityMeasure hn P b eta
        threshold hthreshold hroute intensity count c))

noncomputable def originPoissonCoinTapeKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    ProbabilityTheory.Kernel (OriginConfiguration n)
      (OriginConfiguration n) :=
  ⟨originPoissonCoinTapeLaw hn P b eta threshold hroute intensity,
    measurable_originPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity⟩

instance originPoissonCoinTapeKernel_isMarkov
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    ProbabilityTheory.IsMarkovKernel
      (originPoissonCoinTapeKernel hn P b eta threshold
        hthreshold hroute intensity) :=
  ⟨fun c => originPoissonCoinTapeLaw_isProbabilityMeasure hn P b
    eta threshold hthreshold hroute intensity c⟩

end Kr25Ssmxt

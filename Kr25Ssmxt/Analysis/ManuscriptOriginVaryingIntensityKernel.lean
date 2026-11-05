import Kr25Ssmxt.Analysis.ManuscriptOriginIntensityMeasurable

/-! Joint measurability of the randomized ghost transition when the CV18
volume outcome changes its Poisson intensity. -/

namespace Kr25Ssmxt

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginCoinPairTapeLaw_intensity
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (basePending : Nat) :
    Measurable (fun z : (ManuscriptOriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        z.1.2 basePending (z.1.1, z.2)) := by
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
  have hdirac : Measurable (fun z :
      ((ManuscriptOriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      Measure.dirac (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2)) :=
    Measure.measurable_dirac.comp
      (ManuscriptOriginConfiguration.measurable_advance_coinPair_intensity
        P threshold hthreshold basePending)
  have hbind := measurable_parametric_probability_bind
    (fun _ : (ManuscriptOriginConfiguration n × NNReal) ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) => tapeLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : ((ManuscriptOriginConfiguration n × NNReal) ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
      (Nat → LatticePoint n) =>
      Measure.dirac (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2)) hdirac
  convert hbind using 1
  funext z
  exact (Measure.bind_dirac_eq_map tapeLaw
    (z.1.1.measurable_advance_tape P z.1.2 threshold basePending
      z.2.1 z.2.2)).symm

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginFairCoinTapeLaw_intensity
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (basePending : Nat) :
    Measurable (fun z : ManuscriptOriginConfiguration n × NNReal =>
      manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        z.2 basePending z.1) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let coinLaw := fairCoinStreamLaw.prod fairCoinStreamLaw
  letI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    infer_instance
  have hbind := measurable_parametric_probability_bind
    (fun _ : ManuscriptOriginConfiguration n × NNReal => coinLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : (ManuscriptOriginConfiguration n × NNReal) ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        z.1.2 basePending (z.1.1, z.2))
    (measurable_manuscriptOriginCoinPairTapeLaw_intensity hn P b eta
      threshold hthreshold hroute basePending)
  exact hbind

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginPoissonCoinTapeLaw_intensity
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty) :
    Measurable (fun z : ManuscriptOriginConfiguration n × NNReal =>
      manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute
        z.2 z.1) := by
  have hnext : Measurable (fun z :
      (ManuscriptOriginConfiguration n × NNReal) × Nat =>
      manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        z.1.2 z.2 z.1.1) := by
    apply measurable_from_prod_countable_left
    intro basePending
    exact measurable_manuscriptOriginFairCoinTapeLaw_intensity
      hn P b eta threshold hthreshold hroute basePending
  have hbind := measurable_parametric_probability_bind
    (fun z : ManuscriptOriginConfiguration n × NNReal =>
      ProbabilityTheory.poissonMeasure z.2)
    (measurable_poissonMeasure.comp measurable_snd)
    (fun _ => inferInstance)
    (fun z : (ManuscriptOriginConfiguration n × NNReal) × Nat =>
      manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        z.1.2 z.2 z.1.1) hnext
  exact hbind

end Kr25Ssmxt

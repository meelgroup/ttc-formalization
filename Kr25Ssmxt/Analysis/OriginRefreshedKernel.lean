import Kr25Ssmxt.Analysis.OriginRandomCoinKernel

/-! A fully randomized one-component ghost kernel conditional on the CV18
volume outcome: refresh future source coins, then draw Poisson count, fair
thinning coins, and independent point tape. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def originRefreshedComponentLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : OriginConfiguration n) :
    Measure (OriginConfiguration n) :=
  c.refreshLaw.bind
    (originPoissonCoinTapeLaw hn P b eta threshold hroute intensity)

theorem measurable_originRefreshedComponentLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    Measurable (originRefreshedComponentLaw hn P b eta
      threshold hroute intensity) := by
  have hrefresh : Measurable (fun c : OriginConfiguration n =>
      c.refreshLaw) := measurable_originConfiguration_refreshLaw
  have hnext : Measurable (fun z : OriginConfiguration n ×
      OriginConfiguration n =>
      originPoissonCoinTapeLaw hn P b eta threshold hroute
        intensity z.2) :=
    (measurable_originPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity).comp measurable_snd
  exact measurable_parametric_probability_bind
    (fun c : OriginConfiguration n => c.refreshLaw)
    hrefresh (fun c => c.refreshLaw_isProbabilityMeasure)
    (fun z : OriginConfiguration n ×
      OriginConfiguration n =>
      originPoissonCoinTapeLaw hn P b eta threshold hroute
        intensity z.2) hnext

theorem originRefreshedComponentLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : OriginConfiguration n) :
    IsProbabilityMeasure
      (originRefreshedComponentLaw hn P b eta threshold
        hroute intensity c) := by
  letI : IsProbabilityMeasure c.refreshLaw :=
    c.refreshLaw_isProbabilityMeasure
  unfold originRefreshedComponentLaw
  exact isProbabilityMeasure_bind
    (measurable_originPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity).aemeasurable
    (Filter.Eventually.of_forall (fun refreshed =>
      originPoissonCoinTapeLaw_isProbabilityMeasure hn P b eta
        threshold hthreshold hroute intensity refreshed))

noncomputable def originRefreshedComponentKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    ProbabilityTheory.Kernel (OriginConfiguration n)
      (OriginConfiguration n) :=
  ⟨originRefreshedComponentLaw hn P b eta threshold hroute
      intensity,
    measurable_originRefreshedComponentLaw hn P b eta threshold
      hthreshold hroute intensity⟩

instance originRefreshedComponentKernel_isMarkov
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    ProbabilityTheory.IsMarkovKernel
      (originRefreshedComponentKernel hn P b eta threshold
        hthreshold hroute intensity) :=
  ⟨fun c => originRefreshedComponentLaw_isProbabilityMeasure
    hn P b eta threshold hthreshold hroute intensity c⟩

end Kr25Ssmxt

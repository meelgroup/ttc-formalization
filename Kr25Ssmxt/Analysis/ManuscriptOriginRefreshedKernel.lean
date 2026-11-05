import Kr25Ssmxt.Analysis.ManuscriptOriginRandomCoinKernel

/-! A fully randomized one-component ghost kernel conditional on the CV18
volume outcome: refresh future source coins, then draw Poisson count, fair
thinning coins, and independent point tape. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def manuscriptOriginRefreshedComponentLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    Measure (ManuscriptOriginConfiguration n) :=
  c.refreshLaw.bind
    (manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute intensity)

theorem measurable_manuscriptOriginRefreshedComponentLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    Measurable (manuscriptOriginRefreshedComponentLaw hn P b eta
      threshold hroute intensity) := by
  have hrefresh : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.refreshLaw) := measurable_manuscriptOriginConfiguration_refreshLaw
  have hnext : Measurable (fun z : ManuscriptOriginConfiguration n ×
      ManuscriptOriginConfiguration n =>
      manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute
        intensity z.2) :=
    (measurable_manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity).comp measurable_snd
  exact measurable_parametric_probability_bind
    (fun c : ManuscriptOriginConfiguration n => c.refreshLaw)
    hrefresh (fun c => c.refreshLaw_isProbabilityMeasure)
    (fun z : ManuscriptOriginConfiguration n ×
      ManuscriptOriginConfiguration n =>
      manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute
        intensity z.2) hnext

theorem manuscriptOriginRefreshedComponentLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    IsProbabilityMeasure
      (manuscriptOriginRefreshedComponentLaw hn P b eta threshold
        hroute intensity c) := by
  letI : IsProbabilityMeasure c.refreshLaw :=
    c.refreshLaw_isProbabilityMeasure
  unfold manuscriptOriginRefreshedComponentLaw
  exact isProbabilityMeasure_bind
    (measurable_manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity).aemeasurable
    (Filter.Eventually.of_forall (fun refreshed =>
      manuscriptOriginPoissonCoinTapeLaw_isProbabilityMeasure hn P b eta
        threshold hthreshold hroute intensity refreshed))

noncomputable def manuscriptOriginRefreshedComponentKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    ProbabilityTheory.Kernel (ManuscriptOriginConfiguration n)
      (ManuscriptOriginConfiguration n) :=
  ⟨manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
      intensity,
    measurable_manuscriptOriginRefreshedComponentLaw hn P b eta threshold
      hthreshold hroute intensity⟩

instance manuscriptOriginRefreshedComponentKernel_isMarkov
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) :
    ProbabilityTheory.IsMarkovKernel
      (manuscriptOriginRefreshedComponentKernel hn P b eta threshold
        hthreshold hroute intensity) :=
  ⟨fun c => manuscriptOriginRefreshedComponentLaw_isProbabilityMeasure
    hn P b eta threshold hthreshold hroute intensity c⟩

end Kr25Ssmxt

import ttc.Analysis.OriginVaryingIntensityKernel

/-! Lift the varying-intensity component law through an independent refresh
source, using the fixed source measure as the outer integral. -/

namespace ttc

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem measurable_originPoissonAfterRefresh_intensity
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty) :
    Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        (Nat × (Nat × Nat) → Bool) =>
      originPoissonCoinTapeLaw hn P b eta threshold hroute
        z.1.2 (z.1.1.refreshFuture z.2)) := by
  have hrefresh : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        (Nat × (Nat × Nat) → Bool) => z.1.1.refreshFuture z.2) :=
    OriginConfiguration.measurable_refreshFuture_joint.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hpair : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        (Nat × (Nat × Nat) → Bool) =>
      (z.1.1.refreshFuture z.2, z.1.2)) :=
    hrefresh.prodMk (measurable_snd.comp measurable_fst)
  have hcomp :=
    (measurable_originPoissonCoinTapeLaw_intensity hn P b eta
      threshold hthreshold hroute).comp hpair
  simpa only [Function.comp_def] using hcomp

set_option maxHeartbeats 1000000 in
theorem measurable_originRefreshedSourceFormula_intensity
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty) :
    Measurable (fun z : OriginConfiguration n × NNReal =>
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).bind fun source =>
          originPoissonCoinTapeLaw hn P b eta threshold
            hroute z.2 (z.1.refreshFuture source)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  have hprob : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  exact measurable_parametric_probability_bind
    (fun _ : OriginConfiguration n × NNReal => sourceLaw)
    measurable_const (fun _ => hprob)
    (fun z : (OriginConfiguration n × NNReal) ×
      (Nat × (Nat × Nat) → Bool) =>
      originPoissonCoinTapeLaw hn P b eta threshold hroute
        z.1.2 (z.1.1.refreshFuture z.2))
    (measurable_originPoissonAfterRefresh_intensity hn P b eta
      threshold hthreshold hroute)

set_option maxHeartbeats 1000000 in
theorem originRefreshedComponentLaw_eq_source
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : OriginConfiguration n) :
    originRefreshedComponentLaw hn P b eta threshold
      hroute intensity c =
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).bind fun source =>
        originPoissonCoinTapeLaw hn P b eta threshold
          hroute intensity (c.refreshFuture source) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  have hK := measurable_originPoissonCoinTapeLaw hn P b eta
    threshold hthreshold hroute intensity
  change (sourceLaw.map c.refreshFuture).bind
    (originPoissonCoinTapeLaw hn P b eta threshold hroute
      intensity) =
    sourceLaw.bind fun source =>
      originPoissonCoinTapeLaw hn P b eta threshold hroute
        intensity (c.refreshFuture source)
  exact bind_mapped_measure sourceLaw c.refreshFuture
    c.measurable_refreshFuture _ hK

set_option maxHeartbeats 1000000 in
theorem measurable_originRefreshedComponentLaw_intensity
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty) :
    Measurable (fun z : OriginConfiguration n × NNReal =>
      originRefreshedComponentLaw hn P b eta threshold
        hroute z.2 z.1) := by
  have heq : (fun z : OriginConfiguration n × NNReal =>
      originRefreshedComponentLaw hn P b eta threshold
        hroute z.2 z.1) =
      (fun z => (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).bind fun source =>
          originPoissonCoinTapeLaw hn P b eta threshold
            hroute z.2 (z.1.refreshFuture source)) := by
    funext z
    exact originRefreshedComponentLaw_eq_source hn P b eta
      threshold hthreshold hroute z.2 z.1
  rw [heq]
  exact measurable_originRefreshedSourceFormula_intensity
    hn P b eta threshold hthreshold hroute

end ttc

import Kr25Ssmxt.Analysis.OriginRefreshedCountKernel
import Kr25Ssmxt.Analysis.SourceRefreshIdempotent

/-! A refresh-stationary incoming ghost law evolves by the certified
fixed-level Poisson delete-and-add kernel. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

set_option maxHeartbeats 1000000 in
theorem origin_stationary_fixedLevel_step
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (μ : Measure (OriginConfiguration n))
    (hstationary :
      μ.bind (fun c : OriginConfiguration n => c.refreshLaw) = μ)
    (S : Finset (LatticePoint n))
    (hsupport : (normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0)
    (level : Nat) :
    (μ.bind (originRefreshedComponentLaw hn P b eta threshold
      hroute intensity)).map
        (fun next : OriginConfiguration n =>
          next.source.pointCounts level S) =
    (μ.map (fun c => c.source.pointCounts level S)).bind
      (fun old =>
        (Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
          (Real.toNNReal
            ((normalizedHitAndRunPointLaw hn P b eta hroute.1
              hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
                hroute.2.2.2.2).real {(x : LatticePoint n)} *
              ((unitInterval.toNNReal (survivalProbability level) *
                intensity : NNReal) : Real))))).map
          (fun incoming : S → Nat => fun x : S =>
            (if x.1.toPoint ∈ P.carrier then 0 else old x) +
              incoming x)) := by
  let counts : OriginConfiguration n → (S → Nat) :=
    fun c => c.source.pointCounts level S
  have hcounts : Measurable counts :=
    (measurable_originSourceState_pointCounts level S).comp
      measurable_originConfiguration_source
  let unrefreshed := originPoissonCoinTapeLaw hn P b eta
    threshold hroute intensity
  have hunrefreshed : Measurable unrefreshed :=
    measurable_originPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity
  have hrefresh : Measurable
      (fun c : OriginConfiguration n => c.refreshLaw) :=
    measurable_originConfiguration_refreshLaw
  let q : Measure (S → Nat) := Measure.pi
    (fun x : S => ProbabilityTheory.poissonMeasure
      (Real.toNNReal
        ((normalizedHitAndRunPointLaw hn P b eta hroute.1
          hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
            hroute.2.2.2.2).real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            intensity : NNReal) : Real))))
  let K : (S → Nat) → Measure (S → Nat) := fun old =>
    q.map (fun incoming : S → Nat => fun x : S =>
      (if x.1.toPoint ∈ P.carrier then 0 else old x) + incoming x)
  have hK : Measurable K := measurable_of_countable _
  have hstep : μ.bind
      (originRefreshedComponentLaw hn P b eta threshold
        hroute intensity) = μ.bind unrefreshed := by
    change μ.bind (fun c => c.refreshLaw.bind unrefreshed) =
      μ.bind unrefreshed
    rw [← Measure.bind_bind hrefresh.aemeasurable
      hunrefreshed.aemeasurable, hstationary]
  rw [hstep]
  rw [map_bind_measure μ unrefreshed counts
    hunrefreshed.aemeasurable hcounts]
  have heq : μ.bind (fun c => (unrefreshed c).map counts) =
      μ.bind (fun c => K (counts c)) := by
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro c
    exact originPoissonCoinTapeLaw_fixedLevel_sourceCounts
      hn P b eta threshold hthreshold hroute intensity c S hsupport level
  rw [heq]
  exact (bind_mapped_measure μ counts hcounts K hK).symm

end Kr25Ssmxt

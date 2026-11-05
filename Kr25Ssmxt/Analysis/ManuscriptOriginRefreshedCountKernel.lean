import Kr25Ssmxt.Analysis.ManuscriptOriginSourceCountKernel
import Kr25Ssmxt.Analysis.ManuscriptOriginRefreshedKernel
import Kr25Ssmxt.Analysis.ManuscriptFutureTagLaw

/-! One refreshed ghost component has the fixed-level delete-and-add
Poisson count kernel applied to its refreshed old source counts. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

set_option maxHeartbeats 1000000 in
theorem manuscriptOriginRefreshedComponentLaw_fixedLevel_sourceCounts
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n)
    (S : Finset (LatticePoint n))
    (hsupport : (normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0)
    (level : Nat) :
    (manuscriptOriginRefreshedComponentLaw hn P b eta threshold
      hroute intensity c).map
        (fun next : ManuscriptOriginConfiguration n =>
          next.source.pointCounts level S) =
    (c.refreshLaw.map (fun old => old.source.pointCounts level S)).bind
      (fun old =>
        (Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
          (Real.toNNReal
            ((normalizedHitAndRunPointLaw hn P b hroute.1 eta
              hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
                hroute.2.2.2.2).real {(x : LatticePoint n)} *
              ((unitInterval.toNNReal (survivalProbability level) *
                intensity : NNReal) : Real))))).map
          (fun incoming : S → Nat => fun x : S =>
            (if x.1.toPoint ∈ P.carrier then 0 else old x) +
              incoming x)) := by
  let oldCounts : ManuscriptOriginConfiguration n → (S → Nat) :=
    fun old => old.source.pointCounts level S
  have hold : Measurable oldCounts :=
    (measurable_manuscriptOriginSourceState_pointCounts level S).comp
      measurable_manuscriptOriginConfiguration_source
  let q : Measure (S → Nat) := Measure.pi
    (fun x : S => ProbabilityTheory.poissonMeasure
      (Real.toNNReal
        ((normalizedHitAndRunPointLaw hn P b hroute.1 eta
          hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
            hroute.2.2.2.2).real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            intensity : NNReal) : Real))))
  let K : (S → Nat) → Measure (S → Nat) := fun old =>
    q.map (fun incoming : S → Nat => fun x : S =>
      (if x.1.toPoint ∈ P.carrier then 0 else old x) + incoming x)
  have hK : Measurable K := measurable_of_countable _
  have hinner : Measurable (fun old : ManuscriptOriginConfiguration n =>
      manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute
        intensity old) :=
    measurable_manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity
  unfold manuscriptOriginRefreshedComponentLaw
  rw [map_bind_measure c.refreshLaw
    (manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute
      intensity) oldCounts hinner.aemeasurable hold]
  have heq : c.refreshLaw.bind
      (fun refreshed =>
        (manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold
          hroute intensity refreshed).map oldCounts) =
      c.refreshLaw.bind (fun refreshed => K (oldCounts refreshed)) := by
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro refreshed
    exact manuscriptOriginPoissonCoinTapeLaw_fixedLevel_sourceCounts
      hn P b eta threshold hthreshold hroute intensity refreshed
      S hsupport level
  rw [heq]
  exact (bind_mapped_measure c.refreshLaw oldCounts hold K hK).symm

/-- Refreshing the old ghost source does not alter a level already observed.
Thus the actual component transition has a Poisson delete-and-add kernel at
every level at or below the incoming configuration's current level. -/
theorem manuscriptOriginRefreshedComponentLaw_pastLevel_sourceCounts
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n)
    (S : Finset (LatticePoint n))
    (hsupport : (normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0)
    (level : Nat) (hle : level ≤ c.level) :
    (manuscriptOriginRefreshedComponentLaw hn P b eta threshold
      hroute intensity c).map
        (fun next : ManuscriptOriginConfiguration n =>
          next.source.pointCounts level S) =
    (Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
      (Real.toNNReal
        ((normalizedHitAndRunPointLaw hn P b hroute.1 eta
          hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
            hroute.2.2.2.2).real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            intensity : NNReal) : Real))))).map
      (fun incoming : S → Nat => fun x : S =>
        (if x.1.toPoint ∈ P.carrier then 0 else
          c.source.pointCounts level S x) + incoming x) := by
  rw [manuscriptOriginRefreshedComponentLaw_fixedLevel_sourceCounts
    hn P b eta threshold hthreshold hroute intensity c S hsupport level]
  rw [c.refreshLaw_map_past_pointCounts level hle S]
  have hK : Measurable (fun old : S → Nat =>
      (Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
        (Real.toNNReal
          ((normalizedHitAndRunPointLaw hn P b hroute.1 eta
            hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
              hroute.2.2.2.2).real {(x : LatticePoint n)} *
            ((unitInterval.toNNReal (survivalProbability level) *
              intensity : NNReal) : Real))))).map
        (fun incoming : S → Nat => fun x : S =>
          (if x.1.toPoint ∈ P.carrier then 0 else old x) +
            incoming x)) := measurable_of_countable _
  exact Measure.dirac_bind hK (c.source.pointCounts level S)

/-- At a future level, one actual refreshed component first thins the finite
old source-tag population by independent fair tails, then deletes overlap and
adds the independent Poisson point-count vector of the new component. -/
theorem manuscriptOriginRefreshedComponentLaw_futureLevel_sourceCounts
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n)
    (S : Finset (LatticePoint n))
    (hsupport : (normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0)
    (level : Nat) (hle : c.level ≤ level) :
    (manuscriptOriginRefreshedComponentLaw hn P b eta threshold
      hroute intensity c).map
        (fun next : ManuscriptOriginConfiguration n =>
          next.source.pointCounts level S) =
    ((Measure.pi (fun _ : c.source.valid =>
      ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability (level - c.level)))).map
          (manuscriptFutureTagPointCounts c S)).bind
      (fun old =>
        (Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
          (Real.toNNReal
            ((normalizedHitAndRunPointLaw hn P b hroute.1 eta
              hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
                hroute.2.2.2.2).real {(x : LatticePoint n)} *
              ((unitInterval.toNNReal (survivalProbability level) *
                intensity : NNReal) : Real))))).map
          (fun incoming : S → Nat => fun x : S =>
            (if x.1.toPoint ∈ P.carrier then 0 else old x) +
              incoming x)) := by
  rw [manuscriptOriginRefreshedComponentLaw_fixedLevel_sourceCounts
    hn P b eta threshold hthreshold hroute intensity c S hsupport level]
  rw [c.refreshLaw_future_pointCounts_bernoulli level hle S]

end Kr25Ssmxt

import Kr25Ssmxt.Analysis.ManuscriptAbsoluteComponentSource
import Kr25Ssmxt.Analysis.ManuscriptComponentPredrawTape

/-! An exact absolute-level pre-draw representation of one concrete
manuscript component, with its concrete sampling call still attached. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem communityManuscriptComponentGivenVolume_absolute_predraw
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (outcome : VolumeOutcome) (state : TTCState n)
    (level : Nat) (hrate : state.rate = 1 / (2 : NNReal) ^ level) :
    let intensity := manuscriptIntensity b n threshold outcome.2
    let deleted := state.removeComponent P
    communityManuscriptComponentGivenVolume hn prep P b eta delta threshold
      outcome state =
    ((poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        fairCoinStreamLaw.map fun activeCoins =>
          thinningResult
            (manuscriptRateThinningResult deleted intensity threshold activeCoins)
            (pendingAfter preCoins
              (level + manuscriptRateExit deleted intensity threshold)
              deleted.nextLabel basePending)
            threshold
            (shiftCoins (manuscriptRateExit deleted intensity threshold)
              activeCoins)).bind fun second =>
        ((communityManuscriptOracles hn prep).generateSamples P second.2
          b eta delta).map fun batch => second.1.addBatch batch.2 := by
  dsimp only
  let intensity := manuscriptIntensity b n threshold outcome.2
  let deleted := state.removeComponent P
  let K : TTCState n × Nat → Measure (TTCState n) := fun second =>
    ((communityManuscriptOracles hn prep).generateSamples P second.2
      b eta delta).map fun batch => second.1.addBatch batch.2
  have hK : Measurable K := by
    have hcost := community_manuscript_sample_append_kernel_measurable
      hn prep 1 P b eta delta
    have heq : K = fun second : TTCState n × Nat =>
        (costedBind
          ((communityManuscriptCostedOracles hn prep 1).generateSamplesWithCost
            P second.2 b eta delta)
          (fun batch => costedCharge
            (Measure.dirac (second.1.addBatch batch.2))
            (second.2 * TTCRuntime.appendCopyOperations))).map Prod.fst := by
      funext second
      exact (community_manuscript_sample_append_fst hn prep 1 P
        second.2 b eta delta second.1).symm
    rw [heq]
    exact (Measure.measurable_map _ measurable_fst).comp hcost
  let firstLaw := manuscriptRateThinUntil deleted intensity threshold
  let pendingLaw : TTCState n → Measure Nat :=
    fun first => poissonMeasure (intensity * first.rate)
  let secondLaw : TTCState n → Measure (TTCState n × Nat) :=
    fun first => (pendingLaw first).bind fun pending =>
      thinUntil first pending threshold
  have hrateDeleted : deleted.rate = 1 / (2 : NNReal) ^ level := hrate
  have hstateRate : Measurable (fun first : TTCState n => first.rate) :=
    measurable_fst.comp
      (comap_measurable
        (fun first : TTCState n =>
          (first.rate, first.samples, first.nextLabel)))
  have hpending : Measurable pendingLaw :=
    measurable_poissonMeasure.comp (measurable_const.mul hstateRate)
  have hsecond : Measurable secondLaw :=
    measurable_parametric_probability_bind pendingLaw hpending
      (fun _ => inferInstance)
      (fun pair : TTCState n × Nat => thinUntil pair.1 pair.2 threshold)
      (thinUntil_kernel_measurable threshold)
  unfold communityManuscriptComponentGivenVolume
  change firstLaw.bind (fun first =>
    (pendingLaw first).bind fun pending =>
      (thinUntil first pending threshold).bind K) = _
  have hinner (first : TTCState n) :
      (pendingLaw first).bind (fun pending =>
        (thinUntil first pending threshold).bind K) =
      (secondLaw first).bind K := by
    exact (Measure.bind_bind
      (Measurable.of_discrete :
        Measurable (fun pending : Nat => thinUntil first pending threshold)).aemeasurable
      hK.aemeasurable).symm
  simp_rw [hinner]
  rw [← Measure.bind_bind hsecond.aemeasurable hK.aemeasurable]
  rw [manuscript_poisson_twoLoops_absolute_predraw deleted intensity
    threshold level hrateDeleted]

end Kr25Ssmxt

import ttc.Analysis.AbsoluteComponentSource
import ttc.Analysis.ComponentPredrawTape

/-! An exact absolute-level pre-draw representation of one concrete
paper component, with its concrete sampling call still attached. -/

namespace ttc

open MeasureTheory ProbabilityTheory

theorem communityComponentGivenVolume_absolute_predraw
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (outcome : VolumeOutcome) (state : TTCState n)
    (level : Nat) (hrate : state.p = 1 / (2 : NNReal) ^ level) :
    let intensity := ttcReference.t b n threshold outcome.2
    let deleted := state.removeComponent P
    communityComponentGivenVolume hn prep P b eta delta threshold
      outcome state =
    ((poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        fairCoinStreamLaw.map fun activeCoins =>
          ttcPseudocode.secondLoopResult
            (ttcReference.firstLoopResult deleted intensity threshold activeCoins)
            (pendingAfter preCoins
              (level + ttcReference.firstLoopExit deleted intensity threshold)
              deleted.nextLabel basePending)
            threshold
            (shiftCoins (ttcReference.firstLoopExit deleted intensity threshold)
              activeCoins)).bind fun second =>
        ((ttcSubroutines hn prep).GenerateSamples P second.2
          b eta).map fun batch => second.1.addBatch batch := by
  dsimp only
  let intensity := ttcReference.t b n threshold outcome.2
  let deleted := state.removeComponent P
  let K : TTCState n × Nat → Measure (TTCState n) := fun second =>
    ((ttcSubroutines hn prep).GenerateSamples P second.2
      b eta).map fun batch => second.1.addBatch batch
  have hK : Measurable K := by
    have hcost := community_sample_append_kernel_measurable
      hn prep 1 P b eta delta
    have heq : K = fun second : TTCState n × Nat =>
        (costedBind
          ((ttcCostedSubroutines hn prep 1).generateSamplesWithCost
            P second.2 b eta)
          (fun batch => costedCharge
            (Measure.dirac (second.1.addBatch batch))
            (second.2 * TTCRuntime.appendCopyOperations))).map Prod.fst := by
      funext second
      exact (community_sample_append_fst hn prep 1 P
        second.2 b eta delta second.1).symm
    rw [heq]
    exact (Measure.measurable_map _ measurable_fst).comp hcost
  let firstLaw := ttcReference.firstLoop deleted intensity threshold
  let pendingLaw : TTCState n → Measure Nat :=
    fun first => poissonMeasure (intensity * first.p)
  let secondLaw : TTCState n → Measure (TTCState n × Nat) :=
    fun first => (pendingLaw first).bind fun pending =>
      ttcPseudocode.secondLoop first pending threshold
  have hrateDeleted : deleted.p = 1 / (2 : NNReal) ^ level := hrate
  have hstateRate : Measurable (fun first : TTCState n => first.p) :=
    measurable_fst.comp
      (comap_measurable
        (fun first : TTCState n =>
          (first.p, first.X, first.nextLabel)))
  have hpending : Measurable pendingLaw :=
    measurable_poissonMeasure.comp (measurable_const.mul hstateRate)
  have hsecond : Measurable secondLaw :=
    measurable_parametric_probability_bind pendingLaw hpending
      (fun _ => inferInstance)
      (fun pair : TTCState n × Nat => ttcPseudocode.secondLoop pair.1 pair.2 threshold)
      (thinUntil_kernel_measurable threshold)
  unfold communityComponentGivenVolume
  change firstLaw.bind (fun first =>
    (pendingLaw first).bind fun pending =>
      (ttcPseudocode.secondLoop first pending threshold).bind K) = _
  have hinner (first : TTCState n) :
      (pendingLaw first).bind (fun pending =>
        (ttcPseudocode.secondLoop first pending threshold).bind K) =
      (secondLaw first).bind K := by
    exact (Measure.bind_bind
      (Measurable.of_discrete :
        Measurable (fun pending : Nat => ttcPseudocode.secondLoop first pending threshold)).aemeasurable
      hK.aemeasurable).symm
  simp_rw [hinner]
  rw [← Measure.bind_bind hsecond.aemeasurable hK.aemeasurable]
  rw [poisson_twoLoops_absolute_predraw deleted intensity
    threshold level hrateDeleted]

end ttc

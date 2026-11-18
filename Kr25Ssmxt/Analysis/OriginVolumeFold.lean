import Kr25Ssmxt.Analysis.OriginVolumeKernel
import Kr25Ssmxt.Analysis.GivenVolumeFold

/-! Iterate the refreshed ghost component kernel through a certified finite
list and recover the executable paper state law. -/

namespace Kr25Ssmxt

open MeasureTheory

structure OriginCertifiedComponent
    (n k : Nat) (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta : Real) where
  polytope : PolytopeData n
  route : samplerRadiusRequirement polytope eta ≤ decimalScale b * polytope.inradius ∧
    0 < eta ∧ eta ≤ 1 ∧
    (codedLatticePoints polytope b).Finite ∧
    (codedLatticePoints polytope b).Nonempty
  volumeProbability : IsProbabilityMeasure
    ((ttcSubroutines hn prep).ComputeVolume polytope eta delta)

noncomputable def communityOriginComponentsLaw
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) :
    List (OriginCertifiedComponent n k hn prep b eta delta) →
      OriginConfiguration n →
        Measure (OriginConfiguration n)
  | [], c => Measure.dirac c
  | d :: rest, c =>
      (communityOriginComponentLaw hn prep d.polytope b
        eta delta threshold d.route c).bind
        (communityOriginComponentsLaw hn prep b eta delta
          threshold rest)

theorem measurable_communityOriginComponentsLaw
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List
      (OriginCertifiedComponent n k hn prep b eta delta)) :
    Measurable (communityOriginComponentsLaw hn prep b eta
      delta threshold components) := by
  induction components with
  | nil => exact Measure.measurable_dirac
  | cons d rest ih =>
      have hstep : Measurable (communityOriginComponentLaw
          hn prep d.polytope b eta delta threshold d.route) := by
        exact measurable_originComponentVolumeLaw hn d.polytope
          b eta threshold hthreshold d.route
          ((ttcSubroutines hn prep).ComputeVolume d.polytope
            eta delta) d.volumeProbability
      exact (Measure.measurable_bind' ih).comp hstep

theorem communityOriginComponentsLaw_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List
      (OriginCertifiedComponent n k hn prep b eta delta))
    (c : OriginConfiguration n) :
    IsProbabilityMeasure
      (communityOriginComponentsLaw hn prep b eta delta
        threshold components c) := by
  induction components generalizing c with
  | nil =>
      change IsProbabilityMeasure (Measure.dirac c)
      infer_instance
  | cons d rest ih =>
      letI : IsProbabilityMeasure
          (communityOriginComponentLaw hn prep d.polytope b
            eta delta threshold d.route c) :=
        originComponentVolumeLaw_isProbabilityMeasure hn
          d.polytope b eta threshold hthreshold d.route
          ((ttcSubroutines hn prep).ComputeVolume d.polytope
            eta delta) d.volumeProbability c
      change IsProbabilityMeasure
        ((communityOriginComponentLaw hn prep d.polytope b
          eta delta threshold d.route c).bind
          (communityOriginComponentsLaw hn prep b eta delta
            threshold rest))
      exact isProbabilityMeasure_bind
        (measurable_communityOriginComponentsLaw hn prep b eta
          delta threshold hthreshold rest).aemeasurable
        (Filter.Eventually.of_forall ih)

set_option maxHeartbeats 1000000 in
theorem communityOriginComponentsLaw_map_state
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List
      (OriginCertifiedComponent n k hn prep b eta delta))
    (c : OriginConfiguration n) :
    (communityOriginComponentsLaw hn prep b eta delta
      threshold components c).map
        (fun next : OriginConfiguration n => next.state) =
    ttcReference.loop (ttcSubroutines hn prep)
      b eta delta threshold (components.map (fun d => d.polytope))
      c.state := by
  induction components generalizing c with
  | nil =>
      change (Measure.dirac c).map
        (fun next : OriginConfiguration n => next.state) =
        Measure.dirac c.state
      exact Measure.map_dirac'
        measurable_originConfiguration_state c
  | cons d rest ih =>
      let step := communityOriginComponentLaw hn prep d.polytope
        b eta delta threshold d.route c
      let tail := communityOriginComponentsLaw hn prep b eta
        delta threshold rest
      let programTail := ttcReference.loop
        (ttcSubroutines hn prep) b eta delta threshold
        (rest.map (fun d => d.polytope))
      have htail : Measurable tail :=
        measurable_communityOriginComponentsLaw hn prep b eta
          delta threshold hthreshold rest
      have hvolRest : ∀ P ∈ rest.map (fun d => d.polytope),
          IsProbabilityMeasure
            ((ttcSubroutines hn prep).ComputeVolume P eta
              delta) := by
        intro P hP
        obtain ⟨d', _, rfl⟩ := List.mem_map.mp hP
        exact d'.volumeProbability
      have hprogram : Measurable programTail :=
        measurable_communityProcessComponents hn prep b eta
          delta threshold hthreshold (rest.map (fun d => d.polytope))
          hvolRest
      calc
        (communityOriginComponentsLaw hn prep b eta delta
            threshold (d :: rest) c).map
            (fun next : OriginConfiguration n => next.state) =
          (step.bind tail).map
            (fun next : OriginConfiguration n => next.state) := rfl
        _ = step.bind (fun next =>
            (tail next).map
              (fun c' : OriginConfiguration n => c'.state)) := by
          exact map_bind_measure step tail
            (fun c' : OriginConfiguration n => c'.state)
            htail.aemeasurable measurable_originConfiguration_state
        _ = step.bind (fun next => programTail next.state) := by
          apply Measure.bind_congr_right
          apply Filter.Eventually.of_forall
          intro next
          exact ih next
        _ = (step.map (fun next => next.state)).bind programTail := by
          exact (bind_mapped_measure step (fun next => next.state)
            measurable_originConfiguration_state programTail
            hprogram).symm
        _ = (ttcReference.step
            (ttcSubroutines hn prep) b eta delta threshold
            d.polytope c.state).bind programTail := by
          rw [communityOriginComponentLaw_map_state hn prep
            d.polytope b eta delta threshold hthreshold d.route c]
        _ = ttcReference.loop (ttcSubroutines hn prep)
            b eta delta threshold
            ((d :: rest).map (fun d => d.polytope)) c.state := rfl

end Kr25Ssmxt

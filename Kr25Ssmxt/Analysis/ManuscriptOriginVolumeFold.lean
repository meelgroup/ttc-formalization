import Kr25Ssmxt.Analysis.ManuscriptOriginVolumeKernel
import Kr25Ssmxt.Analysis.ManuscriptGivenVolumeFold

/-! Iterate the refreshed ghost component kernel through a certified finite
list and recover the executable manuscript state law. -/

namespace Kr25Ssmxt

open MeasureTheory

structure ManuscriptOriginCertifiedComponent
    (n k : Nat) (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta : Real) where
  polytope : PolytopeData n
  route : 1 ≤ decimalScale b * polytope.inradius ∧
    0 < eta ∧ eta ≤ 1 ∧
    (codedLatticePoints polytope b).Finite ∧
    (codedLatticePoints polytope b).Nonempty
  volumeProbability : IsProbabilityMeasure
    ((communityManuscriptOracles hn prep).computeVolume polytope eta delta)

noncomputable def communityManuscriptOriginComponentsLaw
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) :
    List (ManuscriptOriginCertifiedComponent n k hn prep b eta delta) →
      ManuscriptOriginConfiguration n →
        Measure (ManuscriptOriginConfiguration n)
  | [], c => Measure.dirac c
  | d :: rest, c =>
      (communityManuscriptOriginComponentLaw hn prep d.polytope b
        eta delta threshold d.route c).bind
        (communityManuscriptOriginComponentsLaw hn prep b eta delta
          threshold rest)

theorem measurable_communityManuscriptOriginComponentsLaw
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List
      (ManuscriptOriginCertifiedComponent n k hn prep b eta delta)) :
    Measurable (communityManuscriptOriginComponentsLaw hn prep b eta
      delta threshold components) := by
  induction components with
  | nil => exact Measure.measurable_dirac
  | cons d rest ih =>
      have hstep : Measurable (communityManuscriptOriginComponentLaw
          hn prep d.polytope b eta delta threshold d.route) := by
        exact measurable_manuscriptOriginComponentVolumeLaw hn d.polytope
          b eta threshold hthreshold d.route
          ((communityManuscriptOracles hn prep).computeVolume d.polytope
            eta delta) d.volumeProbability
      exact (Measure.measurable_bind' ih).comp hstep

theorem communityManuscriptOriginComponentsLaw_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List
      (ManuscriptOriginCertifiedComponent n k hn prep b eta delta))
    (c : ManuscriptOriginConfiguration n) :
    IsProbabilityMeasure
      (communityManuscriptOriginComponentsLaw hn prep b eta delta
        threshold components c) := by
  induction components generalizing c with
  | nil =>
      change IsProbabilityMeasure (Measure.dirac c)
      infer_instance
  | cons d rest ih =>
      letI : IsProbabilityMeasure
          (communityManuscriptOriginComponentLaw hn prep d.polytope b
            eta delta threshold d.route c) :=
        manuscriptOriginComponentVolumeLaw_isProbabilityMeasure hn
          d.polytope b eta threshold hthreshold d.route
          ((communityManuscriptOracles hn prep).computeVolume d.polytope
            eta delta) d.volumeProbability c
      change IsProbabilityMeasure
        ((communityManuscriptOriginComponentLaw hn prep d.polytope b
          eta delta threshold d.route c).bind
          (communityManuscriptOriginComponentsLaw hn prep b eta delta
            threshold rest))
      exact isProbabilityMeasure_bind
        (measurable_communityManuscriptOriginComponentsLaw hn prep b eta
          delta threshold hthreshold rest).aemeasurable
        (Filter.Eventually.of_forall ih)

set_option maxHeartbeats 1000000 in
theorem communityManuscriptOriginComponentsLaw_map_state
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List
      (ManuscriptOriginCertifiedComponent n k hn prep b eta delta))
    (c : ManuscriptOriginConfiguration n) :
    (communityManuscriptOriginComponentsLaw hn prep b eta delta
      threshold components c).map
        (fun next : ManuscriptOriginConfiguration n => next.state) =
    manuscriptProcessComponents (communityManuscriptOracles hn prep)
      b eta delta threshold (components.map (fun d => d.polytope))
      c.state := by
  induction components generalizing c with
  | nil =>
      change (Measure.dirac c).map
        (fun next : ManuscriptOriginConfiguration n => next.state) =
        Measure.dirac c.state
      exact Measure.map_dirac'
        measurable_manuscriptOriginConfiguration_state c
  | cons d rest ih =>
      let step := communityManuscriptOriginComponentLaw hn prep d.polytope
        b eta delta threshold d.route c
      let tail := communityManuscriptOriginComponentsLaw hn prep b eta
        delta threshold rest
      let programTail := manuscriptProcessComponents
        (communityManuscriptOracles hn prep) b eta delta threshold
        (rest.map (fun d => d.polytope))
      have htail : Measurable tail :=
        measurable_communityManuscriptOriginComponentsLaw hn prep b eta
          delta threshold hthreshold rest
      have hvolRest : ∀ P ∈ rest.map (fun d => d.polytope),
          IsProbabilityMeasure
            ((communityManuscriptOracles hn prep).computeVolume P eta
              delta) := by
        intro P hP
        obtain ⟨d', _, rfl⟩ := List.mem_map.mp hP
        exact d'.volumeProbability
      have hprogram : Measurable programTail :=
        measurable_communityManuscriptProcessComponents hn prep b eta
          delta threshold hthreshold (rest.map (fun d => d.polytope))
          hvolRest
      calc
        (communityManuscriptOriginComponentsLaw hn prep b eta delta
            threshold (d :: rest) c).map
            (fun next : ManuscriptOriginConfiguration n => next.state) =
          (step.bind tail).map
            (fun next : ManuscriptOriginConfiguration n => next.state) := rfl
        _ = step.bind (fun next =>
            (tail next).map
              (fun c' : ManuscriptOriginConfiguration n => c'.state)) := by
          exact map_bind_measure step tail
            (fun c' : ManuscriptOriginConfiguration n => c'.state)
            htail.aemeasurable measurable_manuscriptOriginConfiguration_state
        _ = step.bind (fun next => programTail next.state) := by
          apply Measure.bind_congr_right
          apply Filter.Eventually.of_forall
          intro next
          exact ih next
        _ = (step.map (fun next => next.state)).bind programTail := by
          exact (bind_mapped_measure step (fun next => next.state)
            measurable_manuscriptOriginConfiguration_state programTail
            hprogram).symm
        _ = (manuscriptProcessComponent
            (communityManuscriptOracles hn prep) b eta delta threshold
            d.polytope c.state).bind programTail := by
          rw [communityManuscriptOriginComponentLaw_map_state hn prep
            d.polytope b eta delta threshold hthreshold d.route c]
        _ = manuscriptProcessComponents (communityManuscriptOracles hn prep)
            b eta delta threshold
            ((d :: rest).map (fun d => d.polytope)) c.state := rfl

end Kr25Ssmxt

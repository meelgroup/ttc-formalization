import ttc.Analysis.VolumeTrace
import ttc.Analysis.SampleAppendMarginal

/-! Retain one concrete CV18 result in the charged paper component
execution. Both projections recover the original laws exactly. -/

namespace ttc

open MeasureTheory

noncomputable def communityComponentVolumeTrace
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n) :
    Measure ((VolumeOutcome × Nat) × (TTCState n × Nat)) :=
  costedBindTrace
    ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
      P eta delta)
    (communityCostedComponentTail hn prep factor P b eta delta threshold state)

theorem communityComponentVolumeTrace_fst
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n) :
    (communityComponentVolumeTrace hn prep factor P b eta delta
      threshold state).map Prod.fst =
    (ttcCostedSubroutines hn prep factor).computeVolumeWithCost
      P eta delta := by
  unfold communityComponentVolumeTrace
  apply costedBindTrace_fst
  · exact community_component_tail_measurable hn prep factor P b
      eta delta threshold hthreshold state
  · intro outcome
    exact ⟨community_deletion_tail_mass_one hn prep factor P b
      eta delta threshold hthreshold state
      (ttcReference.t b n threshold outcome.2)⟩

theorem communityComponentVolumeTrace_snd
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n) :
    (communityComponentVolumeTrace hn prep factor P b eta delta
      threshold state).map Prod.snd =
    ttcReference.stepWithCost
      (ttcCostedSubroutines hn prep factor)
      b eta delta threshold P state := by
  unfold communityComponentVolumeTrace
  change (costedBindTrace
    ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
      P eta delta)
    (communityCostedComponentTail hn prep factor P b eta delta threshold state)).map
      Prod.snd = costedBind _ _
  apply costedBindTrace_snd
  · exact community_component_tail_measurable hn prep factor P b
      eta delta threshold hthreshold state
  · intro outcome
    exact ⟨community_deletion_tail_mass_one hn prep factor P b
      eta delta threshold hthreshold state
      (ttcReference.t b n threshold outcome.2)⟩

/-- Forgetting the oracle's operation charge recovers the exact CV18
outcome law used by the uncharged paper program. -/
theorem communityComponentVolumeTrace_volumeOutcome
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n) :
    (communityComponentVolumeTrace hn prep factor P b eta delta
      threshold state).map (fun result => result.1.1) =
    (ttcSubroutines hn prep).ComputeVolume P eta delta := by
  have hfst := communityComponentVolumeTrace_fst hn prep factor P
    b eta delta threshold hthreshold state
  have hvolume := communityCosted_volume_fst hn prep factor
    P eta delta
  calc
    (communityComponentVolumeTrace hn prep factor P b eta delta
        threshold state).map (fun result => result.1.1) =
      ((communityComponentVolumeTrace hn prep factor P b eta delta
        threshold state).map Prod.fst).map Prod.fst := by
          rw [Measure.map_map measurable_fst measurable_fst]
          rfl
    _ = _ := by rw [hfst]; exact hvolume

set_option maxHeartbeats 1200000 in
/-- The instrumented component is a measurable kernel in its incoming TTC
state. This allows volume traces to be folded over the component list. -/
theorem communityComponentVolumeTrace_measurable
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (hvolume : IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta)) :
    Measurable (communityComponentVolumeTrace hn prep factor P b
      eta delta threshold) := by
  let first := (ttcCostedSubroutines hn prep factor).computeVolumeWithCost
    P eta delta
  let tail : TTCState n × (VolumeOutcome × Nat) →
      Measure (TTCState n × Nat) := fun z =>
    communityCostedComponentTail hn prep factor P b eta delta threshold
      z.1 z.2.1
  have htail : Measurable tail := by
    have hbase := community_component_tail_joint_measurable
      hn prep factor P b eta delta threshold hthreshold
    have hpair : Measurable (fun z : TTCState n × (VolumeOutcome × Nat) =>
        (z.1, z.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    change Measurable
      ((fun z : TTCState n × VolumeOutcome =>
        communityCostedComponentTail hn prep factor P b eta delta threshold
          z.1 z.2) ∘
        (fun z : TTCState n × (VolumeOutcome × Nat) => (z.1, z.2.1)))
    exact hbase.comp hpair
  have htailProb (z : TTCState n × (VolumeOutcome × Nat)) :
      IsProbabilityMeasure (tail z) := by
    exact ⟨community_deletion_tail_mass_one hn prep factor P b
      eta delta threshold hthreshold z.1
      (ttcReference.t b n threshold z.2.1.2)⟩
  let out : (TTCState n × (VolumeOutcome × Nat)) ×
      (TTCState n × Nat) →
      (VolumeOutcome × Nat) × (TTCState n × Nat) :=
    fun z => (z.1.2, (z.2.1, z.1.2.2 + z.2.2))
  have hout : Measurable out := by fun_prop
  let K : TTCState n × (VolumeOutcome × Nat) →
      Measure ((VolumeOutcome × Nat) × (TTCState n × Nat)) :=
    fun z => (tail z).map fun continuation => out (z, continuation)
  have hK : Measurable K :=
    measurable_parametric_probability_map tail htail htailProb out hout
  letI : IsProbabilityMeasure first := hvolume
  have hmeas := measurable_fixed_sfinite_bind first K hK
  have heq : communityComponentVolumeTrace hn prep factor P b eta
      delta threshold = fun state : TTCState n =>
        first.bind fun result => K (state, result) := by
    funext state
    unfold communityComponentVolumeTrace costedBindTrace
      volumeTracedContinuation
    congr 1
    funext result
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [heq]
  exact hmeas

theorem communityComponentVolumeTrace_isProbabilityMeasure
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n)
    (hvolume : IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta)) :
    IsProbabilityMeasure
      (communityComponentVolumeTrace hn prep factor P b eta delta
        threshold state) := by
  letI : IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta) := hvolume
  unfold communityComponentVolumeTrace
  apply costedBindTrace_isProbabilityMeasure
  · exact community_component_tail_measurable hn prep factor P b
      eta delta threshold hthreshold state
  · intro outcome
    exact ⟨community_deletion_tail_mass_one hn prep factor P b
      eta delta threshold hthreshold state
      (ttcReference.t b n threshold outcome.2)⟩

end ttc

import Kr25Ssmxt.Analysis.MeasurableFirstExitRoundJoint
import Kr25Ssmxt.Analysis.MeasurableThinningResult

/-!
# Joint measurability of TTC thinning

The thinning result must be measurable jointly in its state, pending count, and
coin stream, rather than only for fixed state and count.
-/

namespace Kr25Ssmxt

/--
For a fixed threshold, `ttcPseudocode.secondLoopResult` is jointly measurable in all runtime
inputs and the coin stream.

INTERNAL: joint transition measurability needed to parameterize `ttcPseudocode.secondLoop`.
-/
lemma measurable_thinningResult_joint {n : Nat} (threshold : Real) :
    Measurable (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
      ttcPseudocode.secondLoopResult z.1.1 z.1.2 threshold z.2) := by
  classical
  let exitRound := fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
    ttcPseudocode.secondLoopExitRound z.1.1 z.1.2 threshold z.2
  have hexitRound : Measurable exitRound :=
    measurable_firstExitRound_joint threshold
  have hstateIn : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hstateCoords : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
        (z.1.1.p, z.1.1.X, z.1.1.nextLabel)) :=
    (comap_measurable _).comp hstateIn
  have hrateIn : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.1.p) :=
    measurable_fst.comp hstateCoords
  have hsamplesIn : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.1.X) :=
    (measurable_fst.comp measurable_snd).comp hstateCoords
  have hnextLabel : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.1.nextLabel) :=
    (measurable_snd.comp measurable_snd).comp hstateCoords
  have hpendingIn : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hcoins : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.2) :=
    measurable_snd
  have hcoinsRound : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
        (z.2, exitRound z)) :=
    hcoins.prodMk hexitRound
  have hsurvivesJoint (label : Nat) :
      Measurable (fun p : (Nat × Nat → Bool) × Nat =>
        survives p.1 p.2 label) := by
    apply measurable_from_prod_countable_left
    intro rounds
    apply measurable_to_prop
    have hevent :
        (fun coins : Nat × Nat → Bool => survives coins rounds label) ⁻¹' {True} =
          {coins : Nat × Nat → Bool | survives coins rounds label} := by
      ext coins
      simp
    rw [hevent]
    exact measurableSet_survives rounds label
  have hsamples : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
        samplesAfter z.2 (exitRound z) z.1.1.X) := by
    rw [measurable_finset_iff]
    intro copy
    have hmem : Measurable
        (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
          copy ∈ z.1.1.X) :=
      (measurable_finset_mem copy).comp hsamplesIn
    have hsurvives : Measurable
        (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
          survives z.2 (exitRound z) copy.1) :=
      (hsurvivesJoint copy.1).comp hcoinsRound
    simpa only [samplesAfter, Finset.mem_filter] using hmem.and hsurvives
  have hpendingJoint : Measurable
      (fun p : (Nat × Nat → Bool) × (Nat × Nat × Nat) =>
        pendingAfter p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    apply measurable_from_prod_countable_left
    intro q
    simpa [pendingAfter] using
      (measurable_survivorCount (Finset.range q.2.2)
        (fun i => q.2.1 + i) q.1)
  have hpending : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
        pendingAfter z.2 (exitRound z) z.1.1.nextLabel z.1.2) :=
    hpendingJoint.comp
      (hcoins.prodMk (hexitRound.prodMk (hnextLabel.prodMk hpendingIn)))
  have hrateJoint : Measurable (fun p : NNReal × Nat =>
      p.1 / (2 : NNReal) ^ p.2) := by
    apply measurable_from_prod_countable_left
    intro rounds
    exact measurable_id.div_const ((2 : NNReal) ^ rounds)
  have hrate : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
        z.1.1.p / (2 : NNReal) ^ exitRound z) :=
    hrateJoint.comp (hrateIn.prodMk hexitRound)
  have hstate : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
        { p := z.1.1.p / (2 : NNReal) ^ exitRound z
          X := samplesAfter z.2 (exitRound z) z.1.1.X
          nextLabel := z.1.1.nextLabel : TTCState n }) := by
    rw [measurable_comap_iff]
    exact hrate.prodMk (hsamples.prodMk hnextLabel)
  change Measurable
    (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
      ({ p := z.1.1.p / (2 : NNReal) ^ exitRound z
         X := samplesAfter z.2 (exitRound z) z.1.1.X
         nextLabel := z.1.1.nextLabel : TTCState n },
       pendingAfter z.2 (exitRound z) z.1.1.nextLabel z.1.2))
  exact hstate.prodMk hpending

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · reduced the joint result to `measurable_firstExitRound_joint`
* this round · reduced · strengthened fixed-section thinning measurability to the joint claim
-/

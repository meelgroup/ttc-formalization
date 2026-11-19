import ttc.Analysis.IIDIndexedSelection
import ttc.Analysis.SampleAppendMarginal
import ttc.Analysis.VolumeTrace

/-! The paper's second thinning loop and subsequent concrete sampler
can be driven by a common coin stream and an independent infinite IID point
tape, with the exact same output state law. -/

namespace ttc

open MeasureTheory

theorem community_adaptive_tape_append_law
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (pending : Nat) :
    let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    ((ttcPseudocode.secondLoop s pending threshold).bind fun thinned =>
      ((ttcSubroutines hn prep).GenerateSamples P thinned.2
        b eta).map fun batch => thinned.1.addBatch batch) =
    fairCoinStreamLaw.bind fun coins =>
      (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
        (ttcPseudocode.secondLoopResult s pending threshold coins).1.addBatch
          (fun (i : Fin (ttcPseudocode.secondLoopResult s pending threshold coins).2) =>
            tape (s.nextLabel +
              (pendingSurvivorIndices coins
                (ttcPseudocode.secondLoopExitRound s pending threshold coins)
                s.nextLabel pending).orderEmbOfFin
                (pendingSurvivorIndices_card coins
                  (ttcPseudocode.secondLoopExitRound s pending threshold coins)
                  s.nextLabel pending) i)) := by
  dsimp only
  let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  let K : TTCState n × Nat → Measure (TTCState n) := fun thinned =>
    ((ttcSubroutines hn prep).GenerateSamples P thinned.2
      b eta).map fun batch => thinned.1.addBatch batch
  have hK : Measurable K := by
    have hcost := community_sample_append_kernel_measurable
      hn prep 1 P b eta delta
    have heq : K = fun thinned : TTCState n × Nat =>
        (costedBind
          ((ttcCostedSubroutines hn prep 1).generateSamplesWithCost
            P thinned.2 b eta)
          (fun batch => costedCharge
            (Measure.dirac (thinned.1.addBatch batch))
            (thinned.2 * TTCRuntime.appendCopyOperations))).map Prod.fst := by
      funext thinned
      exact (community_sample_append_fst hn prep 1 P
        thinned.2 b eta delta thinned.1).symm
    rw [heq]
    exact (Measure.measurable_map _ measurable_fst).comp hcost
  change (ttcPseudocode.secondLoop s pending threshold).bind K = _
  rw [show ttcPseudocode.secondLoop s pending threshold =
    fairCoinStreamLaw.map (ttcPseudocode.secondLoopResult s pending threshold) from rfl]
  rw [bind_mapped_measure fairCoinStreamLaw
    (ttcPseudocode.secondLoopResult s pending threshold)
    (measurable_thinningResult s pending threshold) K hK]
  congr 1
  funext coins
  let thinned := ttcPseudocode.secondLoopResult s pending threshold coins
  have hbatch := community_adaptive_batch_from_iid_tape hn prep
    P b eta delta threshold hroute s pending coins
  let f : SampleBatch n thinned.2 → TTCState n :=
    fun batch => thinned.1.addBatch batch
  have hf : Measurable f := by
    exact measurable_addBatch.comp (measurable_const.prodMk measurable_id)
  have hselect : Measurable (fun tape : Nat → LatticePoint n =>
      (fun (i : Fin thinned.2) =>
        tape (s.nextLabel +
          (pendingSurvivorIndices coins
            (ttcPseudocode.secondLoopExitRound s pending threshold coins)
            s.nextLabel pending).orderEmbOfFin
            (pendingSurvivorIndices_card coins
              (ttcPseudocode.secondLoopExitRound s pending threshold coins)
              s.nextLabel pending) i))) := by
    exact Measurable.of_eval (fun i => measurable_pi_apply _)
  have hmap := congrArg (fun μ : Measure (SampleBatch n thinned.2) =>
    μ.map f) hbatch
  rw [Measure.map_map hf hselect] at hmap
  simpa only [K, thinned, f, Function.comp_def] using hmap.symm

end ttc

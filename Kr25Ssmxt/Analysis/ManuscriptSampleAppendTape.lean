import Kr25Ssmxt.Analysis.ManuscriptComponentAbsolutePredraw

/-! The concrete manuscript sampler appends an IID batch. A single infinite
point tape can supply that batch at the fresh contiguous copy labels. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_communityManuscript_sampleAppend_kernel
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta : Real) :
    Measurable (fun second : TTCState n × Nat =>
      ((ttcSubroutines hn prep).GenerateSamples P second.2
        b eta delta).map fun batch => second.1.addBatch batch.2) := by
  have hcost := community_manuscript_sample_append_kernel_measurable
    hn prep 1 P b eta delta
  have heq : (fun second : TTCState n × Nat =>
      ((ttcSubroutines hn prep).GenerateSamples P second.2
        b eta delta).map fun batch => second.1.addBatch batch.2) =
      (fun second =>
        (costedBind
          ((ttcCostedSubroutines hn prep 1).generateSamplesWithCost
            P second.2 b eta delta)
          (fun batch => costedCharge
            (Measure.dirac (second.1.addBatch batch.2))
            (second.2 * TTCRuntime.appendCopyOperations))).map Prod.fst) := by
    funext second
    exact (community_manuscript_sample_append_fst hn prep 1 P
      second.2 b eta delta second.1).symm
  rw [heq]
  exact (Measure.measurable_map _ measurable_fst).comp hcost

theorem communityManuscript_sampleAppend_from_iidTape
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (second : TTCState n × Nat) :
    let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    ((ttcSubroutines hn prep).GenerateSamples P second.2
      b eta delta).map (fun batch => second.1.addBatch batch.2) =
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape => second.1.addBatch
        (fun i : Fin second.2 => tape (second.1.nextLabel + i.val))) := by
  dsimp only
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  letI : IsProbabilityMeasure pointLaw :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  let tapeLaw := Measure.infinitePi (fun _ : Nat => pointLaw)
  let labels : Fin second.2 → Nat := fun i => second.1.nextLabel + i.val
  have hlabels : Function.Injective labels := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel hij)
  have hpoints := iid_tape_injective_selection pointLaw second.2 labels hlabels
  have hpointsMeas : Measurable
      (fun tape : Nat → LatticePoint n =>
        fun i : Fin second.2 => tape (labels i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (labels i))
  have hctor : Measurable
      (fun points : Fin second.2 → LatticePoint n =>
        (true, points)) := by fun_prop
  let select : (Nat → LatticePoint n) → SampleBatch n second.2 :=
    fun tape => (true, fun i => tape (labels i))
  have hselect : Measurable select :=
    measurable_const.prodMk
      (Measurable.of_eval (fun i => measurable_pi_apply (labels i)))
  have hsample : tapeLaw.map select =
      (ttcSubroutines hn prep).GenerateSamples P second.2
        b eta delta := by
    calc
      tapeLaw.map select =
        (tapeLaw.map (fun tape i => tape (labels i))).map
          (fun points => (true, points)) := by
            rw [Measure.map_map hctor hpointsMeas]
            rfl
      _ = iidSampleBatchLaw pointLaw := by rw [hpoints]; rfl
      _ = _ := (communityManuscript_generateSamples_eq_iid hn prep P
        second.2 b eta delta hroute).symm
  let f : SampleBatch n second.2 → TTCState n :=
    fun batch => second.1.addBatch batch.2
  have hf : Measurable f :=
    measurable_addBatch.comp (measurable_const.prodMk measurable_snd)
  calc
    ((ttcSubroutines hn prep).GenerateSamples P second.2
        b eta delta).map f =
      (tapeLaw.map select).map f := by rw [hsample]
    _ = tapeLaw.map (f ∘ select) := by
          rw [Measure.map_map hf hselect]
    _ = _ := rfl

/-- Conditional on any prior thinning history, the concrete IID batch can
be drawn from any injectively indexed locations of one independent point
tape. The labels may be the surviving original Poisson-copy labels. -/
theorem communityManuscript_sampleAppend_from_iidTape_at_labels
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (second : TTCState n × Nat)
    (labels : Fin second.2 → Nat) (hlabels : Function.Injective labels) :
    let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    ((ttcSubroutines hn prep).GenerateSamples P second.2
      b eta delta).map (fun batch => second.1.addBatch batch.2) =
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape => second.1.addBatch
        (fun i : Fin second.2 => tape (labels i))) := by
  dsimp only
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  letI : IsProbabilityMeasure pointLaw :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  let tapeLaw := Measure.infinitePi (fun _ : Nat => pointLaw)
  have hpoints := iid_tape_injective_selection pointLaw second.2 labels hlabels
  have hpointsMeas : Measurable
      (fun tape : Nat → LatticePoint n =>
        fun i : Fin second.2 => tape (labels i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (labels i))
  have hctor : Measurable
      (fun points : Fin second.2 → LatticePoint n =>
        (true, points)) := by fun_prop
  let select : (Nat → LatticePoint n) → SampleBatch n second.2 :=
    fun tape => (true, fun i => tape (labels i))
  have hselect : Measurable select :=
    measurable_const.prodMk hpointsMeas
  have hsample : tapeLaw.map select =
      (ttcSubroutines hn prep).GenerateSamples P second.2
        b eta delta := by
    calc
      tapeLaw.map select =
        (tapeLaw.map (fun tape i => tape (labels i))).map
          (fun points => (true, points)) := by
            rw [Measure.map_map hctor hpointsMeas]
            rfl
      _ = iidSampleBatchLaw pointLaw := by rw [hpoints]; rfl
      _ = _ := (communityManuscript_generateSamples_eq_iid hn prep P
        second.2 b eta delta hroute).symm
  let f : SampleBatch n second.2 → TTCState n :=
    fun batch => second.1.addBatch batch.2
  have hf : Measurable f :=
    measurable_addBatch.comp (measurable_const.prodMk measurable_snd)
  calc
    ((ttcSubroutines hn prep).GenerateSamples P second.2
        b eta delta).map f =
      (tapeLaw.map select).map f := by rw [hsample]
    _ = tapeLaw.map (f ∘ select) := by
          rw [Measure.map_map hf hselect]
    _ = _ := rfl

/-- A concrete manuscript component at a dyadic incoming rate has an exact
level-zero Poisson, absolute-thinning, and IID point-tape representation. -/
theorem communityManuscriptComponentGivenVolume_absolute_tape
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n)
    (level : Nat) (hrate : state.p = 1 / (2 : NNReal) ^ level) :
    let intensity := ttcPseudocode.t b n threshold outcome.2
    let deleted := state.removeComponent P
    let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    communityManuscriptComponentGivenVolume hn prep P b eta delta threshold
      outcome state =
    ((ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        fairCoinStreamLaw.map fun activeCoins =>
          ttcPseudocode.secondLoopResult
            (ttcPseudocode.firstLoopResult deleted intensity threshold activeCoins)
            (pendingAfter preCoins
              (level + ttcPseudocode.firstLoopExit deleted intensity threshold)
              deleted.nextLabel basePending)
            threshold
            (shiftCoins (ttcPseudocode.firstLoopExit deleted intensity threshold)
              activeCoins)).bind fun second =>
        (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
          second.1.addBatch
            (fun i : Fin second.2 => tape (second.1.nextLabel + i.val)) := by
  dsimp only
  rw [communityManuscriptComponentGivenVolume_absolute_predraw
    hn prep P b eta delta threshold outcome state level hrate]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro second
  exact communityManuscript_sampleAppend_from_iidTape
    hn prep P b eta delta hroute second

end Kr25Ssmxt

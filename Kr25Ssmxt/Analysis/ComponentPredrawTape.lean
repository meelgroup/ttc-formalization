import Kr25Ssmxt.Analysis.PoissonPreDraw

/-! For one concrete component with a fixed CV18 outcome, draw a Poisson
population at the incoming rate, thin it through the deterministic first
halving, and attach point marks from a separate IID tape. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

noncomputable def communityComponentGivenVolume
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (outcome : VolumeOutcome) (state : TTCState n) : Measure (TTCState n) :=
  let intensity := ttcReference.t b n threshold outcome.2
  let deleted := state.removeComponent P
  (ttcReference.firstLoop deleted intensity threshold).bind fun first =>
    (poissonMeasure (intensity * first.p)).bind fun pending =>
      (ttcPseudocode.secondLoop first pending threshold).bind fun second =>
        ((ttcSubroutines hn prep).GenerateSamples P second.2 b eta).map fun batch => second.1.addBatch batch

noncomputable def communityComponentPredrawTape
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n) : Measure (TTCState n) :=
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  let intensity := ttcReference.t b n threshold outcome.2
  let deleted := state.removeComponent P
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  (ttcReference.firstLoop deleted intensity threshold).bind fun first =>
    ((poissonMeasure ((intensity * first.p) * (2 : NNReal) ^ rounds)).bind fun basePending =>
      fairCoinStreamLaw.map fun preCoins =>
        pendingAfter preCoins rounds deleted.nextLabel basePending).bind fun pending =>
      fairCoinStreamLaw.bind fun secondCoins =>
        (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun pointTape =>
          (ttcPseudocode.secondLoopResult first pending threshold secondCoins).1.addBatch
            (fun (i : Fin (ttcPseudocode.secondLoopResult first pending threshold secondCoins).2) =>
              pointTape (first.nextLabel +
                (pendingSurvivorIndices secondCoins
                  (ttcPseudocode.secondLoopExitRound first pending threshold secondCoins)
                  first.nextLabel pending).orderEmbOfFin
                  (pendingSurvivorIndices_card secondCoins
                    (ttcPseudocode.secondLoopExitRound first pending threshold secondCoins)
                    first.nextLabel pending) i))

theorem rateThinUntil_predraw_mean
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) :
    ∀ᵐ first ∂ttcReference.firstLoop s intensity threshold,
      (intensity * first.p) *
        (2 : NNReal) ^ (ttcReference.firstLoopExit s intensity threshold) =
      intensity * s.p := by
  have hset : MeasurableSet {first : TTCState n |
      (intensity * first.p) *
        (2 : NNReal) ^ (ttcReference.firstLoopExit s intensity threshold) =
      intensity * s.p} := by
    have hrate : Measurable (fun first : TTCState n => first.p) :=
      measurable_fst.comp
        (comap_measurable
          (fun first : TTCState n =>
            (first.p, first.X, first.nextLabel)))
    change MeasurableSet
      ((fun first : TTCState n =>
        (intensity * first.p) *
          (2 : NNReal) ^ (ttcReference.firstLoopExit s intensity threshold)) ⁻¹'
        {intensity * s.p})
    exact (measurableSet_singleton (intensity * s.p)).preimage
      ((measurable_const.mul hrate).mul_const _)
  unfold ttcReference.firstLoop
  rw [ae_map_iff
    (measurable_rateThinningResult s intensity threshold).aemeasurable
    hset]
  apply Filter.Eventually.of_forall
  intro coins
  simp only [ttcReference.firstLoopResult]
  have hpow : (2 : NNReal) ^
      ttcReference.firstLoopExit s intensity threshold ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  simp [div_eq_mul_inv, mul_assoc]

theorem communityComponentPredrawTape_eq_givenVolume
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n) :
    communityComponentPredrawTape hn prep P b eta delta threshold
      hroute outcome state =
    communityComponentGivenVolume hn prep P b eta delta threshold
      outcome state := by
  unfold communityComponentPredrawTape
    communityComponentGivenVolume
  let intensity := ttcReference.t b n threshold outcome.2
  let deleted := state.removeComponent P
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro first
  dsimp only
  rw [poisson_predraw_at_fixed_rounds
    (intensity * first.p) (ttcReference.firstLoopExit deleted intensity threshold)
    deleted.nextLabel]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pending
  dsimp only
  exact (community_adaptive_tape_append_law hn prep P b eta delta
    threshold hroute first pending).symm

/-- The full uncharged concrete component, including its CV18 call, has the
pre-drawn Poisson and IID-tape representation. -/
theorem communityProcessComponent_eq_predrawTape
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (state : TTCState n) :
    ttcReference.step (ttcSubroutines hn prep) b eta
      delta threshold P state =
    ((ttcSubroutines hn prep).ComputeVolume P eta delta).bind
      fun outcome => communityComponentPredrawTape hn prep P b eta
        delta threshold hroute outcome state := by
  unfold ttcReference.step
  simp_rw [communityComponentPredrawTape_eq_givenVolume hn prep P b
    eta delta threshold hroute]
  rfl

end Kr25Ssmxt

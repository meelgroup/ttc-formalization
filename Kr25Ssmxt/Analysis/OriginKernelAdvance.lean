import Kr25Ssmxt.Analysis.StoppedPrefixSource
import Kr25Ssmxt.Analysis.OriginConfiguration

/-! The ghost transition and the executable source-labelled sampler kernel
use the same deterministic state update for every fixed random tape. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def communityOriginTapeResult
    {n : Nat} (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (pair : (Nat × Nat → Bool) ×
      (Nat × Fin (pendingAfter preCoins preRounds s.nextLabel basePending) →
        Bool))
    (tape : Nat → LatticePoint n) : TTCState n :=
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let rounds := ttcReference.firstLoopExit s intensity threshold
  let first := ttcReference.firstLoopResult s intensity threshold pair.1
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds pair.1) pair.2
  let activeRounds := firstExitRoundSplit first pending threshold
    (shiftCoins rounds pair.1)
    (pendingCoinExtension s.nextLabel pending pair.2)
  second.1.addBatch (fun i : Fin second.2 =>
    tape (twoStageSurvivorLabel preCoins preRounds s.nextLabel
      basePending pair.2 activeRounds i))

theorem measurable_communityOriginTapeResult
    {n : Nat} (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (pair : (Nat × Nat → Bool) ×
      (Nat × Fin (pendingAfter preCoins preRounds s.nextLabel basePending) →
        Bool)) :
    Measurable (communityOriginTapeResult s intensity threshold
      preCoins preRounds basePending pair) := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let rounds := ttcReference.firstLoopExit s intensity threshold
  let first := ttcReference.firstLoopResult s intensity threshold pair.1
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds pair.1) pair.2
  let activeRounds := firstExitRoundSplit first pending threshold
    (shiftCoins rounds pair.1)
    (pendingCoinExtension s.nextLabel pending pair.2)
  let label := twoStageSurvivorLabel preCoins preRounds s.nextLabel
    basePending pair.2 activeRounds
  have hpoints : Measurable
      (fun tape : Nat → LatticePoint n =>
        (fun i : Fin second.2 => tape (label i))) :=
    Measurable.of_eval (fun i => measurable_pi_apply (label i))
  exact measurable_addBatch.comp (measurable_const.prodMk hpoints)

theorem communityOriginTapeKernel_eq_tapeResult
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (intensity : NNReal)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (pair : (Nat × Nat → Bool) ×
      (Nat × Fin (pendingAfter preCoins preRounds s.nextLabel basePending) →
        Bool)) :
    communityOriginTapeKernel hn P b eta threshold hroute
      s intensity preCoins preRounds basePending pair =
    (Measure.infinitePi (fun _ : Nat =>
      normalizedHitAndRunPointLaw hn P b eta hroute.1
        hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)).map
      (communityOriginTapeResult s intensity threshold
        preCoins preRounds basePending pair) := rfl

theorem OriginConfiguration.advance_state_eq_tapeResult
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    let deleted := c.state.removeComponent P
    let preRounds := c.level + ttcReference.firstLoopExit deleted intensity threshold
    let fresh := originalSurvivorCoinRestriction preCoins preRounds
      deleted.nextLabel basePending future
    (c.advance P intensity threshold basePending preCoins future tape).state =
      communityOriginTapeResult deleted intensity threshold
        preCoins preRounds basePending
        (sourceOldCoins c.origin c.source.coins c.level, fresh)
        tape := rfl

/-- Conditional on the Poisson count and both coin arrays, forgetting the
ghost fields of `advance` gives exactly the source-labelled sampler kernel. -/
theorem OriginConfiguration.advance_state_tapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) (intensity : NNReal)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    let deleted := c.state.removeComponent P
    let preRounds := c.level + ttcReference.firstLoopExit deleted intensity threshold
    let fresh := originalSurvivorCoinRestriction preCoins preRounds
      deleted.nextLabel basePending future
    (Measure.infinitePi (fun _ : Nat =>
      normalizedHitAndRunPointLaw hn P b eta hroute.1
        hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)).map
      (fun tape =>
        (c.advance P intensity threshold basePending preCoins future tape).state) =
    communityOriginTapeKernel hn P b eta threshold hroute
      deleted intensity preCoins preRounds basePending
      (sourceOldCoins c.origin c.source.coins c.level, fresh) := by
  dsimp only
  rw [communityOriginTapeKernel_eq_tapeResult]
  congr 1

end Kr25Ssmxt

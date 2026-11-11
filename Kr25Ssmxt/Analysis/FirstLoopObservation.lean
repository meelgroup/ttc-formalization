import Kr25Ssmxt.Analysis.TwoStageSourceProduct

/-! The deterministic rate-thinning loop reads only its fixed-round old
source prefix. -/

namespace Kr25Ssmxt

theorem rateThinningResult_coinPrefix
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (coins : Nat × Nat → Bool) :
    ttcPseudocode.firstLoopResult s intensity threshold
      (coinPrefix (ttcPseudocode.firstLoopExit s intensity threshold) coins) =
    ttcPseudocode.firstLoopResult s intensity threshold coins := by
  dsimp only [ttcPseudocode.firstLoopResult]
  rw [samplesAfter_coinPrefix s
    (ttcPseudocode.firstLoopExit s intensity threshold)
    (ttcPseudocode.firstLoopExit s intensity threshold) (le_refl _) coins]

theorem rateThinningResult_eq_of_prefix_eq
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (coins coins' : Nat × Nat → Bool)
    (hprefix :
      coinPrefix (ttcPseudocode.firstLoopExit s intensity threshold) coins =
      coinPrefix (ttcPseudocode.firstLoopExit s intensity threshold) coins') :
    ttcPseudocode.firstLoopResult s intensity threshold coins =
      ttcPseudocode.firstLoopResult s intensity threshold coins' := by
  calc
    ttcPseudocode.firstLoopResult s intensity threshold coins =
      ttcPseudocode.firstLoopResult s intensity threshold
        (coinPrefix (ttcPseudocode.firstLoopExit s intensity threshold) coins) :=
          (rateThinningResult_coinPrefix s intensity threshold
            coins).symm
    _ = ttcPseudocode.firstLoopResult s intensity threshold
        (coinPrefix (ttcPseudocode.firstLoopExit s intensity threshold) coins') := by
          rw [hprefix]
    _ = ttcPseudocode.firstLoopResult s intensity threshold coins' :=
      rateThinningResult_coinPrefix s intensity threshold coins'

theorem oldRead_globalPrefix
    (origin : Nat → Nat × Nat) (rounds : Nat)
    (source : Nat × (Nat × Nat) → Bool) :
    coinPrefix rounds
      (fun pair : Nat × Nat => source
        ((origin pair.2).1, (pair.1, (origin pair.2).2))) =
    coinPrefix rounds
      (fun pair : Nat × Nat =>
        globalSourcePrefix rounds source
          ((origin pair.2).1, (pair.1, (origin pair.2).2))) := by
  funext pair
  by_cases hround : pair.1 < rounds <;>
    simp [coinPrefix, globalSourcePrefix, hround]

end Kr25Ssmxt

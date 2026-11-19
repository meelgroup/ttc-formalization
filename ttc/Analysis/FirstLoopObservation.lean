import ttc.Analysis.TwoStageSourceProduct

/-! The deterministic rate-thinning loop reads only its fixed-round old
source prefix. -/

namespace ttc

theorem rateThinningResult_coinPrefix
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (coins : Nat × Nat → Bool) :
    ttcReference.firstLoopResult s intensity threshold
      (coinPrefix (ttcReference.firstLoopExit s intensity threshold) coins) =
    ttcReference.firstLoopResult s intensity threshold coins := by
  dsimp only [ttcReference.firstLoopResult]
  rw [samplesAfter_coinPrefix s
    (ttcReference.firstLoopExit s intensity threshold)
    (ttcReference.firstLoopExit s intensity threshold) (le_refl _) coins]

theorem rateThinningResult_eq_of_prefix_eq
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (coins coins' : Nat × Nat → Bool)
    (hprefix :
      coinPrefix (ttcReference.firstLoopExit s intensity threshold) coins =
      coinPrefix (ttcReference.firstLoopExit s intensity threshold) coins') :
    ttcReference.firstLoopResult s intensity threshold coins =
      ttcReference.firstLoopResult s intensity threshold coins' := by
  calc
    ttcReference.firstLoopResult s intensity threshold coins =
      ttcReference.firstLoopResult s intensity threshold
        (coinPrefix (ttcReference.firstLoopExit s intensity threshold) coins) :=
          (rateThinningResult_coinPrefix s intensity threshold
            coins).symm
    _ = ttcReference.firstLoopResult s intensity threshold
        (coinPrefix (ttcReference.firstLoopExit s intensity threshold) coins') := by
          rw [hprefix]
    _ = ttcReference.firstLoopResult s intensity threshold coins' :=
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

end ttc

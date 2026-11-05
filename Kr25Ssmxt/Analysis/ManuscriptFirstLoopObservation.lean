import Kr25Ssmxt.Analysis.ManuscriptTwoStageSourceProduct

/-! The deterministic rate-thinning loop reads only its fixed-round old
source prefix. -/

namespace Kr25Ssmxt

theorem manuscriptRateThinningResult_coinPrefix
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (coins : Nat × Nat → Bool) :
    manuscriptRateThinningResult s intensity threshold
      (coinPrefix (manuscriptRateExit s intensity threshold) coins) =
    manuscriptRateThinningResult s intensity threshold coins := by
  dsimp only [manuscriptRateThinningResult]
  rw [samplesAfter_coinPrefix s
    (manuscriptRateExit s intensity threshold)
    (manuscriptRateExit s intensity threshold) (le_refl _) coins]

theorem manuscriptRateThinningResult_eq_of_prefix_eq
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (coins coins' : Nat × Nat → Bool)
    (hprefix :
      coinPrefix (manuscriptRateExit s intensity threshold) coins =
      coinPrefix (manuscriptRateExit s intensity threshold) coins') :
    manuscriptRateThinningResult s intensity threshold coins =
      manuscriptRateThinningResult s intensity threshold coins' := by
  calc
    manuscriptRateThinningResult s intensity threshold coins =
      manuscriptRateThinningResult s intensity threshold
        (coinPrefix (manuscriptRateExit s intensity threshold) coins) :=
          (manuscriptRateThinningResult_coinPrefix s intensity threshold
            coins).symm
    _ = manuscriptRateThinningResult s intensity threshold
        (coinPrefix (manuscriptRateExit s intensity threshold) coins') := by
          rw [hprefix]
    _ = manuscriptRateThinningResult s intensity threshold coins' :=
      manuscriptRateThinningResult_coinPrefix s intensity threshold coins'

theorem manuscriptOldRead_globalPrefix
    (origin : Nat → Nat × Nat) (rounds : Nat)
    (source : Nat × (Nat × Nat) → Bool) :
    coinPrefix rounds
      (fun pair : Nat × Nat => source
        ((origin pair.2).1, (pair.1, (origin pair.2).2))) =
    coinPrefix rounds
      (fun pair : Nat × Nat =>
        manuscriptGlobalSourcePrefix rounds source
          ((origin pair.2).1, (pair.1, (origin pair.2).2))) := by
  funext pair
  by_cases hround : pair.1 < rounds <;>
    simp [coinPrefix, manuscriptGlobalSourcePrefix, hround]

end Kr25Ssmxt

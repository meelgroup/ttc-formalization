import ttc.Analysis.ObservedRepresentativeExt
import ttc.Analysis.GlobalSourcePrefix

/-! The observed source prefix after appending a component is determined by
the old source prefix and the finite new-component coin prefix. -/

namespace ttc

theorem coinsAppend_observedPrefix_eq_of_prefix_eq
    (sources sources' : Nat → Nat × Nat → Bool)
    (component preRounds activeRounds : Nat)
    (preCoins future future' : Nat × Nat → Bool)
    (hold : originCoinPrefix (preRounds + activeRounds) sources =
      originCoinPrefix (preRounds + activeRounds) sources')
    (hnew : coinPrefix activeRounds future =
      coinPrefix activeRounds future') :
    originCoinPrefix (preRounds + activeRounds)
      (coinsAppend sources component preCoins future preRounds) =
    originCoinPrefix (preRounds + activeRounds)
      (coinsAppend sources' component preCoins future' preRounds) := by
  funext c pair
  by_cases hc : c = component
  · subst c
    by_cases hpre : pair.1 < preRounds
    · simp [originCoinPrefix, coinPrefix, coinsAppend,
        spliceCoins, hpre]
    · by_cases hlevel : pair.1 < preRounds + activeRounds
      · have hfuture : future (pair.1 - preRounds, pair.2) =
            future' (pair.1 - preRounds, pair.2) := by
          have hlt : pair.1 - preRounds < activeRounds := by omega
          have hpoint := congrFun hnew (pair.1 - preRounds, pair.2)
          simpa [coinPrefix, hlt] using hpoint
        simp [originCoinPrefix, coinPrefix, coinsAppend,
          spliceCoins, hpre, hlevel, hfuture]
      · simp [originCoinPrefix, coinPrefix, hlevel]
  · have hpoint := congrFun (congrFun hold c) pair
    simpa [originCoinPrefix, coinPrefix, coinsAppend,
      hc] using hpoint

theorem refreshedSourceCoins_observedPrefix_eq_of_futurePrefix
    (sources : Nat → Nat × Nat → Bool) (level extra : Nat)
    (future future' : Nat × (Nat × Nat) → Bool)
    (hfuture : globalSourcePrefix extra future =
      globalSourcePrefix extra future') :
    originCoinPrefix (level + extra)
      (refreshedSourceCoins sources level future) =
    originCoinPrefix (level + extra)
      (refreshedSourceCoins sources level future') := by
  funext component pair
  by_cases hbefore : pair.1 < level
  · have htotal : pair.1 < level + extra := by omega
    simp [originCoinPrefix, coinPrefix,
      refreshedSourceCoins, spliceCoins, hbefore, htotal]
  · by_cases htotal : pair.1 < level + extra
    · have hlt : pair.1 - level < extra := by omega
      have hpoint := congrFun hfuture
        (component, (pair.1 - level, pair.2))
      have hadd : pair.1 - level + level = pair.1 := by omega
      simpa [originCoinPrefix, coinPrefix,
        refreshedSourceCoins, spliceCoins,
        globalSourcePrefix, hbefore, htotal, hlt, hadd]
        using hpoint
    · simp [originCoinPrefix, coinPrefix, htotal]

end ttc

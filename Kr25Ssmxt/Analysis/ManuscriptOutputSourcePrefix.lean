import Kr25Ssmxt.Analysis.ManuscriptObservedRepresentativeExt
import Kr25Ssmxt.Analysis.ManuscriptGlobalSourcePrefix

/-! The observed source prefix after appending a component is determined by
the old source prefix and the finite new-component coin prefix. -/

namespace Kr25Ssmxt

theorem manuscriptCoinsAppend_observedPrefix_eq_of_prefix_eq
    (sources sources' : Nat → Nat × Nat → Bool)
    (component preRounds activeRounds : Nat)
    (preCoins future future' : Nat × Nat → Bool)
    (hold : manuscriptOriginCoinPrefix (preRounds + activeRounds) sources =
      manuscriptOriginCoinPrefix (preRounds + activeRounds) sources')
    (hnew : coinPrefix activeRounds future =
      coinPrefix activeRounds future') :
    manuscriptOriginCoinPrefix (preRounds + activeRounds)
      (manuscriptCoinsAppend sources component preCoins future preRounds) =
    manuscriptOriginCoinPrefix (preRounds + activeRounds)
      (manuscriptCoinsAppend sources' component preCoins future' preRounds) := by
  funext c pair
  by_cases hc : c = component
  · subst c
    by_cases hpre : pair.1 < preRounds
    · simp [manuscriptOriginCoinPrefix, coinPrefix, manuscriptCoinsAppend,
        spliceCoins, hpre]
    · by_cases hlevel : pair.1 < preRounds + activeRounds
      · have hfuture : future (pair.1 - preRounds, pair.2) =
            future' (pair.1 - preRounds, pair.2) := by
          have hlt : pair.1 - preRounds < activeRounds := by omega
          have hpoint := congrFun hnew (pair.1 - preRounds, pair.2)
          simpa [coinPrefix, hlt] using hpoint
        simp [manuscriptOriginCoinPrefix, coinPrefix, manuscriptCoinsAppend,
          spliceCoins, hpre, hlevel, hfuture]
      · simp [manuscriptOriginCoinPrefix, coinPrefix, hlevel]
  · have hpoint := congrFun (congrFun hold c) pair
    simpa [manuscriptOriginCoinPrefix, coinPrefix, manuscriptCoinsAppend,
      hc] using hpoint

theorem manuscriptRefreshedSourceCoins_observedPrefix_eq_of_futurePrefix
    (sources : Nat → Nat × Nat → Bool) (level extra : Nat)
    (future future' : Nat × (Nat × Nat) → Bool)
    (hfuture : manuscriptGlobalSourcePrefix extra future =
      manuscriptGlobalSourcePrefix extra future') :
    manuscriptOriginCoinPrefix (level + extra)
      (manuscriptRefreshedSourceCoins sources level future) =
    manuscriptOriginCoinPrefix (level + extra)
      (manuscriptRefreshedSourceCoins sources level future') := by
  funext component pair
  by_cases hbefore : pair.1 < level
  · have htotal : pair.1 < level + extra := by omega
    simp [manuscriptOriginCoinPrefix, coinPrefix,
      manuscriptRefreshedSourceCoins, spliceCoins, hbefore, htotal]
  · by_cases htotal : pair.1 < level + extra
    · have hlt : pair.1 - level < extra := by omega
      have hpoint := congrFun hfuture
        (component, (pair.1 - level, pair.2))
      have hadd : pair.1 - level + level = pair.1 := by omega
      simpa [manuscriptOriginCoinPrefix, coinPrefix,
        manuscriptRefreshedSourceCoins, spliceCoins,
        manuscriptGlobalSourcePrefix, hbefore, htotal, hlt, hadd]
        using hpoint
    · simp [manuscriptOriginCoinPrefix, coinPrefix, htotal]

end Kr25Ssmxt

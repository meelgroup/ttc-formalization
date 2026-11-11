import Kr25Ssmxt.Analysis.SourceRefresh

/-! Equality of the observable ghost configuration requires only the
source coins below its current dyadic level. -/

namespace Kr25Ssmxt

theorem OriginConfiguration.observedRepresentative_eq_of_data
    {n : Nat} (a b : OriginConfiguration n)
    (hstate : a.state = b.state)
    (hprocessed : a.source.processed = b.source.processed)
    (hvalid : a.source.valid = b.source.valid)
    (hmarks : a.source.marks = b.source.marks)
    (horigin : a.origin = b.origin)
    (hlevel : a.level = b.level)
    (hprefix : originCoinPrefix a.level a.source.coins =
      originCoinPrefix a.level b.source.coins) :
    a.observedRepresentative = b.observedRepresentative := by
  apply OriginConfiguration.ext_data
  · exact hstate
  · apply OriginSourceState.ext_data
    · exact hprocessed
    · exact hvalid
    · exact hmarks
    · funext component pair
      change refreshedSourceCoins a.source.coins a.level
          (fun _ => false) component pair =
        refreshedSourceCoins b.source.coins b.level
          (fun _ => false) component pair
      rw [← hlevel]
      by_cases htime : pair.1 < a.level
      · have hpoint := congrFun (congrFun hprefix component) pair
        simpa [originCoinPrefix, coinPrefix, htime,
          refreshedSourceCoins, spliceCoins] using hpoint
      · simp [refreshedSourceCoins, spliceCoins, htime]
  · exact horigin
  · exact hlevel

end Kr25Ssmxt

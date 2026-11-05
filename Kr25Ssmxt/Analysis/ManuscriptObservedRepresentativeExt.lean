import Kr25Ssmxt.Analysis.ManuscriptSourceRefresh

/-! Equality of the observable ghost configuration requires only the
source coins below its current dyadic level. -/

namespace Kr25Ssmxt

theorem ManuscriptOriginConfiguration.observedRepresentative_eq_of_data
    {n : Nat} (a b : ManuscriptOriginConfiguration n)
    (hstate : a.state = b.state)
    (hprocessed : a.source.processed = b.source.processed)
    (hvalid : a.source.valid = b.source.valid)
    (hmarks : a.source.marks = b.source.marks)
    (horigin : a.origin = b.origin)
    (hlevel : a.level = b.level)
    (hprefix : manuscriptOriginCoinPrefix a.level a.source.coins =
      manuscriptOriginCoinPrefix a.level b.source.coins) :
    a.observedRepresentative = b.observedRepresentative := by
  apply ManuscriptOriginConfiguration.ext_data
  · exact hstate
  · apply ManuscriptOriginSourceState.ext_data
    · exact hprocessed
    · exact hvalid
    · exact hmarks
    · funext component pair
      change manuscriptRefreshedSourceCoins a.source.coins a.level
          (fun _ => false) component pair =
        manuscriptRefreshedSourceCoins b.source.coins b.level
          (fun _ => false) component pair
      rw [← hlevel]
      by_cases htime : pair.1 < a.level
      · have hpoint := congrFun (congrFun hprefix component) pair
        simpa [manuscriptOriginCoinPrefix, coinPrefix, htime,
          manuscriptRefreshedSourceCoins, spliceCoins] using hpoint
      · simp [manuscriptRefreshedSourceCoins, spliceCoins, htime]
  · exact horigin
  · exact hlevel

end Kr25Ssmxt

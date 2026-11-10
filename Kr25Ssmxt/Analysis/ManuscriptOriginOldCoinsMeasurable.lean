import Kr25Ssmxt.Analysis.ManuscriptSurvivorIndexMeasurable

/-! Joint measurability of the old-copy coin array read from a random ghost
configuration. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_manuscriptSourceOldCoins_joint {n : Nat} :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      manuscriptSourceOldCoins c.origin c.source.coins c.level) := by
  have heval : Measurable (fun z :
      (Nat → Nat × Nat → Bool) × (Nat × (Nat × Nat)) =>
      z.1 z.2.1 z.2.2) := by
    apply measurable_from_prod_countable_left
    intro index
    exact (measurable_pi_apply index.2).comp
      (measurable_pi_apply index.1)
  have horigin : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.origin) := measurable_manuscriptOriginConfiguration_origin
  have hsource : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.source.coins) :=
    measurable_manuscriptOriginSourceState_coins.comp
      measurable_manuscriptOriginConfiguration_source
  have hlevel : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.level) := measurable_manuscriptOriginConfiguration_level
  apply Measurable.of_eval
  intro pair
  have horiginLabel : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.origin pair.2) := (measurable_pi_apply pair.2).comp horigin
  have hindex : Measurable (fun c : ManuscriptOriginConfiguration n =>
      ((c.origin pair.2).1, (c.level + pair.1,
        (c.origin pair.2).2))) :=
    (measurable_fst.comp horiginLabel).prodMk
      ((hlevel.add measurable_const).prodMk
        (measurable_snd.comp horiginLabel))
  exact heval.comp (hsource.prodMk hindex)

theorem measurable_shiftCoins_joint :
    Measurable (fun z : Nat × (Nat × Nat → Bool) =>
      shiftCoins z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro rounds
  exact measurable_shiftCoins rounds

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_controls
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      (c.level + manuscriptRateExit (c.state.removeComponent P)
        intensity threshold, (c.state.removeComponent P).nextLabel)) := by
  have hstate : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.state) := measurable_manuscriptOriginConfiguration_state
  have hdeleted : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.state.removeComponent P) :=
    (measurable_removeComponent P).comp hstate
  have hround : Measurable (fun c : ManuscriptOriginConfiguration n =>
      manuscriptRateExit (c.state.removeComponent P) intensity
        threshold) :=
    (measurable_manuscriptRateExit_joint threshold hthreshold).comp
      (hdeleted.prodMk measurable_const)
  have hlabel : Measurable (fun c : ManuscriptOriginConfiguration n =>
      (c.state.removeComponent P).nextLabel) :=
    (show Measurable (fun s : TTCState n => s.nextLabel) from
      (measurable_snd.comp measurable_snd).comp
        (comap_measurable (fun s : TTCState n =>
          (s.p, s.X, s.nextLabel)))).comp hdeleted
  exact (measurable_manuscriptOriginConfiguration_level.add hround).prodMk
    hlabel

theorem ManuscriptOriginConfiguration.measurable_activeFullCoins
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      let deleted := c.state.removeComponent P
      let preRounds := c.level + manuscriptRateExit deleted intensity
        threshold
      pendingCoinExtension deleted.nextLabel
        (pendingAfter preCoins preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          deleted.nextLabel basePending future)) := by
  exact (measurable_originalSurvivorCoinExtension_parameters
    preCoins future basePending).comp
      (ManuscriptOriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)

end Kr25Ssmxt

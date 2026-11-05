import Kr25Ssmxt.Analysis.ManuscriptProductBindSwap

/-! For one incoming state and fixed component intensity, the manuscript's
Poisson draw and both thinning loops can be driven by an independent Poisson
count and one fair coin array. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem manuscript_poisson_twoLoops_oneCoinStream
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) :
    (manuscriptRateThinUntil s intensity threshold).bind (fun first =>
      (poissonMeasure (intensity * first.rate)).bind fun pending =>
        thinUntil first pending threshold) =
    (poissonMeasure
      (intensity * (s.rate /
        (2 : NNReal) ^ manuscriptRateExit s intensity threshold))).bind
      (fun pending => fairCoinStreamLaw.map fun coins =>
        thinningResult
          (manuscriptRateThinningResult s intensity threshold coins)
          pending threshold
          (shiftCoins (manuscriptRateExit s intensity threshold) coins)) := by
  let rounds := manuscriptRateExit s intensity threshold
  let mean := intensity * (s.rate / (2 : NNReal) ^ rounds)
  let firstResult := manuscriptRateThinningResult s intensity threshold
  let firstLaw := manuscriptRateThinUntil s intensity threshold
  let pendingLaw : TTCState n → Measure Nat :=
    fun first => poissonMeasure (intensity * first.rate)
  let pendingJoint : TTCState n → Measure (TTCState n × Nat) :=
    fun first => (pendingLaw first).map (Prod.mk first)
  let K : TTCState n × Nat → Measure (TTCState n × Nat) :=
    fun pair => thinUntil pair.1 pair.2 threshold
  have hrate : Measurable (fun first : TTCState n => first.rate) :=
    measurable_fst.comp
      (comap_measurable
        (fun first : TTCState n =>
          (first.rate, first.samples, first.nextLabel)))
  have hpendingLaw : Measurable pendingLaw :=
    measurable_poissonMeasure.comp (measurable_const.mul hrate)
  have hpendingJoint : Measurable pendingJoint :=
    measurable_parametric_probability_map pendingLaw hpendingLaw
      (fun _ => inferInstance)
      (fun pair : TTCState n × Nat => pair) measurable_id
  have hK : Measurable K := thinUntil_kernel_measurable threshold
  have hfirst : Measurable firstResult :=
    measurable_manuscriptRateThinningResult s intensity threshold
  let G : (Nat × Nat → Bool) × Nat → Measure (TTCState n × Nat) :=
    fun pair => K (firstResult pair.1, pair.2)
  have hG : Measurable G :=
    hK.comp ((hfirst.comp measurable_fst).prodMk measurable_snd)
  let H : Nat × (Nat × Nat → Bool) → Measure (TTCState n × Nat) :=
    fun pair => G pair.swap
  have hH : Measurable H := hG.comp measurable_swap
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hfirstLaw : firstLaw = fairCoinStreamLaw.map firstResult := rfl
  have hmean (coins : Nat × Nat → Bool) :
      pendingLaw (firstResult coins) = poissonMeasure mean := rfl
  have hpairResult : Measurable
      (fun pair : (Nat × Nat → Bool) × Nat =>
        (firstResult pair.1, pair.2)) :=
    (hfirst.comp measurable_fst).prodMk measurable_snd
  calc
    firstLaw.bind (fun first =>
        (pendingLaw first).bind fun pending => thinUntil first pending threshold) =
      (firstLaw.bind pendingJoint).bind K := by
        rw [Measure.bind_bind hpendingJoint.aemeasurable hK.aemeasurable]
        congr 1
        funext first
        rw [bind_mapped_measure (pendingLaw first) (Prod.mk first)
          measurable_prodMk_left K hK]
    _ = ((fairCoinStreamLaw.prod (poissonMeasure mean)).map
        (fun pair => (firstResult pair.1, pair.2))).bind K := by
          rw [← manuscript_firstLoop_poisson_joint_law s intensity threshold]
    _ = (fairCoinStreamLaw.prod (poissonMeasure mean)).bind G := by
          rw [bind_mapped_measure
            (fairCoinStreamLaw.prod (poissonMeasure mean))
            (fun pair : (Nat × Nat → Bool) × Nat =>
              (firstResult pair.1, pair.2)) hpairResult K hK]
    _ = ((poissonMeasure mean).prod fairCoinStreamLaw).bind H := by
          exact measure_prod_bind_swap fairCoinStreamLaw
            (poissonMeasure mean) G hG
    _ = (poissonMeasure mean).bind (fun pending =>
        (fairCoinStreamLaw.map firstResult).bind
          (fun first => thinUntil first pending threshold)) := by
          rw [Measure.prod]
          rw [Measure.bind_bind
            Measurable.map_prodMk_left.aemeasurable hH.aemeasurable]
          congr 1
          funext pending
          rw [bind_mapped_measure fairCoinStreamLaw (Prod.mk pending)
            measurable_prodMk_left H hH]
          rw [bind_mapped_measure fairCoinStreamLaw firstResult hfirst
            (fun first => thinUntil first pending threshold)
            ((thinUntil_kernel_measurable threshold).comp
              (measurable_id.prodMk measurable_const))]
          rfl
    _ = _ := by
          congr 1
          funext pending
          exact manuscript_twoLoops_givenPending_eq_oneCoinStream
            s intensity threshold pending

end Kr25Ssmxt

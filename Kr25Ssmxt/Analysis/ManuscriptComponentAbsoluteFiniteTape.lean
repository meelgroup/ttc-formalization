import Kr25Ssmxt.Analysis.ManuscriptSampleAppendTape
import Kr25Ssmxt.Analysis.ManuscriptAbsoluteFiniteSource

/-! A full concrete component kernel with an absolute Poisson pre-draw,
finite survivor-indexed active coins, and an IID point tape. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem communityManuscriptComponentGivenVolume_absolute_finite_tape
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n)
    (level : Nat) (hrate : state.rate = 1 / (2 : NNReal) ^ level)
    (hfresh : state.LabelsFresh) :
    let intensity := manuscriptIntensity b n threshold outcome.2
    let deleted := state.removeComponent P
    let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    communityManuscriptComponentGivenVolume hn prep P b eta delta threshold
      outcome state =
    ((poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        let pending := pendingAfter preCoins
          (level + manuscriptRateExit deleted intensity threshold)
          deleted.nextLabel basePending
        (fairCoinStreamLaw.prod
          (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).map
          fun pair =>
            thinningResultSplitFinite
              (manuscriptRateThinningResult deleted intensity threshold pair.1)
              pending threshold
              (shiftCoins (manuscriptRateExit deleted intensity threshold)
                pair.1) pair.2).bind
      fun second =>
        (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
          second.1.addBatch
            (fun i : Fin second.2 => tape (second.1.nextLabel + i.val)) := by
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  let K : TTCState n × Nat → Measure (TTCState n) := fun second =>
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
      second.1.addBatch
        (fun i : Fin second.2 => tape (second.1.nextLabel + i.val))
  let deleted := state.removeComponent P
  let intensity := manuscriptIntensity b n threshold outcome.2
  let source : Measure (TTCState n × Nat) :=
    (poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        fairCoinStreamLaw.map fun activeCoins =>
          thinningResult
            (manuscriptRateThinningResult deleted intensity threshold activeCoins)
            (pendingAfter preCoins
              (level + manuscriptRateExit deleted intensity threshold)
              deleted.nextLabel basePending)
            threshold
            (shiftCoins (manuscriptRateExit deleted intensity threshold)
              activeCoins)
  let finiteSource : Measure (TTCState n × Nat) :=
    (poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        let pending := pendingAfter preCoins
          (level + manuscriptRateExit deleted intensity threshold)
          deleted.nextLabel basePending
        (fairCoinStreamLaw.prod
          (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).map
          fun pair =>
            thinningResultSplitFinite
              (manuscriptRateThinningResult deleted intensity threshold pair.1)
              pending threshold
              (shiftCoins (manuscriptRateExit deleted intensity threshold)
                pair.1) pair.2
  have hsource : source = finiteSource :=
    manuscript_poisson_twoLoops_absolute_finite deleted intensity threshold
      level (state.labelsFresh_removeComponent P hfresh)
  have hbase : communityManuscriptComponentGivenVolume hn prep P b eta delta
      threshold outcome state = source.bind K := by
    exact communityManuscriptComponentGivenVolume_absolute_tape
      hn prep P b eta delta threshold hroute outcome state level hrate
  exact hbase.trans (congrArg (fun μ : Measure (TTCState n × Nat) =>
    μ.bind K) hsource)

end Kr25Ssmxt

import Ttc.Exec.CVGaussianAcceptedWarm
import Ttc.Exec.CostedAdaptiveTerminalWarmQ
import Arlib.Convexity.GaussianCooling.ScaledRawWarm
import Arlib.MarkovChains.Continuous.SpeedyAffine

/-!
# Exact ideal law behind the combined CV rejection round

The continuing implementation tests shrink membership and the final speedy-acceptance
coin in one joint event.  This file identifies its accepted score law with the nested
normalisation used by `lem:map-speedy-to-ball`.  The identification is needed to turn the
additive mixing analysis into a multiplicative warm-start statement for the retained raw
seed.
-/

namespace Ttc.CVIdealCombinedAccepted

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.SpeedyRejection Ttc.CVCombinedContinuingAccept
open scoped ENNReal Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

private theorem proposal_combinedOutput_preimage_inter
    (Q : Measure (State n)) [IsProbabilityMeasure Q]
    {K : Set (State n)} (hK : MeasurableSet K)
    {c s : Real} (hc : c ≠ 0) (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    {S : Set (State n)} (hS : MeasurableSet S) :
    proposal Q (combinedOutput c ⁻¹' S ∩ combinedAccept K c s) =
      ∫⁻ x in c • K, S.indicator
        (fun y ↦ ENNReal.ofReal (speedyAcceptReal c s y)) (c⁻¹ • x) ∂Q := by
  rw [proposal, Measure.prod_apply
    ((hS.preimage (measurable_combinedOutput c)).inter
      (measurableSet_combinedAccept hK hc)),
    ← lintegral_indicator (measurableSet_smul_set hK hc)]
  apply lintegral_congr
  intro x
  by_cases hxK : x ∈ c • K
  · rw [Set.indicator_of_mem hxK]
    by_cases hxS : c⁻¹ • x ∈ S
    · rw [Set.indicator_of_mem hxS]
      have hslice : Prod.mk x ⁻¹'
          (combinedOutput c ⁻¹' S ∩ combinedAccept K c s) =
          Set.Iic (speedyAcceptReal c s (c⁻¹ • x)) := by
        ext u
        simp [combinedOutput, combinedAccept, rescaleCoin, acceptRegion, hxK, hxS]
      rw [hslice, unitCoin_Iic_speedyAccept hs hc2]
    · rw [Set.indicator_of_notMem hxS]
      have hslice : Prod.mk x ⁻¹'
          (combinedOutput c ⁻¹' S ∩ combinedAccept K c s) = (∅ : Set Real) := by
        ext u
        simp [combinedOutput, hxS]
      rw [hslice, measure_empty]
  · rw [Set.indicator_of_notMem hxK]
    have hslice : Prod.mk x ⁻¹'
        (combinedOutput c ⁻¹' S ∩ combinedAccept K c s) = (∅ : Set Real) := by
      ext u
      simp [combinedAccept, hxK]
    rw [hslice, measure_empty]

private theorem combined_numerator_factor
    (Q : Measure (State n)) [IsProbabilityMeasure Q]
    {K : Set (State n)} (hK : MeasurableSet K)
    {c s : Real} (hc : c ≠ 0) (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hshrink : Q (c • K) ≠ 0) {S : Set (State n)} (hS : MeasurableSet S) :
    proposal Q (combinedOutput c ⁻¹' S ∩ combinedAccept K c s) =
      Q (c • K) *
        ((Measure.map (fun x : State n ↦ c⁻¹ • x)
          (Arlib.condOn Q (c • K))).withDensity
            (fun y ↦ ENNReal.ofReal (speedyAcceptReal c s y))) S := by
  rw [proposal_combinedOutput_preimage_inter Q hK hc hs hc2 hS,
    withDensity_apply _ hS]
  have hmap :
      (∫⁻ y in S, ENNReal.ofReal (speedyAcceptReal c s y)
          ∂Measure.map (fun x : State n ↦ c⁻¹ • x) (Arlib.condOn Q (c • K))) =
        ∫⁻ x, S.indicator
          (fun y ↦ ENNReal.ofReal (speedyAcceptReal c s y)) (c⁻¹ • x)
          ∂Arlib.condOn Q (c • K) := by
    rw [← lintegral_indicator hS]
    exact lintegral_map
      (f := S.indicator (fun y : State n ↦ ENNReal.ofReal (speedyAcceptReal c s y)))
      (g := fun x : State n ↦ c⁻¹ • x)
      ((ENNReal.measurable_ofReal.comp (measurable_speedyAcceptReal c s)).indicator hS)
      (measurable_const_smul _)
  rw [hmap, Arlib.condOn_def, lintegral_smul_measure]
  rw [← lintegral_indicator (measurableSet_smul_set hK hc)]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ENNReal.mul_inv_cancel hshrink (measure_ne_top Q (c • K)),
    one_mul]

/-- Conditioning the joint point/coin proposal on the combined event is the same as
first conditioning the point on the shrunken body, rescaling, and then applying the
speedy acceptance density. -/
theorem map_combinedOutput_condOn_proposal
    (Q : Measure (State n)) [IsProbabilityMeasure Q]
    {K : Set (State n)} (hK : MeasurableSet K)
    {c s : Real} (hc : c ≠ 0) (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hshrink : Q (c • K) ≠ 0) :
    Measure.map (combinedOutput c)
        (Arlib.condOn (proposal Q) (combinedAccept K c s)) =
      Arlib.condOn
        ((Measure.map (fun x : State n ↦ c⁻¹ • x)
          (Arlib.condOn Q (c • K))).withDensity
            (fun y ↦ ENNReal.ofReal (speedyAcceptReal c s y))) Set.univ := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_combinedOutput c) hS,
    Arlib.condOn_apply _ (measurableSet_combinedAccept hK hc)
      (hS.preimage (measurable_combinedOutput c)),
    Arlib.condOn_apply _ MeasurableSet.univ hS, Set.inter_univ]
  rw [proposal_combinedAccept_factor Q hK hc hs hc2 hshrink]
  rw [combined_numerator_factor Q hK hc hs hc2 hshrink hS]
  have hQtop : Q (c • K) ≠ ⊤ := measure_ne_top Q (c • K)
  exact ENNReal.mul_div_mul_left _ _ hshrink hQtop

/-- At the exact speedy stationary law, the joint combined rejection returns exactly the
Gaussian cooling target.  This is the zero-error instance of `lem:map-speedy-to-ball`,
after the preceding operational-law identification. -/
theorem map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {i : Nat} (hi : i < m) :
    let c : Real := 1 - 1 / (2 * (n : Real))
    Measure.map (combinedOutput c)
        (Arlib.condOn (proposal (ellGaussianProb K delta (sigmaSq i)))
          (combinedAccept K c (sigmaSq i))) =
      coolLaw m sigmaSq K i := by
  dsimp only
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : Real) < n := by linarith
  have hc0 : 0 < c := by
    dsimp [c]
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hc2 : c ^ 2 ≤ 1 := by
    exact sq_shrink_le_one hn
  have hdeltaC : delta ≤ 1 - c := by simpa [c] using hdeltan
  have hM0 : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0 hc1 hdelta hdeltaC
      (hsigma i)
  have hMtop : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top (hsigma i) K delta hKvol
  letI : IsProbabilityMeasure (ellGaussianProb K delta (sigmaSq i)) :=
    isProbabilityMeasure_ellGaussianProb hM0 hMtop
  have hhalf : ENNReal.ofReal (1 / 2 : Real) ≤
      ellGaussianProb K delta (sigmaSq i) (c • K) := by
    rw [ellGaussianProb_eq_condOn]
    exact half_le_speedyProb_shrunken hn hK hKc hball hKvol hdelta hdeltan
      (hsigma i)
  have hshrink : ellGaussianProb K delta (sigmaSq i) (c • K) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) hhalf)
  rw [map_combinedOutput_condOn_proposal
    (ellGaussianProb K delta (sigmaSq i)) hK hc0.ne' (hsigma i) hc2 hshrink]
  have htv := tvLe_speedyRejection_coolLaw hn hsigma hK hKc hball hKvol
    hdelta hdeltan hi (P := ellGaussianProb K delta (sigmaSq i))
    (ε := 0) (TVLe.refl _) (by simp)
  have htv0 : TVLe
      (Arlib.condOn
        ((Measure.map (fun x : State n ↦ c⁻¹ • x)
            (Arlib.condOn (ellGaussianProb K delta (sigmaSq i)) (c • K))).withDensity
          (fun v ↦ ENNReal.ofReal (speedyAcceptReal c (sigmaSq i) v))) Set.univ)
      (coolLaw m sigmaSq K i) 0 := by
    simpa only [c, mul_zero] using htv
  exact htv0.eq_of_zero

/-- The exact speedy stationary proposal passes the joint shrink/coin test with
probability at least `1/8`. -/
theorem eighth_le_ellGaussianProb_combinedAccept
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {delta s : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) (hs : 0 < s) :
    ENNReal.ofReal (1 / 8 : Real) ≤
      proposal (ellGaussianProb K delta s)
        (combinedAccept K (1 - 1 / (2 * (n : Real))) s) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    dsimp [c]
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc2 : c ^ 2 ≤ 1 := sq_shrink_le_one hn
  have hdeltaC : delta ≤ 1 - c := by simpa [c] using hdeltan
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hM0 : ellGaussianMeasure K delta s Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0 hc1 hdelta hdeltaC hs
  have hMtop : ellGaussianMeasure K delta s Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs K delta hKvol
  letI : IsProbabilityMeasure (ellGaussianProb K delta s) :=
    isProbabilityMeasure_ellGaussianProb hM0 hMtop
  have hhalf : ENNReal.ofReal (1 / 2 : Real) ≤
      ellGaussianProb K delta s (c • K) := by
    rw [ellGaussianProb_eq_condOn]
    exact half_le_speedyProb_shrunken hn hK hKc hball hKvol hdelta hdeltan hs
  have hshrink : ellGaussianProb K delta s (c • K) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) hhalf)
  have hquarter := Ttc.CostedAdaptiveTerminalWarmQ.quarter_le_phasePointProposal_acceptance_of_tvLe
    hn hK hKc hball hKvol hdelta hdeltan hs
    (P := ellGaussianProb K delta s) (eps := 0) (TVLe.refl _) (by simp)
  have hquarter' : ENNReal.ofReal (1 / 4 : Real) ≤
      ((Measure.map (fun x : State n ↦ c⁻¹ • x)
        (Arlib.condOn (ellGaussianProb K delta s) (c • K))).withDensity
          (fun x ↦ ENNReal.ofReal (speedyAcceptReal c s x))) Set.univ := by
    simpa only [Ttc.SpeedyRejection.phasePointProposal, iterate_zero, c] using hquarter
  exact proposal_combinedAccept_ge_eighth
    (ellGaussianProb K delta s) hK hc0.ne' hs hc2 hshrink hhalf hquarter'

/-- A mixed combined round that is accepted retains a raw endpoint warm for the next
speedy phase.  The accepted score costs `16 M` by conditioning; scaling the exact cooling
target into the raw endpoint costs only `2e`.  Thus the raw seed costs
`(16 M) * (2e)`, with no dimension-dependent factor. -/
theorem isWarm_rejectedNext_costedCombinedAccepted_succ
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    {cc : Real} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {rho : Measure (State n)} [IsProbabilityMeasure rho]
    {M zeta : ENNReal} (hwarm : IsWarm M rho (ellGaussianProb K delta (sigmaSq i)))
    (t : Nat)
    (htv : TVLe
      (Measure.map Prod.snd
        (Ttc.CVSequentialPhaseSampler.sampleFromKernel
          (Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
            K hK delta (sigmaSq i) hdelta t) rho))
      (proposal (ellGaussianProb K delta (sigmaSq i))) zeta)
    (heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      proposal (ellGaussianProb K delta (sigmaSq i))
        (combinedAccept K (1 - 1 / (2 * (n : Real))) (sigmaSq i)))
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    IsWarm
      ((16 * M) * ENNReal.ofReal (2 * Real.exp 1))
      (Measure.map Ttc.FiniteContinuingRetryGaussian.rejectedNext
        (Arlib.condOn
          (Ttc.CVSequentialPhaseSampler.sampleFromKernel
            (Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
              K hK delta (sigmaSq i) hdelta t) rho)
          (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept
            K (1 - 1 / (2 * (n : Real))) (sigmaSq i))))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : Real) < n := by linarith
  have hc0 : 0 < c := by
    dsimp [c]
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc2 : c ^ 2 ≤ 1 := sq_shrink_le_one hn
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdeltaC : delta ≤ 1 - c := by simpa [c] using hdeltan
  have hM0 : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0
      hc1 hdelta hdeltaC (hsigma i)
  have hMtop : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top (hsigma i) K delta hKvol
  letI : IsProbabilityMeasure (ellGaussianProb K delta (sigmaSq i)) :=
    isProbabilityMeasure_ellGaussianProb hM0 hMtop
  let nu := Ttc.CVSequentialPhaseSampler.sampleFromKernel
    (Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
      K hK delta (sigmaSq i) hdelta t) rho
  letI : IsProbabilityMeasure nu := by
    dsimp only [nu]
    infer_instance
  have hscore := Ttc.CVGaussianAcceptedWarm.isWarm_costedCombinedAccepted
    hK hdelta hc0.ne' (inferInstance : IsProbabilityMeasure
      (ellGaussianProb K delta (sigmaSq i))) hwarm t htv heighth hzeta
  have hideal := map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
    hn hsigma hK hKc hball hKvol hdelta hdeltan (Nat.lt_of_succ_lt hi)
  change IsWarm (16 * M)
      (Measure.map (Ttc.FiniteContinuingRetryGaussian.acceptedOutput c)
        (Arlib.condOn nu
          (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept K c (sigmaSq i))))
      (Measure.map (combinedOutput c)
        (Arlib.condOn (proposal (ellGaussianProb K delta (sigmaSq i)))
          (combinedAccept K c (sigmaSq i)))) at hscore
  rw [hideal] at hscore
  have hraw := Arlib.MarkovChains.isWarm_map
    (measurable_const_smul c) hscore
  have hraw' : IsWarm (16 * M)
      (Measure.map Ttc.FiniteContinuingRetryGaussian.rejectedNext
        (Arlib.condOn nu
          (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept K c (sigmaSq i))))
      (Measure.map (fun y : State n ↦ c • y) (coolLaw m sigmaSq K i)) := by
    rw [Measure.map_map (measurable_const_smul c)
      (Ttc.FiniteContinuingRetryGaussian.measurable_acceptedOutput c)] at hraw
    have hfun : (fun y : State n ↦ c • y) ∘
        Ttc.FiniteContinuingRetryGaussian.acceptedOutput c =
        Ttc.FiniteContinuingRetryGaussian.rejectedNext := by
      funext z
      unfold Ttc.FiniteContinuingRetryGaussian.acceptedOutput
        Ttc.FiniteContinuingRetryGaussian.rejectedNext
      simp [combinedOutput, combinedNext, hc0.ne']
    rwa [hfun] at hraw
  have hnext := isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb
    hn hsigma hK hKc hball hKvol hi hcc1 hcc hsched hdelta hdeltan
  exact hraw'.trans hnext

/-- Geometry-only wrapper: the exact ideal `1/8` joint-acceptance floor is discharged
internally. -/
theorem isWarm_rejectedNext_costedCombinedAccepted_succ_of_geometry
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    {cc : Real} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {rho : Measure (State n)} [IsProbabilityMeasure rho]
    {M zeta : ENNReal} (hwarm : IsWarm M rho (ellGaussianProb K delta (sigmaSq i)))
    (t : Nat)
    (htv : TVLe
      (Measure.map Prod.snd
        (Ttc.CVSequentialPhaseSampler.sampleFromKernel
          (Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
            K hK delta (sigmaSq i) hdelta t) rho))
      (proposal (ellGaussianProb K delta (sigmaSq i))) zeta)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    IsWarm
      ((16 * M) * ENNReal.ofReal (2 * Real.exp 1))
      (Measure.map Ttc.FiniteContinuingRetryGaussian.rejectedNext
        (Arlib.condOn
          (Ttc.CVSequentialPhaseSampler.sampleFromKernel
            (Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
              K hK delta (sigmaSq i) hdelta t) rho)
          (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept
            K (1 - 1 / (2 * (n : Real))) (sigmaSq i))))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  exact isWarm_rejectedNext_costedCombinedAccepted_succ
    hn hsigma hK hKc hball hKvol hi hcc1 hcc hsched hdelta hdeltan hwarm t htv
      (eighth_le_ellGaussianProb_combinedAccept
        hn hK hKc hball hKvol hdelta hdeltan (hsigma i)) hzeta

end Ttc.CVIdealCombinedAccepted

#print axioms Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_proposal
#print axioms Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
#print axioms Ttc.CVIdealCombinedAccepted.eighth_le_ellGaussianProb_combinedAccept
#print axioms Ttc.CVIdealCombinedAccepted.isWarm_rejectedNext_costedCombinedAccepted_succ
#print axioms Ttc.CVIdealCombinedAccepted.isWarm_rejectedNext_costedCombinedAccepted_succ_of_geometry

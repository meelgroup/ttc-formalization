import Ttc.Exec.CVGaussianWarmFallbackAnalytic
import Arlib.Convexity.GaussianCooling.AdaptiveRestartWarm

/-!
# Accepted-seed warmth at an accelerated Gaussian cooling rate

The older operational wrapper specialized consecutive cooling to `cc <= 1 + 2/n` and
therefore replaced the exact warm factor `(sqrt cc)^n` by `e`.  Accelerated chunks only
have `cc <= 3/2`.  This file retains the exact factor, which is dimension dependent but
has logarithm `O(n)`.
-/

namespace Ttc.CVGaussianAdaptiveAcceptedWarm

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.FiniteContinuingRetryProjectedWarm
open Ttc.FiniteContinuingRetrySelfCurrentWarm
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVIdealCombinedAccepted
open Ttc.CVCombinedContinuingAccept
open Ttc.CVCombinedContinuingRetryPhaseTV
open Arlib.GaussianCooling.Chunked
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Exact accelerated successor factor after the standard interior shrink. -/
noncomputable def acceleratedSeedWarmFactor (n : Nat) (cc : Real) : ENNReal :=
  ENNReal.ofReal (2 * Real.sqrt cc ^ n)

/-- The scaled raw draw is warm for the next speedy target at the exact cooling-ratio
cost.  This is the non-hardcoded version of
`isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb`. -/
theorem isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb_ratio
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 ≤ cc)
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta) (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    IsWarm (acceleratedSeedWarmFactor n cc)
      (Measure.map
        (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq K i))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  have hnreal : (0 : Real) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnone : (1 : Real) ≤ n := by exact_mod_cast hn
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    dsimp [c]
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdc : delta ≤ 1 - c := by simpa [c] using hdeltan
  have him : i < m := Nat.lt_of_succ_lt hi
  have hself := isWarm_map_smul_coolLaw_self hsigma hK hKc hball hfin him hc0 hc1.le
  have hnext := isWarm_coolLaw_succ_of_ratio hi hK hfin hKc hball hsigma hcc1 hsched
  have hgauss := hself.trans hnext
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK hc0.ne'
  have hsupp : Measure.map (fun x : State n ↦ c • x)
      (coolLaw m sigmaSq K i) ((c • K)ᶜ) = 0 := by
    rw [map_smul_coolLaw_eq_condOn hsigma hK hball hfin him hc0,
      Arlib.condOn_apply _ MeasurableSet.univ hcKm.compl, inter_univ]
    have hempty : (c • K)ᶜ ∩ c • K = (∅ : Set (State n)) := compl_inter_self _
    rw [withDensity_apply _ hcKm.compl, Measure.restrict_restrict hcKm.compl,
      hempty, Measure.restrict_empty]
    simp
  rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hK hball hfin hi] at hgauss
  have hraw := isWarm_ellGaussianProb_of_supported_on_shrunken hK hKc hball
    hc0 hc1 hdelta hdc hsupp hgauss
  have hcpow : (1 / 2 : Real) ≤ c ^ n := by
    dsimp [c]
    exact half_le_one_sub_inv_two_mul_pow hn
  have hcinv : (c⁻¹) ^ n ≤ 2 := by
    rw [inv_pow]
    exact (inv_le_comm₀ (pow_pos hc0 n) (by norm_num : (0 : Real) < 2)).2 (by
      norm_num
      exact hcpow)
  apply hraw.mono
  rw [acceleratedSeedWarmFactor, ← ENNReal.ofReal_mul
    (by positivity : 0 ≤ (c⁻¹) ^ n)]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hcinv (pow_nonneg (Real.sqrt_nonneg cc) n))

/-- A combined accepted retry endpoint is warm for the accelerated next phase. -/
theorem isWarm_rejectedNext_costedCombinedAccepted_succ_ratio
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    {cc : Real} (hcc1 : 1 ≤ cc)
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {rho : Measure (State n)} [IsProbabilityMeasure rho]
    {M zeta : ENNReal} (hwarm : IsWarm M rho (ellGaussianProb K delta (sigmaSq i)))
    (t : Nat)
    (htv : TVLe
      (Measure.map Prod.snd
        (sampleFromKernel
          (combinedRoundCostedKernel K hK delta (sigmaSq i) hdelta t) rho))
      (SpeedyRejection.proposal (ellGaussianProb K delta (sigmaSq i))) zeta)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    IsWarm ((16 * M) * acceleratedSeedWarmFactor n cc)
      (Measure.map rejectedNext
        (Arlib.condOn
          (sampleFromKernel
            (combinedRoundCostedKernel K hK delta (sigmaSq i) hdelta t) rho)
          (costedCombinedAccept
            K (1 - 1 / (2 * (n : Real))) (sigmaSq i))))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    dsimp [c]
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hdeltaC : delta ≤ 1 - c := by simpa [c] using hdeltan
  have hM0 : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0
      (by dsimp [c]; exact sub_lt_self 1 (by positivity))
      hdelta hdeltaC (hsigma i)
  have hMtop : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top (hsigma i) K delta hKvol
  letI : IsProbabilityMeasure (ellGaussianProb K delta (sigmaSq i)) :=
    isProbabilityMeasure_ellGaussianProb hM0 hMtop
  let nu := sampleFromKernel
    (combinedRoundCostedKernel K hK delta (sigmaSq i) hdelta t) rho
  letI : IsProbabilityMeasure nu := by dsimp only [nu]; infer_instance
  have hscore := Ttc.CVGaussianAcceptedWarm.isWarm_costedCombinedAccepted
    hK hdelta hc0.ne' (inferInstance : IsProbabilityMeasure
      (ellGaussianProb K delta (sigmaSq i))) hwarm t htv
      (eighth_le_ellGaussianProb_combinedAccept
        hn hK hKc hball hKvol hdelta hdeltan (hsigma i)) hzeta
  have hideal := map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
    hn hsigma hK hKc hball hKvol hdelta hdeltan (Nat.lt_of_succ_lt hi)
  change IsWarm (16 * M)
      (Measure.map (acceptedOutput c)
        (Arlib.condOn nu (costedCombinedAccept K c (sigmaSq i))))
      (Measure.map (combinedOutput c)
        (Arlib.condOn (SpeedyRejection.proposal (ellGaussianProb K delta (sigmaSq i)))
          (combinedAccept K c (sigmaSq i)))) at hscore
  rw [hideal] at hscore
  have hraw := Arlib.MarkovChains.isWarm_map (measurable_const_smul c) hscore
  have hraw' : IsWarm (16 * M)
      (Measure.map rejectedNext
        (Arlib.condOn nu (costedCombinedAccept K c (sigmaSq i))))
      (Measure.map (fun y : State n ↦ c • y) (coolLaw m sigmaSq K i)) := by
    rw [Measure.map_map (measurable_const_smul c) (measurable_acceptedOutput c)] at hraw
    have hfun : (fun y : State n ↦ c • y) ∘ acceptedOutput c = rejectedNext := by
      funext z
      unfold acceptedOutput rejectedNext
      simp [combinedOutput, combinedNext, hc0.ne']
    rwa [hfun] at hraw
  exact hraw'.trans
    (isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb_ratio hn hsigma hK hKc
      hball hKvol hi hcc1 hsched hdelta hdeltan)

private theorem bind_rejectedKernel_le_stationary
    {K : Set (State n)} (hK : MeasurableSet K) {delta s : Real}
    (hdelta : 0 < delta) (pi : Measure (State n)) [IsProbabilityMeasure pi]
    (hpi : pi = ellGaussianProb K delta s) (t : Nat) {c : Real} (hc : c ≠ 0) :
    pi.bind
        (rejectedKernel
          (fun _ ↦ combinedRoundCostedKernel K hK delta s hdelta t)
          (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
          rejectedNext measurable_rejectedNext 0) ≤ pi := by
  subst pi
  let cand := combinedRoundCostedKernel K hK delta s hdelta t
  let A := costedCombinedAccept K c s
  have hfull : Measure.map rejectedNext
      (sampleFromKernel cand (ellGaussianProb K delta s)) = ellGaussianProb K delta s := by
    have hpair := map_snd_sampleFrom_combinedRoundCostedKernel hK delta s hdelta t
      (ellGaussianProb K delta s)
    rw [← Ttc.CVSequentialPhaseSampler.iterate_eq_sampleFrom_iteratedKernel,
      iterate_invariant ((isReversible_lazy
        (isReversible_speedyMetropolisGaussian_prob hK delta s)).invariant) t] at hpair
    have hmap := congrArg (Measure.map combinedNext) hpair
    rw [Measure.map_map measurable_combinedNext measurable_snd] at hmap
    have hright : Measure.map combinedNext
        ((ellGaussianProb K delta s).prod SpeedyRejection.unitCoin) =
        ellGaussianProb K delta s := by
      change Measure.map Prod.fst
        ((ellGaussianProb K delta s).prod SpeedyRejection.unitCoin) = _
      simp
    calc
      Measure.map rejectedNext
          (sampleFromKernel cand (ellGaussianProb K delta s)) =
        Measure.map (combinedNext ∘ Prod.snd)
          (sampleFromKernel cand (ellGaussianProb K delta s)) := by congr 1
      _ = Measure.map combinedNext
          ((ellGaussianProb K delta s).prod SpeedyRejection.unitCoin) := hmap
      _ = ellGaussianProb K delta s := hright
  calc
    (ellGaussianProb K delta s).bind
        (rejectedKernel (fun _ ↦ cand) A
          (measurableSet_costedCombinedAccept hK hc) rejectedNext measurable_rejectedNext 0) ≤
      Measure.map rejectedNext
        (sampleFromKernel cand (ellGaussianProb K delta s)) := by
          rw [Measure.le_iff]
          intro T hT
          rw [Measure.bind_apply hT
            (rejectedKernel (fun _ ↦ cand) A
              (measurableSet_costedCombinedAccept hK hc)
              rejectedNext measurable_rejectedNext 0).aemeasurable,
            Measure.map_apply measurable_rejectedNext hT]
          unfold sampleFromKernel
          rw [Measure.bind_apply (hT.preimage measurable_rejectedNext) cand.aemeasurable]
          apply lintegral_mono
          intro x
          change ((Kernel.map (cand.restrict
            (measurableSet_costedCombinedAccept hK hc).compl) rejectedNext) x) T ≤ _
          rw [Kernel.map_apply _ measurable_rejectedNext,
            Measure.map_apply measurable_rejectedNext hT,
            Kernel.restrict_apply' cand (measurableSet_costedCombinedAccept hK hc).compl _
              (hT.preimage measurable_rejectedNext)]
          exact measure_mono inter_subset_left
    _ = ellGaussianProb K delta s := hfull

private theorem restrict_le_condOn_probability
    {E : Type*} [MeasurableSpace E] (mu : Measure E) [IsProbabilityMeasure mu]
    (A : Set E) (hA : MeasurableSet A) : mu.restrict A ≤ Arlib.condOn mu A := by
  rw [Measure.le_iff]
  intro T hT
  rw [Measure.restrict_apply hT, Arlib.condOn_apply mu hA hT]
  by_cases h0 : mu A = 0
  · have : mu (T ∩ A) = 0 := measure_mono_null inter_subset_right h0
    simp [this]
  · rw [ENNReal.div_eq_inv_mul]
    calc
      mu (T ∩ A) = 1 * mu (T ∩ A) := by rw [one_mul]
      _ ≤ (mu A)⁻¹ * mu (T ∩ A) := by
        gcongr
        exact ENNReal.one_le_inv.mpr prob_le_one

/-- The complete unnormalised first-hit accepted submeasure at an accelerated phase.
The only change from the fixed-rate theorem is the exact factor
`2 * (sqrt cc)^n`. -/
theorem isWarm_seed_acceptedOutputSubmeasure_gaussian_ratio
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    {cc : Real} (hcc1 : 1 ≤ cc)
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {rho : Measure (State n)} [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho (ellGaussianProb K delta (sigmaSq i)))
    (steps : Nat → Nat) (L : Nat) :
    IsWarm
      ((L : ENNReal) * (((16 : ENNReal) * acceleratedSeedWarmFactor n cc) * M))
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf K hK delta (sigmaSq i)
            (1 - 1 / (2 * (n : Real))) hdelta
            (by
              have hnR : (0 : Real) < n := by
                exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
              have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            steps (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) L)))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    dsimp [c]
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  let pi := ellGaussianProb K delta (sigmaSq i)
  have hM0 : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0
      (by dsimp [c]; exact sub_lt_self 1 (by positivity))
      hdelta (by simpa [c] using hdeltan) (hsigma i)
  have hMtop : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top (hsigma i) K delta hKvol
  letI : IsProbabilityMeasure pi := isProbabilityMeasure_ellGaussianProb hM0 hMtop
  apply isWarm_map_seed_acceptedOutputSubmeasure
    (phaseCandidate K hK delta (sigmaSq i) hdelta steps)
    (costedCombinedAccept K c (sigmaSq i))
    (measurableSet_costedCombinedAccept hK hc0.ne')
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost
    augmentedEmbedding measurable_augmentedEmbedding
    (by intro z; simp [augmentedEmbedding, accepted]) rhoPair Prod.snd measurable_snd
    pi (ellGaussianProb K delta (sigmaSq (i + 1))) L
  · have hinit : Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent
        (Measure.map augmentedEmbedding rhoPair) = rho := by
      ext T hT
      rw [Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent,
        Measure.map_apply measurable_current hT,
        Measure.restrict_apply (hT.preimage measurable_current),
        Measure.map_apply measurable_augmentedEmbedding
          ((hT.preimage measurable_current).inter measurableSet_runningStates)]
      dsimp only [rhoPair]
      rw [Measure.map_apply (measurable_seedEmbedding c)]
      congr 1
      ext x
      simp [augmentedEmbedding, seedEmbedding, runningStates, acceptedStates,
        accepted, current]
      exact ((hT.preimage measurable_current).inter measurableSet_runningStates).preimage
        measurable_augmentedEmbedding
    rw [hinit]
    simpa only [pi] using hwarm
  · intro j
    simpa only [phaseCandidate, rejectedKernel] using
      bind_rejectedKernel_le_stationary hK hdelta pi rfl (steps j) hc0.ne'
  · intro j
    let nu := sampleFromKernel
      (combinedRoundCostedKernel K hK delta (sigmaSq i) hdelta (steps j)) pi
    have hpair : Measure.map Prod.snd nu = SpeedyRejection.proposal pi := by
      dsimp only [nu]
      rw [map_snd_sampleFrom_combinedRoundCostedKernel hK delta (sigmaSq i) hdelta]
      rw [← Ttc.CVSequentialPhaseSampler.iterate_eq_sampleFrom_iteratedKernel,
        iterate_invariant ((isReversible_lazy
          (isReversible_speedyMetropolisGaussian_prob hK delta (sigmaSq i))).invariant)
          (steps j)]
    have htv : TVLe (Measure.map Prod.snd nu) (SpeedyRejection.proposal pi) 0 := by
      rw [hpair]
      exact TVLe.refl _
    have hw := isWarm_rejectedNext_costedCombinedAccepted_succ_ratio
      hn hsigma hK hKc hball hKvol hi hcc1 hsched hdelta hdeltan
      (rho := pi) (M := 1) (zeta := 0) (IsWarm.refl pi) (steps j) htv (by simp)
    have hle : pi.bind
        (acceptedProjectedKernel
          (phaseCandidate K hK delta (sigmaSq i) hdelta steps)
          (costedCombinedAccept K c (sigmaSq i))
          (measurableSet_costedCombinedAccept hK hc0.ne')
          (Prod.snd ∘ augmentedAcceptedOutput c)
          (measurable_snd.comp (measurable_augmentedAcceptedOutput c)) j) ≤
        Measure.map rejectedNext
          (Arlib.condOn nu (costedCombinedAccept K c (sigmaSq i))) := by
      change pi.bind
          (acceptedProjectedKernel
            (phaseCandidate K hK delta (sigmaSq i) hdelta steps)
            (costedCombinedAccept K c (sigmaSq i))
            (measurableSet_costedCombinedAccept hK hc0.ne')
            rejectedNext measurable_rejectedNext j) ≤ _
      rw [Measure.le_iff]
      intro T hT
      rw [Measure.bind_apply hT
        (acceptedProjectedKernel
          (phaseCandidate K hK delta (sigmaSq i) hdelta steps)
          (costedCombinedAccept K c (sigmaSq i))
          (measurableSet_costedCombinedAccept hK hc0.ne') rejectedNext
          measurable_rejectedNext j).aemeasurable,
        Measure.map_apply measurable_rejectedNext hT]
      simp_rw [acceptedProjectedKernel, Kernel.map_apply _ measurable_rejectedNext,
        Measure.map_apply measurable_rejectedNext hT]
      have hrestrict : (nu.restrict (costedCombinedAccept K c (sigmaSq i)))
          (rejectedNext ⁻¹' T) =
          ∫⁻ a, ((phaseCandidate K hK delta (sigmaSq i) hdelta steps j).restrict
            (measurableSet_costedCombinedAccept (s := sigmaSq i) hK hc0.ne')) a
              (rejectedNext ⁻¹' T) ∂pi := by
        rw [Measure.restrict_apply (hT.preimage measurable_rejectedNext)]
        dsimp only [nu, sampleFromKernel]
        rw [Measure.bind_apply
          ((hT.preimage measurable_rejectedNext).inter
            (measurableSet_costedCombinedAccept hK hc0.ne'))
          (combinedRoundCostedKernel K hK delta (sigmaSq i) hdelta (steps j)).aemeasurable]
        apply lintegral_congr
        intro a
        rw [phaseCandidate, Kernel.restrict_apply']
        exact hT.preimage measurable_rejectedNext
      rw [← hrestrict]
      exact restrict_le_condOn_probability nu
        (costedCombinedAccept K c (sigmaSq i))
        (measurableSet_costedCombinedAccept hK hc0.ne') _
    exact IsWarm.of_le hle hw |>.mono (by simp [mul_assoc])

/-- Coarse factor used for runtime accounting.  Under the adaptive rate bound `cc<=3/2`,
the exact factor is at most `2^(n+1)`, so its logarithm is linear in dimension. -/
theorem acceleratedSeedWarmFactor_le_pow_two
    {cc : Real} (hcc1 : 1 ≤ cc) (hcc32 : cc ≤ 3 / 2) :
    acceleratedSeedWarmFactor n cc ≤ ENNReal.ofReal ((2 : Real) ^ (n + 1)) := by
  have hsqrt : Real.sqrt cc ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith⟩
  have hpow : Real.sqrt cc ^ n ≤ (2 : Real) ^ n :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt n
  rw [acceleratedSeedWarmFactor, pow_succ]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [pow_nonneg (show (0 : Real) ≤ 2 by norm_num) n]

/-- Literal adaptive-chunk specialization.  This removes the false fixed-rate premise
`cc <= 1+2/n`; the only schedule premise is the already-used chunk-start bound. -/
theorem isWarm_seed_acceptedOutputSubmeasure_gaussian_adaptive
    (hn : 1 ≤ n) {m : Nat} {N s₀ : Real} (hN : 0 < N) (hs₀ : 0 < s₀)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hbelow : adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i) ≤ N)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {rho : Measure (State n)} [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho
      (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)))
    (steps : Nat → Nat) (L : Nat) :
    IsWarm
      ((L : ENNReal) *
        (((16 : ENNReal) *
          acceleratedSeedWarmFactor n (1 + adaptivePhaseRate N s₀ i)) * M))
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf K hK delta (adaptiveSigmaSq N s₀ i)
            (1 - 1 / (2 * (n : Real))) hdelta
            (by
              have hnR : (0 : Real) < n := by
                exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
              have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            steps (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) L)))
      (ellGaussianProb K delta (adaptiveSigmaSq N s₀ (i + 1))) := by
  let a : Real := adaptivePhaseRate N s₀ i
  have ha0 : 0 ≤ a := (adaptiveChunkRate_pos hN hs₀ _).le
  have hcc1 : 1 ≤ 1 + a := by linarith
  have hsched : adaptiveSigmaSq N s₀ (i + 1) =
      (1 + a) * adaptiveSigmaSq N s₀ i := by
    rw [adaptiveSigmaSq_succ_eq_phaseRate hN hs₀ i]
    ring
  simpa only [a] using
    isWarm_seed_acceptedOutputSubmeasure_gaussian_ratio hn
      (fun j ↦ adaptiveSigmaSq_pos hN hs₀ j) hK hKc hball hKvol hi hcc1 hsched
      hdelta hdeltan hwarm steps L

theorem acceleratedSeedWarmFactor_adaptive_le_pow_two
    {N s₀ : Real} (hN : 0 < N) (hs₀ : 0 < s₀) {i : Nat}
    (hbelow : adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i) ≤ N) :
    acceleratedSeedWarmFactor n (1 + adaptivePhaseRate N s₀ i) ≤
      ENNReal.ofReal ((2 : Real) ^ (n + 1)) := by
  have ha0 : 0 ≤ adaptivePhaseRate N s₀ i :=
    (adaptiveChunkRate_pos hN hs₀ _).le
  have ha2 : adaptivePhaseRate N s₀ i ≤ 1 / 2 :=
    adaptiveChunkRate_le_half hN hbelow
  apply acceleratedSeedWarmFactor_le_pow_two
  · linarith
  · linarith

/-- Accepted-budget function for a flattened accelerated schedule. -/
noncomputable def adaptiveAcceptedBudget
    (n : Nat) (N s₀ : Real) (retries : Nat → Nat)
    (warmBudget : Nat → ENNReal) (i : Nat) : ENNReal :=
  (retries i : ENNReal) *
    (((16 : ENNReal) * acceleratedSeedWarmFactor n (1 + adaptivePhaseRate N s₀ i)) *
      warmBudget i)

/-- The exact active-only accepted-sublaw premise consumed by
`gaussianSeedProjectedOperational_activeReferenceTail`, now for the accelerated schedule. -/
theorem activeAcceptedWarm_gaussian_adaptive
    (hn : 1 ≤ n) {m : Nat} {N s₀ : Real} (hN : 0 < N) (hs₀ : 0 < s₀)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    (hbelow : ∀ i, i + 1 < m →
      adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i) ≤ N)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (warmBudget : Nat → ENNReal) (steps : Nat → Nat → Nat)
    (retries : Nat → Nat) :
    ∀ i, i + 1 < m → ∀ (rho : Measure (State n)), IsProbabilityMeasure rho →
      IsWarm (warmBudget i) rho
        (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)) →
        IsWarm (adaptiveAcceptedBudget n N s₀ retries warmBudget i)
          (Measure.map Prod.snd
            (acceptedOutputSubmeasure
              (augmentedMarginalOf K hK delta (adaptiveSigmaSq N s₀ i)
                (1 - 1 / (2 * (n : Real))) hdelta
                (by
                  have hnR : (0 : Real) < n := by
                    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
                  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
                  have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                    linarith
                  linarith)
                (steps i)
                (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho)
                (retries i))))
          (ellGaussianProb K delta (adaptiveSigmaSq N s₀ (i + 1))) := by
  intro i hi rho hprob hwarm
  letI : IsProbabilityMeasure rho := hprob
  simpa only [adaptiveAcceptedBudget] using
    isWarm_seed_acceptedOutputSubmeasure_gaussian_adaptive hn hN hs₀ hK hKc hball
      hKvol hi (hbelow i hi) hdelta hdeltan hwarm (steps i) (retries i)

#print axioms isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb_ratio
#print axioms isWarm_rejectedNext_costedCombinedAccepted_succ_ratio
#print axioms isWarm_seed_acceptedOutputSubmeasure_gaussian_ratio
#print axioms acceleratedSeedWarmFactor_le_pow_two
#print axioms isWarm_seed_acceptedOutputSubmeasure_gaussian_adaptive
#print axioms acceleratedSeedWarmFactor_adaptive_le_pow_two
#print axioms activeAcceptedWarm_gaussian_adaptive

end Ttc.CVGaussianAdaptiveAcceptedWarm

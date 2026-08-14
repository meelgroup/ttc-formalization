import Ttc.Exec.CVGaussianWarmFallbackOperational
import Ttc.Exec.FiniteContinuingRetryProjectedWarm
import Ttc.Exec.CVIdealCombinedAccepted
import Ttc.Exec.CVContinuingRetryParameters

/-! Concrete analytic inputs for the Gaussian random-fallback phase. -/

namespace Ttc.CVGaussianWarmFallbackAnalytic

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.FiniteContinuingRetrySelfCurrentWarm
open Ttc.FiniteContinuingRetryProjectedWarm
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVIdealCombinedAccepted
open Ttc.CVCombinedContinuingAccept Ttc.CVCombinedContinuingRetryPhaseTV
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

private theorem restrict_le_condOn_of_probability
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

private theorem bind_rejectedKernel_le_of_stationary
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
          (sampleFromKernel cand (ellGaussianProb K delta s)) := by
            congr 1
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

/-- Each unnormalised accepted first-hit raw-seed contribution is warm without any
survival normalization.  Consequently all `L` contributions cost only a factor `L`. -/
theorem isWarm_seed_acceptedOutputSubmeasure_gaussian
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    {cc : Real} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {rho : Measure (State n)} [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho (ellGaussianProb K delta (sigmaSq i)))
    (steps : Nat → Nat) (L : Nat) :
    IsWarm
      ((L : ENNReal) *
        (((16 : ENNReal) * ENNReal.ofReal (2 * Real.exp 1)) * M))
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf K hK delta (sigmaSq i)
            (1 - 1 / (2 * (n : Real))) hdelta
            (by
              have hnR : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
              have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            steps (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) L)))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hnR : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
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
          ((hT.preimage measurable_current).inter
            Ttc.FiniteContinuingRetry.measurableSet_runningStates)]
      dsimp only [rhoPair]
      rw [Measure.map_apply (measurable_seedEmbedding c)]
      congr 1
      ext x
      simp [augmentedEmbedding, seedEmbedding,
        Ttc.FiniteContinuingRetry.runningStates, acceptedStates, accepted, current]
      exact ((hT.preimage measurable_current).inter
        Ttc.FiniteContinuingRetry.measurableSet_runningStates).preimage
          measurable_augmentedEmbedding
    rw [hinit]
    simpa only [pi] using hwarm
  · intro j
    simpa only [phaseCandidate, rejectedKernel] using
      bind_rejectedKernel_le_of_stationary hK hdelta pi rfl (steps j) hc0.ne'
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
    have hw := isWarm_rejectedNext_costedCombinedAccepted_succ_of_geometry
      hn hsigma hK hKc hball hKvol hi hcc1 hcc hsched hdelta hdeltan
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
      exact restrict_le_condOn_of_probability nu
        (costedCombinedAccept K c (sigmaSq i))
        (measurableSet_costedCombinedAccept hK hc0.ne') _
    exact IsWarm.of_le hle hw |>.mono (by simp [mul_assoc])

/-- Random-fallback analogue of the augmented selective-TV theorem. -/
theorem tvLe_gaussianWarmFallbackPhase_selective
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (deadline : ENNReal → Nat) (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho]
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (L : Nat) {pi tau : Measure (State n)} [IsProbabilityMeasure tau]
    {M eta r zeta : ENNReal} (heta0 : eta ≠ 0)
    (hs0 : ∀ j, augmentedSurvivalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho j ≠ 0)
    (ha0 : ∀ j, augmentedProposalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho j (costedCombinedAccept K c s) ≠ 0)
    (hwarm : ∀ i : Fin L, IsWarm M
      ((augmentedMarginalOf K hK delta s c hdelta hc
        (fun _ ↦ deadline (M / eta)) rho i).map current) pi)
    (hmix : ∀ nu : Measure (State n),
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (sampleFromKernel
            (iteratedKernel (lazy (speedyMetropolisGaussian K delta s))
              (deadline (M / eta))) nu) tau zeta)
    (hshrink : tau (c • K) ≠ 0)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤ tau (c • K))
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤
      (((Measure.map (fun y : State n ↦ c⁻¹ • y) (condOn tau (c • K))).withDensity
        (fun y ↦ ENNReal.ofReal (speedyAcceptReal c s y))) Set.univ))
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ augmentedSurvivalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho j →
      augmentedProposalOf K hK delta s c hdelta hc
        (fun _ ↦ deadline (M / eta)) rho j (costedCombinedAccept K c s)ᶜ ≤ r) :
    TVLe
      (sampleFromKernel (randomFallbackKernel fallback)
        (augmentedMarginalOf K hK delta s c hdelta hc
          (fun _ ↦ deadline (M / eta)) rho L))
      (scoreSeedReference c
        (Measure.map (combinedOutput c)
          (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s))))
      (32 * zeta + (eta + r ^ L)) := by
  have heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      SpeedyRejection.proposal tau (combinedAccept K c s) :=
    proposal_combinedAccept_ge_eighth tau hK hc hs hc2 hshrink hhalf hquarter
  have hideal0 : SpeedyRejection.proposal tau (combinedAccept K c s) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) heighth)
  let targetScore := Measure.map (combinedOutput c)
    (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s))
  let target := scoreSeedReference c targetScore
  letI : IsProbabilityMeasure
      (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s)) :=
    Arlib.isProbabilityMeasure_condOn _ hideal0 (measure_ne_top _ _)
  letI : IsProbabilityMeasure targetScore :=
    Measure.isProbabilityMeasure_map (measurable_combinedOutput c).aemeasurable
  letI : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map (by fun_prop :
      Measurable (fun y : State n ↦ (y, c • y))).aemeasurable
  apply tvLe_randomFallback_embeddedMarginal_selective
    (phaseCandidate K hK delta s hdelta (fun _ ↦ deadline (M / eta)))
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
    (by intro a; simp [augmentedEmbedding, accepted]) rho L fallback target eta r (32 * zeta)
  · exact hs0
  · exact ha0
  · intro i hi
    let rhoJ := augmentedMarginalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho i
    haveI : IsProbabilityMeasure rhoJ :=
      isProbabilityMeasure_embeddedMarginal
        (phaseCandidate K hK delta s hdelta (fun _ ↦ deadline (M / eta)))
        (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
        rejectedNext measurable_rejectedNext
        (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
        roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
        rho i
    have hsurv : rhoJ Ttc.FiniteContinuingRetry.runningStates ≠ 0 := by
      simpa only [rhoJ, augmentedMarginalOf, augmentedSurvivalOf, embeddedSurvival]
        using hs0 i
    letI : IsProbabilityMeasure (condOn rhoJ Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ hsurv (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    let p := augmentedProposalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho i
    haveI : IsProbabilityMeasure p := by
      change IsProbabilityMeasure
        (sampleFromKernel
          (phaseCandidate K hK delta s hdelta (fun _ ↦ deadline (M / eta)) i)
          ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current))
      infer_instance
    letI : IsProbabilityMeasure (Measure.map Prod.snd p) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    have hcand := tvLe_augmentedProposalOf_at_significant hK hdelta hc deadline rho i
      heta0 (hwarm i) hi hmix
    have hscore : TVLe
        (Measure.map (acceptedOutput c) (condOn p (costedCombinedAccept K c s)))
        targetScore (32 * zeta) := by
      rw [map_acceptedOutput_condOn_costedCombinedAccept
        (nu := p) (K := K) (c := c) (s := s) hK hc]
      exact (Ttc.ContinuingRejectionSignificant.tvLe_condOn_eighth
        (Measure.map Prod.snd p) (SpeedyRejection.proposal tau)
        (measurableSet_combinedAccept hK hc) hcand heighth hzeta).map
          (measurable_combinedOutput c)
    simpa only [p, augmentedProposalOf, target, targetScore, scoreSeedReference] using
      (tvLe_map_augmentedAcceptedOutput_of_score c hc hscore)
  · exact hr
  · exact hreject

/-- The still-running (unnormalised) current-point submeasure preserves the incoming
warmness at every retry.  Accepted absorbing states are deliberately excluded: only this
killed submeasure is conditioned and fed to the next retry sampler. -/
theorem isWarm_runningCurrent_augmentedMarginalOf_gaussian
    {K : Set (State n)} (hK : MeasurableSet K) {delta s c : Real}
    (hdelta : 0 < delta) (hc : c ≠ 0)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    [IsProbabilityMeasure (ellGaussianProb K delta s)] {M : ENNReal}
    (hwarm : IsWarm M rho (ellGaussianProb K delta s))
    (steps : Nat → Nat) : ∀ j,
    IsWarm M
      (Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent
        (augmentedMarginalOf K hK delta s c hdelta hc steps
          (Measure.map (seedEmbedding c) rho) j))
      (ellGaussianProb K delta s) := by
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  apply isWarm_runningCurrent_embeddedMarginal
    (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost
    augmentedEmbedding measurable_augmentedEmbedding rhoPair
    (ellGaussianProb K delta s)
  · have hinit : Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent
        (Measure.map augmentedEmbedding rhoPair) = rho := by
      ext T hT
      rw [Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent,
        Measure.map_apply measurable_current hT,
        Measure.restrict_apply (hT.preimage measurable_current),
        Measure.map_apply measurable_augmentedEmbedding
          ((hT.preimage measurable_current).inter
            Ttc.FiniteContinuingRetry.measurableSet_runningStates)]
      dsimp only [rhoPair]
      rw [Measure.map_apply (measurable_seedEmbedding c)]
      congr 1
      ext x
      simp [augmentedEmbedding, seedEmbedding,
        Ttc.FiniteContinuingRetry.runningStates, acceptedStates, accepted, current]
      exact ((hT.preimage measurable_current).inter
        Ttc.FiniteContinuingRetry.measurableSet_runningStates).preimage
          measurable_augmentedEmbedding
    rw [hinit]
    exact hwarm
  · intro j
    simpa only [phaseCandidate, rejectedKernel] using
      bind_rejectedKernel_le_of_stationary hK hdelta
        (ellGaussianProb K delta s) rfl (steps j) hc

#print axioms isWarm_seed_acceptedOutputSubmeasure_gaussian
#print axioms isWarm_runningCurrent_augmentedMarginalOf_gaussian
#print axioms tvLe_gaussianWarmFallbackPhase_selective

end Ttc.CVGaussianWarmFallbackAnalytic

import Ttc.Exec.CVGaussianSourceWeightedMoment
import Ttc.Exec.CVGaussianScoreAwareMeanBudget
import Ttc.Exec.CVWeightedIndependentStreamAccuracy

/-!
# First-moment and clipping-bias assembly for source-relative mixing

This is the mean-side companion to the weighted source moment bound.  The geometric-mean
argument is repeated for the source-relative slack `C-1`; it yields the same conservative
`scoreAwareMeanEta` used by the established factor-seven implementation.  The cooling
chain length is separated from the number of estimated transitions, as required by the
hybrid schedule (`chainLength = phases + 1`).
-/

set_option autoImplicit false

namespace Ttc.CVRelativeMeanClippingAssembly

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.CVCorrected Ttc.CVCorrectedRuntime Ttc.CVCorrectedClippingBias
open Ttc.CVIndependentStreamMoments Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianOperationalMean Ttc.CVGaussianOperationalAccuracy
open Ttc.CVGaussianScoreAwareMeanBudget Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianSourceWeightedMoment Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianWarmFallbackScoreMoment
open Ttc.CVGaussianBlockRetryParameters Ttc.CVScoreSeedPhaseKernel
open Ttc.CVWeightedIndependentStreamAccuracy
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Increasing the stream-count parameter only decreases the block share. -/
theorem blockShare_mono_streams {m k0 k : Nat} {eps : Real} (hk : k0 <= k)
    (heps : 0 < eps) : blockShare m k eps <= blockShare m k0 eps := by
  unfold blockShare
  apply div_le_div_of_nonneg_left (correctedNu_nonneg (m := m) (ε := eps))
    (by positivity)
  norm_num
  exact_mod_cast hk

/-- Consequently the aggregate first-moment budget is monotone in the stream count. -/
theorem scoreAwareMeanGamma_mono_streams {m k0 k : Nat} {eps : Real}
    (hk : k0 <= k) (heps : 0 < eps) :
    scoreAwareMeanGamma m k eps <= scoreAwareMeanGamma m k0 eps := by
  have hb := blockShare_mono_streams (m := m) hk heps
  have hsqrt : scoreAwareMeanEta m k eps <= scoreAwareMeanEta m k0 eps := by
    unfold scoreAwareMeanEta
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb (by norm_num))
  unfold scoreAwareMeanGamma
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

theorem scoreAwareMeanGamma_le_one_of_correctedRuntimeSamples_le
    {m k : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    (hk : correctedRuntimeSamples m eps <= k) :
    scoreAwareMeanGamma m k eps <= 1 :=
  (scoreAwareMeanGamma_mono_streams hk heps).trans
    (scoreAwareMeanGamma_corrected_le_one heps heps1)

/-- Geometric-mean cancellation for the source-relative slack.  Only `1<C<=2` is used. -/
theorem relativeScoreAwareMixError_mean_le
    {m k chainLength : Nat} {eps R : Real} {sigmaSq : Nat -> Real}
    {K : Set (State n)} {C : Nat -> Real}
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hsigma : forall j, 0 < sigmaSq j)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hC1 : forall i, 1 < C i) (i : Nat) :
    Real.exp (R ^ 2 / (2 * sigmaSq i)) *
        (scoreAwareMixError m k eps
          (relativePhaseSlack chainLength sigmaSq K C)
          (relativePhaseBoundSq R sigmaSq C) i).toReal <=
      scoreAwareMeanEta m k eps *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) := by
  let e : Real := Real.exp (R ^ 2 / (2 * sigmaSq i))
  let d : Real := (scoreAwareMixError m k eps
    (relativePhaseSlack chainLength sigmaSq K C)
    (relativePhaseBoundSq R sigmaSq C) i).toReal
  let b : Real := blockShare m k eps
  let r : Real := chain chainLength sigmaSq K (i + 1) /
    chain chainLength sigmaSq K i
  have hd0 : 0 <= d := ENNReal.toReal_nonneg
  have hb0 : 0 < b := blockShare_pos heps
  have hr0 : 0 < r := div_pos (chain_pos hsigma hball hfin (i + 1))
    (chain_pos hsigma hball hfin i)
  have hshare := scoreAwareMixError_toReal_le_three_share
    (m := m) (k := k) heps heps1
    (relativePhaseSlack_pos (chainLength := chainLength) hsigma hball hfin hC1)
    (relativePhaseBoundSq_pos (R := R) (sigmaSq := sigmaSq) hC1) i
  have hdb : d <= 3 * b := hshare.trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  have hmoment := scoreAwareMixError_mul_boundSq_le_slack
    (m := m) (k := k) heps heps1
    (relativePhaseSlack_pos (chainLength := chainLength) hsigma hball hfin hC1)
    (relativePhaseBoundSq_pos (R := R) (sigmaSq := sigmaSq) hC1) i
  have hmoment' : d * (e ^ 2 * (4 * C i - 1)) <= (C i - 1) * r ^ 2 := by
    change d * (e ^ 2 * (1 + 2 * (2 * C i - 1))) <= (C i - 1) * r ^ 2 at hmoment
    convert hmoment using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hmoment' hd0
  have hright : d * ((C i - 1) * r ^ 2) <=
      (3 * b) * ((C i - 1) * r ^ 2) := by
    exact mul_le_mul_of_nonneg_right hdb
      (mul_nonneg (sub_nonneg.2 (hC1 i).le) (sq_nonneg r))
  have hcoeff : 3 * (C i - 1) <= (7 / 5 : Real) * (4 * C i - 1) := by
    nlinarith [hC1 i]
  have hbrr : 0 <= b * r ^ 2 := mul_nonneg hb0.le (sq_nonneg r)
  have hweighted : (4 * C i - 1) * (e * d) ^ 2 <=
      (4 * C i - 1) * (((7 / 5 : Real) * b) * r ^ 2) := by
    calc
      (4 * C i - 1) * (e * d) ^ 2 =
          d * (d * (e ^ 2 * (4 * C i - 1))) := by ring
      _ <= d * ((C i - 1) * r ^ 2) := hmul
      _ <= (3 * b) * ((C i - 1) * r ^ 2) := hright
      _ = (3 * (C i - 1)) * (b * r ^ 2) := by ring
      _ <= ((7 / 5 : Real) * (4 * C i - 1)) * (b * r ^ 2) :=
        mul_le_mul_of_nonneg_right hcoeff hbrr
      _ = (4 * C i - 1) * (((7 / 5 : Real) * b) * r ^ 2) := by ring
  have hsq : (e * d) ^ 2 <= ((7 / 5 : Real) * b) * r ^ 2 := by
    have hfac : 0 < 4 * C i - 1 := by linarith [hC1 i]
    nlinarith [hweighted]
  have hsqrtSq : scoreAwareMeanEta m k eps ^ 2 = (7 / 5 : Real) * b := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    exact mul_nonneg (by norm_num) hb0.le
  have htarget0 : 0 <= scoreAwareMeanEta m k eps * r :=
    mul_nonneg (scoreAwareMeanEta_nonneg _ _ _) hr0.le
  rw [← hsqrtSq] at hsq
  have : e * d <= scoreAwareMeanEta m k eps * r := by
    nlinarith [sq_nonneg (e * d + scoreAwareMeanEta m k eps * r)]
  simpa only [e, d, r] using this

/-- Operational source-relative first-moment error, including the inactive tail. -/
theorem operational_relative_meanError
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat} {Q : Nat -> Kernel Seed (State n × Seed)}
    [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat -> (Fin k -> Nat -> State n × Seed) -> Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eta)
    {eps R : Real} {sigmaSq : Nat -> Real} {K : Set (State n)} {C : Nat -> Real}
    (hmixError : forall j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m k eps
        (relativePhaseSlack chainLength sigmaSq K C)
        (relativePhaseBoundSq R sigmaSq C)) j)
    (heps : 0 < eps) (heps1 : eps <= 1) (hsigma : forall j, 0 < sigmaSq j)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hC1 : forall i, 1 < C i) :
    forall i : Fin m,
      Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) *
          (hop.mixError (i : Nat)).toReal <=
        scoreAwareMeanEta m k eps *
          (chain chainLength sigmaSq K ((i : Nat) + 1) /
            chain chainLength sigmaSq K (i : Nat)) := by
  intro i
  rw [hmixError i, activeReferenceMixError]
  by_cases hi : (i : Nat) + 1 < m
  · rw [if_pos hi]
    exact relativeScoreAwareMixError_mean_le heps heps1 hsigma hball hfin hC1 i
  · rw [if_neg hi, ENNReal.toReal_zero, mul_zero]
    exact mul_nonneg (scoreAwareMeanEta_nonneg _ _ _)
      (div_nonneg (chain_pos hsigma hball hfin _).le
        (chain_pos hsigma hball hfin _).le)

/-- Empirical phase means telescope for a chain length independent of the phase count. -/
theorem operational_rawPrefix_mem_relErr_chainLength
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat} {Q : Nat -> Kernel Seed (State n × Seed)}
    [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat -> (Fin k -> Nat -> State n × Seed) -> Real} {eps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps) (hk : 0 < k)
    {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R eta gamma : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (heta : 0 <= eta) (hgamma : gamma <= 1)
    (hbudget : 2 * (m : Real) * eta <= gamma)
    (htarget : forall i, Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    (herror : forall i : Fin m,
      Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) *
          (hop.mixError (i : Nat)).toReal <=
        eta * (chain chainLength sigmaSq K ((i : Nat) + 1) /
          chain chainLength sigmaSq K (i : Nat)))
    (hm : 0 < m) :
    chain chainLength sigmaSq K 0 *
        prefixMean (independentPathLaw k (stateScheduleFromSeed Q) mu0)
          (empiricalPhaseFamily (Seed := Seed) k chainLength sigmaSq K) m ∈
      Ttc.relErr gamma (chain chainLength sigmaSq K m) := by
  apply prefixMean_mem_relErr_of_phaseMeans_budget hm heta hgamma hbudget
    (fun i => chain_pos hsigma hball hfin i)
  intro i
  -- The proof of the existing one-phase lemma is independent of the equality
  -- between the number of transitions and the cooling-chain length.
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let g := scalarPhaseScore (Seed := Seed) chainLength sigmaSq K (i : Nat)
  have hg : Measurable g := measurable_scalarPhaseScore hK i
  have htv := tvLe_operational_score_eval_succ hop (i : Nat)
  rw [htarget i] at htv
  have hmean : ∫ omega, g omega ∂scalarLaw ∈ Ttc.relErr eta
      (chain chainLength sigmaSq K ((i : Nat) + 1) /
        chain chainLength sigmaSq K (i : Nat)) := by
    apply integral_phaseScore_interior_mem_Icc_of_tvLe hsigma hKc hball hfin hKR
      (measurable_fst.comp (measurable_pi_apply ((i : Nat) + 1))) htv
      (hop.mixError_ne_top (i : Nat))
    exact herror i
  have hgInt : Integrable g scalarLaw := by
    apply Integrable.of_bound hg.aestronglyMeasurable
      (Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))))
    filter_upwards with omega
    dsimp only [g, scalarPhaseScore]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (phaseScore_nonneg chainLength sigmaSq (interior K) i _)]
    exact phaseScore_le hsigma (interior_subset.trans hKR) i _
  have havg := integral_streamAverage hk scalarLaw hg hgInt
  simpa only [empiricalPhaseFamily, independentPathLaw, scalarLaw, g] using
    (havg ▸ hmean)

/-- Positive dummy at index zero, with an explicit cooling-chain length. -/
noncomputable def positiveScalarPhaseFamilyChainLength {Seed : Type*}
    (chainLength : Nat) (sigmaSq : Nat -> Real) (K : Set (State n)) :
    Nat -> (Nat -> State n × Seed) -> Real
  | 0 => fun _ => 1
  | i + 1 => scalarPhaseScore chainLength sigmaSq K i

theorem measurable_positiveScalarPhaseFamilyChainLength
    {Seed : Type*} [MeasurableSpace Seed] {chainLength : Nat}
    {sigmaSq : Nat -> Real} {K : Set (State n)} (hK : MeasurableSet K) :
    forall j, Measurable
      (positiveScalarPhaseFamilyChainLength (Seed := Seed) chainLength sigmaSq K j)
  | 0 => measurable_const
  | i + 1 => measurable_scalarPhaseScore hK i

theorem positiveScalarPhaseFamilyChainLength_nonneg
    {Seed : Type*} {chainLength : Nat} {sigmaSq : Nat -> Real}
    {K : Set (State n)} :
    forall j omega,
      0 <= positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j omega := by
  intro j omega
  cases j with
  | zero => simp [positiveScalarPhaseFamilyChainLength]
  | succ i =>
      exact phaseScore_nonneg chainLength sigmaSq (interior K) i _

theorem prefixMean_positiveChainLength_eq_empirical
    {Seed : Type*} [MeasurableSpace Seed] {k m chainLength : Nat}
    {Q : Nat -> Kernel Seed (State n × Seed)} [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {sigmaSq : Nat -> Real} {K : Set (State n)} :
    prefixMean (independentPathLaw k (stateScheduleFromSeed Q) mu0)
        (fun j => streamAverage (k := k)
          (positiveScalarPhaseFamilyChainLength (Seed := Seed)
            chainLength sigmaSq K j)) m =
      prefixMean (independentPathLaw k (stateScheduleFromSeed Q) mu0)
        (empiricalPhaseFamily (Seed := Seed) k chainLength sigmaSq K) m := by
  unfold prefixMean
  apply Finset.prod_congr rfl
  intro i hi
  simp only [positiveScalarPhaseFamilyChainLength, empiricalPhaseFamily,
    scalarPhaseScore]

/-- Complete first-moment plus clipping-bias certificate for source-relative mixing.

The remaining `hrawSecond` premise is exactly the weighted phase-moment output; all
mean-TV, telescope, and clipping arithmetic is discharged here. -/
theorem relative_clippedPrefixTarget
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat} {Q : Nat -> Kernel Seed (State n × Seed)}
    [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps R : Real} {sigmaSq : Nat -> Real} {K : Set (State n)}
    {C : Nat -> Real}
    (V : Nat -> (Fin k -> Nat -> State n × Seed) -> Real)
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    (hmixError : forall j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m k eps
        (relativePhaseSlack chainLength sigmaSq K C)
        (relativePhaseBoundSq R sigmaSq C)) j)
    (heps : 0 < eps) (heps1 : eps <= 1) (hm : 0 < m)
    (hkCorrected : correctedRuntimeSamples m eps <= k)
    (hsigma : forall j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : forall i, Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    (hC1 : forall i, 1 < C i)
    (hWint : forall j, Integrable
      (fun omega => streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hW2int : forall j, Integrable
      (fun omega => (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hWEpos : forall j, 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hrawSecond : forall j, ∫ omega, (streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) <=
      2 * (∫ omega, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hVdef : forall j omega, V j omega = min
      (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (correctedAlpha m eps * ∫ z, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) z
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)))
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 <= initialNormalizer) (hvolume : 0 <= volumeTarget)
    (hinitChain : initialNormalizer = chain chainLength sigmaSq K 0)
    (htargetChain : volumeTarget = chain chainLength sigmaSq K m) :
    ClippedPrefixTarget (independentPathLaw k (stateScheduleFromSeed Q) mu0) V m
      initialNormalizer volumeTarget
      ((m : Real) / (2 * correctedAlpha m eps) + scoreAwareMeanGamma m k eps +
        ((m : Real) / (2 * correctedAlpha m eps)) *
          scoreAwareMeanGamma m k eps) := by
  let pathLaw := independentPathLaw k (stateScheduleFromSeed Q) mu0
  let Wbar := fun j => streamAverage (k := k)
    (positiveScalarPhaseFamilyChainLength (Seed := Seed)
      chainLength sigmaSq K j)
  let gamma := scoreAwareMeanGamma m k eps
  have hk : 0 < k := lt_of_lt_of_le
    (correctedRuntimeSamples_pos m eps) hkCorrected
  have hgamma0 : 0 <= gamma := scoreAwareMeanGamma_nonneg _ _ _
  have hgamma1 : gamma <= 1 := by
    simpa only [gamma] using
      scoreAwareMeanGamma_le_one_of_correctedRuntimeSamples_le heps heps1 hkCorrected
  have hmeanError := operational_relative_meanError hop hmixError heps heps1
    hsigma hball hfin hC1
  have hraw0 := operational_rawPrefix_mem_relErr_chainLength hop hk hsigma hK hKc
    hball hfin hKR (scoreAwareMeanEta_nonneg _ _ _) hgamma1
    (by simp [gamma, scoreAwareMeanGamma]) htarget hmeanError hm
  have hpref := prefixMean_positiveChainLength_eq_empirical
    (k := k) (m := m) (chainLength := chainLength) (Q := Q) (mu0 := mu0)
    (sigmaSq := sigmaSq) (K := K)
  have hrawTarget : initialNormalizer * prefixMean pathLaw Wbar m ∈
      Ttc.relErr gamma volumeTarget := by
    rw [hinitChain, hpref, htargetChain]
    exact hraw0
  apply clippedPrefixTarget_of_rawSecondMoment_approx
    (mu := pathLaw) (V := V) (Wbar := Wbar) (k := (8 : Real))
    (alpha := correctedAlpha m eps) (gamma := gamma)
  · norm_num
  · exact correctedAlpha_pos heps
  · exact one_le_correctedAlpha heps heps1
  · exact hinit
  · exact hvolume
  · exact hgamma0
  · rfl
  · intro j omega
    unfold Wbar streamAverage Ttc.CVEst.avgOf streamScore
    apply div_nonneg
    · exact Finset.sum_nonneg fun l _ =>
        positiveScalarPhaseFamilyChainLength_nonneg j (omega l)
    · positivity
  · intro j
    exact measurable_streamAverage
      (measurable_positiveScalarPhaseFamilyChainLength hK j)
  · simpa only [Wbar, pathLaw] using hWint
  · simpa only [Wbar, pathLaw] using hW2int
  · simpa only [Wbar, pathLaw] using hWEpos
  · intro j
    norm_num
    simpa only [Wbar, pathLaw] using hrawSecond j
  · intro j omega
    simpa only [Wbar, pathLaw] using hVdef j omega
  · exact hrawTarget

/-- Bias-aware weighted `4/5` accuracy with the source-relative mean and clipping
premises fully assembled.  The remaining moment-factor hypotheses are precisely the
output of the weighted hybrid moment bundle. -/
theorem relative_weighted_accuracy_four_fifths
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat} {Q : Nat -> Kernel Seed (State n × Seed)}
    [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps beta requested R : Real} {sigmaSq : Nat -> Real} {K : Set (State n)}
    {C factor : Nat -> Real}
    (V W : Nat -> (Fin k -> Nat -> State n × Seed) -> Real)
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    (hmixError : forall j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m k eps
        (relativePhaseSlack chainLength sigmaSq K C)
        (relativePhaseBoundSq R sigmaSq C)) j)
    (heps : 0 < eps) (heps1 : eps <= 1) (hm : 0 < m)
    (hkCorrected : correctedRuntimeSamples m eps <= k)
    (hbeta : 0 <= beta)
    (haccuracyBudget : eps + beta + eps * beta <= requested)
    (hsigma : forall j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : forall i, Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    (hC1 : forall i, 1 < C i)
    (hWint : forall j, Integrable
      (fun omega => streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hW2int : forall j, Integrable
      (fun omega => (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hWEpos : forall j, 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hrawSecond : forall j, ∫ omega, (streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) <=
      2 * (∫ omega, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hVdef : forall j omega, V j omega = min
      (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (correctedAlpha m eps * ∫ z, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) z
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)))
    (hVm : forall j, Measurable (V j)) (hV0 : forall j omega, 0 <= V j omega)
    (hEpos : forall j, 0 < ∫ omega, V j omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hVcap : forall j omega, V j omega <= 2 * correctedAlpha m eps *
      ∫ z, V j z ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hV2 : forall j, Integrable (fun omega => (V j omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hV2cap : forall j omega, (V j omega) ^ 2 <=
      2 * correctedAlpha m eps ^ 2 *
        ∫ z, (V j z) ^ 2 ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hfactor0 : forall j, 0 <= factor j)
    (hphaseMoment : forall j, ∫ omega, (V j omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) <=
      factor j * (∫ omega, V j omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hprefix : forall i, i <= m ->
      prefixMomentRatio factor i <= 1 + eps ^ 2 / 6250)
    (hWm : forall j, Measurable (W j))
    {Eexact : Set (Fin k -> Nat -> State n × Seed)}
    (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw k (stateScheduleFromSeed Q) mu0).real
      Eexactᶜ <= 1 / 20)
    (hExact : forall omega, omega ∈ Eexact ->
      phaseProduct (fun j => streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j)) m omega = phaseProduct W m omega)
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 <= initialNormalizer) (hvolume : 0 <= volumeTarget)
    (hinitChain : initialNormalizer = chain chainLength sigmaSq K 0)
    (htargetChain : volumeTarget = chain chainLength sigmaSq K m)
    (hbetaDef : (m : Real) / (2 * correctedAlpha m eps) +
      scoreAwareMeanGamma m k eps +
      ((m : Real) / (2 * correctedAlpha m eps)) *
        scoreAwareMeanGamma m k eps <= beta) :
    4 / 5 <= (independentPathLaw k (stateScheduleFromSeed Q) mu0).real
      {omega | initialNormalizer * phaseProduct W m omega ∈
        Ttc.relErr requested volumeTarget} := by
  let Wbar := fun j => streamAverage (k := k)
    (positiveScalarPhaseFamilyChainLength (Seed := Seed)
      chainLength sigmaSq K j)
  have hclip0 := relative_clippedPrefixTarget V hop hmixError heps heps1 hm
    hkCorrected hsigma hK hKc hball hfin hKR htarget hC1 hWint hW2int
    hWEpos hrawSecond hVdef initialNormalizer volumeTarget hinit hvolume
    hinitChain htargetChain
  have hclip : ClippedPrefixTarget
      (independentPathLaw k (stateScheduleFromSeed Q) mu0) V m
      initialNormalizer volumeTarget beta := by
    exact Ttc.CV.relErr_mono hbetaDef hvolume hclip0
  apply corrected_independentStreams_accuracy_four_fifths_weighted_biasAware
    (P := stateScheduleFromSeed Q) (Q := Q) (seed := Prod.snd) (mu0 := mu0)
    (etaInner := eps) (beta := beta) (requested := requested)
    V Wbar W factor heps heps1 hbeta haccuracyBudget hVm hV0 hEpos hVcap
    hV2 hV2cap
  · intro j
    exact measurable_streamAverage
      (measurable_positiveScalarPhaseFamilyChainLength hK j)
  · exact hWm
  · intro j omega
    unfold Wbar streamAverage Ttc.CVEst.avgOf streamScore
    apply div_nonneg
    · exact Finset.sum_nonneg fun l _ =>
        positiveScalarPhaseFamilyChainLength_nonneg j (omega l)
    · positivity
  · simpa only [Wbar] using hWint
  · simpa only [Wbar] using hWEpos
  · simpa only [Wbar] using hVdef
  · exact hfactor0
  · exact hphaseMoment
  · exact hprefix
  · exact hEexact
  · exact hExactFail
  · simpa only [Wbar] using hExact
  · exact hop
  · exact hinit
  · exact hvolume
  · exact hclip

#print axioms relativeScoreAwareMixError_mean_le
#print axioms operational_relative_meanError
#print axioms operational_rawPrefix_mem_relErr_chainLength
#print axioms scoreAwareMeanGamma_le_one_of_correctedRuntimeSamples_le
#print axioms relative_clippedPrefixTarget
#print axioms relative_weighted_accuracy_four_fifths

end Ttc.CVRelativeMeanClippingAssembly

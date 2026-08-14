import Ttc.Exec.CVGaussianOperationalAccuracy

/-!
# Mean-error budget from the score-aware share

The score-aware error is bounded in two different ways.  The block-share bound controls
dependence, while the moment-share bound contains the inverse squared score sup norm.
Taking their geometric mean cancels that potentially exponential sup norm and gives a
small relative first-moment error.
-/

namespace Ttc.CVGaussianScoreAwareMeanBudget

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVCorrectedClippingArithmetic
open Ttc.CVGaussianOperationalAccuracy
open Ttc.CVIndependentStreamMoments Ttc.CVIndependentStreamDependence
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackScoreMoment
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Relative mean error obtained by geometrically averaging the two score-aware
constraints. -/
noncomputable def scoreAwareMeanEta (m k : Nat) (eps : Real) : Real :=
  Real.sqrt ((7 / 5 : Real) * blockShare m k eps)

noncomputable def scoreAwareMeanGamma (m k : Nat) (eps : Real) : Real :=
  2 * (m : Real) * scoreAwareMeanEta m k eps

noncomputable def scoreAwareAccuracyBeta (m k : Nat) (eps : Real) : Real :=
  (m : Real) / (2 * correctedAlpha m eps) + scoreAwareMeanGamma m k eps +
    ((m : Real) / (2 * correctedAlpha m eps)) * scoreAwareMeanGamma m k eps

noncomputable def scoreAwareAccuracyRequested (m k : Nat) (eps : Real) : Real :=
  eps + scoreAwareAccuracyBeta m k eps + eps * scoreAwareAccuracyBeta m k eps

theorem scoreAwareMeanEta_nonneg (m k : Nat) (eps : Real) :
    0 ≤ scoreAwareMeanEta m k eps := Real.sqrt_nonneg _

theorem scoreAwareMeanGamma_nonneg (m k : Nat) (eps : Real) :
    0 ≤ scoreAwareMeanGamma m k eps := by
  unfold scoreAwareMeanGamma
  exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    (scoreAwareMeanEta_nonneg _ _ _)

/-- At the corrected sample count the aggregate mean budget is below one. -/
theorem scoreAwareMeanGamma_corrected_le_one
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m (correctedRuntimeSamples m eps) eps ≤ 1 := by
  let x : Real := m
  let k : Real := correctedRuntimeSamples m eps
  let a : Real := correctedAlpha m eps
  let nu : Real := correctedNu m eps
  let b : Real := blockShare m (correctedRuntimeSamples m eps) eps
  have hx0 : 0 ≤ x := by positivity
  have hx1 : 1 ≤ x + 1 := by linarith
  have he2 : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg eps]
  have ha1 : 1 ≤ a := by
    simpa only [a] using one_le_correctedAlpha (m := m) heps heps1
  have hkLower : 100000 * (x + 1) ≤ k := by
    have h := correctedRuntimeSamples_budget (m := m) (eps := eps) heps
    unfold CorrectedSampleBudget at h
    have hk0 : 0 ≤ k := by positivity
    have hke : k * eps ^ 2 ≤ k := mul_le_of_le_one_right hk0 he2
    simpa only [x, k] using h.trans hke
  have hnu : nu ≤ 1 / (100000 * (x + 1)) := by
    have hden : 0 < 100000 * a ^ 4 * (x + 1) := by positivity
    have hsmall : eps ^ 2 ≤ a ^ 4 := he2.trans (one_le_pow₀ ha1)
    dsimp only [nu]
    rw [correctedNu]
    rw [div_le_iff₀ hden]
    rw [one_div, inv_mul_eq_div]
    field_simp [show 100000 * (x + 1) ≠ 0 by positivity]
    nlinarith
  have hb : b ≤ 1 / (80000000000 * (x + 1) ^ 2) := by
    have hkden : 100000 * (x + 1) ≤ k + 1 := hkLower.trans (by linarith)
    have hden0 : 0 < 8 * (k + 1) := by positivity
    have hnu0 : 0 ≤ nu := by
      simpa only [nu] using correctedNu_nonneg (m := m) (ε := eps)
    have hb1 : b ≤ nu / (8 * (100000 * (x + 1))) := by
      dsimp only [b]
      rw [blockShare]
      exact div_le_div_of_nonneg_left hnu0 (by positivity)
        (mul_le_mul_of_nonneg_left hkden (by norm_num))
    calc
      b ≤ nu / (8 * (100000 * (x + 1))) := hb1
      _ ≤ (1 / (100000 * (x + 1))) /
          (8 * (100000 * (x + 1))) := by gcongr
      _ = 1 / (80000000000 * (x + 1) ^ 2) := by
        field_simp [show x + 1 ≠ 0 by positivity]
        <;> ring
  have hb0 : 0 ≤ b := (blockShare_pos heps).le
  have hsmall : 4 * x ^ 2 * ((7 / 5 : Real) * b) ≤ 1 := by
    calc
      4 * x ^ 2 * ((7 / 5 : Real) * b) ≤
          4 * (x + 1) ^ 2 * ((7 / 5 : Real) *
            (1 / (80000000000 * (x + 1) ^ 2))) := by
        gcongr
        nlinarith
      _ = 28 / 400000000000 := by field_simp; ring
      _ ≤ 1 := by norm_num
  have hsqrtSq : (scoreAwareMeanEta m (correctedRuntimeSamples m eps) eps) ^ 2 =
      (7 / 5 : Real) * b := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    simpa only [b] using mul_nonneg (by norm_num) hb0
  have hgamma0 := scoreAwareMeanGamma_nonneg m (correctedRuntimeSamples m eps) eps
  have hgammaSq :
      (scoreAwareMeanGamma m (correctedRuntimeSamples m eps) eps) ^ 2 ≤ 1 := by
    calc
      (scoreAwareMeanGamma m (correctedRuntimeSamples m eps) eps) ^ 2 =
          4 * x ^ 2 * ((7 / 5 : Real) * b) := by
        rw [scoreAwareMeanGamma, mul_pow, mul_pow, hsqrtSq]
        dsimp only [x]
        ring
      _ ≤ 1 := hsmall
  nlinarith [sq_nonneg
    (scoreAwareMeanGamma m (correctedRuntimeSamples m eps) eps + 1)]

/-- The concrete aggregate mean bias is in fact at most one percent of the inner
accuracy. -/
theorem scoreAwareMeanGamma_corrected_le_div_hundred
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m (correctedRuntimeSamples m eps) eps ≤ eps / 100 := by
  let x : Real := m
  let k : Real := correctedRuntimeSamples m eps
  let a : Real := correctedAlpha m eps
  let nu : Real := correctedNu m eps
  let b : Real := blockShare m (correctedRuntimeSamples m eps) eps
  have hx0 : 0 ≤ x := by positivity
  have he2 : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg eps]
  have ha1 : 1 ≤ a := by
    simpa only [a] using one_le_correctedAlpha (m := m) heps heps1
  have hkLower : 100000 * (x + 1) ≤ k := by
    have h := correctedRuntimeSamples_budget (m := m) (eps := eps) heps
    unfold CorrectedSampleBudget at h
    have hk0 : 0 ≤ k := by positivity
    have hke : k * eps ^ 2 ≤ k := mul_le_of_le_one_right hk0 he2
    simpa only [x, k] using h.trans hke
  have hnu : nu ≤ eps ^ 2 / (100000 * (x + 1)) := by
    have ha4 : 1 ≤ a ^ 4 := one_le_pow₀ ha1
    have h100 : (100000 : Real) ≤ 100000 * a ^ 4 := by nlinarith
    dsimp only [nu]
    rw [correctedNu]
    apply div_le_div_of_nonneg_left (sq_nonneg eps) (by positivity)
    exact mul_le_mul_of_nonneg_right h100 (by positivity)
  have hb : b ≤ eps ^ 2 / (80000000000 * (x + 1) ^ 2) := by
    have hkden : 100000 * (x + 1) ≤ k + 1 := hkLower.trans (by linarith)
    have hnu0 : 0 ≤ nu := by
      simpa only [nu] using correctedNu_nonneg (m := m) (ε := eps)
    have hb1 : b ≤ nu / (8 * (100000 * (x + 1))) := by
      dsimp only [b]
      rw [blockShare]
      exact div_le_div_of_nonneg_left hnu0 (by positivity)
        (mul_le_mul_of_nonneg_left hkden (by norm_num))
    calc
      b ≤ nu / (8 * (100000 * (x + 1))) := hb1
      _ ≤ (eps ^ 2 / (100000 * (x + 1))) /
          (8 * (100000 * (x + 1))) := by gcongr
      _ = eps ^ 2 / (80000000000 * (x + 1) ^ 2) := by
        field_simp [show x + 1 ≠ 0 by positivity]
        <;> ring
  have hb0 : 0 ≤ b := (blockShare_pos heps).le
  have hsmall : 4 * x ^ 2 * ((7 / 5 : Real) * b) ≤ eps ^ 2 / 10000 := by
    calc
      4 * x ^ 2 * ((7 / 5 : Real) * b) ≤
          4 * (x + 1) ^ 2 * ((7 / 5 : Real) *
            (eps ^ 2 / (80000000000 * (x + 1) ^ 2))) := by
        gcongr
        nlinarith
      _ = (28 / 400000000000 : Real) * eps ^ 2 := by
        field_simp [show x + 1 ≠ 0 by positivity]
        <;> ring
      _ ≤ eps ^ 2 / 10000 := by
        have := sq_nonneg eps
        nlinarith
  have hsqrtSq : (scoreAwareMeanEta m (correctedRuntimeSamples m eps) eps) ^ 2 =
      (7 / 5 : Real) * b := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    simpa only [b] using mul_nonneg (by norm_num) hb0
  have hgamma0 := scoreAwareMeanGamma_nonneg m (correctedRuntimeSamples m eps) eps
  have hgammaSq :
      (scoreAwareMeanGamma m (correctedRuntimeSamples m eps) eps) ^ 2 ≤
        (eps / 100) ^ 2 := by
    calc
      (scoreAwareMeanGamma m (correctedRuntimeSamples m eps) eps) ^ 2 =
          4 * x ^ 2 * ((7 / 5 : Real) * b) := by
        rw [scoreAwareMeanGamma, mul_pow, mul_pow, hsqrtSq]
        dsimp only [x]
        ring
      _ ≤ eps ^ 2 / 10000 := hsmall
      _ = (eps / 100) ^ 2 := by ring
  nlinarith [sq_nonneg
    (scoreAwareMeanGamma m (correctedRuntimeSamples m eps) eps + eps / 100)]

/-- Running the literal estimator at the corrected inner accuracy `eps/4` leaves enough
room for operational mean bias and clipping while meeting the external request. -/
theorem scoreAwareAccuracyRequested_inner_le
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareAccuracyRequested m
      (correctedRuntimeSamples m (correctedInnerAccuracy eps))
      (correctedInnerAccuracy eps) ≤ eps := by
  let inner := correctedInnerAccuracy eps
  let k := correctedRuntimeSamples m inner
  let gamma := scoreAwareMeanGamma m k inner
  let theta := (m : Real) / (2 * correctedAlpha m inner)
  let beta := scoreAwareAccuracyBeta m k inner
  have hi0 : 0 < inner := by unfold inner correctedInnerAccuracy; positivity
  have hi1 : inner ≤ 1 := by unfold inner correctedInnerAccuracy; linarith
  have hi0' : 0 ≤ inner := hi0.le
  have hg0 : 0 ≤ gamma := scoreAwareMeanGamma_nonneg _ _ _
  have hg : gamma ≤ inner / 100 := by
    simpa only [gamma, k] using
      scoreAwareMeanGamma_corrected_le_div_hundred hi0 hi1
  have ht0 : 0 ≤ theta := by
    unfold theta
    exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (correctedAlpha_pos hi0).le)
  have ht : theta ≤ inner / 200000 := by
    have h := phase_div_correctedAlpha_le (m := m) hi0
    have hiSq : inner ^ 2 ≤ inner := by nlinarith [sq_nonneg (inner - 1)]
    unfold theta
    calc
      (m : Real) / (2 * correctedAlpha m inner) =
          ((m : Real) / correctedAlpha m inner) / 2 := by ring
      _ ≤ (inner ^ 2 / 100000) / 2 := by gcongr
      _ ≤ inner / 200000 := by nlinarith
  have htg : theta * gamma ≤ inner / 20000000 := by
    have hiSq : inner ^ 2 ≤ inner := by nlinarith [sq_nonneg (inner - 1)]
    calc
      theta * gamma ≤ (inner / 200000) * gamma :=
        mul_le_mul_of_nonneg_right ht hg0
      _ ≤ (inner / 200000) * (inner / 100) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ inner / 20000000 := by nlinarith
  have hb : beta ≤ inner / 50 := by
    unfold beta scoreAwareAccuracyBeta
    change theta + gamma + theta * gamma ≤ inner / 50
    nlinarith
  have hb0 : 0 ≤ beta := by
    unfold beta scoreAwareAccuracyBeta
    positivity
  unfold scoreAwareAccuracyRequested
  change inner + beta + inner * beta ≤ eps
  have hib : inner * beta ≤ beta := mul_le_of_le_one_left hb0 hi1
  unfold inner correctedInnerAccuracy at *
  nlinarith

/-- The geometric-mean cancellation.  No first-moment TV premise remains. -/
theorem scoreAwareMixError_mean_le
    {m k chainLength : Nat} {eps R : Real} {sigmaSq : Nat → Real}
    {K : Set (State n)} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7) (i : Nat) :
    Real.exp (R ^ 2 / (2 * sigmaSq i)) *
        (scoreAwareMixError m k eps
          (phaseMomentSlackSeven chainLength sigmaSq K C)
          (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal ≤
      scoreAwareMeanEta m k eps *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) := by
  let e : Real := Real.exp (R ^ 2 / (2 * sigmaSq i))
  let d : Real := (scoreAwareMixError m k eps
    (phaseMomentSlackSeven chainLength sigmaSq K C)
    (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal
  let b : Real := blockShare m k eps
  let r : Real := chain chainLength sigmaSq K (i + 1) /
    chain chainLength sigmaSq K i
  have he0 : 0 < e := Real.exp_pos _
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hb0 : 0 < b := blockShare_pos heps
  have hr0 : 0 < r := div_pos (chain_pos hsigma hball hfin (i + 1))
    (chain_pos hsigma hball hfin i)
  have hshare := scoreAwareMixError_toReal_le_three_share
    (m := m) (k := k) heps heps1
    (phaseMomentSlackSeven_pos (chainLength := chainLength) hsigma hball hfin hC7)
    (phaseScoreTransportBoundSqSeven_pos (R := R) (sigmaSq := sigmaSq)) i
  have hdb : d ≤ 3 * b := by
    refine hshare.trans ?_
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  have hmoment := scoreAwareMixError_mul_boundSq_le_slack
    (m := m) (k := k) heps heps1
    (phaseMomentSlackSeven_pos (chainLength := chainLength) hsigma hball hfin hC7)
    (phaseScoreTransportBoundSqSeven_pos (R := R) (sigmaSq := sigmaSq)) i
  have hmoment' : d * (e ^ 2 * (1 + 2 * 7)) ≤ (7 - C i) * r ^ 2 := by
    simpa only [d, e, r, phaseScoreTransportBoundSqSeven,
      phaseMomentSlackSeven] using hmoment
  norm_num at hmoment'
  have hmul := mul_le_mul_of_nonneg_left hmoment' hd0
  have hright : d * ((7 - C i) * r ^ 2) ≤ (3 * b) * (7 * r ^ 2) := by
    exact mul_le_mul hdb
      (mul_le_mul_of_nonneg_right (by linarith [hC0 i]) (sq_nonneg r))
      (mul_nonneg (sub_nonneg.2 (hC7 i).le) (sq_nonneg r))
      (mul_nonneg (by norm_num) hb0.le)
  have hsq : (e * d) ^ 2 ≤ ((7 / 5 : Real) * b) * r ^ 2 := by
    calc
      (e * d) ^ 2 = (d * (d * (e ^ 2 * 15))) / 15 := by ring
      _ ≤ (d * ((7 - C i) * r ^ 2)) / 15 := by gcongr
      _ ≤ ((3 * b) * (7 * r ^ 2)) / 15 := by gcongr
      _ = ((7 / 5 : Real) * b) * r ^ 2 := by ring
  have hsarg0 : 0 ≤ (7 / 5 : Real) * b := by positivity
  have hsqEta : (scoreAwareMeanEta m k eps) ^ 2 = (7 / 5 : Real) * b := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    simpa only [b] using hsarg0
  have htarget0 : 0 ≤ scoreAwareMeanEta m k eps * r :=
    mul_nonneg (scoreAwareMeanEta_nonneg _ _ _) hr0.le
  rw [← hsqEta] at hsq
  have : e * d ≤ scoreAwareMeanEta m k eps * r := by
    nlinarith [sq_nonneg (e * d + scoreAwareMeanEta m k eps * r)]
  simpa only [e, d, r] using this

/-- Operational form: the score-aware `mixError` identity discharges every phase of the
mean-side TV premise. -/
theorem operational_scoreAware_meanError
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat}
    {Q : Nat → Kernel Seed (State n × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eta : Real}
    (hop : Ttc.CVIndependentStreamDependence.IndependentStreamOperational k
      (Ttc.CVScoreSeedPhaseKernel.stateScheduleFromSeed Q) Q Prod.snd mu0 V m eta)
    {eps R : Real} {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m k eps
        (phaseMomentSlackSeven chainLength sigmaSq K C)
        (phaseScoreTransportBoundSqSeven R sigmaSq)) j)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7) :
    ∀ i : Fin m,
      Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) *
          (hop.mixError (i : Nat)).toReal ≤
        scoreAwareMeanEta m k eps *
          (chain chainLength sigmaSq K ((i : Nat) + 1) /
            chain chainLength sigmaSq K (i : Nat)) := by
  intro i
  rw [hmixError (i : Nat), activeReferenceMixError]
  by_cases hi : (i : Nat) + 1 < m
  · rw [if_pos hi]
    exact scoreAwareMixError_mean_le heps heps1 hsigma hball hfin hC0 hC7 i
  · rw [if_neg hi, ENNReal.toReal_zero, mul_zero]
    exact mul_nonneg (scoreAwareMeanEta_nonneg _ _ _)
      (div_nonneg (chain_pos hsigma hball hfin _).le
        (chain_pos hsigma hball hfin _).le)

/-- Nonnegativity of the literal positive-dummy empirical score. -/
theorem positiveEmpirical_nonneg
    {Seed : Type*} {k m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)} :
    ∀ j omega, 0 ≤ streamAverage (k := k)
      (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j) omega := by
  intro j omega
  unfold streamAverage Ttc.CVEst.avgOf streamScore
  apply div_nonneg
  · exact Finset.sum_nonneg fun l _ => by
      cases j with
      | zero => simp [positiveScalarPhaseFamily]
      | succ i =>
          exact phaseScore_nonneg m sigmaSq (interior K) i _
  · positivity

/-- Every raw empirical mean is positive under the concrete score-aware budget.  This
also covers all irrelevant tail indices: their operational TV error is exactly zero. -/
theorem operational_positiveEmpirical_mean_pos
    {Seed : Type*} [MeasurableSpace Seed]
    {m : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps R : Real}
    {V : Nat →
      (Fin (correctedRuntimeSamples m eps) → Nat → State n × Seed) → Real}
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd mu0 V m eps)
    {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m (correctedRuntimeSamples m eps) eps
        (phaseMomentSlackSeven m sigmaSq K C)
        (phaseScoreTransportBoundSqSeven R sigmaSq)) j)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hm : 0 < m)
    (hsigma : ∀ j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw m sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7) :
    ∀ j, 0 < ∫ omega, streamAverage
      (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j) omega
        ∂independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) mu0 := by
  let k := correctedRuntimeSamples m eps
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let etaMean := scoreAwareMeanEta m k eps
  have hk : 0 < k := correctedRuntimeSamples_pos m eps
  have heta0 : 0 ≤ etaMean := scoreAwareMeanEta_nonneg _ _ _
  have hetaLt : etaMean < 1 := by
    have hg := scoreAwareMeanGamma_corrected_le_one (m := m) heps heps1
    have hm1 : (1 : Real) ≤ m := by exact_mod_cast hm
    have htwo : 2 * etaMean ≤ scoreAwareMeanGamma m k eps := by
      unfold scoreAwareMeanGamma
      exact mul_le_mul_of_nonneg_right (by nlinarith) heta0
    have hlt : 2 * etaMean < 2 := htwo.trans_lt
      (hg.trans_lt (show (1 : Real) < 2 by norm_num))
    linarith
  intro j
  cases j with
  | zero =>
      have havg := integral_streamAverage hk scalarLaw
        (g := fun _ : Nat → State n × Seed => (1 : Real)) measurable_const
        (integrable_const 1)
      have havg' : ∫ omega, streamAverage (k := k)
          (fun _ : Nat → State n × Seed => (1 : Real)) omega
            ∂independentPathLaw k (stateScheduleFromSeed Q) mu0 = 1 := by
        simpa [independentPathLaw, scalarLaw] using havg
      simpa [positiveScalarPhaseFamily, k, havg']
  | succ i =>
      let g : (Nat → State n × Seed) → Real := fun omega =>
        phaseScore m sigmaSq (interior K) i (omega (i + 1)).1
      have hg : Measurable g :=
        (measurable_phaseScore isOpen_interior.measurableSet i).comp
          (measurable_fst.comp (measurable_pi_apply (i + 1)))
      have hgInt : Integrable g scalarLaw := by
        apply Integrable.of_bound hg.aestronglyMeasurable
          (Real.exp (R ^ 2 / (2 * sigmaSq i)))
        filter_upwards with omega
        rw [Real.norm_eq_abs, abs_of_nonneg
          (phaseScore_nonneg m sigmaSq (interior K) i _)]
        exact phaseScore_le hsigma (interior_subset.trans hKR) i _
      have htv := tvLe_operational_score_eval_succ hop i
      rw [htarget i] at htv
      have hmeanError : Real.exp (R ^ 2 / (2 * sigmaSq i)) *
          (hop.mixError i).toReal ≤ etaMean *
            (chain m sigmaSq K (i + 1) / chain m sigmaSq K i) := by
        rw [hmixError i, activeReferenceMixError]
        by_cases hi : i + 1 < m
        · rw [if_pos hi]
          exact scoreAwareMixError_mean_le heps heps1 hsigma hball hfin hC0 hC7 i
        · rw [if_neg hi, ENNReal.toReal_zero, mul_zero]
          exact mul_nonneg heta0 (div_nonneg
            (chain_pos hsigma hball hfin _).le (chain_pos hsigma hball hfin _).le)
      have hmean := integral_phaseScore_interior_mem_Icc_of_tvLe hsigma hKc hball
        hfin hKR (measurable_fst.comp (measurable_pi_apply (i + 1))) htv
        (hop.mixError_ne_top i) hmeanError
      have hratio : 0 < chain m sigmaSq K (i + 1) / chain m sigmaSq K i :=
        div_pos (chain_pos hsigma hball hfin _) (chain_pos hsigma hball hfin _)
      have hscalarPos : 0 < ∫ omega, g omega ∂scalarLaw := by
        have hlower : (1 - etaMean) *
            (chain m sigmaSq K (i + 1) / chain m sigmaSq K i) ≤
              ∫ omega, g omega ∂scalarLaw := by
          simpa only [g, scalarLaw, Function.comp_apply] using hmean.1
        exact (mul_pos (sub_pos.2 hetaLt) hratio).trans_le hlower
      have havg := integral_streamAverage hk scalarLaw hg hgInt
      simpa only [positiveScalarPhaseFamily, independentPathLaw, k, scalarLaw, g,
        ← havg] using hscalarPos

/-- The deterministic caps required by corrected accuracy follow from literal clipping
once the raw relative second moment is at most two. -/
theorem clippedStatistic_caps_of_rawSecond
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {alpha : Real} (halpha : 2 ≤ alpha)
    {Wbar V : Omega → Real}
    (hW0 : ∀ omega, 0 ≤ Wbar omega) (hWm : Measurable Wbar)
    (hWint : Integrable Wbar mu)
    (hW2int : Integrable (fun omega => (Wbar omega) ^ 2) mu)
    (hWEpos : 0 < ∫ omega, Wbar omega ∂mu)
    (hrawSecond : ∫ omega, (Wbar omega) ^ 2 ∂mu ≤
      2 * (∫ omega, Wbar omega ∂mu) ^ 2)
    (hVdef : ∀ omega, V omega = min (Wbar omega)
      (alpha * ∫ z, Wbar z ∂mu)) :
    Measurable V ∧ (∀ omega, 0 ≤ V omega) ∧
      0 < ∫ omega, V omega ∂mu ∧
      (∀ omega, V omega ≤ 2 * alpha * ∫ z, V z ∂mu) ∧
      (∀ omega, (V omega) ^ 2 ≤
        2 * alpha ^ 2 * ∫ z, (V z) ^ 2 ∂mu) := by
  have ha0 : 0 < alpha := by linarith
  have hthreshold0 : 0 ≤ alpha * ∫ z, Wbar z ∂mu :=
    mul_nonneg ha0.le hWEpos.le
  have hVeq : V = fun omega => min (Wbar omega)
      (alpha * ∫ z, Wbar z ∂mu) := funext hVdef
  have hVm : Measurable V := by rw [hVeq]; fun_prop
  have hV0 : ∀ omega, 0 ≤ V omega := fun omega => by
    rw [hVeq]
    exact le_min (hW0 omega) hthreshold0
  have hVW : ∀ omega, V omega ≤ Wbar omega := fun omega => by
    rw [hVeq]
    exact min_le_left _ _
  have hV2int : Integrable (fun omega => (V omega) ^ 2) mu := by
    refine Integrable.mono' hW2int (hVm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (hV0 omega) (hW0 omega)).2 (hVW omega)
  have hlower : (1 - 1 / (2 * alpha)) * (∫ z, Wbar z ∂mu) ≤
      ∫ z, V z ∂mu := by
    have h := expect_trunc_ge_half ha0 hW0 hWm hWint hW2int hWEpos
      hrawSecond (by norm_num)
    rw [hVeq]
    exact h
  have hcoef : (1 / 2 : Real) ≤ 1 - 1 / (2 * alpha) := by
    have hinv : 1 / (2 * alpha) ≤ (1 / 2 : Real) := by
      rw [div_le_iff₀ (mul_pos (by norm_num) ha0)]
      nlinarith
    linarith
  have hhalf : (1 / 2 : Real) * (∫ z, Wbar z ∂mu) ≤
      ∫ z, V z ∂mu :=
    (mul_le_mul_of_nonneg_right hcoef hWEpos.le).trans hlower
  have hVEpos : 0 < ∫ z, V z ∂mu :=
    (mul_pos (by norm_num) hWEpos).trans_le hhalf
  have hVcap : ∀ omega, V omega ≤ 2 * alpha * ∫ z, V z ∂mu := by
    intro omega
    have hmin : V omega ≤ alpha * ∫ z, Wbar z ∂mu := by
      rw [hVeq]
      exact min_le_right _ _
    have hscale : alpha * ∫ z, Wbar z ∂mu ≤
        2 * alpha * ∫ z, V z ∂mu := by
      calc
        alpha * ∫ z, Wbar z ∂mu =
            (2 * alpha) * ((1 / 2 : Real) * ∫ z, Wbar z ∂mu) := by ring
        _ ≤ (2 * alpha) * ∫ z, V z ∂mu :=
          mul_le_mul_of_nonneg_left hhalf (mul_nonneg (by norm_num) ha0.le)
        _ = 2 * alpha * ∫ z, V z ∂mu := by ring
    calc
      V omega ≤ alpha * ∫ z, Wbar z ∂mu := hmin
      _ ≤ 2 * alpha * ∫ z, V z ∂mu := hscale
  have hsqMean : (∫ z, V z ∂mu) ^ 2 ≤ ∫ z, (V z) ^ 2 ∂mu :=
    sq_integral_le_integral_sq hVm hV2int
  have hrawMeanSq : (∫ z, Wbar z ∂mu) ^ 2 ≤
      4 * (∫ z, V z ∂mu) ^ 2 := by
    nlinarith [sq_nonneg ((∫ z, Wbar z ∂mu) - 2 * ∫ z, V z ∂mu)]
  have hV2cap : ∀ omega, (V omega) ^ 2 ≤
      2 * alpha ^ 2 * ∫ z, (V z) ^ 2 ∂mu := by
    intro omega
    have hmin : V omega ≤ alpha * ∫ z, Wbar z ∂mu := by
      rw [hVeq]
      exact min_le_right _ _
    have hsquare : (V omega) ^ 2 ≤
        alpha ^ 2 * (∫ z, Wbar z ∂mu) ^ 2 := by
      simpa only [mul_pow] using
        ((sq_le_sq₀ (hV0 omega)
          (mul_nonneg ha0.le hWEpos.le)).2 hmin)
    -- The sharper `3/4` coefficient from `alpha ≥ 2` pays the factor two.
    have hthreeQuarter : (3 / 4 : Real) * (∫ z, Wbar z ∂mu) ≤
        ∫ z, V z ∂mu := by
      have hc : (3 / 4 : Real) ≤ 1 - 1 / (2 * alpha) := by
        have hinv : 1 / (2 * alpha) ≤ (1 / 4 : Real) := by
          rw [div_le_iff₀ (mul_pos (by norm_num) ha0)]
          nlinarith
        linarith
      exact (mul_le_mul_of_nonneg_right hc hWEpos.le).trans hlower
    have hmeanSqTwo : (∫ z, Wbar z ∂mu) ^ 2 ≤
        2 * ∫ z, (V z) ^ 2 ∂mu := by
      have hs : (∫ z, Wbar z ∂mu) ^ 2 ≤
          (16 / 9 : Real) * (∫ z, V z ∂mu) ^ 2 := by
        nlinarith [sq_nonneg
          (3 * (∫ z, Wbar z ∂mu) - 4 * ∫ z, V z ∂mu)]
      nlinarith
    calc
      (V omega) ^ 2 ≤ alpha ^ 2 * (∫ z, Wbar z ∂mu) ^ 2 := hsquare
      _ ≤ alpha ^ 2 * (2 * ∫ z, (V z) ^ 2 ∂mu) := by gcongr
      _ = 2 * alpha ^ 2 * ∫ z, (V z) ^ 2 ∂mu := by ring
  exact ⟨hVm, hV0, hVEpos, hVcap, hV2cap⟩

/-- Score-aware valid-branch accuracy with the entire mean/clipping/requested scalar
budget fixed concretely.  The output is the literal raw empirical phase product, so the
old external exact-coupling event is discharged by `univ`.

Only the corrected clipped-statistic cap facts remain explicit; these are properties of
the pointwise clipping definition, not Gaussian mixing or mean-telescope assumptions. -/
theorem scoreAware_operational_accuracy_concreteMeanBudget
    {Seed : Type*} [MeasurableSpace Seed]
    {m : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps R : Real} {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (V : Nat →
      (Fin (correctedRuntimeSamples m eps) → Nat → State n × Seed) → Real)
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd mu0 V m eps)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m (correctedRuntimeSamples m eps) eps
        (phaseMomentSlackSeven m sigmaSq K C)
        (phaseScoreTransportBoundSqSeven R sigmaSq)) j)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw m sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7)
    (hexact : ∀ i,
      ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
          ∂(coolLaw m sigmaSq K i) ≤
        C i * (∫ x, phaseScore m sigmaSq (interior K) i x
          ∂(coolLaw m sigmaSq K i)) ^ 2)
    (hm : 0 < m)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega
      ∂independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) mu0)
    (hVcap : ∀ j omega, V j omega ≤
      2 * correctedAlpha m eps * ∫ z, V j z
        ∂independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) mu0)
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤
      2 * correctedAlpha m eps ^ 2 * ∫ z, (V j z) ^ 2
        ∂independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) mu0)
    (hVdef : ∀ j omega, V j omega = min
      (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j) omega)
      (correctedAlpha m eps * ∫ z,
        streamAverage (k := correctedRuntimeSamples m eps)
          (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j) z
        ∂independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) mu0))
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hinitChain : initialNormalizer = chain m sigmaSq K 0)
    (htargetChain : volumeTarget = chain m sigmaSq K m) :
    4 / 5 ≤
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) mu0).real
        {omega | initialNormalizer * phaseProduct
          (fun j => streamAverage (k := correctedRuntimeSamples m eps)
            (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)) m omega ∈
          Ttc.relErr
            (scoreAwareAccuracyRequested m (correctedRuntimeSamples m eps) eps)
            volumeTarget} := by
  let k := correctedRuntimeSamples m eps
  let gamma := scoreAwareMeanGamma m k eps
  let beta := scoreAwareAccuracyBeta m k eps
  let requested := scoreAwareAccuracyRequested m k eps
  let W := fun j => streamAverage (k := k)
    (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)
  have hgamma0 : 0 ≤ gamma := scoreAwareMeanGamma_nonneg _ _ _
  have hgamma1 : gamma ≤ 1 := by
    simpa only [gamma, k] using scoreAwareMeanGamma_corrected_le_one heps heps1
  have hbeta0 : 0 ≤ beta := by
    unfold beta scoreAwareAccuracyBeta
    have ha := correctedAlpha_pos (m := m) heps
    positivity
  have hmeanError := operational_scoreAware_meanError hop hmixError heps heps1
    hsigma hball hfin hC0 hC7
  have hWbarEpos := operational_positiveEmpirical_mean_pos hop hmixError heps heps1
    hm hsigma hK hKc hball hfin hKR htarget hC0 hC7
  apply scoreAware_operational_accuracy_four_fifths
    (V := V) (W := W) hop hmixError rfl rfl heps heps1 hbeta0 hgamma0
    hgamma1 (scoreAwareMeanEta_nonneg _ _ _)
    (by simp [gamma, k, scoreAwareMeanGamma])
    (by simp [requested, scoreAwareAccuracyRequested, beta, k])
    hsigma hK hKc hball hfin hKR htarget hC0 hC7 hexact hmeanError hm
    (by simpa only [k, W] using
      (positiveEmpirical_nonneg (Seed := Seed) (k := k) (m := m)
        (sigmaSq := sigmaSq) (K := K)))
    (by simpa only [k, W] using hWbarEpos)
    hVm hV0 hEpos hVcap hV2cap hVdef
    (fun j => measurable_streamAverage
      (measurable_positiveScalarPhaseFamily hK j))
    (Eexact := Set.univ) MeasurableSet.univ
    (by simp)
    (by intro omega homega; rfl)
    initialNormalizer volumeTarget hinit hvolume hinitChain htargetChain
    (by simp [beta, scoreAwareAccuracyBeta, gamma, k])

/-- The literal corrected phase statistic used by the final operational theorem. -/
noncomputable def clippedPositiveEmpiricalFamily
    {Seed : Type*} [MeasurableSpace Seed]
    (m : Nat) (eps : Real) (Q : Nat → Kernel Seed (State n × Seed))
    [∀ i, IsMarkovKernel (Q i)] (mu0 : Measure (State n × Seed))
    (sigmaSq : Nat → Real) (K : Set (State n)) :
    Nat → (Fin (correctedRuntimeSamples m eps) → Nat → State n × Seed) → Real :=
  fun j omega =>
    let Wbar := streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)
    min (Wbar omega) (correctedAlpha m eps *
      ∫ z, Wbar z ∂independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) mu0)

/-- Strongest literal valid-branch accuracy theorem: both the corrected statistic and
the realised output are fixed definitions.  There are no mean-error, clipping-cap, raw
positivity, or coupling binders. -/
theorem scoreAware_operational_accuracy_literal
    {Seed : Type*} [MeasurableSpace Seed]
    {m : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps R : Real} {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd mu0
      (clippedPositiveEmpiricalFamily m eps Q mu0 sigmaSq K) m eps)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m (correctedRuntimeSamples m eps) eps
        (phaseMomentSlackSeven m sigmaSq K C)
        (phaseScoreTransportBoundSqSeven R sigmaSq)) j)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw m sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7)
    (hexact : ∀ i,
      ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
          ∂(coolLaw m sigmaSq K i) ≤
        C i * (∫ x, phaseScore m sigmaSq (interior K) i x
          ∂(coolLaw m sigmaSq K i)) ^ 2)
    (hm : 0 < m)
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hinitChain : initialNormalizer = chain m sigmaSq K 0)
    (htargetChain : volumeTarget = chain m sigmaSq K m) :
    4 / 5 ≤
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) mu0).real
        {omega | initialNormalizer * phaseProduct
          (fun j => streamAverage (k := correctedRuntimeSamples m eps)
            (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)) m omega ∈
          Ttc.relErr
            (scoreAwareAccuracyRequested m (correctedRuntimeSamples m eps) eps)
            volumeTarget} := by
  let k := correctedRuntimeSamples m eps
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let pathLaw := independentPathLaw k (stateScheduleFromSeed Q) mu0
  let Wbar := fun j => streamAverage (k := k)
    (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)
  let V := clippedPositiveEmpiricalFamily m eps Q mu0 sigmaSq K
  have hk : 0 < k := correctedRuntimeSamples_pos m eps
  have halpha : 2 ≤ correctedAlpha m eps := by
    have ha := correctedAlpha_ge_hundred_thousand (m := m) heps heps1
    linarith
  have hscalar := positiveScalarPhaseFamily_memLp_and_factorSeven hop hmixError
    rfl rfl heps heps1 hsigma hKc hball hfin hKR htarget hC0 hC7 hexact
  have hWm : ∀ j, Measurable (Wbar j) := fun j =>
    measurable_streamAverage (measurable_positiveScalarPhaseFamily hK j)
  have hWint : ∀ j, Integrable (Wbar j) pathLaw := by
    intro j
    have h := (memLp_streamAverage (k := k) scalarLaw (hscalar j).1).integrable
      one_le_two
    simpa only [Wbar, pathLaw, scalarLaw, independentPathLaw] using h
  have hW2int : ∀ j, Integrable (fun omega => (Wbar j omega) ^ 2) pathLaw := by
    intro j
    have h := integrable_streamAverage_sq (k := k) scalarLaw (hscalar j).1
    simpa only [Wbar, pathLaw, scalarLaw, independentPathLaw] using h
  have hWEpos := operational_positiveEmpirical_mean_pos hop hmixError heps heps1
    hm hsigma hK hKc hball hfin hKR htarget hC0 hC7
  have hrawTwo : ∀ j, ∫ omega, (Wbar j omega) ^ 2 ∂pathLaw ≤
      2 * (∫ omega, Wbar j omega ∂pathLaw) ^ 2 := by
    intro j
    have hsix := scalar_seven_to_streamAverage_six hk scalarLaw
      (measurable_positiveScalarPhaseFamily hK j) (hscalar j).1 (hscalar j).2
    have hkR : (0 : Real) < k := by exact_mod_cast hk
    have hk6 : (6 : Real) ≤ k := by
      exact_mod_cast (show 6 ≤ k from (eight_le_correctedRuntimeSamples heps heps1).trans' (by omega))
    have hcoef : 1 + 6 / (k : Real) ≤ 2 := by
      have := (div_le_one hkR).2 hk6
      linarith
    have hmean0 : 0 ≤ (∫ omega, Wbar j omega ∂pathLaw) ^ 2 := sq_nonneg _
    have hsix' : ∫ omega, (Wbar j omega) ^ 2 ∂pathLaw ≤
        (1 + 6 / (k : Real)) * (∫ omega, Wbar j omega ∂pathLaw) ^ 2 := by
      simpa only [Wbar, pathLaw, scalarLaw, independentPathLaw] using hsix
    exact hsix'.trans (mul_le_mul_of_nonneg_right hcoef hmean0)
  have hstats : ∀ j,
      Measurable (V j) ∧ (∀ omega, 0 ≤ V j omega) ∧
      0 < ∫ omega, V j omega ∂pathLaw ∧
      (∀ omega, V j omega ≤
        2 * correctedAlpha m eps * ∫ z, V j z ∂pathLaw) ∧
      (∀ omega, (V j omega) ^ 2 ≤
        2 * correctedAlpha m eps ^ 2 * ∫ z, (V j z) ^ 2 ∂pathLaw) := by
    intro j
    apply clippedStatistic_caps_of_rawSecond halpha
      (positiveEmpirical_nonneg (Seed := Seed) (k := k) (m := m)
        (sigmaSq := sigmaSq) (K := K) j)
      (hWm j) (hWint j) (hW2int j)
      (by simpa only [k, Wbar, pathLaw] using hWEpos j) (hrawTwo j)
    intro omega
    simp only [V, clippedPositiveEmpiricalFamily, Wbar, pathLaw, k]
  apply scoreAware_operational_accuracy_concreteMeanBudget
    (V := V) hop hmixError heps heps1 hsigma hK hKc hball hfin hKR htarget
    hC0 hC7 hexact hm
    (fun j => (hstats j).1)
    (fun j => (hstats j).2.1)
    (fun j => (hstats j).2.2.1)
    (fun j => (hstats j).2.2.2.1)
    (fun j => (hstats j).2.2.2.2)
    (by intro j omega
        simp only [V, clippedPositiveEmpiricalFamily])
    initialNormalizer volumeTarget hinit hvolume hinitChain htargetChain

#print axioms scoreAwareMixError_mean_le
#print axioms operational_scoreAware_meanError
#print axioms scoreAwareMeanGamma_corrected_le_one
#print axioms scoreAware_operational_accuracy_concreteMeanBudget
#print axioms clippedStatistic_caps_of_rawSecond
#print axioms scoreAware_operational_accuracy_literal

end Ttc.CVGaussianScoreAwareMeanBudget

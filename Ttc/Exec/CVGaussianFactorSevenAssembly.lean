import Ttc.Exec.CVGaussianScoreAwareMoment
import Ttc.Exec.CVGaussianScoreAwareIndependent
import Ttc.Exec.CVIndependentStreamBiasAccuracy
import Ttc.Exec.CVCorrectedClippingArithmetic
import Ttc.Exec.CVGaussianGuardedExpectedVolume

/-!
# Parameter-compatible factor-seven Gaussian assembly

This file uses the spare moment room in the score-aware Gaussian operation before
clipping.  An operational scalar score is transported with relative second-moment
factor `7`; averaging `k` independent complete streams changes this to `1 + 6/k`.
For the actual corrected parameters

`k = correctedRuntimeSamples m eps`, `alpha = correctedAlpha m eps`,

the clipping normalization then fits below the corrected estimator's required factor
`1 + 8/k`.  Thus no false numerical hypothesis such as `k + 8 <= alpha` is needed.

The final theorems deliberately retain the geometric cool-law identification, exact
ideal score moment, raw telescope, and exact-path coupling as named premises.  These are
the statistic/geometry facts specific to the selected cooling schedule, rather than
hidden oracle assumptions.
-/

namespace Ttc.CVGaussianFactorSevenAssembly

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVIndependentStreamMoments Ttc.CVIndependentStreamDependence
open Ttc.CVIndependentStreamBiasAccuracy Ttc.CVCorrectedClippingBias
open Ttc.CVCorrectedClippingArithmetic
open Ttc.CVGaussianWarmFallbackScoreMoment Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVIndependentStreamGeneralizedCertificate
open Ttc.CVGaussianGuardedExpectedVolume Ttc.CVGuardedGeneralizedPublic
open Ttc.CVGaussianScoreAwareParameters
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## Factor-parametric and factor-seven score transport -/

/-- TV transport of a bounded Gaussian ratio score with an arbitrary target factor.
The additive TV error is paid from the exact gap `T - C`. -/
theorem operational_phaseScore_sq_moment_le_factor
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {chainLength : Nat} {sigmaSq : Nat → Real} {i : Nat}
    {K : Set (State n)} {X : Omega → State n} {e : ENNReal}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (hX : Measurable X)
    (hTV : TVLe (Measure.map X mu) (coolLaw chainLength sigmaSq K i) e)
    (he : e ≠ ⊤) {C T : Real} (hC0 : 0 ≤ C) (hCT : C ≤ T)
    (hexact :
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂(coolLaw chainLength sigmaSq K i) ≤
        C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : e.toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * T)) ≤
      (T - C) *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2) :
    ∫ omega, phaseScore chainLength sigmaSq (interior K) i (X omega) ^ 2 ∂mu ≤
      T * (∫ omega,
        phaseScore chainLength sigmaSq (interior K) i (X omega) ∂mu) ^ 2 := by
  have hgap : 0 ≤ T - C := sub_nonneg.2 hCT
  have hmain := phaseScore_interior_sq_moment_le_of_tvLe hsigma hKc hball hfin
    hKR hX hTV he hC0 hgap hexact
  have heq : C + (T - C) = T := by ring
  have hslack' : e.toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 *
          (1 + 2 * (C + (T - C)))) ≤
      (T - C) *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2 := by
    rw [heq]
    exact hslack
  simpa only [heq] using hmain hslack'

/-- Target-factor-seven specialization.  Its transport multiplier is exactly
`exp(...)^2 * (1 + 14)`. -/
theorem operational_phaseScore_sq_moment_le_seven
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {chainLength : Nat} {sigmaSq : Nat → Real} {i : Nat}
    {K : Set (State n)} {X : Omega → State n} {e : ENNReal}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (hX : Measurable X)
    (hTV : TVLe (Measure.map X mu) (coolLaw chainLength sigmaSq K i) e)
    (he : e ≠ ⊤) {C : Real} (hC0 : 0 ≤ C) (hC7 : C ≤ 7)
    (hexact :
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂(coolLaw chainLength sigmaSq K i) ≤
        C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : e.toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 7)) ≤
      (7 - C) *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2) :
    ∫ omega, phaseScore chainLength sigmaSq (interior K) i (X omega) ^ 2 ∂mu ≤
      7 * (∫ omega,
        phaseScore chainLength sigmaSq (interior K) i (X omega) ∂mu) ^ 2 := by
  exact operational_phaseScore_sq_moment_le_factor hsigma hKc hball hfin hKR hX
    hTV he hC0 hC7 hexact hslack

/-- Path-law form of the generic score transport.  It also supplies the `L^2`
premise consumed by the independent-stream averaging theorem. -/
theorem operational_path_phaseScore_memLp_and_sq_moment_le_factor
    {Seed : Type*} [MeasurableSpace Seed]
    {k mPhases : Nat}
    {Q : Nat → Kernel Seed (State n × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q)
      Q Prod.snd mu0 V mPhases eta)
    {chainLength : Nat} {sigmaSq : Nat → Real} {i : Nat}
    {K : Set (State n)}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    {C T : Real} (hC0 : 0 ≤ C) (hCT : C ≤ T)
    (hexact :
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂(coolLaw chainLength sigmaSq K i) ≤
        C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : (hop.mixError i).toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * T)) ≤
      (T - C) *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × Seed ↦
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧
      ∫ omega, (g omega) ^ 2 ∂pathLaw ≤
        T * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  dsimp only
  let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let X : (Nat → State n × Seed) → State n :=
    fun omega ↦ (omega (i + 1)).1
  have hfm := measurable_phaseScore (m := chainLength) (σsq := sigmaSq)
    (K := interior K) isOpen_interior.measurableSet i
  have hbound : ∀ x, |phaseScore chainLength sigmaSq (interior K) i x| ≤
      Real.exp (R ^ 2 / (2 * sigmaSq i)) := by
    intro x
    rw [abs_of_nonneg
      (phaseScore_nonneg chainLength sigmaSq (interior K) i x)]
    exact phaseScore_le hsigma (interior_subset.trans hKR) i x
  constructor
  · exact memLp_pathScore_of_bounded hfm hbound i
  · have htv := tvLe_operational_score_eval_succ hop i
    rw [htarget] at htv
    exact operational_phaseScore_sq_moment_le_factor hsigma hKc hball hfin hKR
      (by fun_prop) htv (hop.mixError_ne_top i) hC0 hCT hexact hslack

/-! ## Score-aware factor-seven parameters -/

noncomputable def phaseMomentSlackSeven (chainLength : Nat)
    (sigmaSq : Nat → Real) (K : Set (State n)) (C : Nat → Real)
    (i : Nat) : Real :=
  (7 - C i) *
    (chain chainLength sigmaSq K (i + 1) /
      chain chainLength sigmaSq K i) ^ 2

noncomputable def phaseScoreTransportBoundSqSeven (R : Real)
    (sigmaSq : Nat → Real) (i : Nat) : Real :=
  Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 7)

theorem phaseMomentSlackSeven_pos
    {chainLength : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    {C : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hC7 : ∀ i, C i < 7) (i : Nat) :
    0 < phaseMomentSlackSeven chainLength sigmaSq K C i := by
  unfold phaseMomentSlackSeven
  have hi := chain_pos (m := chainLength) hsigma hball hfin i
  have hi1 := chain_pos (m := chainLength) hsigma hball hfin (i + 1)
  exact mul_pos (sub_pos.2 (hC7 i)) (sq_pos_of_pos (div_pos hi1 hi))

theorem phaseScoreTransportBoundSqSeven_pos
    {R : Real} {sigmaSq : Nat → Real} (i : Nat) :
    0 < phaseScoreTransportBoundSqSeven R sigmaSq i := by
  unfold phaseScoreTransportBoundSqSeven
  positivity

theorem scoreAware_phaseScore_slack_seven
    {m k chainLength : Nat} {eps R : Real} {sigmaSq : Nat → Real}
    {K : Set (State n)} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hC7 : ∀ i, C i < 7) (i : Nat) :
    (scoreAwareMixError m k eps
        (phaseMomentSlackSeven chainLength sigmaSq K C)
        (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal *
      (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 7)) ≤
        (7 - C i) *
          (chain chainLength sigmaSq K (i + 1) /
            chain chainLength sigmaSq K i) ^ 2 := by
  exact scoreAwareMixError_mul_boundSq_le_slack heps heps1
    (phaseMomentSlackSeven_pos hsigma hball hfin hC7)
    (phaseScoreTransportBoundSqSeven_pos (R := R) (sigmaSq := sigmaSq)) i

/-- Active score-aware phases have scalar factor `7` when the exact cool-law factor is
strictly below `7`. -/
theorem operational_path_phaseScore_scoreAware_active_seven
    {Seed : Type*} [MeasurableSpace Seed]
    {k mPhases chainLength : Nat}
    {Q : Nat → Kernel Seed (State n × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q)
      Q Prod.snd mu0 V mPhases eta)
    {mParam kParam : Nat} {eps R : Real} {slack boundSq : Nat → Real}
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError mPhases
      (scoreAwareMixError mParam kParam eps slack boundSq) j)
    {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (hslackDef : slack = phaseMomentSlackSeven chainLength sigmaSq K C)
    (hboundDef : boundSq = phaseScoreTransportBoundSqSeven R sigmaSq)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7)
    (hexact : ∀ i,
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂(coolLaw chainLength sigmaSq K i) ≤
        C i * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    {i : Nat} (hi : i + 1 < mPhases) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × Seed ↦
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧
      ∫ omega, (g omega) ^ 2 ∂pathLaw ≤
        7 * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  apply operational_path_phaseScore_memLp_and_sq_moment_le_factor hop hsigma hKc
    hball hfin hKR (htarget i) (hC0 i) (hC7 i).le (hexact i)
  rw [hmixError i, activeReferenceMixError, if_pos hi, hslackDef, hboundDef]
  exact scoreAware_phaseScore_slack_seven heps heps1 hsigma hball hfin hC7 i

/-! ## Independent averaging and corrected clipping -/

variable {Path : Type*} [MeasurableSpace Path]

/-- A scalar factor `7` becomes the empirical factor `1 + 6/k`. -/
theorem scalar_seven_to_streamAverage_six
    {k : Nat} (hk : 0 < k) (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hL2 : MemLp g 2 mu)
    (hsq : ∫ x, (g x) ^ 2 ∂mu ≤
      7 * (∫ x, g x ∂mu) ^ 2) :
    ∫ omega, (streamAverage (k := k) g omega) ^ 2
        ∂(independentStreamLaw mu) ≤
      (1 + 6 / (k : Real)) *
        (∫ omega, streamAverage (k := k) g omega
          ∂(independentStreamLaw mu)) ^ 2 := by
  have hmean := integral_streamAverage hk mu hg (hL2.integrable one_le_two)
  rw [hmean]
  exact integral_streamAverage_sq_le_seven hk mu hg hL2 rfl hsq

/-- At the literal corrected runtime parameters, clipping a raw empirical factor
`1 + 6/k` gives the estimator-required factor `1 + 8/k`. -/
theorem clipped_sq_moment_le_eight_correctedRuntime_of_raw_six
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {mu : Measure Path} [IsProbabilityMeasure mu]
    {Wbar V : Path → Real}
    (hW0 : ∀ omega, 0 ≤ Wbar omega) (hWm : Measurable Wbar)
    (hWint : Integrable Wbar mu)
    (hW2int : Integrable (fun omega ↦ (Wbar omega) ^ 2) mu)
    (hWEpos : 0 < ∫ omega, Wbar omega ∂mu)
    (hrawSecond : ∫ omega, (Wbar omega) ^ 2 ∂mu ≤
      (1 + 6 / (correctedRuntimeSamples m eps : Real)) *
        (∫ omega, Wbar omega ∂mu) ^ 2)
    (hVdef : ∀ omega, V omega = min (Wbar omega)
      (correctedAlpha m eps * ∫ z, Wbar z ∂mu)) :
    Integrable (fun omega ↦ (V omega) ^ 2) mu ∧
      ∫ omega, (V omega) ^ 2 ∂mu ≤
        (1 + 8 / (correctedRuntimeSamples m eps : Real)) *
          (∫ omega, V omega ∂mu) ^ 2 := by
  let k : Nat := correctedRuntimeSamples m eps
  let alpha : Real := correctedAlpha m eps
  have hk8 : 8 ≤ k := eight_le_correctedRuntimeSamples heps heps1
  have hk0R : (0 : Real) < (k : Real) := by
    exact_mod_cast (show 0 < k by omega)
  have halpha0 : 0 < alpha := by
    have := correctedAlpha_ge_hundred_thousand (m := m) heps heps1
    dsimp only [alpha]
    linarith
  have hVeq : V = fun omega ↦ min (Wbar omega)
      (alpha * ∫ z, Wbar z ∂mu) := by
    funext omega
    simpa only [alpha] using hVdef omega
  have hthreshold0 : 0 ≤ alpha * ∫ z, Wbar z ∂mu :=
    mul_nonneg halpha0.le hWEpos.le
  have hV0 : ∀ omega, 0 ≤ V omega := fun omega ↦ by
    rw [hVeq]
    exact le_min (hW0 omega) hthreshold0
  have hVm : Measurable V := by
    rw [hVeq]
    exact hWm.min measurable_const
  have hVW : ∀ omega, V omega ≤ Wbar omega := fun omega ↦ by
    rw [hVeq]
    exact min_le_left _ _
  have hV2int : Integrable (fun omega ↦ (V omega) ^ 2) mu := by
    refine Integrable.mono' hW2int (hVm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (hV0 omega) (hW0 omega)).2 (hVW omega)
  constructor
  · exact hV2int
  · have hrawTwo :
        (1 + 6 / (k : Real)) ≤ 2 := by
      have hk6 : (6 : Real) ≤ (k : Real) := by exact_mod_cast (hk8.trans' (by omega))
      have : 6 / (k : Real) ≤ 1 := (div_le_one hk0R).2 hk6
      linarith
    have hlower :
        (1 - 1 / (2 * alpha)) * (∫ omega, Wbar omega ∂mu) ≤
          ∫ omega, V omega ∂mu := by
      have h := expect_trunc_ge_half halpha0 hW0 hWm hWint hW2int hWEpos
        (by simpa only [k] using hrawSecond) hrawTwo
      rw [hVeq]
      exact h
    have hden0 : 0 < 1 - 1 / (2 * alpha) := by
      simpa only [alpha] using
        correctedRuntime_clippingDenominator_pos (m := m) heps heps1
    have hVsecond : ∫ omega, (V omega) ^ 2 ∂mu ≤
        ∫ omega, (Wbar omega) ^ 2 ∂mu :=
      integral_mono hV2int hW2int fun omega ↦
        (sq_le_sq₀ (hV0 omega) (hW0 omega)).2 (hVW omega)
    have hmean : ∫ omega, Wbar omega ∂mu ≤
        (∫ omega, V omega ∂mu) / (1 - 1 / (2 * alpha)) := by
      rw [le_div_iff₀ hden0]
      simpa [mul_comm] using hlower
    have hVmean0 : 0 ≤ ∫ omega, V omega ∂mu := integral_nonneg hV0
    calc
      ∫ omega, (V omega) ^ 2 ∂mu ≤
          ∫ omega, (Wbar omega) ^ 2 ∂mu := hVsecond
      _ ≤ (1 + 6 / (k : Real)) *
          (∫ omega, Wbar omega ∂mu) ^ 2 := by
        simpa only [k] using hrawSecond
      _ ≤ (1 + 6 / (k : Real)) *
          ((∫ omega, V omega ∂mu) /
            (1 - 1 / (2 * alpha))) ^ 2 := by
        gcongr
      _ = ((1 + 6 / (k : Real)) /
          (1 - 1 / (2 * alpha)) ^ 2) *
            (∫ omega, V omega ∂mu) ^ 2 := by field_simp
      _ ≤ (1 + 8 / (k : Real)) *
          (∫ omega, V omega ∂mu) ^ 2 := by
        gcongr
        simpa only [k, alpha] using
          correctedRuntime_six_over_clipping_sq_le_eight (m := m) heps heps1

/-- Complete scalar-seven to clipped-factor-eight bridge for one phase. -/
theorem clipped_streamAverage_sq_moment_le_eight_of_scalar_seven
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {mu : Measure Path} [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hgL2 : MemLp g 2 mu)
    (hscalarSq : ∫ x, (g x) ^ 2 ∂mu ≤
      7 * (∫ x, g x ∂mu) ^ 2)
    (hW0 : ∀ omega,
      0 ≤ streamAverage (k := correctedRuntimeSamples m eps) g omega)
    (hWEpos : 0 < ∫ omega,
      streamAverage (k := correctedRuntimeSamples m eps) g omega
        ∂independentStreamLaw mu)
    {V : (Fin (correctedRuntimeSamples m eps) → Path) → Real}
    (hVdef : ∀ omega, V omega =
      min (streamAverage (k := correctedRuntimeSamples m eps) g omega)
        (correctedAlpha m eps *
          ∫ z, streamAverage (k := correctedRuntimeSamples m eps) g z
            ∂independentStreamLaw mu)) :
    Integrable (fun omega ↦ (V omega) ^ 2) (independentStreamLaw mu) ∧
      ∫ omega, (V omega) ^ 2 ∂independentStreamLaw mu ≤
        (1 + 8 / (correctedRuntimeSamples m eps : Real)) *
          (∫ omega, V omega ∂independentStreamLaw mu) ^ 2 := by
  let k := correctedRuntimeSamples m eps
  have hk0 : 0 < k := correctedRuntimeSamples_pos m eps
  let Wbar : (Fin k → Path) → Real := streamAverage (k := k) g
  have hWm : Measurable Wbar := measurable_streamAverage hg
  have hWint : Integrable Wbar (independentStreamLaw mu) :=
    (memLp_streamAverage (k := k) mu hgL2).integrable one_le_two
  have hW2int : Integrable (fun omega ↦ (Wbar omega) ^ 2)
      (independentStreamLaw mu) := integrable_streamAverage_sq mu hgL2
  have hraw := scalar_seven_to_streamAverage_six hk0 mu hg hgL2 hscalarSq
  exact clipped_sq_moment_le_eight_correctedRuntime_of_raw_six heps heps1
    hW0 hWm hWint hW2int hWEpos hraw hVdef

/-! ## Bias-aware corrected accuracy -/

/-- Bias-aware corrected `4/5` accuracy from scalar factor seven.

The theorem fixes the independent sample count to `correctedRuntimeSamples`.  It derives
all `L^2` and phase-moment premises for the clipped statistic.  The remaining explicit
binders are the pointwise statistic facts (`hWbar0`, clipping definition and corrected
caps), the exact-path coupling, the operational dependence package, and the raw
Gaussian telescope. -/
theorem corrected_independentStreams_accuracy_four_fifths_biasAware_of_scalarSeven
    {X Seed : Type*} [MeasurableSpace X] [MeasurableSpace Seed]
    {m : Nat} {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {mu0 : Measure X} [IsProbabilityMeasure mu0]
    {etaInner beta gamma requested : Real}
    (g : Nat → (Nat → X) → Real)
    (V W : Nat →
      (Fin (correctedRuntimeSamples m etaInner) → Nat → X) → Real)
    (heta : 0 < etaInner) (heta1 : etaInner ≤ 1)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hbudget : etaInner + beta + etaInner * beta ≤ requested)
    (hg : ∀ j, Measurable (g j))
    (hgL2 : ∀ j, MemLp (g j) 2 (inhomogeneousPathMeasure P mu0))
    (hscalarSq : ∀ j,
      ∫ x, (g j x) ^ 2 ∂inhomogeneousPathMeasure P mu0 ≤
        7 * (∫ x, g j x ∂inhomogeneousPathMeasure P mu0) ^ 2)
    (hWbar0 : ∀ j omega,
      0 ≤ streamAverage
        (k := correctedRuntimeSamples m etaInner) (g j) omega)
    (hWbarEpos : ∀ j, 0 <
      ∫ omega,
        streamAverage (k := correctedRuntimeSamples m etaInner) (g j) omega
        ∂independentPathLaw (correctedRuntimeSamples m etaInner) P mu0)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 <
      ∫ omega, V j omega
        ∂independentPathLaw (correctedRuntimeSamples m etaInner) P mu0)
    (hVcap : ∀ j omega, V j omega ≤
      2 * correctedAlpha m etaInner *
        ∫ z, V j z
          ∂independentPathLaw (correctedRuntimeSamples m etaInner) P mu0)
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤
      2 * correctedAlpha m etaInner ^ 2 *
        ∫ z, (V j z) ^ 2
          ∂independentPathLaw (correctedRuntimeSamples m etaInner) P mu0)
    (hVdef : ∀ j omega, V j omega =
      min (streamAverage
        (k := correctedRuntimeSamples m etaInner) (g j) omega)
        (correctedAlpha m etaInner *
          ∫ z, streamAverage
              (k := correctedRuntimeSamples m etaInner) (g j) z
            ∂independentPathLaw
              (correctedRuntimeSamples m etaInner) P mu0))
    (hWm : ∀ j, Measurable (W j))
    {Eexact : Set
      (Fin (correctedRuntimeSamples m etaInner) → Nat → X)}
    (hEexact : MeasurableSet Eexact)
    (hExactFail :
      (independentPathLaw (correctedRuntimeSamples m etaInner) P mu0).real
        Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact,
      phaseProduct
          (fun j ↦ streamAverage
            (k := correctedRuntimeSamples m etaInner) (g j)) m omega =
        phaseProduct W m omega)
    (hop : IndependentStreamOperational
      (correctedRuntimeSamples m etaInner) P Q seed mu0 V m etaInner)
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hclipBudget :
      (m : Real) / (2 * correctedAlpha m etaInner) + gamma +
        ((m : Real) / (2 * correctedAlpha m etaInner)) * gamma ≤ beta)
    (hrawTelescope : initialNormalizer *
      prefixMean
        (independentPathLaw (correctedRuntimeSamples m etaInner) P mu0)
        (fun j ↦ streamAverage
          (k := correctedRuntimeSamples m etaInner) (g j)) m ∈
      Ttc.relErr gamma volumeTarget) :
    4 / 5 ≤
      (independentPathLaw (correctedRuntimeSamples m etaInner) P mu0).real
        {omega | initialNormalizer * phaseProduct W m omega ∈
          Ttc.relErr requested volumeTarget} := by
  let k : Nat := correctedRuntimeSamples m etaInner
  let scalarLaw : Measure (Nat → X) := inhomogeneousPathMeasure P mu0
  let pathLaw : Measure (Fin k → Nat → X) := independentPathLaw k P mu0
  let Wbar : Nat → (Fin k → Nat → X) → Real :=
    fun j ↦ streamAverage (k := k) (g j)
  have hk0 : 0 < k := correctedRuntimeSamples_pos m etaInner
  have hk8Nat : 8 ≤ k := eight_le_correctedRuntimeSamples heta heta1
  have hk8 : (8 : Real) ≤ (k : Real) := by exact_mod_cast hk8Nat
  have halpha0 : 0 < correctedAlpha m etaInner := by
    have ha := correctedAlpha_ge_hundred_thousand (m := m) heta heta1
    linarith
  have halpha1 : 1 ≤ correctedAlpha m etaInner := by
    have ha := correctedAlpha_ge_hundred_thousand (m := m) heta heta1
    linarith
  have hWbarm : ∀ j, Measurable (Wbar j) :=
    fun j ↦ measurable_streamAverage (hg j)
  have hWint : ∀ j, Integrable (Wbar j) pathLaw := by
    intro j
    have h := (memLp_streamAverage (k := k) scalarLaw (hgL2 j)).integrable
      one_le_two
    simpa only [pathLaw, independentPathLaw, scalarLaw, Wbar] using h
  have hW2int : ∀ j, Integrable (fun omega ↦ (Wbar j omega) ^ 2) pathLaw := by
    intro j
    have h := integrable_streamAverage_sq (k := k) scalarLaw (hgL2 j)
    simpa only [pathLaw, independentPathLaw, scalarLaw, Wbar] using h
  have hrawSix : ∀ j,
      ∫ omega, (Wbar j omega) ^ 2 ∂pathLaw ≤
        (1 + 6 / (k : Real)) *
          (∫ omega, Wbar j omega ∂pathLaw) ^ 2 := by
    intro j
    have h := scalar_seven_to_streamAverage_six hk0 scalarLaw
      (hg j) (hgL2 j) (hscalarSq j)
    simpa only [pathLaw, independentPathLaw, scalarLaw, Wbar] using h
  have hrawEight : ∀ j,
      ∫ omega, (Wbar j omega) ^ 2 ∂pathLaw ≤
        (1 + 8 / (k : Real)) *
          (∫ omega, Wbar j omega ∂pathLaw) ^ 2 := by
    intro j
    refine (hrawSix j).trans ?_
    have hkpos : (0 : Real) < (k : Real) := by exact_mod_cast hk0
    have hsixEight : 6 / (k : Real) ≤ 8 / (k : Real) := by
      exact div_le_div_of_nonneg_right (by norm_num) hkpos.le
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hV2phase : ∀ j,
      Integrable (fun omega ↦ (V j omega) ^ 2) pathLaw ∧
        ∫ omega, (V j omega) ^ 2 ∂pathLaw ≤
          (1 + 8 / (k : Real)) *
            (∫ omega, V j omega ∂pathLaw) ^ 2 := by
    intro j
    have h := clipped_sq_moment_le_eight_correctedRuntime_of_raw_six
      (m := m) (eps := etaInner) heta heta1
      (mu := pathLaw) (Wbar := Wbar j) (V := V j)
      (by simpa only [k, Wbar] using hWbar0 j)
      (hWbarm j) (hWint j) (hW2int j)
      (by simpa only [k, pathLaw, Wbar] using hWbarEpos j)
      (hrawSix j)
      (by simpa only [k, pathLaw, Wbar] using hVdef j)
    simpa only [k] using h
  have hclip : ClippedPrefixTarget pathLaw V m
      initialNormalizer volumeTarget beta := by
    apply clippedPrefixTarget_of_rawSecondMoment_approx
      (mu := pathLaw) (V := V) (Wbar := Wbar)
      (k := (k : Real)) (alpha := correctedAlpha m etaInner)
      hk8 halpha0 halpha1 hinit hvolume hgamma hclipBudget
      (by simpa only [k, Wbar] using hWbar0)
      hWbarm hWint hW2int
      (by simpa only [k, pathLaw, Wbar] using hWbarEpos)
      hrawEight
      (by simpa only [k, pathLaw, Wbar] using hVdef)
    simpa only [k, pathLaw, Wbar] using hrawTelescope
  apply corrected_independentStreams_accuracy_four_fifths_biasAware
    (P := P) (Q := Q) (seed := seed) (mu0 := mu0)
    (V := V) (Wbar := Wbar) (W := W)
    heta heta1 hbeta hbudget (correctedRuntimeSamples_budget heta)
    hVm hV0 hEpos hVcap
    (by intro j; exact (hV2phase j).1)
    hV2cap hWbarm hWm
    (by simpa only [k, Wbar] using hWbar0)
    hWint
    (by simpa only [k, pathLaw, Wbar] using hWbarEpos)
    (by simpa only [k, pathLaw, Wbar] using hVdef)
    (by intro j; exact (hV2phase j).2)
    hEexact hExactFail hExact hop initialNormalizer volumeTarget hinit hvolume
  simpa only [pathLaw] using hclip

/-! ## Cost erasure and guarded public adapter -/

/-- Transfer a path-law accuracy theorem to the corresponding honest costed execution.
This is the exact erasure step used by the guarded Gaussian public constructor. -/
theorem independentCosted_accuracy_of_pathAccuracy
    {E : Type} [MeasurableSpace E]
    {k : Nat} {P : Nat → Kernel E E} [∀ i, IsMarkovKernel (P i)]
    {Qcost : Nat → Kernel E (ENNReal × E)} [∀ i, IsMarkovKernel (Qcost i)]
    {mu0 : Measure E} [IsProbabilityMeasure mu0]
    {est : (Fin k → Nat → E) → Real} (hest : Measurable est)
    (hforget : ∀ i x, Measure.map Prod.snd (Qcost i x) = P i x)
    {target : Set Real} (htarget : MeasurableSet target)
    (haccuracy : 4 / 5 ≤ (independentPathLaw k P mu0).real
      {omega | est omega ∈ target}) :
    4 / 5 ≤ (independentCostedLaw k Qcost mu0).real
      {omega | independentValue est omega ∈ target} := by
  let G : Set (Fin k → Nat → E) := {omega | est omega ∈ target}
  have hG : MeasurableSet G := htarget.preimage hest
  have hmap := map_independentStatePaths_independentCostedLaw
    k P Qcost mu0 hforget
  have heq : (independentCostedLaw k Qcost mu0).real
      (independentStatePaths ⁻¹' G) =
      (independentPathLaw k P mu0).real G := by
    change ((independentCostedLaw k Qcost mu0)
      (independentStatePaths ⁻¹' G)).toReal = _
    rw [← Measure.map_apply measurable_independentStatePaths hG, hmap]
    rfl
  change 4 / 5 ≤ (independentCostedLaw k Qcost mu0).real
    (independentStatePaths ⁻¹' G)
  rw [heq]
  exact haccuracy

/-- Guarded Gaussian expected-query oracle from valid-branch *path-law* accuracy.

The existing Gaussian guarded constructor asks for accuracy on the costed law.  This
adapter proves that premise by exact cost erasure, so the caller may supply the output of
`corrected_independentStreams_accuracy_four_fifths_biasAware_of_scalarSeven` directly.
Expected cost remains discharged by
`gaussianClosedRaw_expected_le_of_operational` (or an equivalent envelope theorem). -/
noncomputable def guardedExpectedQueryVolumeAlgorithm_gaussianCapped_of_pathAccuracy
    (hn : 1 ≤ n)
    (rawEnvelope : VolumeInput n → Real)
    (k m : VolumeInput n → Nat)
    (delta sigmaSq shrink : VolumeInput n → Nat → Real)
    (hdelta : ∀ a i, 0 < delta a i) (hshrink : ∀ a i, shrink a i ≠ 0)
    (steps : VolumeInput n → Nat → Nat → Nat)
    (retries : VolumeInput n → Nat → Nat)
    (fallback tail : ∀ a : VolumeInput n, Nat → Measure (ScoreSeed n))
    [∀ a i, IsProbabilityMeasure (fallback a i)]
    [∀ a i, IsProbabilityMeasure (tail a i)]
    (mu0 : ∀ a : VolumeInput n, Measure (ScoreSeed n))
    [∀ a, IsProbabilityMeasure (mu0 a)]
    (est : ∀ a, ClosedAdmissible a →
      (Fin (k a) → Nat → ScoreSeed n) → Real)
    (hest : ∀ a h, Measurable (est a h))
    (hexpected : ∀ a h,
      (∫⁻ omega, gaussianClosedRawCost k m a h omega
        ∂gaussianClosedRawLaw k m delta sigmaSq shrink hdelta hshrink steps
          retries fallback tail mu0 a h) ≤ ENNReal.ofReal (rawEnvelope a))
    (hpathAccuracy : ∀ a (h : ClosedAdmissible a),
      4 / 5 ≤
        (independentPathLaw (k a)
          (stateScheduleFromSeed
            (activeReferenceTailSchedule (m a)
              (warmFallbackSchedule a.1 h.2.2.2.2.1.measurableSet
                (delta a) (sigmaSq a) (shrink a) (hdelta a) (hshrink a)
                (steps a) (retries a) (fallback a)) (tail a)))
          (mu0 a)).real
          {omega | est a h omega ∈
            Icc ((1 - a.2.1) * (volume a.1).toReal)
              ((1 + a.2.1) * (volume a.1).toReal)}) :
    Ttc.ExpectedQueryVolumeAlgorithm n := by
  apply guardedExpectedQueryVolumeAlgorithm_gaussianCapped hn rawEnvelope k m
    delta sigmaSq shrink hdelta hshrink steps retries fallback tail mu0 est hest
    hexpected
  intro a h
  unfold gaussianClosedRawLaw gaussianClosedRawValue
  apply independentCosted_accuracy_of_pathAccuracy
    (P := stateScheduleFromSeed
      (activeReferenceTailSchedule (m a)
        (warmFallbackSchedule a.1 h.2.2.2.2.1.measurableSet
          (delta a) (sigmaSq a) (shrink a) (hdelta a) (hshrink a)
          (steps a) (retries a) (fallback a)) (tail a)))
    (Qcost := costedStateScheduleFromSeed
      (costedActiveReferenceTailSchedule (m a)
        (warmFallbackCostedSchedule a.1 h.2.2.2.2.1.measurableSet
          (delta a) (sigmaSq a) (shrink a) (hdelta a) (hshrink a)
          (steps a) (retries a) (fallback a)) (tail a)))
    (mu0 := mu0 a) (est := est a h) (hest a h)
  · intro i z
    apply map_snd_costedStateActiveReferenceTailSchedule
      (m a)
      (warmFallbackSchedule a.1 h.2.2.2.2.1.measurableSet
        (delta a) (sigmaSq a) (shrink a) (hdelta a) (hshrink a)
        (steps a) (retries a) (fallback a))
      (warmFallbackCostedSchedule a.1 h.2.2.2.2.1.measurableSet
        (delta a) (sigmaSq a) (shrink a) (hdelta a) (hshrink a)
        (steps a) (retries a) (fallback a))
      (tail a)
    intro j x
    exact map_snd_gaussianWarmFallbackCostedPhaseKernel
      h.2.2.2.2.1.measurableSet (delta a j) (sigmaSq a j) (shrink a j)
      (hdelta a j) (hshrink a j) (steps a j) (retries a j) (fallback a j) x
  · exact measurableSet_Icc
  · exact hpathAccuracy a h

#print axioms operational_phaseScore_sq_moment_le_factor
#print axioms operational_phaseScore_sq_moment_le_seven
#print axioms operational_path_phaseScore_memLp_and_sq_moment_le_factor
#print axioms scoreAware_phaseScore_slack_seven
#print axioms operational_path_phaseScore_scoreAware_active_seven
#print axioms scalar_seven_to_streamAverage_six
#print axioms clipped_sq_moment_le_eight_correctedRuntime_of_raw_six
#print axioms clipped_streamAverage_sq_moment_le_eight_of_scalar_seven
#print axioms corrected_independentStreams_accuracy_four_fifths_biasAware_of_scalarSeven
#print axioms independentCosted_accuracy_of_pathAccuracy
#print axioms guardedExpectedQueryVolumeAlgorithm_gaussianCapped_of_pathAccuracy

end Ttc.CVGaussianFactorSevenAssembly

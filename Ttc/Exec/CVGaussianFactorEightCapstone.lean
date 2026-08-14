import Ttc.Exec.CVGaussianWarmFallbackScoreMoment
import Ttc.Exec.CVGaussianScoreAwareMoment
import Ttc.Exec.CVIndependentStreamMoments
import Ttc.Exec.CVIndependentStreamBiasAccuracy
import Ttc.Volume.CVCorrectedRuntime

/-!
# Factor-eight Gaussian score and clipping bridge

The corrected estimator needs a relative second-moment factor `1 + 8/k` *after*
clipping.  A scalar factor `8` first becomes `1 + 7/k` after averaging `k`
independent complete streams.  This file records the remaining clipping step with its
honest numerical hypothesis: the truncation level must leave enough room to absorb the
loss in the clipped mean.

In particular, no claim is made here that the current choices
`correctedAlpha m eps` and `correctedRuntimeSamples m eps` satisfy that room
hypothesis; they do not in general, since the latter is just larger than the former.
-/

namespace Ttc.CVGaussianFactorEightCapstone

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVIndependentStreamMoments
open Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianWarmFallbackScoreMoment
open Ttc.CVScoreSeedPhaseKernel
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The TV-to-score-moment argument with an arbitrary target factor `T`.

This is the factor-parametric form of
`operational_phaseScore_sq_moment_le_nine`.  The additive TV error must fit in
the gap `T - C` between the exact score factor and the requested operational one.
-/
theorem operational_phaseScore_sq_moment_le_factor
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {m : Nat} {sigmaSq : Nat → Real} {i : Nat} {K : Set (State n)}
    {X : Ω → State n} {e : ENNReal}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (hX : Measurable X)
    (hTV : TVLe (Measure.map X mu) (coolLaw m sigmaSq K i) e) (he : e ≠ ⊤)
    {C T : Real} (hC0 : 0 ≤ C) (hCT : C ≤ T)
    (hexact : ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
        ∂(coolLaw m sigmaSq K i) ≤
      C * (∫ x, phaseScore m sigmaSq (interior K) i x
        ∂(coolLaw m sigmaSq K i)) ^ 2)
    (hslack : e.toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * T)) ≤
      (T - C) * (chain m sigmaSq K (i + 1) / chain m sigmaSq K i) ^ 2) :
    ∫ omega, phaseScore m sigmaSq (interior K) i (X omega) ^ 2 ∂mu ≤
      T * (∫ omega, phaseScore m sigmaSq (interior K) i (X omega) ∂mu) ^ 2 := by
  have hs : 0 ≤ T - C := sub_nonneg.2 hCT
  have hmain := phaseScore_interior_sq_moment_le_of_tvLe hsigma hKc hball hfin
    hKR hX hTV he hC0 hs hexact
  have heq : C + (T - C) = T := by ring
  have hslack' : e.toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 *
          (1 + 2 * (C + (T - C)))) ≤
      (T - C) * (chain m sigmaSq K (i + 1) / chain m sigmaSq K i) ^ 2 := by
    rw [heq]
    exact hslack
  simpa only [heq] using hmain hslack'

/-- Factor-eight specialization of the parametric TV transport theorem. -/
theorem operational_phaseScore_sq_moment_le_eight
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {m : Nat} {sigmaSq : Nat → Real} {i : Nat} {K : Set (State n)}
    {X : Ω → State n} {e : ENNReal}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (hX : Measurable X)
    (hTV : TVLe (Measure.map X mu) (coolLaw m sigmaSq K i) e) (he : e ≠ ⊤)
    {C : Real} (hC0 : 0 ≤ C) (hC8 : C ≤ 8)
    (hexact : ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
        ∂(coolLaw m sigmaSq K i) ≤
      C * (∫ x, phaseScore m sigmaSq (interior K) i x
        ∂(coolLaw m sigmaSq K i)) ^ 2)
    (hslack : e.toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 8)) ≤
      (8 - C) * (chain m sigmaSq K (i + 1) / chain m sigmaSq K i) ^ 2) :
    ∫ omega, phaseScore m sigmaSq (interior K) i (X omega) ^ 2 ∂mu ≤
      8 * (∫ omega, phaseScore m sigmaSq (interior K) i (X omega) ∂mu) ^ 2 := by
  exact operational_phaseScore_sq_moment_le_factor hsigma hKc hball hfin hKR hX
    hTV he hC0 hC8 hexact hslack

/-- Path-law version of the arbitrary-factor transport theorem. -/
theorem operational_path_phaseScore_memLp_and_sq_moment_le_factor
    {Seed : Type*} [MeasurableSpace Seed]
    {k mPhases : Nat}
    {Q : Nat → Kernel Seed (State n × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q)
      Q Prod.snd mu0 V mPhases eta)
    {chainLength : Nat} {sigmaSq : Nat → Real} {i : Nat} {K : Set (State n)}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : Measure.map Prod.fst (hop.tau i) = coolLaw chainLength sigmaSq K i)
    {C T : Real} (hC0 : 0 ≤ C) (hCT : C ≤ T)
    (hexact : ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
        ∂(coolLaw chainLength sigmaSq K i) ≤
      C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
        ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : (hop.mixError i).toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * T)) ≤
      (T - C) *
        (chain chainLength sigmaSq K (i + 1) / chain chainLength sigmaSq K i) ^ 2) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × Seed ↦
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧ ∫ omega, (g omega) ^ 2 ∂pathLaw ≤
      T * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  dsimp only
  let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let X : (Nat → State n × Seed) → State n := fun omega ↦ (omega (i + 1)).1
  have hfm := measurable_phaseScore (m := chainLength) (σsq := sigmaSq)
    (K := interior K) isOpen_interior.measurableSet i
  have hbound : ∀ x, |phaseScore chainLength sigmaSq (interior K) i x| ≤
      Real.exp (R ^ 2 / (2 * sigmaSq i)) := by
    intro x
    rw [abs_of_nonneg (phaseScore_nonneg chainLength sigmaSq (interior K) i x)]
    exact phaseScore_le hsigma (interior_subset.trans hKR) i x
  constructor
  · exact memLp_pathScore_of_bounded hfm hbound i
  · have htv := tvLe_operational_score_eval_succ hop i
    rw [htarget] at htv
    exact operational_phaseScore_sq_moment_le_factor hsigma hKc hball hfin hKR
      (by fun_prop) htv (hop.mixError_ne_top i) hC0 hCT hexact hslack

/-- Factor-eight moment slack for one phase. -/
noncomputable def phaseMomentSlackEight (chainLength : Nat)
    (sigmaSq : Nat → Real) (K : Set (State n)) (C : Nat → Real) (i : Nat) : Real :=
  (8 - C i) * (chain chainLength sigmaSq K (i + 1) /
    chain chainLength sigmaSq K i) ^ 2

/-- Factor-eight bounded-score multiplier for TV transport. -/
noncomputable def phaseScoreTransportBoundSqEight (R : Real)
    (sigmaSq : Nat → Real) (i : Nat) : Real :=
  Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 8)

theorem phaseMomentSlackEight_pos
    {chainLength : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    {C : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hC8 : ∀ i, C i < 8) (i : Nat) :
    0 < phaseMomentSlackEight chainLength sigmaSq K C i := by
  unfold phaseMomentSlackEight
  have hi := chain_pos (m := chainLength) hsigma hball hfin i
  have hi1 := chain_pos (m := chainLength) hsigma hball hfin (i + 1)
  exact mul_pos (sub_pos.2 (hC8 i)) (sq_pos_of_pos (div_pos hi1 hi))

theorem phaseScoreTransportBoundSqEight_pos
    {R : Real} {sigmaSq : Nat → Real} (i : Nat) :
    0 < phaseScoreTransportBoundSqEight R sigmaSq i := by
  unfold phaseScoreTransportBoundSqEight
  positivity

/-- The score-aware mixing share pays exactly for factor-eight transport. -/
theorem scoreAware_phaseScore_slack_eight
    {m k chainLength : Nat} {eps R : Real} {sigmaSq : Nat → Real}
    {K : Set (State n)} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hC8 : ∀ i, C i < 8) (i : Nat) :
    (Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError m k eps
        (phaseMomentSlackEight chainLength sigmaSq K C)
        (phaseScoreTransportBoundSqEight R sigmaSq) i).toReal *
      (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 8)) ≤
        (8 - C i) * (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2 := by
  exact Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError_mul_boundSq_le_slack
    heps heps1 (phaseMomentSlackEight_pos hsigma hball hfin hC8)
    (phaseScoreTransportBoundSqEight_pos (R := R) (sigmaSq := sigmaSq)) i

/-- Active factor-eight score moment for a score-aware operational path. -/
theorem operational_path_phaseScore_scoreAware_active_eight
    {Seed : Type*} [MeasurableSpace Seed]
    {k mPhases chainLength : Nat}
    {Q : Nat → Kernel Seed (State n × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q)
      Q Prod.snd mu0 V mPhases eta)
    {mParam kParam : Nat} {eps R : Real} {slack boundSq : Nat → Real}
    (hmixError : ∀ j, hop.mixError j =
      Ttc.CVGaussianWarmFallbackCappedOperational.activeReferenceMixError mPhases
        (Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError
          mParam kParam eps slack boundSq) j)
    {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (hslackDef : slack = phaseMomentSlackEight chainLength sigmaSq K C)
    (hboundDef : boundSq = phaseScoreTransportBoundSqEight R sigmaSq)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC8 : ∀ i, C i < 8)
    (hexact : ∀ i,
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂(coolLaw chainLength sigmaSq K i) ≤
        C i * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    {i : Nat} (hi : i + 1 < mPhases) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × Seed ↦
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧ ∫ omega, (g omega) ^ 2 ∂pathLaw ≤
      8 * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  apply operational_path_phaseScore_memLp_and_sq_moment_le_factor hop hsigma hKc
    hball hfin hKR (htarget i) (hC0 i) (hC8 i).le (hexact i)
  rw [hmixError i,
    Ttc.CVGaussianWarmFallbackCappedOperational.activeReferenceMixError,
    if_pos hi, hslackDef, hboundDef]
  exact scoreAware_phaseScore_slack_eight heps heps1 hsigma hball hfin hC8 i

/-! ## The parameter-compatible factor-seven route -/

/-- Factor-seven moment slack for one phase. -/
noncomputable def phaseMomentSlackSeven (chainLength : Nat)
    (sigmaSq : Nat → Real) (K : Set (State n)) (C : Nat → Real) (i : Nat) : Real :=
  (7 - C i) * (chain chainLength sigmaSq K (i + 1) /
    chain chainLength sigmaSq K i) ^ 2

/-- Factor-seven bounded-score multiplier for TV transport. -/
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
    (Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError m k eps
        (phaseMomentSlackSeven chainLength sigmaSq K C)
        (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal *
      (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 7)) ≤
        (7 - C i) * (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2 := by
  exact Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError_mul_boundSq_le_slack
    heps heps1 (phaseMomentSlackSeven_pos hsigma hball hfin hC7)
    (phaseScoreTransportBoundSqSeven_pos (R := R) (sigmaSq := sigmaSq)) i

/-- Active factor-seven score moment for the unchanged score-aware operational core. -/
theorem operational_path_phaseScore_scoreAware_active_seven
    {Seed : Type*} [MeasurableSpace Seed]
    {k mPhases chainLength : Nat}
    {Q : Nat → Kernel Seed (State n × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q)
      Q Prod.snd mu0 V mPhases eta)
    {mParam kParam : Nat} {eps R : Real} {slack boundSq : Nat → Real}
    (hmixError : ∀ j, hop.mixError j =
      Ttc.CVGaussianWarmFallbackCappedOperational.activeReferenceMixError mPhases
        (Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError
          mParam kParam eps slack boundSq) j)
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
    MemLp g 2 pathLaw ∧ ∫ omega, (g omega) ^ 2 ∂pathLaw ≤
      7 * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  apply operational_path_phaseScore_memLp_and_sq_moment_le_factor hop hsigma hKc
    hball hfin hKR (htarget i) (hC0 i) (hC7 i).le (hexact i)
  rw [hmixError i,
    Ttc.CVGaussianWarmFallbackCappedOperational.activeReferenceMixError,
    if_pos hi, hslackDef, hboundDef]
  exact scoreAware_phaseScore_slack_seven heps heps1 hsigma hball hfin hC7 i

variable {Path : Type*} [MeasurableSpace Path]

/-- A scalar factor `8` becomes the raw empirical factor `1 + 7/k` on `k`
independent complete streams. -/
theorem integral_streamAverage_sq_le_eight
    {k : Nat} (hk : 0 < k) (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hL2 : MemLp g 2 mu)
    {mean : Real} (hmean : ∫ x, g x ∂mu = mean)
    (hsq : ∫ x, (g x) ^ 2 ∂mu ≤ 8 * mean ^ 2) :
    ∫ omega, (streamAverage (k := k) g omega) ^ 2
        ∂(independentStreamLaw mu) ≤
      (1 + 7 / (k : Real)) * mean ^ 2 := by
  simpa only [show (8 : Real) - 1 = 7 by norm_num] using
    integral_streamAverage_sq_le hk mu hg hL2 hmean hsq

/-- A scalar factor `7` becomes `1 + 6/k` after independent averaging. -/
theorem integral_streamAverage_sq_le_seven
    {k : Nat} (hk : 0 < k) (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hL2 : MemLp g 2 mu)
    {mean : Real} (hmean : ∫ x, g x ∂mu = mean)
    (hsq : ∫ x, (g x) ^ 2 ∂mu ≤ 7 * mean ^ 2) :
    ∫ omega, (streamAverage (k := k) g omega) ^ 2
        ∂(independentStreamLaw mu) ≤
      (1 + 6 / (k : Real)) * mean ^ 2 := by
  simpa only [show (7 : Real) - 1 = 6 by norm_num] using
    integral_streamAverage_sq_le hk mu hg hL2 hmean hsq

/-- The extra `2/k` between the raw factor `1 + 6/k` and the corrected target
`1 + 8/k` absorbs clipping whenever `k ≤ alpha + 2` and `alpha ≥ 10`. -/
theorem six_over_clipping_sq_le_eight
    {k alpha : Real} (hk : 8 ≤ k) (halpha : 10 ≤ alpha)
    (hupper : k ≤ alpha + 2) :
    (1 + 6 / k) / (1 - 1 / (2 * alpha)) ^ 2 ≤ 1 + 8 / k := by
  have hk0 : 0 < k := by linarith
  have ha0 : 0 < alpha := by linarith
  have hd0 : 0 < 1 - 1 / (2 * alpha) := by
    rw [sub_pos, div_lt_one (by positivity)]
    linarith
  rw [div_le_iff₀ (sq_pos_of_pos hd0)]
  field_simp [ne_of_gt hk0, ne_of_gt ha0]
  nlinarith [mul_nonneg (sub_nonneg.2 (show 0 ≤ alpha + 2 - k by linarith))
      (show 0 ≤ 4 * alpha - 1 by linarith),
    sq_nonneg (2 * alpha - 10)]

/-- The repository's corrected truncation parameter is far above the small constant
needed by `six_over_clipping_sq_le_eight`. -/
theorem ten_le_correctedAlpha {m : Nat} {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    10 ≤ Ttc.CVCorrected.correctedAlpha m eps := by
  have he2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have he2le : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg eps]
  rw [Ttc.CVCorrected.correctedAlpha, le_div_iff₀ he2]
  have hm : (1 : Real) ≤ (m : Real) + 1 := by positivity
  nlinarith

/-- Actual `correctedRuntimeSamples` arithmetic discharges the clipping-room
inequality for the factor-seven route. -/
theorem correctedRuntimeSamples_six_over_clipping_sq_le_eight
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    let k := Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps
    let alpha := Ttc.CVCorrected.correctedAlpha m eps
    (1 + 6 / (k : Real)) / (1 - 1 / (2 * alpha)) ^ 2 ≤
      1 + 8 / (k : Real) := by
  dsimp only
  apply six_over_clipping_sq_le_eight
  · have hk : 0 < Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps :=
      Ttc.CVCorrectedRuntime.correctedRuntimeSamples_pos m eps
    have halpha := ten_le_correctedAlpha (m := m) heps heps1
    have hkUpper := Ttc.CVCorrectedRuntime.correctedRuntimeSamples_cast_lt
      (m := m) heps
    rw [Ttc.CVCorrected.correctedAlpha] at halpha hkUpper ⊢
    exact_mod_cast (show 8 ≤ Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps by
      by_contra h
      have hkLe : Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps ≤ 7 := by omega
      have hkCast : (Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps : Real) ≤ 7 := by
        exact_mod_cast hkLe
      have hbase : (10 : Real) ≤
          100000 * ((m : Real) + 1) / eps ^ 2 := halpha
      linarith)
  · exact ten_le_correctedAlpha heps heps1
  · exact (Ttc.CVCorrectedRuntime.correctedRuntimeSamples_cast_lt
      (m := m) heps).le

/-- Numerical room needed to turn the raw empirical factor `1 + 7/k` into the
post-clipping factor `1 + 8/k`.

The convenient sufficient condition `k + 8 ≤ alpha` is deliberately visible.
-/
theorem seven_over_clipping_sq_le_eight
    {k alpha : Real} (hk : 8 ≤ k) (hroom : k + 8 ≤ alpha) :
    (1 + 7 / k) / (1 - 1 / (2 * alpha)) ^ 2 ≤ 1 + 8 / k := by
  have hk0 : 0 < k := by linarith
  have ha0 : 0 < alpha := by linarith
  have hd0 : 0 < 1 - 1 / (2 * alpha) := by
    rw [sub_pos, div_lt_one (by positivity)]
    linarith
  rw [div_le_iff₀ (sq_pos_of_pos hd0)]
  field_simp [ne_of_gt hk0, ne_of_gt ha0]
  nlinarith [sq_nonneg (alpha - (k + 8)),
    mul_nonneg (sub_nonneg.2 hroom) (by linarith : 0 ≤ alpha + k)]

/-- Clipping an empirical score preserves the corrected factor `1 + 8/k`, provided
the explicit numerical room from `seven_over_clipping_sq_le_eight` is available.

The result also returns square-integrability of the clipped score, which is another
premise of corrected `lem:accuracy`.
-/
theorem clipped_sq_moment_le_eight_of_raw_seven
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {k : Nat} {alpha : Real} {Wbar V : Ω → Real}
    (hk : 8 ≤ k) (hroom : (k : Real) + 8 ≤ alpha)
    (hW0 : ∀ omega, 0 ≤ Wbar omega) (hWm : Measurable Wbar)
    (hWint : Integrable Wbar mu)
    (hW2int : Integrable (fun omega ↦ (Wbar omega) ^ 2) mu)
    (hWEpos : 0 < ∫ omega, Wbar omega ∂mu)
    (hrawSecond : ∫ omega, (Wbar omega) ^ 2 ∂mu ≤
      (1 + 7 / (k : Real)) * (∫ omega, Wbar omega ∂mu) ^ 2)
    (hVdef : ∀ omega, V omega = min (Wbar omega)
      (alpha * ∫ z, Wbar z ∂mu)) :
    Integrable (fun omega ↦ (V omega) ^ 2) mu ∧
      ∫ omega, (V omega) ^ 2 ∂mu ≤
        (1 + 8 / (k : Real)) * (∫ omega, V omega ∂mu) ^ 2 := by
  have hkR : (8 : Real) ≤ (k : Real) := by exact_mod_cast hk
  have ha0 : 0 < alpha := by linarith
  have hVeq : V = fun omega ↦ min (Wbar omega)
      (alpha * ∫ z, Wbar z ∂mu) := funext hVdef
  have hthreshold0 : 0 ≤ alpha * ∫ z, Wbar z ∂mu :=
    mul_nonneg ha0.le hWEpos.le
  have hV0 : ∀ omega, 0 ≤ V omega := fun omega ↦ by
    rw [hVdef omega]
    exact le_min (hW0 omega) hthreshold0
  have hVm : Measurable V := by
    rw [hVeq]
    exact hWm.min measurable_const
  have hVW : ∀ omega, V omega ≤ Wbar omega := fun omega ↦ by
    rw [hVdef omega]
    exact min_le_left _ _
  have hV2int : Integrable (fun omega ↦ (V omega) ^ 2) mu := by
    refine Integrable.mono' hW2int (hVm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (hV0 omega) (hW0 omega)).2 (hVW omega)
  constructor
  · exact hV2int
  · have hlower :
        (1 - 1 / (2 * alpha)) * (∫ omega, Wbar omega ∂mu) ≤
          ∫ omega, V omega ∂mu := by
      have hk7 : (7 : Real) ≤ (k : Real) := by linarith
      have h := expect_trunc_ge_half_of_seven_le ha0 hk7 hW0 hWm hWint hW2int
        hWEpos hrawSecond
      rw [hVeq]
      exact h
    have hd0 : 0 < 1 - 1 / (2 * alpha) := by
      rw [sub_pos, div_lt_one (by positivity)]
      linarith
    have hVsecond : ∫ omega, (V omega) ^ 2 ∂mu ≤
        ∫ omega, (Wbar omega) ^ 2 ∂mu :=
      integral_mono hV2int hW2int fun omega ↦
        (sq_le_sq₀ (hV0 omega) (hW0 omega)).2 (hVW omega)
    have hmean : ∫ omega, Wbar omega ∂mu ≤
        (∫ omega, V omega ∂mu) / (1 - 1 / (2 * alpha)) := by
      rw [le_div_iff₀ hd0]
      simpa [mul_comm] using hlower
    have hmean0 : 0 ≤ ∫ omega, Wbar omega ∂mu := hWEpos.le
    have hVmean0 : 0 ≤ ∫ omega, V omega ∂mu :=
      integral_nonneg hV0
    calc
      ∫ omega, (V omega) ^ 2 ∂mu ≤
          ∫ omega, (Wbar omega) ^ 2 ∂mu := hVsecond
      _ ≤ (1 + 7 / (k : Real)) *
          (∫ omega, Wbar omega ∂mu) ^ 2 := hrawSecond
      _ ≤ (1 + 7 / (k : Real)) *
          ((∫ omega, V omega ∂mu) / (1 - 1 / (2 * alpha))) ^ 2 := by
        gcongr
      _ = ((1 + 7 / (k : Real)) /
          (1 - 1 / (2 * alpha)) ^ 2) *
            (∫ omega, V omega ∂mu) ^ 2 := by field_simp
      _ ≤ (1 + 8 / (k : Real)) *
          (∫ omega, V omega ∂mu) ^ 2 := by
        gcongr
        exact seven_over_clipping_sq_le_eight hkR hroom

#print axioms operational_phaseScore_sq_moment_le_factor
#print axioms operational_phaseScore_sq_moment_le_eight
#print axioms operational_path_phaseScore_memLp_and_sq_moment_le_factor
#print axioms scoreAware_phaseScore_slack_eight
#print axioms operational_path_phaseScore_scoreAware_active_eight
#print axioms integral_streamAverage_sq_le_eight
#print axioms seven_over_clipping_sq_le_eight
#print axioms clipped_sq_moment_le_eight_of_raw_seven

end Ttc.CVGaussianFactorEightCapstone

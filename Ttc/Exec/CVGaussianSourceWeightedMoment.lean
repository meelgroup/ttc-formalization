import Ttc.Exec.CVSourceWeightedClipping
import Ttc.Exec.CVGaussianFactorSevenAssembly
import Ttc.Exec.CVGaussianWarmFallbackScoreMoment

/-!
# Source-weighted operational Gaussian moments

Instead of transporting every scalar score to the coarse factor seven, transport phase
`i` from its exact factor `C i` only to `2*C i - 1`.  The TV slack is `C i - 1`, which
is positive for every genuine cooling phase.  Averaging `2*k` streams then gives exactly
the original source empirical factor with effective sample count `k`.
-/

set_option autoImplicit false

namespace Ttc.CVGaussianSourceWeightedMoment

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVIndependentStreamMoments
open Ttc.CVGaussianFactorSevenAssembly Ttc.CVGaussianScoreAwareParameters
open Ttc.CVIndependentStreamDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVSourceWeightedClipping Ttc.CVHybridSchedule
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianWarmFallbackScoreMoment
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def relativePhaseSlack (chainLength : Nat)
    (sigmaSq : Nat -> Real) (K : Set (State n)) (C : Nat -> Real)
    (i : Nat) : Real :=
  (C i - 1) *
    (chain chainLength sigmaSq K (i + 1) /
      chain chainLength sigmaSq K i) ^ 2

noncomputable def relativePhaseBoundSq (R : Real)
    (sigmaSq : Nat -> Real) (C : Nat -> Real) (i : Nat) : Real :=
  Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 *
    (1 + 2 * (2 * C i - 1))

theorem relativePhaseSlack_pos
    {chainLength : Nat} {sigmaSq : Nat -> Real} {K : Set (State n)}
    {C : Nat -> Real}
    (hsigma : forall j, 0 < sigmaSq j)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hC1 : forall i, 1 < C i) (i : Nat) :
    0 < relativePhaseSlack chainLength sigmaSq K C i := by
  unfold relativePhaseSlack
  exact mul_pos (sub_pos.mpr (hC1 i))
    (sq_pos_of_pos (div_pos (chain_pos hsigma hball hfin (i + 1))
      (chain_pos hsigma hball hfin i)))

theorem relativePhaseBoundSq_pos
    {R : Real} {sigmaSq : Nat -> Real} {C : Nat -> Real}
    (hC1 : forall i, 1 < C i) (i : Nat) :
    0 < relativePhaseBoundSq R sigmaSq C i := by
  unfold relativePhaseBoundSq
  have : 0 < 1 + 2 * (2 * C i - 1) := by nlinarith [hC1 i]
  positivity

/-- Active operational phase moment with source-relative, rather than uniform, slack. -/
theorem operational_path_phaseScore_scoreAware_relative
    {Seed : Type*} [MeasurableSpace Seed]
    {k mPhases chainLength : Nat}
    {Q : Nat -> Kernel Seed (State n × Seed)} [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat -> (Fin k -> Nat -> State n × Seed) -> Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q)
      Q Prod.snd mu0 V mPhases eta)
    {mParam kParam : Nat} {eps R : Real} {slack boundSq : Nat -> Real}
    (hmixError : forall j, hop.mixError j = activeReferenceMixError mPhases
      (scoreAwareMixError mParam kParam eps slack boundSq) j)
    {sigmaSq : Nat -> Real} {K : Set (State n)} {C : Nat -> Real}
    (hslackDef : slack = relativePhaseSlack chainLength sigmaSq K C)
    (hboundDef : boundSq = relativePhaseBoundSq R sigmaSq C)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hsigma : forall j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : forall i, Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    (hC1 : forall i, 1 < C i)
    (hexact : forall i,
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂coolLaw chainLength sigmaSq K i <=
        C i * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂coolLaw chainLength sigmaSq K i) ^ 2)
    {i : Nat} (hi : i + 1 < mPhases) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat -> State n × Seed =>
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw /\
      (∫ omega, (g omega) ^ 2 ∂pathLaw) <=
        (2 * C i - 1) * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  apply operational_path_phaseScore_memLp_and_sq_moment_le_factor hop hsigma hKc
    hball hfin hKR (htarget i) (by linarith [hC1 i])
    (by linarith [hC1 i]) (hexact i)
  rw [hmixError i, activeReferenceMixError, if_pos hi, hslackDef, hboundDef]
  change (scoreAwareMixError mParam kParam eps
      (relativePhaseSlack chainLength sigmaSq K C)
      (relativePhaseBoundSq R sigmaSq C) i).toReal *
        relativePhaseBoundSq R sigmaSq C i <= _
  have h := scoreAwareMixError_mul_boundSq_le_slack
    (m := mParam) (k := kParam) (eps := eps)
    (slack := relativePhaseSlack chainLength sigmaSq K C)
    (boundSq := relativePhaseBoundSq R sigmaSq C) heps heps1
    (relativePhaseSlack_pos (chainLength := chainLength) hsigma hball hfin hC1)
    (relativePhaseBoundSq_pos (R := R) (sigmaSq := sigmaSq) hC1) i
  exact h.trans_eq (by unfold relativePhaseSlack; ring)

/-! ## TV-robust target variants

The operational sampler may target a truncated Gaussian law rather than the full
`coolLaw`.  The next-score TV estimate compares the actual law with `hop.tau`; the
additional target-TV premise below spends the truncation budget by the triangle
inequality before applying the bounded-observable moment transport theorem.
-/

theorem operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV
    {Seed : Type*} [MeasurableSpace Seed]
    {k mPhases chainLength : Nat}
    {Q : Nat -> Kernel Seed (State n × Seed)} [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat -> (Fin k -> Nat → State n × Seed) -> Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q)
      Q Prod.snd mu0 V mPhases eta)
    {sigmaSq : Nat -> Real} {i : Nat} {K : Set (State n)}
    (hsigma : forall j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    {targetError : ENNReal}
    (htargetTV : TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw chainLength sigmaSq K i) targetError)
    (htargetError : targetError ≠ ⊤)
    {C T : Real} (hC0 : 0 ≤ C) (hCT : C ≤ T)
    (hexact : ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
        ∂(coolLaw chainLength sigmaSq K i) ≤
      C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
        ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : (hop.mixError i + targetError).toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * T)) ≤
      (T - C) *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × Seed =>
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧
      (∫ omega, (g omega) ^ 2 ∂pathLaw) ≤
        T * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  dsimp only
  let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let X : (Nat → State n × Seed) → State n :=
    fun omega => (omega (i + 1)).1
  have hfm := measurable_phaseScore (m := chainLength)
    (σsq := sigmaSq) (K := interior K) isOpen_interior.measurableSet i
  have hbound : ∀ x, |phaseScore chainLength sigmaSq (interior K) i x| ≤
      Real.exp (R ^ 2 / (2 * sigmaSq i)) := by
    intro x
    rw [abs_of_nonneg (phaseScore_nonneg chainLength sigmaSq (interior K) i x)]
    exact phaseScore_le hsigma (interior_subset.trans hKR) i x
  constructor
  · exact memLp_pathScore_of_bounded hfm hbound i
  · have htv0 := tvLe_operational_score_eval_succ hop i
    have htv : TVLe (Measure.map X pathLaw)
        (coolLaw chainLength sigmaSq K i)
        (hop.mixError i + targetError) := by
      exact htv0.trans htargetTV
    exact operational_phaseScore_sq_moment_le_factor hsigma hKc hball hfin hKR
      (by fun_prop) htv
      (ENNReal.add_ne_top.2 ⟨hop.mixError_ne_top i, htargetError⟩)
      hC0 hCT hexact hslack

theorem operational_path_phaseScore_scoreAware_relative_of_targetTV
    {Seed : Type*} [MeasurableSpace Seed]
    {k mPhases chainLength : Nat}
    {Q : Nat -> Kernel Seed (State n × Seed)} [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat -> (Fin k -> Nat -> State n × Seed) -> Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q)
      Q Prod.snd mu0 V mPhases eta)
    {sigmaSq : Nat -> Real} {K : Set (State n)} {C : Nat -> Real}
    {targetError : Nat -> ENNReal}
    (hsigma : forall j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (htargetTV : forall i, TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw chainLength sigmaSq K i) (targetError i))
    (htargetError : forall i, targetError i ≠ ⊤)
    (hC1 : forall i, 1 < C i)
    (hexact : forall i,
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂(coolLaw chainLength sigmaSq K i) <=
        C i * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : forall i,
      (hop.mixError i + targetError i).toReal *
          (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 *
            (1 + 2 * (2 * C i - 1))) <=
        (C i - 1) *
          (chain chainLength sigmaSq K (i + 1) /
            chain chainLength sigmaSq K i) ^ 2)
    {i : Nat} (hi : i + 1 < mPhases) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × Seed =>
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧
      (∫ omega, (g omega) ^ 2 ∂pathLaw) ≤
        (2 * C i - 1) * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  have hslack' : (hop.mixError i + targetError i).toReal *
      (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 *
        (1 + 2 * (2 * C i - 1))) <=
      (2 * C i - 1 - C i) *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2 := by
    convert hslack i using 1 <;> ring
  have h := operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV
    (C := C i) (T := 2 * C i - 1) hop hsigma hKc hball hfin hKR
      (htargetTV i) (htargetError i)
      (by linarith [hC1 i]) (by linarith [hC1 i]) (hexact i) hslack'
  simpa only [sub_eq_add_neg] using h

/-! Averaging `2*k` source-relative scalar scores recovers exactly the source empirical
phase factor at sample count `k`. -/
theorem relativeScalar_to_doubledStreamAverage_sourceFactor
    {Path : Type*} [MeasurableSpace Path]
    {n k : Nat} (hk : 0 < k) {N s0 : Real} (i : Nat)
    (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path -> Real} (hg : Measurable g) (hgL2 : MemLp g 2 mu)
    {mean : Real} (hmean : ∫ x, g x ∂mu = mean)
    (hsq : ∫ x, (g x) ^ 2 ∂mu <=
      (2 * phaseVarFactor n 1 N s0 i - 1) * mean ^ 2) :
    (∫ omega, (streamAverage (k := 2 * k) g omega) ^ 2
        ∂independentStreamLaw mu) <=
      phaseVarFactor n (k : Real) N s0 i * mean ^ 2 := by
  have havg := integral_streamAverage_sq_le (show 0 < 2 * k by omega)
    mu hg hgL2 hmean hsq
  rw [doubledSamples_relativeSlack_factor i hk] at havg
  exact havg

/-- Complete one-phase bridge: source-relative scalar transport, doubled independent
averaging, and clipping yield the exact nonuniform factor consumed by the corrected
weighted recursion. -/
theorem relativeScalar_doubledAverage_clippedFactor
    {Path : Type*} [MeasurableSpace Path]
    {n k : Nat} (hn : 1 <= n) (hk : 0 < k)
    {N s0 alpha : Real} (hN : 0 < N) (hs0 : 0 < s0) (i : Nat)
    (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path -> Real} (hg : Measurable g) (hgL2 : MemLp g 2 mu)
    {mean : Real} (hmean : ∫ x, g x ∂mu = mean)
    (hsq : ∫ x, (g x) ^ 2 ∂mu <=
      (2 * phaseVarFactor n 1 N s0 i - 1) * mean ^ 2)
    (halpha : 1 < alpha)
    (hfactorTwo : phaseVarFactor n (k : Real) N s0 i <= 2)
    {V : (Fin (2 * k) -> Path) -> Real}
    (hW0 : forall omega,
      0 <= streamAverage (k := 2 * k) g omega)
    (hWEpos : 0 < ∫ omega, streamAverage (k := 2 * k) g omega
      ∂independentStreamLaw mu)
    (hVdef : forall omega, V omega =
      min (streamAverage (k := 2 * k) g omega)
        (alpha * ∫ z, streamAverage (k := 2 * k) g z
          ∂independentStreamLaw mu)) :
    Integrable (fun omega => (V omega) ^ 2) (independentStreamLaw mu) /\
      (∫ omega, (V omega) ^ 2 ∂independentStreamLaw mu) <=
        clippedFactor alpha (phaseVarFactor n (k : Real) N s0 i) *
          (∫ omega, V omega ∂independentStreamLaw mu) ^ 2 := by
  let Wbar := streamAverage (k := 2 * k) g
  have hWm : Measurable Wbar := measurable_streamAverage hg
  have hWint : Integrable Wbar (independentStreamLaw mu) :=
    (memLp_streamAverage (k := 2 * k) mu hgL2).integrable one_le_two
  have hW2int : Integrable (fun omega => (Wbar omega) ^ 2)
      (independentStreamLaw mu) := integrable_streamAverage_sq mu hgL2
  have hraw := relativeScalar_to_doubledStreamAverage_sourceFactor hk i mu hg hgL2
    hmean hsq
  have hmeanAvg := integral_streamAverage (show 0 < 2 * k by omega) mu hg
    (hgL2.integrable one_le_two)
  have hraw' : (∫ omega, (Wbar omega) ^ 2 ∂independentStreamLaw mu) <=
      phaseVarFactor n (k : Real) N s0 i *
        (∫ omega, Wbar omega ∂independentStreamLaw mu) ^ 2 := by
    dsimp only [Wbar]
    rw [hmeanAvg, hmean]
    exact hraw
  apply clipped_sq_moment_le_factor halpha
  · exact zero_le_one.trans (phaseVarFactor_one_le hn
      (by exact_mod_cast hk) hN hs0 i)
  · exact hfactorTwo
  · exact hW0
  · exact hWm
  · exact hWint
  · exact hW2int
  · exact hWEpos
  · exact hraw'
  · exact hVdef

#print axioms operational_path_phaseScore_scoreAware_relative
#print axioms relativeScalar_to_doubledStreamAverage_sourceFactor
#print axioms relativeScalar_doubledAverage_clippedFactor

end Ttc.CVGaussianSourceWeightedMoment

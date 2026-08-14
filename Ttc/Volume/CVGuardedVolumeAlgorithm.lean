/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVConcreteRunwiseCapstone
import Ttc.Volume.CVBodyRegularization

/-!
# Guarded public volume algorithm from the concrete adaptive laws

The radius-four truncation theorem has a fixed dimension-dependent error floor.  Therefore
the public constructor below makes its exact input-indexed tail guard explicit.  Invalid
accuracy/confidence/body inputs are totalized by a Dirac law and a zero estimator; this is
semantically irrelevant because `VolumeAlgorithm.correct` quantifies only over admissible
inputs.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive

variable {n : Nat}

abbrev VolumeInput (n : Nat) := Set (Space n) × Real × Real

noncomputable def guardedAccuracy (a : VolumeInput n) : Real := min a.2.1 1
noncomputable def guardedEta (a : VolumeInput n) : Real := guardedAccuracy a / 4
noncomputable def guardedC (a : VolumeInput n) : Real := Ttc.CV.cvRadius a.1
noncomputable def guardedS0 (a : VolumeInput n) : Real :=
  polynomialEndpointSigmaSq n (guardedEta a)
noncomputable def guardedJ (a : VolumeInput n) : Nat :=
  adaptiveTerminalChunk (guardedC a ^ 2 * n) (guardedS0 a)
noncomputable def guardedM (a : VolumeInput n) : Nat :=
  adaptiveChunkOffset (guardedC a ^ 2 * n) (guardedS0 a) (guardedJ a)
noncomputable def guardedK (a : VolumeInput n) : Nat :=
  concreteEstimatorSamples (guardedJ a) (guardedAccuracy a / 4)
noncomputable def guardedR (a : VolumeInput n) : Nat := concreteRunwiseReps a.2.2
noncomputable def guardedMix (a : VolumeInput n) : Real :=
  runwiseChosenMixError (guardedM a) (guardedK a)
noncomputable def guardedSteps (a : VolumeInput n) : Fin (guardedM a + 1) -> Nat :=
  runwiseMixingSteps n (guardedC a ^ 2 * n) (guardedS0 a) (guardedM a) (guardedK a)

/-- The sole residual feasibility condition, with no confidence/repetition factor. -/
def ConcreteRunwiseTailGuard (a : VolumeInput n) : Prop :=
  RunwiseRadiusFourTailFits n (guardedM a) (guardedK a)

abbrev GuardedRunCoin (n : Nat) (a : VolumeInput n) :=
  Fin (guardedR a) -> Fin (guardedM a + 1) -> Fin (guardedK a) -> Space n

noncomputable def guardedPhaseLaw (a : VolumeInput n) :
    Fin (guardedM a + 1) -> Fin (guardedK a) -> Measure (Space n) :=
  fun i _ => adaptiveTerminalWarmLaw (guardedC a ^ 2 * n) (guardedS0 a)
    endpointRho a.1 (guardedSteps a) i

noncomputable def guardedRawRunLaw (a : VolumeInput n) : Measure (GuardedRunCoin n a) :=
  runMeasure (packedPhaseLaw
    (Ttc.CVRunwise.iidRunFamily (r := guardedR a) (guardedPhaseLaw a)))

/-- Total law for every input, including invalid ones. -/
noncomputable def guardedRunLaw (a : VolumeInput n) : Measure (GuardedRunCoin n a) :=
  by
    classical
    exact if IsProbabilityMeasure (guardedRawRunLaw a) then guardedRawRunLaw a
      else Measure.dirac (fun _ _ _ => 0)

instance isProbabilityMeasure_guardedRunLaw (a : VolumeInput n) :
    IsProbabilityMeasure (guardedRunLaw a) := by
  classical
  unfold guardedRunLaw
  split_ifs with h
  · exact h
  · infer_instance

theorem guardedRunLaw_eq_raw (a : VolumeInput n)
    (h : IsProbabilityMeasure (guardedRawRunLaw a)) :
    guardedRunLaw a = guardedRawRunLaw a := by
  classical
  simp [guardedRunLaw, h]

noncomputable def guardedScore (a : VolumeInput n) :
    Fin (guardedM a + 1) -> Fin (guardedK a) -> Space n -> Real :=
  fun i _ => phaseScore (guardedM a + 1)
    (adaptiveSigmaSq (guardedC a ^ 2 * n) (guardedS0 a)) a.1 i

noncomputable def guardedRawEstimator (a : VolumeInput n) (omega : GuardedRunCoin n a) : Real :=
  medianSel fun t =>
    (2 * Real.pi * guardedS0 a) ^ ((n : Real) / 2) *
      ∏ i, oneRunPhaseAvg (guardedK a) (guardedScore a) i (omega t)

/-- Total measurable estimator: nonmeasurable bodies are outside the public correctness
contract and return zero. -/
noncomputable def guardedEstimator (a : VolumeInput n) (omega : GuardedRunCoin n a) : Real :=
  by
    classical
    exact if MeasurableSet a.1 then guardedRawEstimator a omega else 0

theorem measurable_guardedRawEstimator (a : VolumeInput n) (hKm : MeasurableSet a.1) :
    Measurable (guardedRawEstimator a) := by
  unfold guardedRawEstimator
  apply measurable_medianSel
  intro t
  apply measurable_const.mul
  apply Finset.measurable_fun_prod
  intro i hi
  exact (measurable_oneRunPhaseAvg
    (fun i l => measurable_phaseScore hKm i) i).comp (measurable_pi_apply t)

theorem measurable_guardedEstimator (a : VolumeInput n) : Measurable (guardedEstimator a) := by
  classical
  by_cases hKm : MeasurableSet a.1
  · unfold guardedEstimator
    simpa only [if_pos hKm] using measurable_guardedRawEstimator a hKm
  · unfold guardedEstimator
    simpa only [if_neg hKm] using (measurable_const : Measurable (fun _ : GuardedRunCoin n a => (0 : Real)))

theorem guardedEstimator_eq_raw (a : VolumeInput n) (hKm : MeasurableSet a.1) :
    guardedEstimator a = guardedRawEstimator a := by
  classical
  unfold guardedEstimator
  funext omega
  simp only [if_pos hKm]

/-- On admissible closed inputs, the raw dependent run law is a probability measure. -/
theorem isProbabilityMeasure_guardedRawRunLaw
    (hn : 21 <= n) (a : VolumeInput n)
    (heps : 0 < a.2.1)
    (hKc : Convex Real a.1) (hKcl : IsClosed a.1)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ a.1) (hfin : volume a.1 ≠ ⊤) :
    IsProbabilityMeasure (guardedRawRunLaw a) := by
  have hn2 : 2 <= n := by omega
  have hn1 : 1 <= n := by omega
  have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
  have hacc : 0 < guardedAccuracy a := by
    unfold guardedAccuracy
    positivity
  have hacc1 : guardedAccuracy a <= 1 := min_le_right _ _
  have heta : 0 < guardedEta a := by unfold guardedEta; positivity
  have hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos hn1 heta
  have hN : 0 < guardedC a ^ 2 * (n : Real) := by positivity
  have hk : 0 < guardedK a := by
    exact concreteEstimatorSamples_pos (guardedJ a) (guardedAccuracy a / 4)
  have hepsMix0 : 0 < guardedMix a := runwiseChosenMixError_pos (guardedM a) hk
  have hepsMix32 : guardedMix a <= 1 / 32 :=
    runwiseChosenMixError_le_one_div_32 (guardedM a) hk
  have hbelow : forall j, j + 1 < guardedM a + 1 ->
      adaptiveChunkStart (guardedC a ^ 2 * n) (guardedS0 a)
        (adaptivePhaseChunk (guardedC a ^ 2 * n) (guardedS0 a) j) <=
          guardedC a ^ 2 * n := by
    intro j hj
    have hjm : j < guardedM a := by omega
    have hchunk : adaptivePhaseChunk (guardedC a ^ 2 * n) (guardedS0 a) j < guardedJ a :=
      adaptivePhaseChunk_lt_of_lt_offset hN hs0 hjm
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs0 hchunk).le
  have hcold : 4 * (n : Real) * guardedS0 a <= endpointRho ^ 2 :=
    polynomialEndpointSigmaSq_coldBall hn1 heta (by
      unfold guardedEta
      linarith)
  have hsteps : forall i : Fin (guardedM a + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq (guardedC a ^ 2 * n) (guardedS0 a) i <= 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma (guardedC a ^ 2 * n) (guardedS0 a) i ^ 2 *
          (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / guardedMix a)) /
            (adaptiveTerminalDelta (n := n) (guardedC a ^ 2 * n)
              (guardedS0 a) i * Real.log 2) ^ 2 + 1 <= (guardedSteps a i : Real) := by
    intro i _
    exact runwiseMixingSteps_spec n (guardedC a ^ 2 * n) (guardedS0 a)
      (guardedM a) (guardedK a) i
  letI hphaseProb : forall i l, IsProbabilityMeasure (guardedPhaseLaw a i l) := fun i l =>
    isProbabilityMeasure_adaptiveTerminalWarmLaw hn hN hs0 hKcl.measurableSet hKc
      hclosedBall hfin endpointRho_pos (endpointRho_lt_shrink hn2) hcold hbelow
      hepsMix0 hepsMix32 (guardedSteps a) hsteps i
  letI : forall t i l, IsProbabilityMeasure
      (Ttc.CVRunwise.iidRunFamily (r := guardedR a) (guardedPhaseLaw a) t i l) :=
    fun t i l => hphaseProb i l
  unfold guardedRawRunLaw
  infer_instance

/-! ## Public guarded constructor -/

/-- A genuine public `VolumeAlgorithm`, conditional on the exact radius-four tail guard for
every admissible closed input.  The guard cannot presently be removed at fixed dimension. -/
noncomputable def guardedConcreteVolumeAlgorithm (n : Nat) (hn : 21 <= n)
    (htail : forall (K : Set (Space n)) (eps p : Real),
      0 < eps -> 0 < p -> p < 1 -> Convex Real K -> IsClosed K ->
      Bornology.IsBounded K -> 0 < volume K -> closedBall (0 : Space n) 1 ⊆ K ->
      volume K ≠ ⊤ -> ConcreteRunwiseTailGuard (n := n) (K, eps, p)) :
    Ttc.VolumeAlgorithm n :=
  Ttc.VolumeAlgorithm.ofClosedInputLaws n (by omega)
    (GuardedRunCoin n) guardedRunLaw guardedEstimator measurable_guardedEstimator
    (fun K eps p heps hp hp1 hKc hKcl hKb hvol hclosedBall hfin => by
      let a : VolumeInput n := (K, eps, p)
      have hrawProb : IsProbabilityMeasure (guardedRawRunLaw a) :=
        isProbabilityMeasure_guardedRawRunLaw hn a heps hKc hKcl hclosedBall hfin
      have hlaw : guardedRunLaw a = guardedRawRunLaw a := guardedRunLaw_eq_raw a hrawProb
      have hest : guardedEstimator a = guardedRawEstimator a :=
        guardedEstimator_eq_raw a hKcl.measurableSet
      have hgeom := closure_concrete_geometry (n := n) (by omega) hKc
        (ball_subset_closedBall.trans hclosedBall) hfin
      have hKR : K ⊆ closedBall 0 (Ttc.CV.cvRadius K * Real.sqrt n) := by
        simpa [hKcl.closure_eq] using hgeom.2.2.2.2.2.2.2
      have hacc : 0 < guardedAccuracy a := by
        unfold guardedAccuracy
        positivity
      have hacc1 : guardedAccuracy a <= 1 := min_le_right _ _
      have hmain := concrete_adaptive_runwise_volume_accuracy hn hKc hKcl hKb hvol
        hclosedBall hfin (Ttc.CV.cvRadius_pos K) hacc hacc1 hp hp1 hKR
        (htail K eps p heps hp hp1 hKc hKcl hKb hvol hclosedBall hfin)
      have hmain' : 1 - p <= (guardedRawRunLaw a).real
          {omega | guardedRawEstimator a omega ∈
            Ttc.relErr (guardedAccuracy a) (volume K).toReal} := by
        convert hmain using 1 <;>
          simp only [a, guardedAccuracy, guardedEta, guardedC, guardedS0, guardedJ,
            guardedM, guardedK, guardedR, guardedMix, guardedSteps, guardedPhaseLaw,
            guardedRawRunLaw, guardedScore, guardedRawEstimator] <;> rfl
      letI : IsProbabilityMeasure (guardedRawRunLaw a) := hrawProb
      have hmono : (guardedRawRunLaw a).real
          {omega | guardedRawEstimator a omega ∈
            Ttc.relErr (guardedAccuracy a) (volume K).toReal} <=
          (guardedRawRunLaw a).real
          {omega | guardedRawEstimator a omega ∈
            Ttc.relErr eps (volume K).toReal} := by
        apply measureReal_mono
        · intro omega homega
          exact Ttc.CV.relErr_mono (min_le_left _ _) (volume K).toReal_nonneg homega
        · exact measure_ne_top _ _
      rw [hlaw, hest]
      exact hmain'.trans hmono)

/-! ### Axiom audit -/

#print axioms isProbabilityMeasure_guardedRawRunLaw
#print axioms guardedConcreteVolumeAlgorithm

end Ttc.CVAdaptive

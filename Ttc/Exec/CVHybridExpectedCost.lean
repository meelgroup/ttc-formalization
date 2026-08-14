/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CostedBackend
import Ttc.Exec.VolumePriceCV
import Ttc.Exec.CoolDrawPrice
import Ttc.Exec.PolyRun
import Ttc.Volume.CVHybridVolumeAlgorithm
import Ttc.Volume.CVOperationalRuntime

/-!
# Honest cost attachment for the guarded CV branch of the hybrid volume oracle

`Ttc.CVAdaptive.hybridConcreteVolumeAlgorithm` is an unconditional semantic
`VolumeAlgorithm`: on inputs satisfying `ConcreteRunwiseTailGuard` it is the concrete
adaptive Cousins--Vempala estimator, and otherwise it falls back to hit-and-miss Monte
Carlo.  This file records the guarded branch as an explicit package and attaches to it the
arithmetic expected-cost envelope already proved in `CVOperationalRuntime`.

This is deliberately not a `CostedBackend`.  That interface asks for

```
volumeWork : ι -> Nat
volumePrice : Nat
volumeWork_le : forall i, volumeWork i <= volumePrice
```

whereas rejection sampling is currently priced by an integral of a random round count.
There is no execution semantics in the repository relating those rejection trajectories,
the bounded-step Markov chains, the phase/sample loops, and membership queries.  The
predicate `GuardedCVExpectedExecution` below states exactly the missing binder: a future
execution relation must identify the output law and prove an integrable expected work
bound.  In particular, no deterministic `Nat` work is manufactured here.

`VolumePriceCV` and `CoolDrawPrice` are imported to make the interface comparison explicit.
Their prices concern the older uniform cooling schedule and remain conditional on their own
mixing binders; they are not silently substituted for the adaptive radius-four schedule.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CV.Adaptive

variable {n : Nat}

/-! ## The precise guarded semantic branch -/

/-- All geometric and numeric hypotheses under which the hybrid oracle takes its proved
adaptive CV branch.  Keeping this as one proposition makes downstream TTC attachments state
the guard rather than accidentally charging the Monte Carlo fallback at the CV price. -/
structure GuardedCVClosedInput (a : VolumeInput n) : Prop where
  accuracy_pos : 0 < a.2.1
  confidence_pos : 0 < a.2.2
  confidence_lt_one : a.2.2 < 1
  convex : Convex Real a.1
  closed : IsClosed a.1
  bounded : Bornology.IsBounded a.1
  volume_pos : 0 < volume a.1
  unit_closedBall_subset : closedBall (0 : Space n) 1 ⊆ a.1
  volume_ne_top : volume a.1 ≠ ⊤
  tail_guard : ConcreteRunwiseTailGuard a

/-- The semantic and branch-reduction facts that are available before any operational cost
model is supplied. -/
def VolumeAlgorithmSemanticCorrect (V : VolumeAlgorithm n) : Prop :=
  ∀ (K : Set (Space n)) (eps p : Real), 0 < eps -> 0 < p -> p < 1 ->
    Convex Real K -> ball (0 : Space n) 1 ⊆ K -> volume K ≠ ⊤ ->
      1 - p ≤ (V.μ {omega | V.est K eps p omega ∈
        Ttc.relErr eps (volume K).toReal}).toReal

/-- The semantic and branch-reduction facts that are available before any operational cost
model is supplied. -/
def HybridCVGuardedSemanticContract (hn : 21 ≤ n) : Prop :=
  VolumeAlgorithmSemanticCorrect (hybridConcreteVolumeAlgorithm n hn) ∧
    ∀ a : VolumeInput n, GuardedCVClosedInput a ->
      hybridRunLaw a = Measure.map Sum.inl (guardedRawRunLaw a) ∧
        ∀ omega, hybridEstimator a (Sum.inl omega) = guardedRawEstimator a omega

/-- The public hybrid algorithm satisfies the semantic contract, and its law and estimator
are definitionally reduced to the concrete CV branch on guarded closed inputs. -/
theorem hybridConcreteVolumeAlgorithm_guarded_semantic_contract (hn : 21 ≤ n) :
    HybridCVGuardedSemanticContract hn := by
  constructor
  · exact (hybridConcreteVolumeAlgorithm n hn).correct
  · intro a ha
    exact hybrid_reduces_to_cv_on_guard hn a.1 a.2.1 a.2.2 ha.accuracy_pos
      ha.convex ha.closed ha.unit_closedBall_subset ha.volume_ne_top ha.tail_guard

/-- The local accuracy conclusion on the branch that is assigned the CV price. -/
theorem guardedCVClosedInput_accuracy (hn : 21 ≤ n) (a : VolumeInput n)
    (ha : GuardedCVClosedInput a) :
    1 - a.2.2 ≤ (hybridRunLaw a).real
      {omega | hybridEstimator a omega ∈ Ttc.relErr a.2.1 (volume a.1).toReal} := by
  exact hybridRunLaw_correct hn ha.accuracy_pos ha.confidence_pos ha.confidence_lt_one
    ha.convex ha.closed ha.bounded ha.volume_pos ha.unit_closedBall_subset ha.volume_ne_top

/-! ## Adaptive arithmetic price -/

/-- The explicit real-valued accounting envelope for the guarded adaptive CV branch.

Its terms are: two expected ambient cold-start proposals, the factor four from speedy
acceptance/rejection, the explicit median repetition and per-phase sample counts, the
adaptive phase-count bound, and the proved radius-four mixing deadline envelope.  It is an
arithmetic/expected-round expression, not yet a membership-query runtime. -/
noncomputable def guardedCVArithmeticPrice (a : VolumeInput n) : Real :=
  adaptiveOperationalAccountingEnvelope n
    (guardedC a ^ 2 * (n : Real)) (guardedS0 a) (guardedMix a)
    (guardedR a : Real) (guardedK a : Real)

/-- The exact phase/sample/mixing accounting is bounded by `guardedCVArithmeticPrice`.
This packages the already-proved polynomial endpoint, adaptive phase bound, concrete sample
count, repetition count, and radius-four deadline into one visible price expression. -/
theorem guardedCV_accounting_le_arithmeticPrice (hn : 21 ≤ n) (a : VolumeInput n)
    (heps : 0 < a.2.1) :
    2 + 4 * (guardedR a : Real) * (guardedK a : Real) *
          (guardedM a : Real) *
          adaptiveRadiusFourMixingEnvelope n (guardedC a ^ 2 * (n : Real))
            (guardedS0 a) (guardedMix a)
      ≤ guardedCVArithmeticPrice a := by
  have hn1 : 1 ≤ n := by omega
  have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
  have hacc : 0 < guardedAccuracy a := by
    unfold guardedAccuracy
    positivity
  have heta : 0 < guardedEta a := by
    unfold guardedEta
    positivity
  have hN : 0 < guardedC a ^ 2 * (n : Real) := by positivity
  have hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos hn1 heta
  have hk : 0 < guardedK a :=
    concreteEstimatorSamples_pos (guardedJ a) (guardedAccuracy a / 4)
  have hmix0 : 0 < guardedMix a := runwiseChosenMixError_pos (guardedM a) hk
  have hmix32 : guardedMix a ≤ 1 / 32 :=
    runwiseChosenMixError_le_one_div_32 (guardedM a) hk
  have hmix1 : guardedMix a ≤ 1 := hmix32.trans (by norm_num)
  have hlogmix : 0 ≤ Real.log (1 / guardedMix a) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hmix0]
    simpa using hmix1
  have hq0 : 0 ≤ adaptiveRadiusFourMixingEnvelope n
      (guardedC a ^ 2 * (n : Real)) (guardedS0 a) (guardedMix a) := by
    unfold adaptiveRadiusFourMixingEnvelope
    positivity
  have h := adaptive_operational_accounting_le
    (n := n) (N := guardedC a ^ 2 * (n : Real)) (s₀ := guardedS0 a)
    (epsMix := guardedMix a) (runs := guardedR a) (drawsPerPhase := guardedK a)
    (q := adaptiveRadiusFourMixingEnvelope n (guardedC a ^ 2 * (n : Real))
      (guardedS0 a) (guardedMix a))
    hN hs0 (by positivity) (by positivity) hq0 le_rfl
  simpa only [guardedCVArithmeticPrice, guardedM, guardedJ] using h

/-! ## The missing expected execution relation -/

/-- The honest remaining operational binder.

`Executes xi output work` is intentionally supplied by a future operational semantics.  A
certificate must show that every trace is recognized by that semantics, its output law is
the proved guarded raw CV output law, and its natural-number work is integrable with the
advertised expected bound.  Merely choosing a zero work function cannot discharge this
predicate unless the supplied execution relation certifies that choice.

The execution trace space may contain more randomness than `GuardedRunCoin`: rejection
trajectories and intermediate Markov-chain states are absent from the current estimator coin
space and must be represented by an eventual implementation. -/
def GuardedCVExpectedExecution
    (a : VolumeInput n) {Xi : Type*} [MeasurableSpace Xi]
    (nu : Measure Xi) (output : Xi -> Real) (work : Xi -> Nat)
    (Executes : Xi -> Real -> Nat -> Prop) : Prop :=
  (∀ xi, Executes xi (output xi) (work xi)) ∧
    Measurable output ∧ Measurable work ∧
    Measure.map output nu =
      Measure.map (guardedRawEstimator a) (guardedRawRunLaw a) ∧
    Integrable (fun xi => (work xi : Real)) nu ∧
    (∫ xi, (work xi : Real) ∂nu) ≤ guardedCVArithmeticPrice a

/-- What the deterministic `CostedBackend` interface can recover from an actual backend:
a pointwise natural-number bound.  This theorem documents the exact target type; an
expected-cost certificate above does not imply it. -/
theorem costedBackend_volumeWork_is_pointwise
    {iota : Type*} {P : Params} {volumeSpec sampleSpec : Oracles n iota -> Prop}
    (B : CostedBackend P volumeSpec sampleSpec) :
    ∀ i, B.volumeWork i ≤ B.volumePrice :=
  B.volumeWork_le

/-! ### Axiom audit -/

#print axioms hybridConcreteVolumeAlgorithm_guarded_semantic_contract
#print axioms guardedCVClosedInput_accuracy
#print axioms guardedCV_accounting_le_arithmeticPrice
#print axioms costedBackend_volumeWork_is_pointwise

end Ttc.CVAdaptive

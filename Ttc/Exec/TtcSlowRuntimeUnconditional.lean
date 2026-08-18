import Ttc.Exec.TtcSlowRuntimeFinal
import Ttc.Exec.TtcCallCircumAdmissible
import Ttc.Exec.CVSlowActualSteps
import Ttc.Exec.CVSlowRefreshSteps
import Ttc.Exec.CVSlowActualCostEnvelope

/-!
# The **unconditional** TTC runtime capstone for the slow canonical volume route

`Ttc/Exec/TtcSlowRuntimeFinal.lean` carries the same assembly with one residual hypothesis
`SlowCostSideHypothesis`, because at the time it was written the *actual* (compounding
actual-warmness) per-phase mixing deadline of the slow canonical schedule had no proved
bound.  It now has one — `Ttc.CVSlowActualSteps.slowCanonicalSteps_min_le` — and this
file redoes the assembly with the residual discharged.  The old file stays as a record.

Two things change with respect to the conditional assembly.

## 1. The admissibility predicate pins the declared radius

The assembly is instantiated through the **generic** consumer
`Ttc.TtcShapedRuntime.ttc_runtime_of_effectiveCertificatesGen` at

* `Adm := Ttc.TtcCallCircumAdmissible.cvAdmCircum`, which says
  `CVAdmissible K R2 ∧ R2 = (circumR (interior K)) ^ 2`;
* `radialR := fun n K ↦ circumR (interior K)`.

Because the predicate *pins* `R2` to the value the construction actually runs at, the
`hrad` and `heff` binders are both equalities, and **no monotonicity of the overhead
envelope in the declared squared radius is used anywhere.**  (That monotonicity is genuinely
awkward for this envelope: its phase count `slowPhasesP n R2` sits inside a logarithm and is
multiplied by itself.)  It also removes the interior-to-body radius move from the weakening
step, since the certificate's radial slot is now the interior circumradius itself.

## 2. The overhead envelope is built on the actual deadline

`Ttc.CVSlowEffectiveOverhead.slowUniformOverheadQ` — the *reference-warm* cap — is replaced
by `Ttc.CVSlowActualCostEnvelope.slowActualOverhead` at the two real envelopes

* `slowUncLenv` — the actual per-run retry cap
  `Ttc.CVSlowActualSteps.slowActualRetriesCap`, and
* `slowUncTenv` — the actual per-phase deadline envelope
  `Ttc.CVSlowActualSteps.slowMinStepsEnvelope`, plus `2` for the ceiling.

Both are the quantities the schedule's own analysis produces, so the frontier's `hsteps`
and `hscalar` binders are discharged outright, and nothing is assumed.

The `64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2` prefix is kept verbatim from the
conditional assembly: it is what pays for the accuracy clip and the budget's accuracy-slot
move in the weakening step, and `Ttc.TtcSlowRuntimeFinal.sourceOneRunQueryBudget_clip_eps`
is proved for exactly that shape.

## Main results

* `slowUncCertificate_H` — the `H` binder of the generic consumer, with no residual.
* `ttc_volume_runtime_unconditional` — the capstone.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.TtcSlowRuntimeUnconditional

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling
open Ttc.CVSourcePolynomialCutoffCapstone (sourceLogFactor sourceOneRunQueryEnvelope
  sourceOneRunQueryBudget sourceLogFactor_pos)
open Ttc.CVEffectiveTotalise (CVValidInput)
open Ttc.TtcCircumRadius (circumR circumR_nonneg)
open Ttc.CVSlowEffectiveOverhead (slowPhasesP slowStreamsP)
open Ttc.CVSlowTotalFamilies
open Ttc.CVSlowOneRunValid
open Ttc.CVSlowCanonicalTailPhases
open Ttc.CVSlowCanonicalHopAssembly
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVSlowCanonicalRetainedReference
open Ttc.CVSlowSourceReferenceCertificate (slowInitialPair slowReferenceWarm
  slowSourceInitialVariance slowScoreAwareSteps)
open Ttc.CVSlowRadiusQCanonicalOperational (slowCanonicalSteps)
open Ttc.CVGaussianScoreAwareParameters (scoreAwareRetries scoreAwareEta scoreAwareZeta)
open Ttc.CVSlowCanonicalAccuracyBudget (slowAccuracyRequested)
open Ttc.CVSlowAccuracyStrict
open Ttc.CVCorrectedRuntime (correctedRuntimeSamples correctedRuntimeSamples_pos)
open Ttc.CVSlowUniformShareBounds (scoreAwareRetries_slowUniform_le)
open Ttc.CVSourceReferenceTVCapstone
open Ttc.CVSlowActualSteps (slowActualRetriesCap)
open Ttc.CVSlowRefreshSteps (slowMinStepsEnvelope slowCanonicalSteps_min_le
  cast_slowMinStepsCap_le slowMinStepsEnvelope_nonneg)
open Ttc.CVSlowActualCostEnvelope (slowActualOverhead one_le_slowActualOverhead
  slowActualOverhead_nonneg slowActual_hscalar)
open Ttc.TtcCallCircumAdmissible (cvAdmCircum cvAdmCircum_imp_cvAdmissible
  circumInterior_sq_le_of_cvAdmCircum cvAdmCircum_callBody)
open Ttc.TtcSlowRuntimeFinal (clipInput clipInput_valid clipInput_eps_pos
  slowRealisedAccuracy slowFinalOmega slowFinalLaw slowFinalCost slowFinalValue
  measurable_slowFinalCost measurable_slowFinalValue one_le_sourceLogFactor
  sourceOneRunQueryBudget_clip_eps)
open scoped ENNReal Classical BigOperators

variable {n : Nat}

/-! ## Step 1 — the actual-schedule parameters, as functions of the declared data -/

/-- The mixing parameter the slow canonical schedule runs at, written as a function of the
declared squared radius alone. -/
noncomputable def slowUncQ (n : Nat) (R2 epsP : Real) : Real :=
  slowUniformQ n (slowPhasesP n R2) (slowStreamsP n R2 epsP) epsP (Real.sqrt R2)

/-- **The actual per-run retry envelope.**  This is the cap of
`Ttc.CVSlowUniformShareBounds.scoreAwareRetries_slowUniform_le`, at the schedule's own
share-family parameters. -/
noncomputable def slowUncLenv (n : Nat) (R2 epsP : Real) : Real :=
  (slowActualRetriesCap n (slowPhasesP n R2) (slowStreamsP n R2 epsP) epsP
    (Real.sqrt R2) : Real)

/-- **The actual per-phase deadline envelope.**  This is
`Ttc.CVSlowActualSteps.slowMinStepsEnvelope` — the deadline of the *compounding*
actual-warm schedule — plus `2`, which pays for the ceiling and the `+ 1` of
`Ttc.CVSlowActualSteps.slowCanonicalSteps_min_le`. -/
noncomputable def slowUncTenv (n : Nat) (R2 epsP : Real) : Real :=
  slowMinStepsEnvelope n (slowPhasesP n R2) (slowStreamsP n R2 epsP)
    (slowUncQ n R2 epsP) epsP (Real.sqrt R2) + 2

/-! ## Step 2 — the overhead envelope and the effective runtime constant -/

/-- **The overhead envelope the unconditional assembly is instantiated at.**
Cousins–Vempala's own Theorem 1.1 expression is multiplied by this, and by nothing else.

It is `Ttc.TtcSlowRuntimeFinal.slowFinalOV` with the reference-warm cap
`slowUniformOverheadQ` replaced by the actual-warm `slowActualOverhead` at the two envelopes
of Step 1. -/
noncomputable def slowUncOV (n : Nat) (R2 eps p : Real) : Real :=
  64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
    slowActualOverhead n R2 (min eps 1 / 2) p
      (slowUncLenv n R2 (min eps 1 / 2)) (slowUncTenv n R2 (min eps 1 / 2))

/-- The per-input effective runtime constant: the same expression at the **interior**
circumradius, which is precisely the radius `cvAdmCircum` declares. -/
noncomputable def slowUncEffective (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowUncOV n ((circumR (interior a.1)) ^ 2) a.2.1 a.2.2

theorem one_le_slowUncOV (n : Nat) (R2 eps p : Real) : 1 ≤ slowUncOV n R2 eps p := by
  unfold slowUncOV
  have h1 : (1 : Real) ≤ (max 1 eps) ^ 2 := by
    have := le_max_left (1 : Real) eps
    nlinarith
  have h2 : (1 : Real) ≤ sourceLogFactor n ^ 2 := by
    have := one_le_sourceLogFactor (n : Real)
    nlinarith
  have h3 : (1 : Real) ≤ slowActualOverhead n R2 (min eps 1 / 2) p
      (slowUncLenv n R2 (min eps 1 / 2)) (slowUncTenv n R2 (min eps 1 / 2)) :=
    one_le_slowActualOverhead _ _ _ _ _ _
  have h64 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 := by nlinarith
  have h641 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 := by nlinarith
  nlinarith

theorem slowUncOV_nonneg (n : Nat) (R2 eps p : Real) : 0 ≤ slowUncOV n R2 eps p :=
  zero_le_one.trans (one_le_slowUncOV n R2 eps p)

theorem slowUncEffective_nonneg (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    0 ≤ slowUncEffective n a := slowUncOV_nonneg _ _ _ _

/-- **The `heff` binder of the generic consumer, at `Adm := cvAdmCircum`.**

No monotonicity: `cvAdmCircum` pins `R2` to `(circumR (interior K)) ^ 2`, so the two sides
are literally the same expression. -/
theorem slowUncEffective_le_slowUncOV
    (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real)
    (hK : cvAdmCircum n K R2) :
    slowUncEffective n (K, eps, p) ≤ slowUncOV n R2 eps p := by
  show slowUncOV n ((circumR (interior K)) ^ 2) eps p ≤ slowUncOV n R2 eps p
  rw [hK.2]

/-! ## Step 3 — the same parameters at a concrete input -/

/-- `slowUncQ` at the input's own declared data. -/
noncomputable def slowUncQAt (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowUncQ n (slowR2 n a) (slowEpsInt n a)

/-- `slowUncLenv` at the input's own declared data. -/
noncomputable def slowUncLenvAt (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowUncLenv n (slowR2 n a) (slowEpsInt n a)

/-- `slowUncTenv` at the input's own declared data. -/
noncomputable def slowUncTenvAt (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowUncTenv n (slowR2 n a) (slowEpsInt n a)

/-- The declared squared radius really is the square of the declared radius, so the
envelope's `Real.sqrt R2` is the radius the schedule runs at. -/
theorem sqrt_slowR2 (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Real.sqrt (slowR2 n a) = slowRadius n a :=
  Real.sqrt_sq (circumR_nonneg _)

theorem slowUncQAt_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowUncQAt n a =
      slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a) (slowRadius n a) := by
  unfold slowUncQAt slowUncQ
  rw [sqrt_slowR2]
  rfl

theorem slowUncLenvAt_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowUncLenvAt n a =
      (slowActualRetriesCap n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a) : Real) := by
  unfold slowUncLenvAt slowUncLenv
  rw [sqrt_slowR2]
  rfl

theorem slowUncTenvAt_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowUncTenvAt n a =
      slowMinStepsEnvelope n (slowPhases n a) (slowStreams n a)
        (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowEpsInt n a) (slowRadius n a) + 2 := by
  unfold slowUncTenvAt slowUncTenv
  rw [sqrt_slowR2]
  have hq : slowUncQ n (slowR2 n a) (slowEpsInt n a) =
      slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a) := slowUncQAt_eq n a
  rw [hq]
  rfl

/-! ## Step 4 — the producer, with the cost side discharged

This is `Ttc.TtcSlowRuntimeFinal.exists_slowCertificate_of_valid` with its residual
`SlowCostSideRealised` hypothesis replaced by the two proved facts

* `Ttc.CVSlowActualSteps.slowCanonicalSteps_min_le` — the frontier's `hsteps` at
  `T := ⌈slowMinStepsEnvelope …⌉₊ + 1`, for the *actual* (compounding-warmness) schedule;
* `Ttc.CVSlowActualCostEnvelope.slowActual_hscalar` — the frontier's `hscalar` at the
  overhead built on exactly those two envelopes.

Nothing is assumed. -/

/-- **The one-run certificate on a valid input of accuracy at most one, unconditionally.** -/
theorem exists_slowUncCertificate_of_valid
    {n : Nat} (hn : 21 ≤ n) {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) (heps1 : a.2.1 ≤ 1) :
    ∃ r : Measure (slowOmega n a),
      SourceReferenceTVOneRunCertificate (slowLaw n a) r (slowCost n a) (slowValue n a)
        (slowActualOverhead n (slowR2 n a) (slowEpsInt n a) a.2.2
          (slowUncLenvAt n a) (slowUncTenvAt n a))
        n (circumR (interior a.1)) (slowRealisedAccuracy n a)
        ((1 - slowRealisedAccuracy n a) * (volume (interior a.1)).toReal)
        ((1 + slowRealisedAccuracy n a) * (volume (interior a.1)).toReal) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hK, hKc, hball, hfin, hvolEq, hKR, hRR⟩ :=
    Ttc.CVValidInteriorBridge.validInput_interior_facts h h.isBounded
  have heps : (0 : Real) < slowEpsInt n a := by
    have := h.1; unfold slowEpsInt; linarith
  have heps1' : slowEpsInt n a ≤ 1 := by unfold slowEpsInt; linarith
  haveI : IsProbabilityMeasure (slowInitialPair n) :=
    canonical_isProbabilityMeasure_slowInitialPair hn
  haveI hprob : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a) (slowRadius n a))
      (slowSourceInitialVariance n) (interior a.1) j) := fun j ↦
    slowIsProbabilityMeasure_stationaryTail h hn j
  haveI hmk := fun i ↦ slowIsMarkovKernel_costedSchedule (a := a) h hn i
  haveI hQmk : ∀ i, IsMarkovKernel (slowCanonicalActiveSchedule (n := n) hn1
      (slowPhases n a + 1) (slowStreams n a)
      (q := slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
      (canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
      (canonical_hs0 hn) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
      (slowUniformSlack n (slowPhases n a) (interior a.1))
      (slowUniformBoundSq n (slowRadius n a)) i) := fun i ↦
    canonical_isMarkovKernel_activeSchedule hn (R2 := slowR2 n a)
      (eps := slowEpsInt n a) (R := slowRadius n a) hK hKc hball i
  haveI hQmk' := fun i ↦ canonical_isMarkovKernel_activeSchedule hn (R2 := slowR2 n a)
    (eps := slowEpsInt n a) (R := slowRadius n a) (K := interior a.1) hK hKc hball i
  obtain ⟨-, -, hbslack, hbbound, -, hbq4, -, -, -, -, -⟩ :=
    slowUniformParameters_valid (n := n) hn1 (slowPhases n a) (slowStreams n a)
      (R := slowRadius n a) heps hK hball hfin
  obtain ⟨hop, htau, hmixError⟩ := exists_slowCanonicalHop_literal hn
    (slowPhases n a) (slowStreams n a) (correctedRuntimeSamples_pos _ _) hbq4 heps heps1'
    hK hKc hball hfin (0 : Real) hbslack hbbound rfl
  have hexact := canonical_hexact hn (R := slowRadius n a) (R2 := slowR2 n a)
    (le_refl _) hK hKc hball hfin hKR
  have hmoments := slowCanonical_momentBinders_all hn (slowPhases n a) heps heps1'
    hK hKc hball hfin hKR hbq4 (0 : Real)
    (slowUniformSlack n (slowPhases n a) (interior a.1))
    (slowUniformBoundSq n (slowRadius n a)) rfl hop htau hmixError hexact
  -- the actual per-run retry cap
  have hretries : ∀ i,
      scoreAwareRetries (slowPhases n a + 1) (slowStreams n a) (slowEpsInt n a / 2)
        (slowUniformSlack n (slowPhases n a) (interior a.1))
        (slowUniformBoundSq n (slowRadius n a)) i ≤
      slowActualRetriesCap n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a) := fun i ↦
    scoreAwareRetries_slowUniform_le hn1 (by linarith : (0 : Real) < slowEpsInt n a / 2)
      hK hball hfin i
  -- the actual per-phase mixing deadline
  have hq0 : (0 : Real) < slowUniformQ n (slowPhases n a) (slowStreams n a)
      (slowEpsInt n a) (slowRadius n a) :=
    lt_of_lt_of_le (by norm_num)
      (four_le_slowUniformQ hn1 (slowPhases n a) (slowStreams n a)
        (slowEpsInt n a) (slowRadius n a))
  have hEnv0 : 0 ≤ slowMinStepsEnvelope n (slowPhases n a) (slowStreams n a)
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a) (slowRadius n a))
      (slowEpsInt n a) (slowRadius n a) := slowMinStepsEnvelope_nonneg hn1 heps
  have hsteps : ∀ i, i < slowPhases n a →
      slowCanonicalSteps slowReferenceWarm n
        (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowSourceInitialVariance n) (interior a.1)
        (scoreAwareRetries (slowPhases n a + 1) (slowStreams n a) (slowEpsInt n a / 2)
          (slowUniformSlack n (slowPhases n a) (interior a.1))
          (slowUniformBoundSq n (slowRadius n a)))
        (scoreAwareEta (slowPhases n a + 1) (slowStreams n a) (slowEpsInt n a / 2)
          (slowUniformSlack n (slowPhases n a) (interior a.1))
          (slowUniformBoundSq n (slowRadius n a)))
        (scoreAwareZeta (slowPhases n a + 1) (slowStreams n a) (slowEpsInt n a / 2)
          (slowUniformSlack n (slowPhases n a) (interior a.1))
          (slowUniformBoundSq n (slowRadius n a)))
        i 0 ≤
      ⌈slowMinStepsEnvelope n (slowPhases n a) (slowStreams n a)
        (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowEpsInt n a) (slowRadius n a)⌉₊ + 1 := fun i hi ↦
    slowCanonicalSteps_min_le hn1 (slowPhases n a) (slowStreams n a) hq0 heps
      hK hball hfin hi
  -- the two real envelopes, and the casts the cost layer consumes
  have hLcast : (slowActualRetriesCap n (slowPhases n a) (slowStreams n a)
      (slowEpsInt n a) (slowRadius n a) : Real) ≤ slowUncLenvAt n a :=
    le_of_eq (slowUncLenvAt_eq n a).symm
  have hLenv0 : (0 : Real) ≤ slowUncLenvAt n a := by
    rw [slowUncLenvAt_eq]; positivity
  have hTcast : ((⌈slowMinStepsEnvelope n (slowPhases n a) (slowStreams n a)
        (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowEpsInt n a) (slowRadius n a)⌉₊ + 1 : Nat) : Real) ≤ slowUncTenvAt n a := by
    rw [slowUncTenvAt_eq]
    exact cast_slowMinStepsCap_le n _ _ _ _ _ hEnv0
  have hTenv0 : (0 : Real) ≤ slowUncTenvAt n a := by
    rw [slowUncTenvAt_eq]; linarith
  -- the cost side
  have hscalar := slowActual_hscalar n hn1
    (m := slowPhases n a) (k := slowStreams n a)
    (L := slowActualRetriesCap n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
      (slowRadius n a))
    (T := ⌈slowMinStepsEnvelope n (slowPhases n a) (slowStreams n a)
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (slowEpsInt n a) (slowRadius n a)⌉₊ + 1)
    (R := slowRadius n a) (requested := slowRealisedAccuracy n a) (R2 := slowR2 n a)
    (epsP := slowEpsInt n a) (p := a.2.2)
    (Lenv := slowUncLenvAt n a) (Tenv := slowUncTenvAt n a)
    (slowAccuracyRequested_half_pos (slowPhases n a) (slowStreams n a) h.1)
    (slowAccuracyRequested_half_lt_one (slowPhases n a) h.1 heps1)
    (le_refl _) (le_refl _) hLcast hTcast hLenv0 hTenv0
  obtain ⟨r, hr⟩ := exists_slowOneRunCertificate_canonical hn
    (eps := slowEpsInt n a) (R := slowRadius n a) (R2 := slowR2 n a)
    heps heps1' (le_refl _) hK hKc hball hfin hKR rfl
    hmoments.1 hmoments.2.1 hmoments.2.2.1 hmoments.2.2.2.1 hmoments.2.2.2.2
    (runtimeConstant := slowActualOverhead n (slowR2 n a) (slowEpsInt n a) a.2.2
      (slowUncLenvAt n a) (slowUncTenvAt n a))
    (⌈slowMinStepsEnvelope n (slowPhases n a) (slowStreams n a)
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (slowEpsInt n a) (slowRadius n a)⌉₊ + 1)
    (slowActualRetriesCap n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
      (slowRadius n a))
    (fun i hi ↦ hsteps i hi) (fun i _ ↦ hretries i) hscalar
  refine ⟨r, ?_⟩
  rw [slowLaw_of_valid h hn]
  exact hr

/-! ## Step 5 — the weakening

Two moves, one fewer than in the conditional assembly: because the consumer's radial
parameter is now the **interior** circumradius — the very radius the schedule runs at — the
interior-to-body radius move disappears.  What remains is

* the budget's accuracy slot, from the realised accuracy up to the clipped requested one
  (`Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb`, factor `64`) and then to the
  requested one (`Ttc.TtcSlowRuntimeFinal.sourceOneRunQueryBudget_clip_eps`, factor
  `(max 1 eps) ^ 2 * sourceLogFactor n ^ 2`);
* the accepted output window, from the realised relative error to the requested one
  (`Ttc.CVSourceReferenceWeaken.Icc_relErr_subset`, using
  `volume (interior a.1) = volume a.1`). -/

/-- **The certificate at the consumer's parameters, unconditionally.** -/
theorem exists_slowUncFinalCertificate
    {n : Nat} (hn : 21 ≤ n) {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) :
    ∃ r : Measure (slowFinalOmega n a),
      SourceReferenceTVOneRunCertificate (slowFinalLaw n a) r (slowFinalCost n a)
        (slowFinalValue n a) (slowUncEffective n a) n (circumR (interior a.1)) a.2.1
        ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal) := by
  have hn1 : 1 ≤ n := by omega
  have hb0 : (0 : Real) < min a.2.1 1 := clipInput_eps_pos h
  have hb1 : min a.2.1 1 ≤ 1 := min_le_right _ _
  have hR0 : (0 : Real) ≤ circumR (interior a.1) := circumR_nonneg _
  obtain ⟨r, hr⟩ := exists_slowUncCertificate_of_valid hn (clipInput_valid h) hb1
  refine ⟨r, hr.weaken_of_subset ?_ ?_⟩
  · -- the budget
    have hrc0 : (0 : Real) ≤ slowActualOverhead n (slowR2 n (clipInput a))
        (slowEpsInt n (clipInput a)) a.2.2
        (slowUncLenvAt n (clipInput a)) (slowUncTenvAt n (clipInput a)) :=
      slowActualOverhead_nonneg _ _ _ _ _ _
    have hreq0 : 0 < slowRealisedAccuracy n (clipInput a) :=
      slowAccuracyRequested_half_pos (slowPhases n (clipInput a))
        (slowStreams n (clipInput a)) hb0
    have hhalf : min a.2.1 1 / 2 ≤ slowRealisedAccuracy n (clipInput a) :=
      half_le_slowAccuracyRequested (slowPhases n (clipInput a))
        (slowStreams n (clipInput a)) hb0
    have habs := Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb
      (rc := slowActualOverhead n (slowR2 n (clipInput a)) (slowEpsInt n (clipInput a))
        a.2.2 (slowUncLenvAt n (clipInput a)) (slowUncTenvAt n (clipInput a)))
      (R := circumR (interior a.1)) (R' := circumR (interior a.1))
      (e := slowRealisedAccuracy n (clipInput a)) (eps := min a.2.1 1) (n := n)
      hrc0 hn1 hb0 hb1 hreq0 hhalf hR0 (le_refl _)
    have hclip := sourceOneRunQueryBudget_clip_eps (n := n)
      (rc := 64 * slowActualOverhead n (slowR2 n (clipInput a))
        (slowEpsInt n (clipInput a)) a.2.2
        (slowUncLenvAt n (clipInput a)) (slowUncTenvAt n (clipInput a)))
      (R := circumR (interior a.1)) (eps := a.2.1) (by positivity) h.1
    have hrw : slowUncEffective n a =
        64 * (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2 *
          slowActualOverhead n (slowR2 n (clipInput a)) (slowEpsInt n (clipInput a))
            a.2.2 (slowUncLenvAt n (clipInput a)) (slowUncTenvAt n (clipInput a)) := rfl
    have hconst : 64 * slowActualOverhead n (slowR2 n (clipInput a))
          (slowEpsInt n (clipInput a)) a.2.2
          (slowUncLenvAt n (clipInput a)) (slowUncTenvAt n (clipInput a)) *
          (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2 ≤ slowUncEffective n a :=
      le_of_eq (by rw [hrw]; ring)
    have hcore : (0 : Real) ≤
        max (circumR (interior a.1) ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / a.2.1 ^ 2 *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / a.2.1) ^ 2 *
          sourceLogFactor ((n : Real) / a.2.1) ^ 2 := by
      have h0 : (0 : Real) ≤
          max (circumR (interior a.1) ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) :=
        le_max_of_le_right (by positivity)
      have h1 : (0 : Real) ≤ sourceLogFactor (1 / a.2.1) := (sourceLogFactor_pos _).le
      have h2 : (0 : Real) ≤ sourceLogFactor ((n : Real) / a.2.1) :=
        (sourceLogFactor_pos _).le
      have h3 : (0 : Real) ≤ sourceLogFactor n := (sourceLogFactor_pos _).le
      have h4 : (0 : Real) ≤
          max (circumR (interior a.1) ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) /
            a.2.1 ^ 2 := by positivity
      positivity
    exact habs.trans (hclip.trans
      (Ttc.CVSourceReferenceWeaken.sourceOneRunQueryBudget_mono_constant hconst hcore))
  · -- the accepted output window
    have hle : slowRealisedAccuracy n (clipInput a) ≤ a.2.1 :=
      (slowAccuracyRequested_half_le (slowPhases n (clipInput a)) hb0 hb1).trans
        (min_le_left _ _)
    exact Ttc.CVSourceReferenceWeaken.Icc_relErr_subset hle ENNReal.toReal_nonneg
      (Ttc.CVValidInteriorBridge.toReal_volume_interior_eq_of_convex h.2.2.2.1)

/-! ## Step 6 — the `H` binder and the implementation -/

/-- **The `H` binder of `Ttc.TtcShapedRuntime.ttc_runtime_of_effectiveCertificatesGen`**,
at `radialR := fun n K ↦ circumR (interior K)`, **with no residual hypothesis.** -/
theorem slowUncCertificate_H :
    ∀ n, 21 ≤ n → ∀ a : Ttc.CVAdaptive.VolumeInput n, CVValidInput a →
      ∃ r : Measure (slowFinalOmega n a),
        SourceReferenceTVOneRunCertificate (slowFinalLaw n a) r (slowFinalCost n a)
          (slowFinalValue n a) (slowUncEffective n a) n (circumR (interior a.1)) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal) :=
  fun _ hn _ h ↦ exists_slowUncFinalCertificate hn h

/-- **The TTC volume implementation built from the slow canonical route**, with no residual
hypothesis. -/
noncomputable def slowUncImplementation :
    Ttc.CVShaped.CVShapedExpectedImplementation cvAdmCircum
      (Ttc.TtcShapedRuntime.shapeOf slowUncOV) :=
  Ttc.TtcShapedRuntime.implementationOfEffectiveCertificatesGen cvAdmCircum
    cvAdmCircum_imp_cvAdmissible (fun _ K ↦ circumR (interior K))
    circumInterior_sq_le_of_cvAdmCircum slowUncOV one_le_slowUncOV
    slowUncEffective slowUncEffective_nonneg slowUncEffective_le_slowUncOV
    slowFinalOmega slowFinalLaw slowFinalCost slowFinalValue
    measurable_slowFinalCost measurable_slowFinalValue slowUncCertificate_H

section Capstone

open Ttc.CVShaped
open Ttc.TtcShapedRuntime
open Ttc.TTCCVExpectedImplementation
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem

variable {A : Type*}

/-- **TTC's accuracy and query cost, from the slow canonical volume construction —
unconditionally.**

There is no oracle binder, no certificate binder, no implementation binder and **no
cost-side binder**: the volume subroutine is `slowUncImplementation.algorithm n`, built here
out of the slow canonical Gaussian-cooling construction, and the two conjuncts are about the
one law `canonicalFullOperationalLaw V P` that executes it.

**The cost envelope.**  The volume term is the per-cube sum of
`cvComplexityShapeClipped * slowUncOV`, each cube taken at **its own interior circumradius
squared** — the radius the construction actually runs at, pinned by
`Ttc.TtcCallCircumAdmissible.cvAdmCircum` — where

  `slowUncOV n R2 eps p = 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
      slowActualOverhead n R2 (min eps 1 / 2) p
        (slowUncLenv n R2 (min eps 1 / 2)) (slowUncTenv n R2 (min eps 1 / 2))`.

That is an explicit closed-form polynomial-and-logarithm expression in `n`, `R2`, `eps`,
built out of the schedule's own phase count, stream count, actual retry cap and **actual**
per-phase mixing deadline — the latter including the slow schedule's compounding-warmness
overhead, whose logarithm grows linearly in the phase index.  It is **not** the paper's
`O(m · n^5 · rho^2 · r_max)` exponents, and no constant here is pretending to be one: what
is proved is a bound at this explicit shape, not a match with the paper's asymptotics. -/
theorem ttc_volume_runtime_unconditional
    {n : Nat} (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let I := slowUncImplementation
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      shapedVolumeQueryEnvelopeAt I atoms phi eps deltaRun
        (fun j ↦ (circumR (interior (callBody atoms phi eps deltaRun j))) ^ 2) +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) :=
  ttc_runtime_of_effectiveCertificatesGen cvAdmCircum cvAdmCircum_imp_cvAdmissible
    (fun _ K ↦ circumR (interior K)) circumInterior_sq_le_of_cvAdmCircum
    slowUncOV one_le_slowUncOV slowUncEffective slowUncEffective_nonneg
    slowUncEffective_le_slowUncOV slowFinalOmega slowFinalLaw slowFinalCost slowFinalValue
    measurable_slowFinalCost measurable_slowFinalValue slowUncCertificate_H
    atoms phi eps delta
    (fun j ↦ (circumR (interior (callBody atoms phi eps (4 * delta / 5) j))) ^ 2)
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol
    (fun j ↦ cvAdmCircum_callBody atoms phi eps (4 * delta / 5)
      h_eps_pos h_eps_le (le_trans (by norm_num) hn) hphi hvol j)

end Capstone

section AxiomCheck

#print axioms slowUncEffective_le_slowUncOV
#print axioms one_le_slowUncOV
#print axioms slowUncQAt_eq
#print axioms slowUncLenvAt_eq
#print axioms slowUncTenvAt_eq
#print axioms exists_slowUncCertificate_of_valid
#print axioms exists_slowUncFinalCertificate
#print axioms slowUncCertificate_H
#print axioms slowUncImplementation
#print axioms ttc_volume_runtime_unconditional

end AxiomCheck

end Ttc.TtcSlowRuntimeUnconditional

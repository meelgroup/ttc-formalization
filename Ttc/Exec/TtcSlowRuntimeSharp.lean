import Ttc.Exec.TtcSlowRuntimeUnconditional
import Ttc.Exec.CVSharpFrontier
import Ttc.Exec.CVSharpSlowSteps

/-!
# The **sharp** unconditional TTC runtime capstone for the slow canonical volume route

`Ttc/Exec/TtcSlowRuntimeUnconditional.lean` carries the same assembly at the *loose*
slack / score-transport pair

* `slack := Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack n m K`  (`… / 2`),
* `boundSq := Ttc.CVSlowCanonicalUniformParameters.slowUniformBoundSq n R`
  (`phaseScoreTransportBoundSqSeven`),

whose induced share floor carries a **dimension-dependent** exponent `8 n R²`.  This file
redoes the assembly at the **sharp** pair

* `slack := Ttc.CVSharpUniformParameters.slowSharpSlack n m K`  (`… / 6`),
* `boundSq := Ttc.CVSharpScoreTransport.slowSharpBoundSq n R`,

whose share floor `Ttc.CVSharpUniformParameters.slowSharpFloor6` has the **dimension-free**
exponent `8 R²`.  The proved per-phase mixing deadline envelope improves accordingly:
`Ttc.CVSharpSlowSteps.slowSharpStepsEnvelope_le_min` machine-checks

  `slowSharpStepsEnvelope n m k q epsP R ≤ slowRefreshSteps.slowMinStepsEnvelope n m k q epsP R`

under `2 ≤ n` and `1 ≤ R` (both hold at every input the capstone runs on, since
`ball 0 1 ⊆ K ⊆ closedBall 0 R` forces `1 ≤ R` and the capstone assumes `21 ≤ n`).  The old
file stays as the record of the loose route.

## What had to be mirrored, and what did not

The sharp frontier certificate
`Ttc.CVSharpFrontier.exists_slowOneRunCertificate_canonical_sharp` states its conclusion
about the law of the canonical **costed** active schedule at the *sharp* pair.  Since
`Ttc.CVSlowTotalFamilies.slowLaw` hard-codes the loose pair inside that schedule term, the
law family had to be mirrored here: `slowSharpLaw`, `slowSharpLaw_of_valid`,
`slowSharpFinalLaw`, together with the Markov instance
`slowSharpIsMarkovKernel_costedSchedule`.

Nothing else was mirrored.  `slowOmega`, `slowCost`, `slowValue` and every parameter
abbreviation (`slowRadius`, `slowR2`, `slowEpsInt`, `slowPhases`, `slowStreams`) of
`Ttc.CVSlowTotalFamilies` are independent of the slack / transport pair and are reused
verbatim, as are `Ttc.TtcSlowRuntimeFinal.clipInput`, `slowFinalOmega`, `slowFinalCost`,
`slowFinalValue` and their two measurability facts.  The truncation radius is unchanged
too: the sharp route keeps `Ttc.CVSlowCanonicalUniformParameters.slowUniformQ`, so
`Ttc.TtcSlowRuntimeUnconditional.slowUncQ` is reused as the mixing parameter.

## The two envelopes that change

* `slowSharpLenv` — the per-run retry cap `Ttc.CVSharpSlowSteps.slowSharpRetriesCapAt`,
  i.e. `Ttc.CVSharpUniformParameters.slowSharpRetriesCap (m+1) k (epsP/2) R`, in place of
  `Ttc.CVSlowActualSteps.slowActualRetriesCap`;
* `slowSharpTenv` — the per-phase deadline envelope
  `Ttc.CVSharpSlowSteps.slowSharpStepsEnvelope`, plus `2` for the ceiling and the `+ 1` of
  `Ttc.CVSharpSlowSteps.slowCanonicalSteps_sharp_le`, in place of
  `Ttc.CVSlowRefreshSteps.slowMinStepsEnvelope`.

Both are the quantities the sharp analysis produces, so the sharp frontier's `hsteps`,
`hretries` and `hscalar` binders are discharged outright, and nothing is assumed.

The `64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2` prefix is kept verbatim from the loose
assembly: `Ttc.TtcSlowRuntimeFinal.sourceOneRunQueryBudget_clip_eps` is proved for exactly
that shape.

## Main results

* `slowSharpCertificate_H` — the `H` binder of the generic consumer, with no residual.
* `ttc_volume_runtime_sharp` — the capstone.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.TtcSlowRuntimeSharp

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
open Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVSlowSourceReferenceCertificate (slowInitialPair slowReferenceWarm
  slowSourceInitialVariance slowScoreAwareSteps)
open Ttc.CVSlowRadiusQCanonicalOperational (slowCanonicalSteps)
open Ttc.CVGaussianScoreAwareParameters (scoreAwareRetries scoreAwareEta scoreAwareZeta)
open Ttc.CVSlowCanonicalAccuracyBudget (slowAccuracyRequested)
open Ttc.CVSlowAccuracyStrict
open Ttc.CVCorrectedRuntime (correctedRuntimeSamples correctedRuntimeSamples_pos)
open Ttc.CVSourceReferenceTVCapstone
open Ttc.CVSlowActualCostEnvelope (slowActualOverhead one_le_slowActualOverhead
  slowActualOverhead_nonneg slowActual_hscalar)
open Ttc.TtcCallCircumAdmissible (cvAdmCircum cvAdmCircum_imp_cvAdmissible
  circumInterior_sq_le_of_cvAdmCircum cvAdmCircum_callBody)
open Ttc.TtcSlowRuntimeFinal (clipInput clipInput_valid clipInput_eps_pos
  slowRealisedAccuracy slowFinalOmega slowFinalCost slowFinalValue
  measurable_slowFinalCost measurable_slowFinalValue one_le_sourceLogFactor
  sourceOneRunQueryBudget_clip_eps)
open Ttc.TtcSlowRuntimeUnconditional (slowUncQ sqrt_slowR2 slowUncQAt_eq)
open Ttc.CVSharpUniformParameters (slowSharpSlack slowSharpRetriesCap
  scoreAwareRetries_slowSharp_le)
open Ttc.CVSharpScoreTransport (slowSharpBoundSq)
open Ttc.CVSharpFrontier (slowSharpParameters_valid slowSharp_momentBinders_all
  canonical_hR2_sharp canonical_hretries_sharp
  exists_slowOneRunCertificate_canonical_sharp)
open Ttc.CVSharpSlowSteps (slowSharpRetriesCapAt slowSharpStepsEnvelope
  slowSharpStepsEnvelope_nonneg cast_slowSharpStepsCap_le slowCanonicalSteps_sharp_le)
open scoped ENNReal Classical BigOperators

variable {n : Nat}

/-! ## Step 0 — the law family at the sharp pair

`Ttc.CVSlowTotalFamilies.slowLaw` writes the *loose* slack / transport pair into the
schedule term, so it is not the law the sharp certificate is about.  These four
declarations are its verbatim mirror with `slowUniformSlack ↦ slowSharpSlack` and
`slowUniformBoundSq ↦ slowSharpBoundSq`; every other family of that file is reused. -/

/-- The canonical **costed** active schedule at the **sharp** pair is Markov, at the
parameter choices of `Ttc.CVSlowTotalFamilies`.  The instance derivation is structural in
the slack / transport pair, so this is
`Ttc.CVSlowTotalFamilies.slowIsMarkovKernel_costedSchedule`'s proof verbatim. -/
theorem slowSharpIsMarkovKernel_costedSchedule
    {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) (hn : 21 ≤ n) (i : Nat) :
    IsMarkovKernel (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
      (slowPhases n a + 1) (slowStreams n a)
      (q := slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
      (canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
      (canonical_hs0 hn) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
      (slowSharpSlack n (slowPhases n a) (interior a.1))
      (slowSharpBoundSq n (slowRadius n a)) i) := by
  letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a) (slowRadius n a))
      (slowSourceInitialVariance n) (interior a.1) j) := fun j ↦
    slowIsProbabilityMeasure_stationaryTail h hn j
  infer_instance

/-- **The law of one run at the sharp pair, totalised.**  The mirror of
`Ttc.CVSlowTotalFamilies.slowLaw`, with the same `dite` guard `CVValidInput a ∧ 21 ≤ n`. -/
noncomputable def slowSharpLaw (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measure (slowOmega n a) :=
  if h : CVValidInput a ∧ 21 ≤ n then
    @independentHeterogeneousRetainedPathLaw _ _ _ _ (slowStreams n a)
      (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
        (slowPhases n a + 1) (slowStreams n a)
        (q := slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
        (canonical_hq0 h.2 (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
        (canonical_hs0 h.2) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
        (slowSharpSlack n (slowPhases n a) (interior a.1))
        (slowSharpBoundSq n (slowRadius n a)))
      (fun i ↦ slowSharpIsMarkovKernel_costedSchedule h.1 h.2 i)
      (slowInitialPair n) (slowPhases n a)
  else Measure.dirac (Classical.arbitrary _)

/-- **The unfolding of `slowSharpLaw` on the guarded branch.** -/
theorem slowSharpLaw_of_valid {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) (hn : 21 ≤ n) :
    slowSharpLaw n a =
      @independentHeterogeneousRetainedPathLaw _ _ _ _ (slowStreams n a)
        (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
          (slowPhases n a + 1) (slowStreams n a)
          (q := slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
            (slowRadius n a))
          (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
          (canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
          (canonical_hs0 hn) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
          (slowSharpSlack n (slowPhases n a) (interior a.1))
          (slowSharpBoundSq n (slowRadius n a)))
        (fun i ↦ slowSharpIsMarkovKernel_costedSchedule h hn i)
        (slowInitialPair n) (slowPhases n a) :=
  dif_pos ⟨h, hn⟩

/-- The law of one run at the sharp pair, at the clipped input.  The `Omega`, cost and
value families are `Ttc.TtcSlowRuntimeFinal`'s, unchanged. -/
noncomputable def slowSharpFinalLaw (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measure (slowFinalOmega n a) := slowSharpLaw n (clipInput a)

/-! ## Step 1 — the sharp schedule parameters, as functions of the declared data

The mixing parameter is unchanged: the sharp route sharpens the slack and the score
transport bound, not the truncation radius, so
`Ttc.TtcSlowRuntimeUnconditional.slowUncQ` is reused. -/

/-- **The sharp per-run retry envelope.**  This is the cap of
`Ttc.CVSharpUniformParameters.scoreAwareRetries_slowSharp_le`, in the exact spelling
`Ttc.CVSharpSlowSteps.slowCanonicalSteps_sharp_le` consumes. -/
noncomputable def slowSharpLenv (n : Nat) (R2 epsP : Real) : Real :=
  (slowSharpRetriesCapAt n (slowPhasesP n R2) (slowStreamsP n R2 epsP) epsP
    (Real.sqrt R2) : Real)

/-- **The sharp per-phase deadline envelope.**  This is
`Ttc.CVSharpSlowSteps.slowSharpStepsEnvelope` — the deadline of the compounding
actual-warm schedule at the *dimension-free* share floor — plus `2`, which pays for the
ceiling and the `+ 1` of `Ttc.CVSharpSlowSteps.slowCanonicalSteps_sharp_le`. -/
noncomputable def slowSharpTenv (n : Nat) (R2 epsP : Real) : Real :=
  slowSharpStepsEnvelope n (slowPhasesP n R2) (slowStreamsP n R2 epsP)
    (slowUncQ n R2 epsP) epsP (Real.sqrt R2) + 2

/-! ## Step 2 — the overhead envelope and the effective runtime constant -/

/-- **The overhead envelope the sharp assembly is instantiated at.**
Cousins–Vempala's own Theorem 1.1 expression is multiplied by this, and by nothing else.

It is `Ttc.TtcSlowRuntimeUnconditional.slowUncOV` with the two loose per-phase envelopes
replaced by the sharp ones of Step 1. -/
noncomputable def slowSharpOV (n : Nat) (R2 eps p : Real) : Real :=
  64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
    slowActualOverhead n R2 (min eps 1 / 2) p
      (slowSharpLenv n R2 (min eps 1 / 2)) (slowSharpTenv n R2 (min eps 1 / 2))

/-- The per-input effective runtime constant: the same expression at the **interior**
circumradius, which is precisely the radius `cvAdmCircum` declares. -/
noncomputable def slowSharpEffective (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowSharpOV n ((circumR (interior a.1)) ^ 2) a.2.1 a.2.2

theorem one_le_slowSharpOV (n : Nat) (R2 eps p : Real) : 1 ≤ slowSharpOV n R2 eps p := by
  unfold slowSharpOV
  have h1 : (1 : Real) ≤ (max 1 eps) ^ 2 := by
    have := le_max_left (1 : Real) eps
    nlinarith
  have h2 : (1 : Real) ≤ sourceLogFactor n ^ 2 := by
    have := one_le_sourceLogFactor (n : Real)
    nlinarith
  have h3 : (1 : Real) ≤ slowActualOverhead n R2 (min eps 1 / 2) p
      (slowSharpLenv n R2 (min eps 1 / 2)) (slowSharpTenv n R2 (min eps 1 / 2)) :=
    one_le_slowActualOverhead _ _ _ _ _ _
  have h64 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 := by nlinarith
  have h641 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 := by nlinarith
  nlinarith

theorem slowSharpOV_nonneg (n : Nat) (R2 eps p : Real) : 0 ≤ slowSharpOV n R2 eps p :=
  zero_le_one.trans (one_le_slowSharpOV n R2 eps p)

theorem slowSharpEffective_nonneg (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    0 ≤ slowSharpEffective n a := slowSharpOV_nonneg _ _ _ _

/-- **The `heff` binder of the generic consumer, at `Adm := cvAdmCircum`.**

No monotonicity: `cvAdmCircum` pins `R2` to `(circumR (interior K)) ^ 2`, so the two sides
are literally the same expression. -/
theorem slowSharpEffective_le_slowSharpOV
    (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real)
    (hK : cvAdmCircum n K R2) :
    slowSharpEffective n (K, eps, p) ≤ slowSharpOV n R2 eps p := by
  show slowSharpOV n ((circumR (interior K)) ^ 2) eps p ≤ slowSharpOV n R2 eps p
  rw [hK.2]

/-! ## Step 3 — the same parameters at a concrete input -/

/-- `slowSharpLenv` at the input's own declared data. -/
noncomputable def slowSharpLenvAt (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowSharpLenv n (slowR2 n a) (slowEpsInt n a)

/-- `slowSharpTenv` at the input's own declared data. -/
noncomputable def slowSharpTenvAt (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowSharpTenv n (slowR2 n a) (slowEpsInt n a)

theorem slowSharpLenvAt_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowSharpLenvAt n a =
      (slowSharpRetriesCapAt n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a) : Real) := by
  unfold slowSharpLenvAt slowSharpLenv
  rw [sqrt_slowR2]
  rfl

theorem slowSharpTenvAt_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowSharpTenvAt n a =
      slowSharpStepsEnvelope n (slowPhases n a) (slowStreams n a)
        (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowEpsInt n a) (slowRadius n a) + 2 := by
  unfold slowSharpTenvAt slowSharpTenv
  rw [sqrt_slowR2]
  have hq : slowUncQ n (slowR2 n a) (slowEpsInt n a) =
      slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a) := slowUncQAt_eq n a
  rw [hq]
  rfl

/-! ## Step 4 — the producer, with the cost side discharged at the sharp floor

This is `Ttc.TtcSlowRuntimeUnconditional.exists_slowUncCertificate_of_valid` with the
loose frontier replaced by
`Ttc.CVSharpFrontier.exists_slowOneRunCertificate_canonical_sharp` and its three cost-side
binders discharged from the sharp chain:

* `Ttc.CVSharpSlowSteps.slowCanonicalSteps_sharp_le` — `hsteps` at
  `T := ⌈slowSharpStepsEnvelope …⌉₊ + 1`;
* `Ttc.CVSharpUniformParameters.scoreAwareRetries_slowSharp_le` — `hretries` at
  `L := slowSharpRetriesCapAt …`;
* `Ttc.CVSlowActualCostEnvelope.slowActual_hscalar` — `hscalar`, unchanged: the cost layer
  is parametric in `(Lenv, Tenv)`.

Nothing is assumed. -/

/-- The canonical **seed** schedule at the sharp pair is Markov: the sharp analogue of
`Ttc.CVSlowOneRunValid.canonical_isMarkovKernel_activeSchedule`, whose proof is structural
in the slack / transport pair. -/
theorem slowSharpIsMarkovKernel_activeSchedule
    (hn : 21 ≤ n) {eps R R2 : Real} {K : Set (Ttc.Space n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : Ttc.Space n) 1 ⊆ K) (i : Nat) :
    IsMarkovKernel (slowCanonicalActiveSchedule (by omega : 1 ≤ n)
      (slowCanonicalPhases n R2 + 1)
      (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
      (q := slowUniformQ n (slowCanonicalPhases n R2)
        (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
      (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (canonical_hq0 hn R2 eps R) (canonical_hs0 hn) K hK 0 slowReferenceWarm
      (slowSharpSlack n (slowCanonicalPhases n R2) K) (slowSharpBoundSq n R) i) := by
  letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (slowCanonicalPhases n R2)
        (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) := fun j ↦
    canonical_isProbabilityMeasure_slowStationaryTail hn hK hKc hball j
  infer_instance

/-- **The one-run certificate on a valid input of accuracy at most one, at the sharp
pair.** -/
theorem exists_slowSharpCertificate_of_valid
    {n : Nat} (hn : 21 ≤ n) {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) (heps1 : a.2.1 ≤ 1) :
    ∃ r : Measure (slowOmega n a),
      SourceReferenceTVOneRunCertificate (slowSharpLaw n a) r (slowCost n a)
        (slowValue n a)
        (slowActualOverhead n (slowR2 n a) (slowEpsInt n a) a.2.2
          (slowSharpLenvAt n a) (slowSharpTenvAt n a))
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
  haveI hmk := fun i ↦ slowSharpIsMarkovKernel_costedSchedule (a := a) h hn i
  haveI hQmk : ∀ i, IsMarkovKernel (slowCanonicalActiveSchedule (n := n) hn1
      (slowPhases n a + 1) (slowStreams n a)
      (q := slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
      (canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
      (canonical_hs0 hn) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
      (slowSharpSlack n (slowPhases n a) (interior a.1))
      (slowSharpBoundSq n (slowRadius n a)) i) := fun i ↦
    slowSharpIsMarkovKernel_activeSchedule hn (R2 := slowR2 n a)
      (eps := slowEpsInt n a) (R := slowRadius n a) hK hKc hball i
  haveI hQmk' := fun i ↦ slowSharpIsMarkovKernel_activeSchedule hn (R2 := slowR2 n a)
    (eps := slowEpsInt n a) (R := slowRadius n a) (K := interior a.1) hK hKc hball i
  obtain ⟨-, -, hbslack, hbbound, -, hbq4, -, -, -, -, -⟩ :=
    slowSharpParameters_valid (n := n) hn1 (slowPhases n a) (slowStreams n a)
      (R := slowRadius n a) heps hK hball hfin
  obtain ⟨hop, htau, hmixError⟩ := exists_slowCanonicalHop_literal hn
    (slowPhases n a) (slowStreams n a) (correctedRuntimeSamples_pos _ _) hbq4 heps heps1'
    hK hKc hball hfin (0 : Real) hbslack hbbound rfl
  have hexact := canonical_hexact hn (R := slowRadius n a) (R2 := slowR2 n a)
    (le_refl _) hK hKc hball hfin hKR
  have hmoments := slowSharp_momentBinders_all hn (slowPhases n a) heps heps1'
    hK hKc hball hfin hKR hbq4 (0 : Real) rfl hop htau hmixError hexact
    (canonical_hR2_sharp (R := slowRadius n a) (R2 := slowR2 n a) hn (le_refl _))
  -- the sharp per-run retry cap
  have hretries : ∀ i,
      scoreAwareRetries (slowPhases n a + 1) (slowStreams n a) (slowEpsInt n a / 2)
        (slowSharpSlack n (slowPhases n a) (interior a.1))
        (slowSharpBoundSq n (slowRadius n a)) i ≤
      slowSharpRetriesCapAt n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a) := fun i ↦
    scoreAwareRetries_slowSharp_le hn1 (by linarith : (0 : Real) < slowEpsInt n a / 2)
      hK hball hfin i
  -- the sharp per-phase mixing deadline
  have hq0 : (0 : Real) < slowUniformQ n (slowPhases n a) (slowStreams n a)
      (slowEpsInt n a) (slowRadius n a) :=
    lt_of_lt_of_le (by norm_num)
      (four_le_slowUniformQ hn1 (slowPhases n a) (slowStreams n a)
        (slowEpsInt n a) (slowRadius n a))
  have hEnv0 : 0 ≤ slowSharpStepsEnvelope n (slowPhases n a) (slowStreams n a)
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a) (slowRadius n a))
      (slowEpsInt n a) (slowRadius n a) := slowSharpStepsEnvelope_nonneg hn1 heps
  have hsteps : ∀ i, i < slowPhases n a →
      slowCanonicalSteps slowReferenceWarm n
        (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowSourceInitialVariance n) (interior a.1)
        (scoreAwareRetries (slowPhases n a + 1) (slowStreams n a) (slowEpsInt n a / 2)
          (slowSharpSlack n (slowPhases n a) (interior a.1))
          (slowSharpBoundSq n (slowRadius n a)))
        (scoreAwareEta (slowPhases n a + 1) (slowStreams n a) (slowEpsInt n a / 2)
          (slowSharpSlack n (slowPhases n a) (interior a.1))
          (slowSharpBoundSq n (slowRadius n a)))
        (scoreAwareZeta (slowPhases n a + 1) (slowStreams n a) (slowEpsInt n a / 2)
          (slowSharpSlack n (slowPhases n a) (interior a.1))
          (slowSharpBoundSq n (slowRadius n a)))
        i 0 ≤
      ⌈slowSharpStepsEnvelope n (slowPhases n a) (slowStreams n a)
        (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowEpsInt n a) (slowRadius n a)⌉₊ + 1 := fun i hi ↦
    slowCanonicalSteps_sharp_le hn1 (slowPhases n a) (slowStreams n a) hq0 heps
      hK hball hfin hi
  -- the two real envelopes, and the casts the cost layer consumes
  have hLcast : (slowSharpRetriesCapAt n (slowPhases n a) (slowStreams n a)
      (slowEpsInt n a) (slowRadius n a) : Real) ≤ slowSharpLenvAt n a :=
    le_of_eq (slowSharpLenvAt_eq n a).symm
  have hLenv0 : (0 : Real) ≤ slowSharpLenvAt n a := by
    rw [slowSharpLenvAt_eq]; positivity
  have hTcast : ((⌈slowSharpStepsEnvelope n (slowPhases n a) (slowStreams n a)
        (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowEpsInt n a) (slowRadius n a)⌉₊ + 1 : Nat) : Real) ≤ slowSharpTenvAt n a := by
    rw [slowSharpTenvAt_eq]
    exact cast_slowSharpStepsCap_le n _ _ _ _ _ hEnv0
  have hTenv0 : (0 : Real) ≤ slowSharpTenvAt n a := by
    rw [slowSharpTenvAt_eq]; linarith
  -- the cost side
  have hscalar := slowActual_hscalar n hn1
    (m := slowPhases n a) (k := slowStreams n a)
    (L := slowSharpRetriesCapAt n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
      (slowRadius n a))
    (T := ⌈slowSharpStepsEnvelope n (slowPhases n a) (slowStreams n a)
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (slowEpsInt n a) (slowRadius n a)⌉₊ + 1)
    (R := slowRadius n a) (requested := slowRealisedAccuracy n a) (R2 := slowR2 n a)
    (epsP := slowEpsInt n a) (p := a.2.2)
    (Lenv := slowSharpLenvAt n a) (Tenv := slowSharpTenvAt n a)
    (slowAccuracyRequested_half_pos (slowPhases n a) (slowStreams n a) h.1)
    (slowAccuracyRequested_half_lt_one (slowPhases n a) h.1 heps1)
    (le_refl _) (le_refl _) hLcast hTcast hLenv0 hTenv0
  obtain ⟨r, hr⟩ := exists_slowOneRunCertificate_canonical_sharp hn
    (eps := slowEpsInt n a) (R := slowRadius n a) (R2 := slowR2 n a)
    heps heps1' (le_refl _) hK hKc hball hfin hKR rfl
    hmoments.1 hmoments.2.1 hmoments.2.2.1 hmoments.2.2.2.1 hmoments.2.2.2.2
    (runtimeConstant := slowActualOverhead n (slowR2 n a) (slowEpsInt n a) a.2.2
      (slowSharpLenvAt n a) (slowSharpTenvAt n a))
    (⌈slowSharpStepsEnvelope n (slowPhases n a) (slowStreams n a)
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (slowEpsInt n a) (slowRadius n a)⌉₊ + 1)
    (slowSharpRetriesCapAt n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
      (slowRadius n a))
    (fun i hi ↦ hsteps i hi) (fun i _ ↦ hretries i) hscalar
  refine ⟨r, ?_⟩
  rw [slowSharpLaw_of_valid h hn]
  exact hr

/-! ## Step 5 — the weakening

Exactly the loose file's two moves, at the sharp envelopes:

* the budget's accuracy slot, from the realised accuracy up to the clipped requested one
  (`Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb`, factor `64`) and then to the
  requested one (`Ttc.TtcSlowRuntimeFinal.sourceOneRunQueryBudget_clip_eps`, factor
  `(max 1 eps) ^ 2 * sourceLogFactor n ^ 2`);
* the accepted output window, from the realised relative error to the requested one
  (`Ttc.CVSourceReferenceWeaken.Icc_relErr_subset`, using
  `volume (interior a.1) = volume a.1`).

There is no interior-to-body radius move: `cvAdmCircum` pins the certificate's radial slot
to the interior circumradius the construction runs at. -/

/-- **The sharp certificate at the consumer's parameters.** -/
theorem exists_slowSharpFinalCertificate
    {n : Nat} (hn : 21 ≤ n) {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) :
    ∃ r : Measure (slowFinalOmega n a),
      SourceReferenceTVOneRunCertificate (slowSharpFinalLaw n a) r (slowFinalCost n a)
        (slowFinalValue n a) (slowSharpEffective n a) n (circumR (interior a.1)) a.2.1
        ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal) := by
  have hn1 : 1 ≤ n := by omega
  have hb0 : (0 : Real) < min a.2.1 1 := clipInput_eps_pos h
  have hb1 : min a.2.1 1 ≤ 1 := min_le_right _ _
  have hR0 : (0 : Real) ≤ circumR (interior a.1) := circumR_nonneg _
  obtain ⟨r, hr⟩ := exists_slowSharpCertificate_of_valid hn (clipInput_valid h) hb1
  refine ⟨r, hr.weaken_of_subset ?_ ?_⟩
  · -- the budget
    have hrc0 : (0 : Real) ≤ slowActualOverhead n (slowR2 n (clipInput a))
        (slowEpsInt n (clipInput a)) a.2.2
        (slowSharpLenvAt n (clipInput a)) (slowSharpTenvAt n (clipInput a)) :=
      slowActualOverhead_nonneg _ _ _ _ _ _
    have hreq0 : 0 < slowRealisedAccuracy n (clipInput a) :=
      slowAccuracyRequested_half_pos (slowPhases n (clipInput a))
        (slowStreams n (clipInput a)) hb0
    have hhalf : min a.2.1 1 / 2 ≤ slowRealisedAccuracy n (clipInput a) :=
      half_le_slowAccuracyRequested (slowPhases n (clipInput a))
        (slowStreams n (clipInput a)) hb0
    have habs := Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb
      (rc := slowActualOverhead n (slowR2 n (clipInput a)) (slowEpsInt n (clipInput a))
        a.2.2 (slowSharpLenvAt n (clipInput a)) (slowSharpTenvAt n (clipInput a)))
      (R := circumR (interior a.1)) (R' := circumR (interior a.1))
      (e := slowRealisedAccuracy n (clipInput a)) (eps := min a.2.1 1) (n := n)
      hrc0 hn1 hb0 hb1 hreq0 hhalf hR0 (le_refl _)
    have hclip := sourceOneRunQueryBudget_clip_eps (n := n)
      (rc := 64 * slowActualOverhead n (slowR2 n (clipInput a))
        (slowEpsInt n (clipInput a)) a.2.2
        (slowSharpLenvAt n (clipInput a)) (slowSharpTenvAt n (clipInput a)))
      (R := circumR (interior a.1)) (eps := a.2.1) (by positivity) h.1
    have hrw : slowSharpEffective n a =
        64 * (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2 *
          slowActualOverhead n (slowR2 n (clipInput a)) (slowEpsInt n (clipInput a))
            a.2.2 (slowSharpLenvAt n (clipInput a))
            (slowSharpTenvAt n (clipInput a)) := rfl
    have hconst : 64 * slowActualOverhead n (slowR2 n (clipInput a))
          (slowEpsInt n (clipInput a)) a.2.2
          (slowSharpLenvAt n (clipInput a)) (slowSharpTenvAt n (clipInput a)) *
          (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2 ≤ slowSharpEffective n a :=
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
theorem slowSharpCertificate_H :
    ∀ n, 21 ≤ n → ∀ a : Ttc.CVAdaptive.VolumeInput n, CVValidInput a →
      ∃ r : Measure (slowFinalOmega n a),
        SourceReferenceTVOneRunCertificate (slowSharpFinalLaw n a) r (slowFinalCost n a)
          (slowFinalValue n a) (slowSharpEffective n a) n (circumR (interior a.1)) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal) :=
  fun _ hn _ h ↦ exists_slowSharpFinalCertificate hn h

/-- **The TTC volume implementation built from the slow canonical route at the sharp
slack / transport pair**, with no residual hypothesis. -/
noncomputable def slowSharpImplementation :
    Ttc.CVShaped.CVShapedExpectedImplementation cvAdmCircum
      (Ttc.TtcShapedRuntime.shapeOf slowSharpOV) :=
  Ttc.TtcShapedRuntime.implementationOfEffectiveCertificatesGen cvAdmCircum
    cvAdmCircum_imp_cvAdmissible (fun _ K ↦ circumR (interior K))
    circumInterior_sq_le_of_cvAdmCircum slowSharpOV one_le_slowSharpOV
    slowSharpEffective slowSharpEffective_nonneg slowSharpEffective_le_slowSharpOV
    slowFinalOmega slowSharpFinalLaw slowFinalCost slowFinalValue
    measurable_slowFinalCost measurable_slowFinalValue slowSharpCertificate_H

section Capstone

open Ttc.CVShaped
open Ttc.TtcShapedRuntime
open Ttc.TTCCVExpectedImplementation
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem

variable {A : Type*}

/-- **TTC's accuracy and query cost, from the slow canonical volume construction at the
sharp slack / score-transport pair — unconditionally.**

There is no oracle binder, no certificate binder, no implementation binder and **no
cost-side binder**: the volume subroutine is `slowSharpImplementation.algorithm n`, built
here out of the slow canonical Gaussian-cooling construction run at
`Ttc.CVSharpUniformParameters.slowSharpSlack` and
`Ttc.CVSharpScoreTransport.slowSharpBoundSq`, and the two conjuncts are about the one law
`canonicalFullOperationalLaw V P` that executes it.

**The cost envelope.**  The volume term is the per-cube sum of
`cvComplexityShapeClipped * slowSharpOV`, each cube taken at **its own interior
circumradius squared** — the radius the construction actually runs at, pinned by
`Ttc.TtcCallCircumAdmissible.cvAdmCircum` — where

  `slowSharpOV n R2 eps p = 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
      slowActualOverhead n R2 (min eps 1 / 2) p
        (slowSharpLenv n R2 (min eps 1 / 2)) (slowSharpTenv n R2 (min eps 1 / 2))`.

That is an explicit closed-form polynomial-and-logarithm expression in `n`, `R2`, `eps`,
built out of the schedule's own phase count, stream count, the **sharp** retry cap
`Ttc.CVSharpUniformParameters.slowSharpRetriesCap` and the **sharp** per-phase mixing
deadline envelope `Ttc.CVSharpSlowSteps.slowSharpStepsEnvelope`, the latter still including
the slow schedule's compounding-warmness overhead but at the *dimension-free* share floor
`min (blockShare …) (1 / (54 * exp (8 R^2) ^ 2))`.  It is **not** the paper's
`O(m · n^5 · rho^2 · r_max)` exponents, and no constant here is pretending to be one: what
is proved is a bound at this explicit shape, not a match with the paper's asymptotics.

**What "sharp" buys, quantitatively.**  `Ttc.CVSharpSlowSteps.slowSharpStepsEnvelope_le_min`
machine-checks that this deadline envelope is below the loose route's best envelope
`Ttc.CVSlowRefreshSteps.slowMinStepsEnvelope` (under `2 ≤ n` and `1 ≤ R`, both of which
hold on every cube this capstone runs on), and
`Ttc.CVSharpUniformParameters.slowSharpRetriesCap_le_slowUniformRetriesCap` does the same
for the retry cap.  Neither comparison is used in the proof below; the capstone is a bound
at the sharp shape, and the comparison is the separate statement that the sharp shape is
the smaller one. -/
theorem ttc_volume_runtime_sharp
    {n : Nat} (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let I := slowSharpImplementation
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
    slowSharpOV one_le_slowSharpOV slowSharpEffective slowSharpEffective_nonneg
    slowSharpEffective_le_slowSharpOV slowFinalOmega slowSharpFinalLaw slowFinalCost
    slowFinalValue measurable_slowFinalCost measurable_slowFinalValue
    slowSharpCertificate_H
    atoms phi eps delta
    (fun j ↦ (circumR (interior (callBody atoms phi eps (4 * delta / 5) j))) ^ 2)
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol
    (fun j ↦ cvAdmCircum_callBody atoms phi eps (4 * delta / 5)
      h_eps_pos h_eps_le (le_trans (by norm_num) hn) hphi hvol j)

end Capstone

section AxiomCheck

#print axioms slowSharpEffective_le_slowSharpOV
#print axioms one_le_slowSharpOV
#print axioms slowSharpLaw_of_valid
#print axioms slowSharpLenvAt_eq
#print axioms slowSharpTenvAt_eq
#print axioms exists_slowSharpCertificate_of_valid
#print axioms exists_slowSharpFinalCertificate
#print axioms slowSharpCertificate_H
#print axioms slowSharpImplementation
#print axioms ttc_volume_runtime_sharp

end AxiomCheck

end Ttc.TtcSlowRuntimeSharp

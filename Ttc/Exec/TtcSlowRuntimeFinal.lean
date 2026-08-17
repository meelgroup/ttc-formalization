import Ttc.Exec.TtcShapedRuntimeFromCertificates
import Ttc.Exec.CVSlowTotalFamilies
import Ttc.Exec.CVSlowEffectiveOverhead
import Ttc.Exec.CVSlowCanonicalTailPhases
import Ttc.Exec.CVBudgetEpsAbsorb
import Ttc.Exec.CVSlowAccuracyStrict

/-!
# The unconditional TTC runtime capstone for the slow canonical volume route

This file joins the two halves of the runtime assembly:

* the **consumer**, `Ttc.TtcShapedRuntime.ttc_runtime_of_effectiveCertificates21`, which
  turns per-input one-run certificates into TTC's accuracy **and** query-cost bound;
* the **producer**, `Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical`, the
  slow canonical one-run certificate at the canonical parameter choices.

## The accuracy clip

`Ttc.CVEffectiveTotalise.CVValidInput` bounds the confidence `p` but **not** the accuracy
`eps`: it asks only `0 < a.2.1`.  The producer, on the other hand, needs its internal
accuracy in `(0, 1]`, and `Ttc.CVSlowAccuracyStrict`'s three strict bounds all carry
`epsIn ≤ 1`.  So the construction is run at the *clipped* accuracy

  `clipInput a = (a.1, min a.2.1 1, a.2.2)`,

which is a valid input whenever `a` is, and whose accuracy is in `(0, 1]`.  Nothing is lost
on the accuracy side (`min a.2.1 1 ≤ a.2.1`, so the realised window still sits inside the
requested one), and on the cost side the clip is paid for by the factor
`(max 1 eps) ^ 2 * sourceLogFactor n ^ 2` in the overhead envelope — see
`sourceOneRunQueryBudget_clip_eps`.

## The overhead envelope

The envelope the assembly is instantiated at is

  `slowFinalOV n R2 eps p = 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
      slowUniformOverheadQ n R2 (min eps 1 / 2) p`,

whose three explicit prefactors are, in order: the `64` of
`Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb` (moving the budget's accuracy slot
from the realised accuracy to the requested one), and the two factors that pay for the
accuracy clip above.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.TtcSlowRuntimeFinal

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling
open Ttc.CVSourcePolynomialCutoffCapstone (sourceLogFactor sourceOneRunQueryEnvelope
  sourceOneRunQueryBudget sourceLogFactor_pos)
open Ttc.CVEffectiveTotalise (CVValidInput)
open Ttc.TtcCircumRadius (circumR circumR_nonneg circumR_sq_le_of_cvAdmBall)
open Ttc.CVSlowEffectiveOverhead (slowUniformOverheadQ slowUniformOverheadQ_mono
  slowUniformOverheadQ_nonneg one_le_slowUniformOverheadQ slowUniformEffectiveQ
  slowUniformRetriesQ slowUniformDeadlineQ slowPhasesP slowStreamsP
  slowUniform_hscalarQ_circumR)
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
open Ttc.TtcCallBallAdmissible (callDeclaredR2)
open Ttc.CVSourceReferenceTVCapstone
open scoped ENNReal Classical BigOperators

variable {n : Nat}

/-! ## Step 1 — the accuracy clip -/

/-- The input with its accuracy clipped to `(0, 1]`.  The body and the confidence are
untouched. -/
noncomputable def clipInput (a : Ttc.CVAdaptive.VolumeInput n) :
    Ttc.CVAdaptive.VolumeInput n :=
  (a.1, min a.2.1 1, a.2.2)

@[simp] theorem clipInput_fst (a : Ttc.CVAdaptive.VolumeInput n) :
    (clipInput a).1 = a.1 := rfl

@[simp] theorem clipInput_eps (a : Ttc.CVAdaptive.VolumeInput n) :
    (clipInput a).2.1 = min a.2.1 1 := rfl

@[simp] theorem clipInput_p (a : Ttc.CVAdaptive.VolumeInput n) :
    (clipInput a).2.2 = a.2.2 := rfl

theorem clipInput_valid {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) :
    CVValidInput (clipInput a) :=
  ⟨lt_min h.1 zero_lt_one, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem clipInput_eps_pos {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) :
    0 < min a.2.1 1 := lt_min h.1 zero_lt_one

theorem clipInput_eps_le_one (a : Ttc.CVAdaptive.VolumeInput n) :
    min a.2.1 1 ≤ 1 := min_le_right _ _

theorem clipInput_eps_le (a : Ttc.CVAdaptive.VolumeInput n) :
    min a.2.1 1 ≤ a.2.1 := min_le_left _ _

/-! ## Step 2 — the price of the clip, inside the source-shaped budget -/

theorem one_le_sourceLogFactor (x : Real) : 1 ≤ sourceLogFactor x := le_max_left _ _

theorem sourceLogFactor_one : sourceLogFactor 1 = 1 := by
  unfold sourceLogFactor
  simp

/-- **The clip is paid for by an explicit factor.**

The source-shaped budget is *decreasing* in its accuracy slot, so replacing the requested
accuracy `eps` by the clipped `min eps 1` can only enlarge it.  The loss is bounded by the
explicit factor `(max 1 eps) ^ 2 * sourceLogFactor n ^ 2` on the runtime constant: the
quadratic slot loses exactly `eps ^ 2`, and the two accuracy-dependent clipped logarithms
lose at most `sourceLogFactor n ^ 2` between them (they are clipped below at `1`, and at
`min eps 1 = 1` they are `sourceLogFactor 1 = 1` and `sourceLogFactor n`). -/
theorem sourceOneRunQueryEnvelope_clip_eps
    {rc R eps : Real} {n : Nat} (hrc : 0 ≤ rc) (heps : 0 < eps) :
    sourceOneRunQueryEnvelope rc n R (min eps 1) ≤
      sourceOneRunQueryEnvelope (rc * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2) n R eps := by
  have hA0 : (0 : Real) ≤ max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) :=
    le_max_of_le_right (by positivity)
  have hLn : (1 : Real) ≤ sourceLogFactor n := one_le_sourceLogFactor _
  have hLn0 : (0 : Real) ≤ sourceLogFactor n := zero_le_one.trans hLn
  rcases le_total eps 1 with hle | hgt
  · -- the clip is inactive
    have hmin : min eps 1 = eps := min_eq_left hle
    have hmax : max 1 eps = 1 := max_eq_left hle
    rw [hmin, hmax]
    unfold sourceOneRunQueryEnvelope
    have hcore : (0 : Real) ≤ max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 *
        sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
        sourceLogFactor ((n : Real) / eps) ^ 2 := by
      have h1 : (0 : Real) ≤ max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 := by
        positivity
      have h2 : (0 : Real) ≤ sourceLogFactor (1 / eps) := (sourceLogFactor_pos _).le
      have h3 : (0 : Real) ≤ sourceLogFactor ((n : Real) / eps) := (sourceLogFactor_pos _).le
      positivity
    have hrc' : rc ≤ rc * 1 ^ 2 * sourceLogFactor n ^ 2 := by
      have : rc * 1 ≤ rc * sourceLogFactor n ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hrc
        nlinarith
      simpa using this
    exact mul_le_mul_of_nonneg_right hrc' hcore
  · -- the clip is active
    have hmin : min eps 1 = 1 := min_eq_right hgt
    have hmax : max 1 eps = eps := max_eq_right hgt
    have heps0 : eps ≠ 0 := heps.ne'
    rw [hmin, hmax]
    unfold sourceOneRunQueryEnvelope
    have hL1 : (1 : Real) ≤ sourceLogFactor (1 / eps) := one_le_sourceLogFactor _
    have hL2 : (1 : Real) ≤ sourceLogFactor ((n : Real) / eps) := one_le_sourceLogFactor _
    have hrw : rc * eps ^ 2 * sourceLogFactor n ^ 2 *
        (max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
          sourceLogFactor ((n : Real) / eps) ^ 2) =
        rc * (max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) *
          sourceLogFactor n ^ 2 * sourceLogFactor n ^ 2) *
          (sourceLogFactor (1 / eps) ^ 2 * sourceLogFactor ((n : Real) / eps) ^ 2) := by
      field_simp
    rw [hrw]
    have hleft : rc * (max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / 1 ^ 2 *
        sourceLogFactor n ^ 2 * sourceLogFactor (1 / 1) ^ 2 *
        sourceLogFactor ((n : Real) / 1) ^ 2) =
        rc * (max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) *
          sourceLogFactor n ^ 2 * sourceLogFactor n ^ 2) := by
      simp only [one_pow, div_one, sourceLogFactor_one]
      ring
    rw [hleft]
    have hbulk : (0 : Real) ≤ rc * (max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) *
        sourceLogFactor n ^ 2 * sourceLogFactor n ^ 2) := by positivity
    have hfac1 : (1 : Real) ≤ sourceLogFactor (1 / eps) ^ 2 := by nlinarith
    have hfac2 : (1 : Real) ≤ sourceLogFactor ((n : Real) / eps) ^ 2 := by nlinarith
    have hfac : (1 : Real) ≤ sourceLogFactor (1 / eps) ^ 2 *
        sourceLogFactor ((n : Real) / eps) ^ 2 := by nlinarith
    exact le_mul_of_one_le_right hbulk hfac

/-- `ENNReal` form of `sourceOneRunQueryEnvelope_clip_eps`. -/
theorem sourceOneRunQueryBudget_clip_eps
    {rc R eps : Real} {n : Nat} (hrc : 0 ≤ rc) (heps : 0 < eps) :
    sourceOneRunQueryBudget rc n R (min eps 1) ≤
      sourceOneRunQueryBudget (rc * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2) n R eps := by
  unfold sourceOneRunQueryBudget
  exact ENNReal.ofReal_le_ofReal (sourceOneRunQueryEnvelope_clip_eps hrc heps)

/-! ## Step 3 — the overhead envelope and the effective runtime constant -/

/-- **The overhead envelope the assembly is instantiated at.**  Cousins–Vempala's own
Theorem 1.1 expression is multiplied by this, and by nothing else. -/
noncomputable def slowFinalOV (n : Nat) (R2 eps p : Real) : Real :=
  64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
    slowUniformOverheadQ n R2 (min eps 1 / 2) p

/-- The per-input effective runtime constant: the same expression at the body's own
squared circumradius. -/
noncomputable def slowFinalEffective (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  64 * (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2 *
    slowUniformOverheadQ n (circumR a.1 ^ 2) (min a.2.1 1 / 2) a.2.2

theorem one_le_slowFinalOV (n : Nat) (R2 eps p : Real) : 1 ≤ slowFinalOV n R2 eps p := by
  unfold slowFinalOV
  have h1 : (1 : Real) ≤ (max 1 eps) ^ 2 := by
    have := le_max_left (1 : Real) eps
    nlinarith
  have h2 : (1 : Real) ≤ sourceLogFactor n ^ 2 := by
    have := one_le_sourceLogFactor (n : Real)
    nlinarith
  have h3 : (1 : Real) ≤ slowUniformOverheadQ n R2 (min eps 1 / 2) p :=
    one_le_slowUniformOverheadQ _ _ _ _
  have h64 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 := by nlinarith
  have h641 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 := by nlinarith
  nlinarith

theorem slowFinalOV_nonneg (n : Nat) (R2 eps p : Real) : 0 ≤ slowFinalOV n R2 eps p :=
  zero_le_one.trans (one_le_slowFinalOV n R2 eps p)

theorem slowFinalEffective_nonneg (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    0 ≤ slowFinalEffective n a := by
  unfold slowFinalEffective
  have h1 : (0 : Real) ≤ (max 1 a.2.1) ^ 2 := sq_nonneg _
  have h2 : (0 : Real) ≤ sourceLogFactor n ^ 2 := sq_nonneg _
  have h3 : (0 : Real) ≤ slowUniformOverheadQ n (circumR a.1 ^ 2) (min a.2.1 1 / 2) a.2.2 :=
    slowUniformOverheadQ_nonneg _ _ _ _
  positivity

/-- The `heff` binder of the assembly, at `runtimeConstant = 1`: the only input-dependent
factor is the overhead, and it is monotone in the declared squared radius. -/
theorem slowFinalEffective_le_slowFinalOV
    (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real)
    (hK : Ttc.CVShaped.cvAdmBall n K R2) :
    slowFinalEffective n (K, eps, p) ≤ slowFinalOV n R2 eps p := by
  unfold slowFinalEffective slowFinalOV
  have hmono : slowUniformOverheadQ n (circumR K ^ 2) (min eps 1 / 2) p ≤
      slowUniformOverheadQ n R2 (min eps 1 / 2) p :=
    slowUniformOverheadQ_mono n (min eps 1 / 2) p (circumR_sq_le_of_cvAdmBall hK)
  have hpre : (0 : Real) ≤ 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 := by
    have h1 : (0 : Real) ≤ (max 1 eps) ^ 2 := sq_nonneg _
    have h2 : (0 : Real) ≤ sourceLogFactor n ^ 2 := sq_nonneg _
    positivity
  exact mul_le_mul_of_nonneg_left hmono hpre

/-! ## Step 4 — the one residual obligation

Every binder of `Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` is discharged
below except its `hsteps`, the **per-phase mixing deadline of the recursive actual-warm
schedule**.

The repository bounds `Ttc.CVSlowSourceReferenceCertificate.slowScoreAwareSteps` — the
deadline at the *constant* reference warmness `slowReferenceWarm` and at the run-global
radius `slowGlobalRadiusQ` — by `slowUniformDeadlineCap`
(`Ttc.CVSlowUniformShareBounds.slowScoreAwareSteps_uniform_active_le`).  The frontier's
`hsteps`, however, is about
`Ttc.CVSlowRadiusQCanonicalOperational.slowCanonicalSteps`, whose warmness slot is the
*recursive* budget `2 * slowWarmBudget slowReferenceWarm …` and whose radius slot is the
`R`-aware `slowUniformQ`.  Those are different functions, and no bridge between them exists
in the development (the cold analogue,
`Ttc.CVRecursiveActualWarmRuntimeEnvelope.adjustableSpeedyDeadline_globalRadius_recursiveWarm_le`,
is stated at the cold schedule's `fixedSigmaSq` / `coldAcceptedFactor` /
`globalLogarithmicDelta`, none of which is the slow source schedule's).

So it is carried here as an explicit, named hypothesis and threaded all the way to the
capstone.  It is a *cost* statement only — no accuracy claim depends on it.

**It is stated as the bundled existential `SlowCostSideRealised`, not as the flat
inequality `deadline ≤ slowUniformDeadlineQ`.**  That flat form (`SlowDeadlineCapped`
below) is *sufficient* but is very probably **false**: the recursive warm budget multiplies
by `slowAcceptedFactor` at every phase, so `log (slowWarmBudget … i)` grows linearly in `i`
while `slowUniformDeadlineQ`'s payload is constant in the phase index.  Assuming a false
hypothesis would make the capstone vacuous, so what is assumed instead is exactly the
statement the runtime analysis has to establish: *some* per-phase deadline `T` bounds the
schedule's own selected deadline and still fits the declared one-run query budget.  The
budget has enormous slack for this — its Cousins–Vempala core factor is at least
`max (R² n², n³) / eps²` — so the bundled form is plausibly true where the flat one is
not. -/
noncomputable def slowRealisedAccuracy (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowAccuracyRequested (slowPhases n a) (slowStreams n a) (slowEpsInt n a)

/-- The deadline the slow canonical schedule actually selects at phase `i`, at this file's
parameter choices.  This is the left-hand side of the frontier's `hsteps` binder. -/
noncomputable def slowSelectedDeadline (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n)
    (i : Nat) : Nat :=
  slowCanonicalSteps slowReferenceWarm n
    (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a) (slowRadius n a))
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
    i 0

/-- **The residual cost-side obligation.**  There is a per-phase deadline `T` that bounds
the schedule's own selected deadline on every active phase and whose contribution to the
run's total query count fits the declared one-run query budget at this file's runtime
constant. -/
def SlowCostSideRealised (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Prop :=
  ∃ T : Nat,
    (∀ i, i < slowPhases n a → slowSelectedDeadline n a i ≤ T) ∧
    ((slowStreams n a : ENNReal) * (slowPhases n a : ENNReal) *
        ENNReal.ofReal (10 *
          (slowUniformRetriesQ n (slowR2 n a) (slowEpsInt n a) (slowRadius n a) : Real) *
          (T : Real) * (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget
        (slowUniformOverheadQ n (circumR (interior a.1) ^ 2) (slowEpsInt n a) a.2.2) n
        (slowRadius n a) (slowRealisedAccuracy n a))

/-- The flat sufficient condition: the schedule's own selected deadline is under the
*declared* cap `slowUniformDeadlineQ` on every active phase.  See the section docstring for
why this is stated only as a sufficient condition and is not the assumed one. -/
def SlowDeadlineCapped (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Prop :=
  ∀ i, i < slowPhases n a →
    slowSelectedDeadline n a i ≤
      slowUniformDeadlineQ n (slowR2 n a) (slowEpsInt n a) (slowRadius n a)

/-- `SlowDeadlineCapped` is sufficient: at `T := slowUniformDeadlineQ …` the scalar
conjunct is `Ttc.CVSlowEffectiveOverhead.slowUniform_hscalarQ_circumR`, which is already
proved. -/
theorem slowCostSideRealised_of_deadlineCapped
    {n : Nat} {a : Ttc.CVAdaptive.VolumeInput n} (hn : 21 ≤ n)
    (h : CVValidInput a) (heps1 : a.2.1 ≤ 1) (hcap : SlowDeadlineCapped n a) :
    SlowCostSideRealised n a := by
  have hn1 : 1 ≤ n := by omega
  have heps : (0 : Real) < slowEpsInt n a := by
    have := h.1; unfold slowEpsInt; linarith
  have heps1' : slowEpsInt n a ≤ 1 := by unfold slowEpsInt; linarith
  refine ⟨slowUniformDeadlineQ n (slowR2 n a) (slowEpsInt n a) (slowRadius n a), hcap, ?_⟩
  exact slowUniform_hscalarQ_circumR n hn1 (K := interior a.1)
    (m := slowPhases n a) (k := slowStreams n a)
    (epsP := slowEpsInt n a) (requested := slowRealisedAccuracy n a) (p := a.2.2)
    heps heps1' (slowAccuracyRequested_half_pos (slowPhases n a) (slowStreams n a) h.1)
    (slowAccuracyRequested_half_lt_one (slowPhases n a) h.1 heps1) (le_refl _) (le_refl _)

/-! ## Step 5 — the producer, at this file's parameter choices -/

/-- **The one-run certificate on a valid input of accuracy at most one.**

This is `Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` with every binder
discharged at the parameter choices of `Ttc.CVSlowTotalFamilies`, except the cost side's
`hsteps`/`hscalar` pair, which is the hypothesis `SlowCostSideRealised n a`. -/
theorem exists_slowCertificate_of_valid
    {n : Nat} (hn : 21 ≤ n) {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) (heps1 : a.2.1 ≤ 1) (hcost : SlowCostSideRealised n a) :
    ∃ r : Measure (slowOmega n a),
      SourceReferenceTVOneRunCertificate (slowLaw n a) r (slowCost n a) (slowValue n a)
        (slowUniformOverheadQ n (circumR (interior a.1) ^ 2) (slowEpsInt n a) a.2.2)
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
  -- the seed schedule
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
  -- the same instance in the producer's own spelling of the phase and stream counts
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
  have hretries : ∀ i,
      scoreAwareRetries (slowPhases n a + 1) (slowStreams n a) (slowEpsInt n a / 2)
        (slowUniformSlack n (slowPhases n a) (interior a.1))
        (slowUniformBoundSq n (slowRadius n a)) i ≤
      slowUniformRetriesQ n (slowR2 n a) (slowEpsInt n a) (slowRadius n a) := fun i ↦
    scoreAwareRetries_slowUniform_le hn1 (m := slowPhases n a + 1)
      (k := slowStreams n a) (chainLength := slowPhases n a)
      (eps := slowEpsInt n a / 2) (R := slowRadius n a) (by linarith)
      hK hball hfin i
  obtain ⟨T, hsteps, hscalar⟩ := hcost
  obtain ⟨r, hr⟩ := exists_slowOneRunCertificate_canonical hn
    (eps := slowEpsInt n a) (R := slowRadius n a) (R2 := slowR2 n a)
    heps heps1' (le_refl _) hK hKc hball hfin hKR rfl
    hmoments.1 hmoments.2.1 hmoments.2.2.1 hmoments.2.2.2.1 hmoments.2.2.2.2
    (runtimeConstant :=
      slowUniformOverheadQ n (circumR (interior a.1) ^ 2) (slowEpsInt n a) a.2.2)
    T (slowUniformRetriesQ n (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
    (fun i hi ↦ hsteps i hi) (fun i _ ↦ hretries i) hscalar
  refine ⟨r, ?_⟩
  rw [slowLaw_of_valid h hn]
  exact hr

/-! ## Step 6 — the four total families the assembly consumes -/

/-- The index type of one run, at the clipped input. -/
abbrev slowFinalOmega (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Type :=
  slowOmega n (clipInput a)

/-- The law of one run, at the clipped input. -/
noncomputable def slowFinalLaw (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measure (slowFinalOmega n a) := slowLaw n (clipInput a)

/-- The recorded query cost of one run, at the clipped input. -/
noncomputable def slowFinalCost (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowFinalOmega n a → ENNReal := slowCost n (clipInput a)

/-- The estimate one run reports, at the clipped input. -/
noncomputable def slowFinalValue (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowFinalOmega n a → Real := slowValue n (clipInput a)

theorem measurable_slowFinalCost (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measurable (slowFinalCost n a) := measurable_slowCost n (clipInput a)

theorem measurable_slowFinalValue (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measurable (slowFinalValue n a) := measurable_slowValue n (clipInput a)

/-! ## Step 7 — the weakening -/

/-- **The certificate at the consumer's parameters.**

Three moves: the budget's accuracy slot goes from the realised accuracy up to the clipped
requested accuracy (`Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb`, factor `64`,
which simultaneously moves the radius from `circumR (interior a.1)` to `circumR a.1`), then
from the clipped accuracy to the requested one (`sourceOneRunQueryBudget_clip_eps`), and
the accepted output window widens from the realised relative error to the requested one
(`Ttc.CVSourceReferenceWeaken.Icc_relErr_subset`, using
`volume (interior a.1) = volume a.1`). -/
theorem exists_slowFinalCertificate
    {n : Nat} (hn : 21 ≤ n) {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a)
    (hcost : SlowCostSideRealised n (clipInput a)) :
    ∃ r : Measure (slowFinalOmega n a),
      SourceReferenceTVOneRunCertificate (slowFinalLaw n a) r (slowFinalCost n a)
        (slowFinalValue n a) (slowFinalEffective n a) n (circumR a.1) a.2.1
        ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal) := by
  have hn1 : 1 ≤ n := by omega
  have hb0 : (0 : Real) < min a.2.1 1 := clipInput_eps_pos h
  have hb1 : min a.2.1 1 ≤ 1 := min_le_right _ _
  have hRR : circumR (interior a.1) ≤ circumR a.1 :=
    Ttc.CVValidInteriorBridge.circumR_interior_le h.isBounded
  have hR0 : (0 : Real) ≤ circumR (interior a.1) := circumR_nonneg _
  obtain ⟨r, hr⟩ := exists_slowCertificate_of_valid hn (clipInput_valid h) hb1 hcost
  refine ⟨r, hr.weaken_of_subset ?_ ?_⟩
  · -- the budget
    have hrc0 : (0 : Real) ≤
        slowUniformOverheadQ n (circumR (interior a.1) ^ 2)
          (slowEpsInt n (clipInput a)) a.2.2 := slowUniformOverheadQ_nonneg _ _ _ _
    have hreq0 : 0 < slowRealisedAccuracy n (clipInput a) :=
      slowAccuracyRequested_half_pos (slowPhases n (clipInput a))
        (slowStreams n (clipInput a)) hb0
    have hhalf : min a.2.1 1 / 2 ≤ slowRealisedAccuracy n (clipInput a) :=
      half_le_slowAccuracyRequested (slowPhases n (clipInput a))
        (slowStreams n (clipInput a)) hb0
    have habs := Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb
      (rc := slowUniformOverheadQ n (circumR (interior a.1) ^ 2)
        (slowEpsInt n (clipInput a)) a.2.2)
      (R := circumR (interior a.1)) (R' := circumR a.1)
      (e := slowRealisedAccuracy n (clipInput a)) (eps := min a.2.1 1) (n := n)
      hrc0 hn1 hb0 hb1 hreq0 hhalf hR0 hRR
    have hclip := sourceOneRunQueryBudget_clip_eps (n := n)
      (rc := 64 * slowUniformOverheadQ n (circumR (interior a.1) ^ 2)
        (slowEpsInt n (clipInput a)) a.2.2)
      (R := circumR a.1) (eps := a.2.1) (by positivity) h.1
    have hsq : circumR (interior a.1) ^ 2 ≤ circumR a.1 ^ 2 := by nlinarith
    have hmono0 : slowUniformOverheadQ n (circumR (interior a.1) ^ 2)
        (slowEpsInt n (clipInput a)) a.2.2 ≤
        slowUniformOverheadQ n (circumR a.1 ^ 2) (slowEpsInt n (clipInput a)) a.2.2 :=
      slowUniformOverheadQ_mono n _ _ hsq
    have hpre : (0 : Real) ≤ 64 * (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2 := by
      have h1 : (0 : Real) ≤ (max 1 a.2.1) ^ 2 := sq_nonneg _
      have h2 : (0 : Real) ≤ sourceLogFactor n ^ 2 := sq_nonneg _
      positivity
    have hconst : 64 * slowUniformOverheadQ n (circumR (interior a.1) ^ 2)
          (slowEpsInt n (clipInput a)) a.2.2 * (max 1 a.2.1) ^ 2 *
          sourceLogFactor n ^ 2 ≤ slowFinalEffective n a := by
      unfold slowFinalEffective
      calc 64 * slowUniformOverheadQ n (circumR (interior a.1) ^ 2)
              (slowEpsInt n (clipInput a)) a.2.2 * (max 1 a.2.1) ^ 2 *
              sourceLogFactor n ^ 2
          = (64 * (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2) *
              slowUniformOverheadQ n (circumR (interior a.1) ^ 2)
                (slowEpsInt n (clipInput a)) a.2.2 := by ring
        _ ≤ (64 * (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2) *
              slowUniformOverheadQ n (circumR a.1 ^ 2)
                (slowEpsInt n (clipInput a)) a.2.2 :=
            mul_le_mul_of_nonneg_left hmono0 hpre
    have hcore : (0 : Real) ≤
        max (circumR a.1 ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / a.2.1 ^ 2 *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / a.2.1) ^ 2 *
          sourceLogFactor ((n : Real) / a.2.1) ^ 2 := by
      have h0 : (0 : Real) ≤ max (circumR a.1 ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) :=
        le_max_of_le_right (by positivity)
      have h1 : (0 : Real) ≤ sourceLogFactor (1 / a.2.1) := (sourceLogFactor_pos _).le
      have h2 : (0 : Real) ≤ sourceLogFactor ((n : Real) / a.2.1) :=
        (sourceLogFactor_pos _).le
      have h3 : (0 : Real) ≤ sourceLogFactor n := (sourceLogFactor_pos _).le
      have h4 : (0 : Real) ≤
          max (circumR a.1 ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / a.2.1 ^ 2 := by
        positivity
      positivity
    exact habs.trans (hclip.trans
      (Ttc.CVSourceReferenceWeaken.sourceOneRunQueryBudget_mono_constant hconst hcore))
  · -- the accepted output window
    have hle : slowRealisedAccuracy n (clipInput a) ≤ a.2.1 :=
      (slowAccuracyRequested_half_le (slowPhases n (clipInput a)) hb0 hb1).trans
        (min_le_left _ _)
    exact Ttc.CVSourceReferenceWeaken.Icc_relErr_subset hle ENNReal.toReal_nonneg
      (Ttc.CVValidInteriorBridge.toReal_volume_interior_eq_of_convex h.2.2.2.1)

/-! ## Step 8 — the `H` binder and the capstone -/

/-- The residual cost-side obligation, quantified the way the assembly asks for it. -/
def SlowCostSideHypothesis : Prop :=
  ∀ (n : Nat), 21 ≤ n → ∀ a : Ttc.CVAdaptive.VolumeInput n, CVValidInput a →
    SlowCostSideRealised n (clipInput a)

/-- **The `H` binder of `Ttc.TtcShapedRuntime.ttc_runtime_of_effectiveCertificates21`**,
verbatim in the consumer's shape, at this file's four total families. -/
theorem slowOneRunCertificate_H (hcost : SlowCostSideHypothesis) :
    ∀ n, 21 ≤ n → ∀ a : Ttc.CVAdaptive.VolumeInput n, CVValidInput a →
      ∃ r : Measure (slowFinalOmega n a),
        SourceReferenceTVOneRunCertificate (slowFinalLaw n a) r (slowFinalCost n a)
          (slowFinalValue n a) (slowFinalEffective n a) n (circumR a.1) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal) :=
  fun n hn a h ↦ exists_slowFinalCertificate hn h (hcost n hn a h)

/-- **The TTC volume implementation built from the slow canonical route.** -/
noncomputable def slowImplementation (hcost : SlowCostSideHypothesis) :
    Ttc.CVShaped.CVShapedExpectedImplementation Ttc.CVShaped.cvAdmBall
      (Ttc.TtcShapedRuntime.shapeOf slowFinalOV) :=
  Ttc.TtcShapedRuntime.implementationOfEffectiveCertificates21 slowFinalOV
    one_le_slowFinalOV slowFinalEffective slowFinalEffective_nonneg
    slowFinalEffective_le_slowFinalOV slowFinalOmega slowFinalLaw slowFinalCost
    slowFinalValue measurable_slowFinalCost measurable_slowFinalValue
    (slowOneRunCertificate_H hcost)

section Capstone

open Ttc.CVShaped
open Ttc.TtcShapedRuntime
open Ttc.TTCCVExpectedImplementation
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem

variable {A : Type*}

/-- **TTC's accuracy and query cost, from the slow canonical volume construction.**

There is no oracle binder, no certificate binder and no implementation binder: the volume
subroutine is `(slowImplementation hcost).algorithm n`, built here out of the slow
canonical Gaussian-cooling construction, and the two conjuncts are about the one law
`canonicalFullOperationalLaw V P` that executes it.

**The cost envelope.**  The volume term is the per-cube sum of
`cvComplexityShapeClipped * slowFinalOV` at each cube's own *declared* outer radius
squared (`callDeclaredR2`), where

  `slowFinalOV n R2 eps p = 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
      slowUniformOverheadQ n R2 (min eps 1 / 2) p`.

That is an explicit closed-form polynomial-and-logarithm expression in `n`, `R2`, `eps`,
built out of the schedule's own phase count, stream count, retry cap and mixing deadline.
It is **not** the paper's `O(m · n^5 · rho^2 · r_max)` exponents, and no constant here is
pretending to be one: what is proved is a bound at this explicit shape, not a match with
the paper's asymptotics.

**The residual hypothesis.**  `hcost : SlowCostSideHypothesis` is the one obligation this
development does not discharge — the per-phase mixing deadline of the *recursive
actual-warm* slow schedule, bundled with its contribution to the one-run query budget.  See
the Step 4 docstring for exactly what is missing and why it is stated in bundled form.
Nothing in the accuracy conjunct depends on it. -/
theorem ttc_volume_runtime_slow
    (hcost : SlowCostSideHypothesis)
    {n : Nat} (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let I := slowImplementation hcost
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      shapedVolumeQueryEnvelopeAt I atoms phi eps deltaRun
        (fun j ↦ callDeclaredR2 atoms phi eps deltaRun j) +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) :=
  ttc_runtime_of_effectiveCertificates21 slowFinalOV one_le_slowFinalOV
    slowFinalEffective slowFinalEffective_nonneg slowFinalEffective_le_slowFinalOV
    slowFinalOmega slowFinalLaw slowFinalCost slowFinalValue
    measurable_slowFinalCost measurable_slowFinalValue (slowOneRunCertificate_H hcost)
    atoms phi eps delta h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol

end Capstone

section AxiomCheck

#print axioms clipInput_valid
#print axioms sourceOneRunQueryBudget_clip_eps
#print axioms one_le_slowFinalOV
#print axioms slowFinalEffective_le_slowFinalOV

end AxiomCheck

end Ttc.TtcSlowRuntimeFinal

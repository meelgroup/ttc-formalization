import ArlibCommunity.Algorithms.CV18.Program
import Kr25Ssmxt.Analysis.CV18VolumeAdapter
import Kr25Ssmxt.Analysis.TheoremProof
import ArlibCommunity.Algorithms.CV18

/-!
# Discharging TTC's volume oracle with arlib-community CV18

This module instantiates `NormalizedCV18VolumeProvider` with the executable,
scheduled and amplified membership-oracle program proved correct in the current
`arlib-community` CV18 development.  The only geometric work here is the
already-proved normalization of a TTC polytope and a harmless explicit choice
of its second-moment parameter.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Kr25Ssmxt
namespace CommunityCV18

open ArlibCommunity.Algorithms.CV18

/-- A TTC normalized polytope as the convex-body input expected by CV18. -/
def input {n : Nat} (P : PolytopeData n) : VolumeInput n where
  body :=
    { carrier := P.cv18Body
      convex' := P.cv18Body_convex
      isCompact' := Metric.isCompact_of_isClosed_isBounded
        P.cv18Body_closed P.cv18Body_bounded
      nonempty' := ⟨0, P.closedUnitBall_subset_cv18Body
        (Metric.mem_closedBall_self (by norm_num : (0 : Real) ≤ 1))⟩ }
  unitBall_subset := P.closedUnitBall_subset_cv18Body

@[simp] theorem input_body {n : Nat} (P : PolytopeData n) :
    ((input P).body : Set (AmbientSpace n)) = P.cv18Body := by
  rfl

/-- Exact decidable membership in the finite halfspace presentation. -/
noncomputable def oracle {n : Nat} (P : PolytopeData n) : MembershipOracle (input P) := by
  classical
  exact
    { query := query P
      correct := fun x => by
        simp [query] }

lemma roundness_pos {n : Nat} (P : PolytopeData n) : 0 < roundness P := by
  unfold roundness
  positivity

lemma wellRounded {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    WellRounded (params hn P eta delta h) (input P) := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have habs : uniformSecondMoment (input P) ≤
      |uniformSecondMoment (input P)| := le_abs_self _
  have hnonneg : 0 ≤ |uniformSecondMoment (input P)| + 1 := by positivity
  have hmoment : uniformSecondMoment (input P) =
      (∫ x in P.cv18Body, ‖x‖ ^ 2) / (volume P.cv18Body).toReal := by
    rfl
  rw [hmoment] at habs hnonneg
  change uniformSecondMoment (input P) ≤ roundness P * (n : Real)
  rw [hmoment]
  unfold roundness
  nlinarith

instance law_probability {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    IsProbabilityMeasure (law hn P eta delta h) := by
  apply MembershipOracleProgram.runEstimate_isProbabilityMeasure
  exact (amplifyOracleProgram_semantics
    figureOneFinalScheduledCappedValueProgram (params hn P eta delta h)
      (oracle P).query
      (figureOneFinalScheduledCappedValueProgram_stronglyMeasurable
        (params hn P eta delta h) (input P) (oracle P))).1.estimateMeasurable

private lemma relErr_half_mono {x target eta : Real} (htarget : 0 ≤ target)
    (heta : 0 ≤ eta) (hx : x ∈ Arlib.relErr (eta / 2) target) :
    x ∈ Arlib.relErr eta target := by
  rw [Arlib.mem_relErr] at hx ⊢
  constructor <;> nlinarith [htarget, heta]

lemma taggedLaw_spec {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    IsProbabilityMeasure (taggedLaw hn P eta delta h) ∧
      (taggedLaw hn P eta delta h).real {o | o.1 = false} ≤ delta ∧
      ∀ᵐ o ∂taggedLaw hn P eta delta h, o.1 = true →
        (o.2 : Real) ∈ Arlib.relErr eta (volume P.cv18Body).toReal := by
  letI : IsProbabilityMeasure (law hn P eta delta h) :=
    law_probability hn P eta delta h
  -- The public arlib-community headline for the named CV18 program.
  obtain ⟨_, _, hfinal⟩ := cv18TheoremOneOne_program
  have hevent : accurateOutcome (params hn P eta delta h) (input P) =
      successSet P eta := by
    rfl
  have hsuccessCommunity :=
    (hfinal (params hn P eta delta h) (input P) (oracle P)
      (wellRounded hn P eta delta h)).1
  have hsuccessCommunity' :
      1 - delta / 2 ≤ (law hn P eta delta h).real
        (accurateOutcome (params hn P eta delta h) (input P)) := by
    change 1 - delta / 2 ≤
      ((law hn P eta delta h)
        (accurateOutcome (params hn P eta delta h) (input P))).toReal
    rw [← outcomeProbability_eq_measure]
    simpa [law, algorithm, cv18Program, params, volumeAlgorithmLaw, oracle]
      using hsuccessCommunity
  rw [hevent] at hsuccessCommunity'
  have hsuccess : 1 - delta ≤ (law hn P eta delta h).real (successSet P eta) := by
    linarith [h.2.2.1]
  have haccuracy : ∀ x,
      x ∈ successSet P eta →
      (Real.toNNReal x : Real) ∈ Arlib.relErr eta (volume P.cv18Body).toReal := by
    intro x hx
    have hx' : x ∈ Arlib.relErr (eta / 2) (volume P.cv18Body).toReal := by
      exact hx
    have htarget : 0 ≤ (volume P.cv18Body).toReal := ENNReal.toReal_nonneg
    have hx0 : 0 ≤ x := by
      rw [Arlib.mem_relErr] at hx'
      have heta1 := h.2.1
      nlinarith [hx'.1]
    rw [Real.coe_toNNReal x hx0]
    exact relErr_half_mono htarget h.1.le hx'
  have hgeneric := taggedVolumeLaw_spec (law hn P eta delta h)
    (good := successSet P eta) (by exact measurableSet_Icc)
    measurable_real_toNNReal hsuccess haccuracy
  simpa [taggedLaw, successTag, taggedVolumeLaw, volumeSuccessTag] using hgeneric

/-- Contract of the direct CV18 call declared on the model surface. -/
theorem communityCV18VolumeLaw_spec {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    IsProbabilityMeasure (communityCV18VolumeLaw hn P eta delta) ∧
      (communityCV18VolumeLaw hn P eta delta).real {o | o.1 = false} ≤ delta ∧
      ∀ᵐ o ∂communityCV18VolumeLaw hn P eta delta, o.1 = true →
        (o.2 : Real) ∈ Arlib.relErr eta (volume P.carrier).toReal := by
  have htag := taggedLaw_spec hn P eta delta h
  letI : IsProbabilityMeasure (taggedLaw hn P eta delta h) := htag.1
  simpa only [communityCV18VolumeLaw, dif_pos h] using
    P.rescaleCV18Law_spec (taggedLaw hn P eta delta h) htag.2.1 htag.2.2

/-- The requested TTC normalized-volume provider, with no volume-oracle or
mixing hypothesis left to the caller. -/
def provider (n : Nat) (hn : 3 ≤ n) : NormalizedCV18VolumeProvider n :=
  NormalizedCV18VolumeProvider.ofAdmissible
    (fun P eta delta h => taggedLaw hn P eta delta h)
    (fun P eta delta h => (taggedLaw_spec hn P eta delta h).1)
    (fun P eta delta h => (taggedLaw_spec hn P eta delta h).2.1)
    (fun P eta delta h => (taggedLaw_spec hn P eta delta h).2.2)

/-- Replace the volume field of any TTC oracle bundle by the discharged
community CV18 implementation. -/
def install {n k : Nat} (hn : 3 ≤ n) (O : TTCOracles n k) : TTCOracles n k :=
  O.withNormalizedCV18Volume (provider n hn)

theorem install_volume_contract {n k : Nat} (hn : 3 ≤ n)
    (O : TTCOracles n k) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams) :
    ComputeVolumeContract (install hn O) F hbounded p :=
  withNormalizedCV18Volume_volume_contract O (provider n hn) F hbounded p

/-- The community theorem also supplies an explicit membership-query bound
for exactly the program used by `provider`. -/
theorem membershipCostBound {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    ∃ C : Real, 0 < C ∧ ∃ calls,
      (algorithm (params hn P eta delta h)).MembershipCostBound calls ∧
      calls ≤ Nat.ceil
        (C * (volumeScheduledBaseComplexityRate (params hn P eta delta h) *
          protectedLog (1 / (params hn P eta delta h).p))) := by
  -- The public arlib-community headline for the named CV18 program.
  obtain ⟨C, hC, htheorem⟩ := cv18TheoremOneOne_program
  let q := params hn P eta delta h
  have hsteps : modelTerminalPhaseSteps q = terminalPhaseSteps q := by
    unfold modelTerminalPhaseSteps terminalPhaseSteps
    rw [Nat.sInf_def]
    rfl
  have hrate : volumeTheoremOneOneRate q =
      volumeScheduledBaseComplexityRate q * protectedLog (1 / q.p) := by
    simp only [volumeTheoremOneOneRate, hsteps,
      volumeScheduledBaseComplexityRate, figureOneScheduledAccuracyLog,
      figureOneScheduledCoreError, figureOneScheduledRadialError,
      figureOneCorrectedBlockMixingError, figureOneSafeRetryCount,
      figureOnePerSampleMixingError, figureOneDependentEpsilon,
      figureOneDependentAlpha, figureOneDependentPhaseCount,
      figureOneDependentMaxSampleCount, figureOneFixedSampleCount,
      figureOneSampleCount]
  obtain ⟨_, calls, hcalls, hle⟩ :=
    htheorem q (input P) (oracle P) (wellRounded hn P eta delta h)
  refine ⟨C, hC, calls, hcalls, ?_⟩
  rw [← hrate]
  exact hle

#print axioms provider
#print axioms membershipCostBound
#print axioms install_volume_contract

end CommunityCV18
end Kr25Ssmxt

import Kr25Ssmxt.Analysis.CV18VolumeAdapter
import Kr25Ssmxt.Model.Theorem
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
    { query := fun x => if x ∈ P.cv18Body then true else false
      correct := fun x => by
        change (if x ∈ P.cv18Body then true else false) = true ↔ x ∈ P.cv18Body
        simp }

/-- A positive roundness factor large enough for the actual second moment.
It is data passed to CV18, not an additional hypothesis. -/
def roundness {n : Nat} (P : PolytopeData n) : Real :=
  |uniformSecondMoment (input P)| + 1

lemma roundness_pos {n : Nat} (P : PolytopeData n) : 0 < roundness P := by
  unfold roundness
  positivity

/-- We run the community algorithm at half the requested error and failure
budgets.  This handles TTC's allowed endpoint `eta = 1`/`delta = 1`, while
CV18's public parameter type asks for strict inequalities. -/
def params {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) : VolumeParams where
  n := n
  dim_ok := hn
  eps := eta / 2
  heps := by
    constructor
    · exact div_pos h.1 (by norm_num)
    · linarith [h.2.1]
  p := delta / 2
  hp := by
    constructor
    · exact div_pos h.2.2.1 (by norm_num)
    · linarith [h.2.2.2]
  roundness := roundness P
  roundness_pos := roundness_pos P

lemma wellRounded {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    WellRounded (params hn P eta delta h) (input P) := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have habs : uniformSecondMoment (input P) ≤
      |uniformSecondMoment (input P)| := le_abs_self _
  have hnonneg : 0 ≤ |uniformSecondMoment (input P)| + 1 := by positivity
  unfold WellRounded params roundness
  nlinarith

/-- The concrete amplified program selected by the community capstone. -/
def algorithm : VolumeAlgorithm :=
  amplifyOracleProgram figureOneFinalScheduledCappedValueProgram

/-- The real-valued estimator law before TTC tagging and affine rescaling. -/
def law {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) : Measure Real :=
  volumeAlgorithmLaw algorithm (params hn P eta delta h) (input P) (oracle P)

instance law_probability {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    IsProbabilityMeasure (law hn P eta delta h) := by
  apply MembershipOracleProgram.runEstimate_isProbabilityMeasure
  exact (amplifyOracleProgram_semantics
    figureOneFinalScheduledCappedValueProgram (params hn P eta delta h)
      (oracle P).query
      (figureOneFinalScheduledCappedValueProgram_stronglyMeasurable
        (params hn P eta delta h) (input P) (oracle P))).1.estimateMeasurable

/-- The CV18 success event tagged as TTC's `Bool × NNReal` outcome. -/
def taggedLaw {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    Measure VolumeOutcome :=
  taggedVolumeLaw (law hn P eta delta h)
    (accurateOutcome (params hn P eta delta h) (input P)) Real.toNNReal

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
  obtain ⟨_, _, hfinal⟩ := volumeTheorem_finalScheduled
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
    simpa [law, algorithm, params] using hsuccessCommunity
  have hsuccess : 1 - delta ≤ (law hn P eta delta h).real
      (accurateOutcome (params hn P eta delta h) (input P)) := by
    linarith [h.2.2.1]
  have haccuracy : ∀ x,
      x ∈ accurateOutcome (params hn P eta delta h) (input P) →
      (Real.toNNReal x : Real) ∈ Arlib.relErr eta (volume P.cv18Body).toReal := by
    intro x hx
    have hx' : x ∈ Arlib.relErr (eta / 2) (volume P.cv18Body).toReal := by
      change x ∈ Arlib.relErr (eta / 2) (euclideanVolume (input P)) at hx
      simpa only [euclideanVolume, input_body] using hx
    have htarget : 0 ≤ (volume P.cv18Body).toReal := ENNReal.toReal_nonneg
    have hx0 : 0 ≤ x := by
      rw [Arlib.mem_relErr] at hx'
      have heta1 := h.2.1
      nlinarith [hx'.1]
    rw [Real.coe_toNNReal x hx0]
    exact relErr_half_mono htarget h.1.le hx'
  change IsProbabilityMeasure
      (taggedVolumeLaw (law hn P eta delta h)
        (accurateOutcome (params hn P eta delta h) (input P)) Real.toNNReal) ∧
    (taggedVolumeLaw (law hn P eta delta h)
      (accurateOutcome (params hn P eta delta h) (input P)) Real.toNNReal).real
        {o | o.1 = false} ≤ delta ∧
    ∀ᵐ o ∂taggedVolumeLaw (law hn P eta delta h)
      (accurateOutcome (params hn P eta delta h) (input P)) Real.toNNReal,
      o.1 = true → (o.2 : Real) ∈ Arlib.relErr eta (volume P.cv18Body).toReal
  exact taggedVolumeLaw_spec (law hn P eta delta h)
      (accurateOutcome_measurable (params hn P eta delta h) (input P))
      measurable_real_toNNReal hsuccess haccuracy

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

theorem install_samples_contract {n k : Nat} (hn : 3 ≤ n)
    (O : TTCOracles n k) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams)
    (h : GenerateSamplesContract O F hbounded p) :
    GenerateSamplesContract (install hn O) F hbounded p :=
  withNormalizedCV18Volume_samples_contract O (provider n hn) F hbounded p h

/-- TTC's headline accuracy theorem with the volume premise eliminated by
the current arlib-community CV18 capstone.  A sampling contract remains an
independent input, exactly as in TTC's model interface. -/
theorem ttc_volume_accuracy
    (hprior : Prior) {n k : Nat} (hn : 3 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (O : TTCOracles n k)
    (hsamples : GenerateSamplesContract O F hbounded p)
    (hregime :
      let D := O.preprocessing.run F hbounded
      let b := (O.preprocessing.choosePrecision D p).value
      D.componentCount = 0 ∨
        p.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real)) :
    IsProbabilityMeasure (Kr25Ssmxt.ttc F hbounded p (install hn O)) ∧
      (Kr25Ssmxt.ttc F hbounded p (install hn O)).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr p.epsilon (volume (solutionSet F)).toReal} ≥
        1 - p.delta := by
  apply Kr25Ssmxt.ttc_volume_accuracy hprior (by omega) F hbounded p (install hn O)
    (install_volume_contract hn O F hbounded p)
    (install_samples_contract hn O F hbounded p hsamples)
  simpa [install, TTCOracles.withNormalizedCV18Volume] using hregime

/-- The community theorem also supplies an explicit membership-query bound
for exactly the program used by `provider`. -/
theorem membershipCostBound {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    ∃ C : Real, 0 < C ∧ ∃ calls,
      (algorithm (params hn P eta delta h)).MembershipCostBound calls ∧
      calls ≤ Nat.ceil
        (C * (volumeScheduledBaseComplexityRate (params hn P eta delta h) *
          protectedLog (1 / (params hn P eta delta h).p))) := by
  obtain ⟨C, hC, htheorem⟩ := volumeTheorem_finalScheduled
  obtain ⟨_, calls, hcalls, hle⟩ :=
    htheorem (params hn P eta delta h) (input P) (oracle P)
      (wellRounded hn P eta delta h)
  exact ⟨C, hC, calls, hcalls.toMembershipCostBound, hle⟩

#print axioms provider
#print axioms membershipCostBound
#print axioms install_volume_contract
#print axioms ttc_volume_accuracy

end CommunityCV18
end Kr25Ssmxt

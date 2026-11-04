import Kr25Ssmxt.Model.Run
import Kr25Ssmxt.Analysis.CV18HitAndRunOracles
import Kr25Ssmxt.Analysis.TTCPaperRuntime
import Kr25Ssmxt.Analysis.ManuscriptComponentExpectation
import Kr25Ssmxt.Analysis.CV18RoundnessBound
import Kr25Ssmxt.Analysis.RateLogBound
import Kr25Ssmxt.Analysis.NormalizedDiameterRuntime
import Kr25Ssmxt.Analysis.ClippedVolumeRate
import Kr25Ssmxt.Analysis.ThresholdCapBound
import Kr25Ssmxt.Analysis.UniformBudgetAlgebra
import Kr25Ssmxt.Analysis.ManuscriptRateKernelMeasurable
import Kr25Ssmxt.Analysis.ManuscriptRunMarginal

namespace Kr25Ssmxt

open MeasureTheory

/-!
# The public TTC theorems

The proved accuracy statement below is for the older `communityTTC` core. The
current manuscript's algorithm is `communityManuscriptTTC`, with a separate
rate-thinning loop, scaled intensity, volume clipping, and output normalization.
An exact finite expected-operation bound for the charged newer program is
proved below, including the corrected headline's explicit geometric monomial.
The charged-to-uncharged output marginal is proved. A Lean polylogarithmic
estimate for the imported CV18 scheduled factors remains open.

`Prior` exposes the remaining high-intensity Poissonized streaming theorem as a hypothesis.
The deterministic preprocessing, oracle contracts, empty case, lattice
comparison, measure normalization, and final error composition are proved in this project.
-/

/--
The older TTC program using the current arlib-community CV18 and finite-step
Hit-and-Run/KV97 implementations returns a probability law on single nonnegative estimates,
and its estimate is within relative error `ε` of the Lebesgue volume of the existentially
projected real solution set with probability at least `1 - δ`.  The two geometric-oracle
contracts are discharged in the proof rather than exposed as assumptions. This
statement does not yet establish manuscript Theorem 1, because its program and
its public high-intensity and `Prior` premises differ from the printed claim.

PAPER: sections/analysis.tex:314-326
-/
theorem ttc_volume_accuracy
    (hprior : Prior)
    {n k : Nat}
    (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (prep : TTCPreprocessor n k)
    (hregime :
      let D := prep.run F hbounded
      let b := (prep.choosePrecision D params).value
      D.componentCount = 0 ∨
        params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real)) :
    MeasureTheory.IsProbabilityMeasure (communityTTC hn F hbounded params prep) ∧
      (communityTTC hn F hbounded params prep).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr params.epsilon
              (MeasureTheory.volume (solutionSet F)).toReal} ≥
        1 - params.delta := by
  exact ttc_volume_accuracy_communityCV18_hitAndRun
    hprior hn F hbounded params prep hregime

/--
An accounting statement toward Theorem 3 (`thm:runtime`).  For the decomposition
actually produced by TTC, `communityMembershipRuntimeCertificate` fixes the CV18 query
budget to the syntax-derived budget of the imported amplified program and fixes the
sampler steps to the imported finite Hit-and-Run deadline.  The first conjunct certifies
the CV18 budget against arlib-community's charged semantics.  The second adds an
externally measured preprocessing and CV18 non-query costs to the geometric certificate.
The latter is assumed componentwise bounded by `C * n * rᵢ * (Qᵢ + 1)` and appears
explicitly on the right side. A separate theorem below bounds the expected
operations of the charged manuscript program; the growth of this certificate's
computed factors has not been established here.

PAPER: sections/analysis.tex:52-72
-/
theorem ttc_total_runtime_theorem3 {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat)
    (cv18NonQueryOperations :
      Fin (prep.run F hbounded).componentCount → Nat)
    (hcv18NonQuery :
      let D := prep.run F hbounded
      let b := (prep.choosePrecision D p).value
      let cert := communityMembershipRuntimeCertificate hn D b p
      ∀ i : Fin D.componentCount,
        cv18NonQueryOperations i ≤
          cv18NonQueryFactor *
            TTCRuntime.membershipQueryOperations n
              (D.component i).presentation.facetCount
              (cert.volumeQueryCount i + 1)) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    let cert := communityMembershipRuntimeCertificate hn D b p
    (∀ i : Fin D.componentCount,
        CommunityCV18.MembershipCostCertified (by omega) (D.component i)
          p.epsilonPrime (p.deltaPrime D.componentCount)) ∧
      ((preprocessingOperations + cert.operations +
          ∑ i, cv18NonQueryOperations i : Nat) : Real) ≤
        preprocessingOperations +
        TTCRuntime.theorem3HeadlineCore D.componentCount n
            (TTCRuntime.theorem3RMax D) (TTCRuntime.theorem3Rho D) *
          TTCRuntime.theorem3SuppressedFactor p.epsilon
            (TTCRuntime.sampleCap p D.componentCount)
            (TTCRuntime.theorem3VolumeOverhead cert (TTCRuntime.theorem3Rho D))
            (TTCRuntime.theorem3SamplingOverhead cert (TTCRuntime.theorem3Rho D)) +
        (cert.cv18NonQueryAllowance cv18NonQueryFactor : Real) := by
  dsimp only at hcv18NonQuery ⊢
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  let cert := communityMembershipRuntimeCertificate hn D b p
  have hbase := PaperRuntime.community_runtime_cost_bound hn F hbounded p prep
    preprocessingOperations
  dsimp only at hbase
  constructor
  · exact hbase.1
  · have hsum : (∑ i : Fin D.componentCount, cv18NonQueryOperations i) ≤
        cert.cv18NonQueryAllowance cv18NonQueryFactor := by
      exact Finset.sum_le_sum fun i _ => hcv18NonQuery i
    calc
      ((preprocessingOperations + cert.operations +
          ∑ i, cv18NonQueryOperations i : Nat) : Real) =
          ((preprocessingOperations + cert.operations : Nat) : Real) +
            (∑ i, cv18NonQueryOperations i : Nat) := by push_cast; ring
      _ ≤ (preprocessingOperations +
          TTCRuntime.theorem3HeadlineCore D.componentCount n
            (TTCRuntime.theorem3RMax D) (TTCRuntime.theorem3Rho D) *
            TTCRuntime.theorem3SuppressedFactor p.epsilon
              (TTCRuntime.sampleCap p D.componentCount)
              (TTCRuntime.theorem3VolumeOverhead cert (TTCRuntime.theorem3Rho D))
              (TTCRuntime.theorem3SamplingOverhead cert (TTCRuntime.theorem3Rho D))) +
            (cert.cv18NonQueryAllowance cv18NonQueryFactor : Real) := by
        exact add_le_add hbase.2 (by exact_mod_cast hsum)
      _ = _ := by ring

/-- Expected arithmetic-operation cost of the concrete charged manuscript TTC
program, with preprocessing and every component's explicit budget included. -/
theorem ttc_expected_runtime_explicit {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations cv18NonQueryFactor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudget hn p D.componentCount b
            cv18NonQueryFactor (D.component i) := by
  exact community_manuscript_expected_cost_explicit hn F hbounded p prep
    preprocessingOperations cv18NonQueryFactor

/-- The proved expected-cost allowance with the first thinning loop's
decimal-precision dependence exposed as a term linear in `b`. -/
theorem ttc_expected_runtime_linear_precision {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations cv18NonQueryFactor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudgetLinearPrecision hn p
            D.componentCount b cv18NonQueryFactor (D.component i) := by
  dsimp only
  calc
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ i : Fin (prep.run F hbounded).componentCount,
          TTCRuntime.manuscriptExpectedComponentBudget hn p
            (prep.run F hbounded).componentCount
            (prep.choosePrecision (prep.run F hbounded) p).value
            cv18NonQueryFactor ((prep.run F hbounded).component i) :=
      ttc_expected_runtime_explicit hn F hbounded p prep
        preprocessingOperations cv18NonQueryFactor
    _ ≤ _ := by
      gcongr
      exact TTCRuntime.manuscriptExpectedComponentBudget_le_linearPrecision hn p
        (prep.run F hbounded).componentCount
        (prep.choosePrecision (prep.run F hbounded) p).value
        cv18NonQueryFactor _

/-- Whole-run expected arithmetic cost with the normalized sampler deadline
expressed through `ρ`, `b`, and `R_max`, using the imported mixing theorem. -/
theorem ttc_expected_runtime_geometric {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations cv18NonQueryFactor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudgetGeometric hn D p b
            cv18NonQueryFactor i := by
  dsimp only
  let D := prep.run F hbounded
  let choice := prep.choosePrecision D p
  have hbase := ttc_expected_runtime_linear_precision hn F hbounded p prep
    preprocessingOperations cv18NonQueryFactor
  dsimp only at hbase
  calc
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudgetLinearPrecision hn p
            D.componentCount choice.value cv18NonQueryFactor (D.component i) := hbase
    _ ≤ _ := by
      gcongr
      exact TTCRuntime.manuscriptExpectedComponentBudgetLinearPrecision_le_geometric
        hn D p choice.value cv18NonQueryFactor choice.adequate _

/-- Whole-run expected-cost bound with the sampler deadline and first-loop
count reduced to `ρ`, `b`, and the global outer radius. -/
theorem ttc_expected_runtime_geometric_clip {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations cv18NonQueryFactor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudgetGeometricClip hn D p b
            cv18NonQueryFactor i := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  have hbase := ttc_expected_runtime_geometric hn F hbounded p prep
    preprocessingOperations cv18NonQueryFactor
  dsimp only at hbase
  calc
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudgetGeometric hn D p b
            cv18NonQueryFactor i := hbase
    _ ≤ _ := by
      gcongr
      exact TTCRuntime.manuscriptExpectedComponentBudgetGeometric_le_clip
        hn D p b cv18NonQueryFactor _

/-- Expected arithmetic cost of the manuscript TTC run with both imported
oracle schedules substituted into the per-component budget. -/
theorem ttc_expected_runtime_theorem3_expanded {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations cv18NonQueryFactor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudgetTheorem3 hn D p b
            cv18NonQueryFactor i := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  have hbase := ttc_expected_runtime_geometric_clip hn F hbounded p prep
    preprocessingOperations cv18NonQueryFactor
  dsimp only at hbase
  calc
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudgetGeometricClip hn D p b
            cv18NonQueryFactor i := hbase
    _ ≤ _ := by
      gcongr
      exact TTCRuntime.manuscriptExpectedComponentBudgetGeometricClip_le_theorem3
        hn D p b cv18NonQueryFactor _

/-- The fixed CV18 non-query charge requested for Theorem 3: one
membership-equivalent allowance per query and for setup. -/
theorem ttc_expected_runtime_theorem3_fixed_charge {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations 1 ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudgetTheorem3 hn D p b 1 i := by
  exact ttc_expected_runtime_theorem3_expanded hn F hbounded p prep
    preprocessingOperations 1

/-- Uniform finite-component form, exposing the manuscript's leading `m`.
The CV18 logarithmic maximum is over actual normalized components. -/
theorem ttc_expected_runtime_uniform_budget {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations 1 ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        TTCRuntime.theorem3UniformComponentBudget hn D p b 1 := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  have hbase := ttc_expected_runtime_theorem3_fixed_charge hn F hbounded p prep
    preprocessingOperations
  dsimp only at hbase
  calc
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudgetTheorem3 hn D p b 1 i := hbase
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ _i : Fin D.componentCount,
          TTCRuntime.theorem3UniformComponentBudget hn D p b 1 := by
      gcongr
      exact TTCRuntime.manuscriptExpectedComponentBudgetTheorem3_le_uniform
        hn D p b 1 _
    _ = _ := by simp [D, b]

/-- Corrected expected arithmetic-operation bound for the costed manuscript
TTC execution. The explicit parameter factor contains the CV18 scheduled
logarithmic product and the Hit-and-Run mixing logarithm. -/
theorem ttc_expected_runtime_theorem3_headline_scale {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations 1 ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.theorem3RMax D : Real) *
          (TTCRuntime.theorem3Rho D) ^ 2 *
          TTCRuntime.theorem3PrecisionScale b
            (TTCRuntime.theorem3OuterRadiusMax D) *
          ((TTCRuntime.sampleCap p D.componentCount : Real) + 1) *
          (TTCRuntime.theorem3ParameterFactor hn D p + 1)) := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  have hbase := ttc_expected_runtime_uniform_budget hn F hbounded p prep
    preprocessingOperations
  dsimp only at hbase
  by_cases hm : 0 < D.componentCount
  · exact hbase.trans (by
      gcongr
      exact TTCRuntime.theorem3UniformComponentBudget_le_headline_scale
        hn D p b hm)
  · have hzero : D.componentCount = 0 := by omega
    dsimp [D] at hzero
    simpa only [hzero, Nat.cast_zero, zero_mul, add_zero] using hbase

theorem ttc_theorem3_headline_budget_finite {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    (preprocessingOperations : ENNReal) + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.theorem3RMax D : Real) *
          (TTCRuntime.theorem3Rho D) ^ 2 *
          TTCRuntime.theorem3PrecisionScale b
            (TTCRuntime.theorem3OuterRadiusMax D) *
          ((TTCRuntime.sampleCap p D.componentCount : Real) + 1) *
          (TTCRuntime.theorem3ParameterFactor hn D p + 1)) ≠ ⊤ := by
  dsimp only
  exact ENNReal.add_ne_top.mpr ⟨by simp,
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top⟩

/-- Corrected Theorem 3: the charged execution has exactly the manuscript TTC
output law and its expected arithmetic cost has the preprocessing term plus
the explicit `m n⁵ ρ² r_max (1+b+log⁺ R_max)` scale. -/
theorem ttc_theorem3_corrected_expected_runtime {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    (communityManuscriptTTCWithCost hn F hbounded p prep
      preprocessingOperations 1).map Prod.fst =
        communityManuscriptTTC hn F hbounded p prep ∧
    (∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations 1) ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.theorem3RMax D : Real) *
          (TTCRuntime.theorem3Rho D) ^ 2 *
          TTCRuntime.theorem3PrecisionScale b
            (TTCRuntime.theorem3OuterRadiusMax D) *
          ((TTCRuntime.sampleCap p D.componentCount : Real) + 1) *
          (TTCRuntime.theorem3ParameterFactor hn D p + 1)) := by
  dsimp only
  exact ⟨community_manuscript_costed_output_fst hn F hbounded p prep
    preprocessingOperations 1,
    ttc_expected_runtime_theorem3_headline_scale hn F hbounded p prep
      preprocessingOperations⟩

#krModelClosureOfType ttc_volume_accuracy
#krModelClosureOfType ttc_total_runtime_theorem3
#krModelClosureOfType ttc_expected_runtime_explicit
#krModelClosureOfType ttc_expected_runtime_linear_precision
#krModelClosureOfType ttc_expected_runtime_geometric
#krModelClosureOfType ttc_expected_runtime_geometric_clip
#krModelClosureOfType ttc_expected_runtime_theorem3_expanded
#krModelClosureOfType ttc_expected_runtime_theorem3_fixed_charge
#krModelClosureOfType ttc_expected_runtime_uniform_budget
#krModelClosureOfType ttc_expected_runtime_theorem3_headline_scale
#krModelClosureOfType ttc_theorem3_corrected_expected_runtime
#krModelClosureOfType ttc_theorem3_headline_budget_finite
#krSurplusIn Kr25Ssmxt.Model from ttc_volume_accuracy ttc_total_runtime_theorem3
  ttc_expected_runtime_explicit ttc_expected_runtime_linear_precision
  ttc_expected_runtime_geometric ttc_expected_runtime_geometric_clip
  ttc_expected_runtime_theorem3_expanded
  ttc_expected_runtime_theorem3_fixed_charge
  ttc_expected_runtime_uniform_budget
  ttc_expected_runtime_theorem3_headline_scale
  ttc_theorem3_headline_budget_finite
  StreamingCoreAccuracy communityManuscriptTTC
  TTCRuntime.deletionPassOperations TTCRuntime.rateThinningRoundOperations
  TTCRuntime.countThinningRoundOperations TTCRuntime.samplingAttemptOperations
  TTCRuntime.poissonDrawOperations TTCRuntime.appendCopyOperations
  manuscriptRateThinWithCost manuscriptCountThinWithCost

/-!
Both public statements are recursively sealed above.  `communityTTC` and every executable
adapter it unfolds are defined under `Model/`; `Analysis/` is used only to prove the two
statements.
-/

#print axioms ttc_volume_accuracy
#print axioms ttc_total_runtime_theorem3
#print axioms ttc_expected_runtime_explicit
#print axioms ttc_expected_runtime_linear_precision
#print axioms ttc_expected_runtime_geometric
#print axioms ttc_expected_runtime_geometric_clip
#print axioms ttc_expected_runtime_theorem3_expanded
#print axioms ttc_expected_runtime_theorem3_fixed_charge
#print axioms ttc_expected_runtime_uniform_budget
#print axioms ttc_expected_runtime_theorem3_headline_scale
#print axioms ttc_theorem3_corrected_expected_runtime
#print axioms ttc_theorem3_headline_budget_finite

end Kr25Ssmxt

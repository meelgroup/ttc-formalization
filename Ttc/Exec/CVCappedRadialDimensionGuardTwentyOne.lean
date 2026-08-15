import Ttc.Exec.CVCappedRadialLogInterface
import Ttc.Exec.CVSourceDimensionGuard

/-!
# Dimension dispatch for the capped radial-log implementation

The operational speedy-walk theorem starts at dimension 21.  This module keeps that
fact visible while still constructing the all-dimensional expected-query interface
required by the public CV structure.  Dimensions below 21 use the existing exact
semantic volume witness.  They are a fixed finite-dimensional fallback only; no claim
is made that its zero recorded query cost is an implementation of an oracle program.

The TTC theorem below remains explicitly guarded by `21 <= n`.  Thus TTC never silently
uses the semantic fallback as operational code.
-/

set_option autoImplicit false

namespace Ttc.CVCappedRadialDimensionGuardTwentyOne

open MeasureTheory Set
open Ttc.CVCappedRadialLogInterface
open Ttc.CVHotRefreshHonestRuntime
open Ttc.TTCCVExpectedImplementation
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem
open Ttc.CanonicalOwnerRateCutoff
open Ttc.KV97RoundedEndpointBridge
open scoped ENNReal BigOperators Classical

/-- A harmless explicit exponential envelope for the finitely many semantic fallback
dimensions.  The exact semantic witness has bound zero, hence satisfies this envelope. -/
noncomputable def belowTwentyOneSemanticEnvelope (n : Nat) : ENNReal :=
  if n < 21 then ENNReal.ofReal (2 : Real) ^ (21 * 21) else 0

/-- Dispatch to a high-dimensional operational algorithm, using the exact semantic
witness only when `n < 21`. -/
noncomputable def expectedAlgorithmWithExactBelowTwentyOne
    (high : forall n, 21 <= n -> Ttc.ExpectedQueryVolumeAlgorithm n)
    (n : Nat) : Ttc.ExpectedQueryVolumeAlgorithm n :=
  if hn : 21 <= n then high n hn else Ttc.ExpectedQueryVolumeAlgorithm.exactExpected n

@[simp] theorem expectedAlgorithmWithExactBelowTwentyOne_high
    (high : forall n, 21 <= n -> Ttc.ExpectedQueryVolumeAlgorithm n)
    {n : Nat} (hn : 21 <= n) :
    expectedAlgorithmWithExactBelowTwentyOne high n = high n hn := by
  unfold expectedAlgorithmWithExactBelowTwentyOne
  simp only [dif_pos hn]

@[simp] theorem expectedAlgorithmWithExactBelowTwentyOne_low
    (high : forall n, 21 <= n -> Ttc.ExpectedQueryVolumeAlgorithm n)
    {n : Nat} (hn : n < 21) :
    expectedAlgorithmWithExactBelowTwentyOne high n =
      Ttc.ExpectedQueryVolumeAlgorithm.exactExpected n := by
  unfold expectedAlgorithmWithExactBelowTwentyOne
  rw [dif_neg (by omega : ¬ (21 <= n))]

theorem exactBelowTwentyOne_expectedBound_le_semanticEnvelope
    (high : forall n, 21 <= n -> Ttc.ExpectedQueryVolumeAlgorithm n)
    {n : Nat} (hn : n < 21) (K : Set (Ttc.Space n)) (eps p : Real) :
    (expectedAlgorithmWithExactBelowTwentyOne high n).expectedBound K eps p <=
      belowTwentyOneSemanticEnvelope n := by
  rw [expectedAlgorithmWithExactBelowTwentyOne_low high hn]
  simp [belowTwentyOneSemanticEnvelope, hn]

/-- An operational implementation in dimensions at least 21 extends to the all-dimensional
capped radial-log structure using only the explicitly marked semantic fallback below 21. -/
noncomputable def cappedRadialLogImplementationOfHighDimension
    (high : forall n, 21 <= n -> Ttc.ExpectedQueryVolumeAlgorithm n)
    (runtimeConstant : Real) (hconstant : 0 <= runtimeConstant)
    (hhigh : forall (n : Nat) (hn21 : 21 <= n)
      (K : Set (Ttc.Space n)) (eps p R2 : Real),
      0 < eps -> eps < 1 -> 0 < p -> p < 1 -> CVAdmissible K R2 ->
      (high n hn21).expectedBound K eps p <= ENNReal.ofReal
        (runtimeConstant * cvCappedRadialLogComplexityShapeClipped n R2 eps p)) :
    CVCappedRadialLogExpectedImplementation where
  algorithm := expectedAlgorithmWithExactBelowTwentyOne high
  runtimeConstant := runtimeConstant
  runtimeConstant_nonneg := hconstant
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    by_cases hn21 : 21 <= n
    · rw [expectedAlgorithmWithExactBelowTwentyOne_high high hn21]
      exact hhigh n hn21 K eps p R2 heps heps1 hp hp1 hK
    · rw [expectedAlgorithmWithExactBelowTwentyOne_low high (by omega)]
      simp

/-- TTC-facing capstone.  The algorithm family contains the low-dimensional semantic
fallback, but this operational TTC theorem still requires `21 <= n`. -/
theorem ttc_volume_estimate_of_highDimensionWithExactBelowTwentyOne
    {A : Type*} {n : Nat}
    (high : forall n, 21 <= n -> Ttc.ExpectedQueryVolumeAlgorithm n)
    (runtimeConstant : Real) (hconstant : 0 <= runtimeConstant)
    (hhigh : forall (d : Nat) (hd21 : 21 <= d)
      (K : Set (Ttc.Space d)) (eps p R2 : Real),
      0 < eps -> eps < 1 -> 0 < p -> p < 1 -> CVAdmissible K R2 ->
      (high d hd21).expectedBound K eps p <= ENNReal.ofReal
        (runtimeConstant * cvCappedRadialLogComplexityShapeClipped d R2 eps p))
    (atoms : A -> LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps <= 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta <= 1)
    (hn : 21 <= n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let I := cappedRadialLogImplementationOfHighDimension high runtimeConstant
      hconstant hhigh
    let deltaRun := 4 * delta / 5
    let hn1 : 1 <= n := le_trans (by norm_num) hn
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta <= (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) <=
      cappedRadialVolumeQueryEnvelope I atoms phi eps deltaRun +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  exact ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation
    (cappedRadialLogImplementationOfHighDimension high runtimeConstant hconstant hhigh)
    atoms phi eps delta h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol

#print axioms expectedAlgorithmWithExactBelowTwentyOne
#print axioms exactBelowTwentyOne_expectedBound_le_semanticEnvelope
#print axioms cappedRadialLogImplementationOfHighDimension
#print axioms ttc_volume_estimate_of_highDimensionWithExactBelowTwentyOne

end Ttc.CVCappedRadialDimensionGuardTwentyOne

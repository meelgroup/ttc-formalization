/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.PolyAccuracy
import Ttc.Volume.ExpectedQueryOracle

/-!
# Actual volume-query accounting for `ttcPoly`

`Ttc.PolyAccuracy` already proves the semantic TTC accuracy theorem for an arbitrary
`VolumeAlgorithm`.  This file attaches the stronger `ExpectedQueryVolumeAlgorithm`
interface to the *same* calls made by `Vol_ED`: one call for every entry of the
preprocessed DNF, on exactly the rounded body read by `Ttc.volOfAlg`.

This is deliberately only the volume half of TTC's oracle accounting.  The current
`Ttc.SamplerCost` price is a modelling charge and is not connected to an executable
sampling trace, so it is not combined with the actual membership-query random variable
defined here.
-/

namespace Ttc

open MeasureTheory
open scoped ENNReal BigOperators

variable {A : Type*} {n : Nat}

/-- The actual membership-query count of all volume calls made by `Vol_ED` on a DNF.

The `j`th summand uses the same body, accuracy and confidence parameters as
`Ttc.volGoodOf` and `Ttc.volOfAlg`.  In particular, the cost and estimator read the same
global coin `omega`; no independent or postulated price is substituted. -/
noncomputable def volOfExpectedAlgQueryCost
    (V : ExpectedQueryVolumeAlgorithm n) (M : A -> Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} -> Space n) (gamma epsPrime deltaPrime : Real)
    (omega : V.Ω) : ENNReal :=
  ∑ j : Fin D.length,
    V.queryCost
      (roundBody (cen ⟨D.get j, List.get_mem D j⟩) gamma (region M (D.get j)))
      epsPrime deltaPrime omega

/-- The corresponding input-wise sum of the oracle's certified expected bounds. -/
noncomputable def volOfExpectedAlgQueryBound
    (V : ExpectedQueryVolumeAlgorithm n) (M : A -> Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} -> Space n) (gamma epsPrime deltaPrime : Real) :
    ENNReal :=
  ∑ j : Fin D.length,
    V.expectedBound
      (roundBody (cen ⟨D.get j, List.get_mem D j⟩) gamma (region M (D.get j)))
      epsPrime deltaPrime

theorem measurable_volOfExpectedAlgQueryCost
    (V : ExpectedQueryVolumeAlgorithm n) (M : A -> Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} -> Space n) (gamma epsPrime deltaPrime : Real) :
    let _ := V.mΩ
    Measurable (volOfExpectedAlgQueryCost V M D cen gamma epsPrime deltaPrime) := by
  let _ := V.mΩ
  classical
  unfold volOfExpectedAlgQueryCost
  exact Finset.measurable_sum _ fun j _ => V.queryCost_meas _ _ _

/-- Expected actual membership queries add across precisely the finite list of volume
calls performed by `Vol_ED`. -/
theorem lintegral_volOfExpectedAlgQueryCost_le
    (V : ExpectedQueryVolumeAlgorithm n) (M : A -> Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} -> Space n) (gamma epsPrime deltaPrime : Real) :
    (∫⁻ omega, volOfExpectedAlgQueryCost V M D cen gamma epsPrime deltaPrime omega ∂V.μ)
      <= volOfExpectedAlgQueryBound V M D cen gamma epsPrime deltaPrime := by
  classical
  unfold volOfExpectedAlgQueryCost volOfExpectedAlgQueryBound
  rw [lintegral_finsetSum]
  · exact Finset.sum_le_sum fun j _ => V.expectedQueryCost_le
      (roundBody (cen ⟨D.get j, List.get_mem D j⟩) gamma (region M (D.get j)))
      epsPrime deltaPrime
  · intro j _
    exact V.queryCost_meas _ _ _

/-- The actual total volume-query count at the canonical data used by `ttcPoly`. -/
noncomputable def ttcPolyVolumeQueryCost
    (atoms : A -> LinAtom n) (phi : BForm A) (eps delta : Real)
    (V : ExpectedQueryVolumeAlgorithm n) (omega : V.Ω) : ENNReal :=
  volOfExpectedAlgQueryCost V (atomSet (algAtoms atoms phi eps delta))
    (toDNFd (preprocess atoms phi)) (algCen atoms phi eps delta)
    (algGamma atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
    (algBlock atoms phi eps delta).deltaPrime omega

/-- The input-wise expected volume-query budget of `ttcPoly`. -/
noncomputable def ttcPolyVolumeQueryBound
    (atoms : A -> LinAtom n) (phi : BForm A) (eps delta : Real)
    (V : ExpectedQueryVolumeAlgorithm n) : ENNReal :=
  volOfExpectedAlgQueryBound V (atomSet (algAtoms atoms phi eps delta))
    (toDNFd (preprocess atoms phi)) (algCen atoms phi eps delta)
    (algGamma atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
    (algBlock atoms phi eps delta).deltaPrime

theorem measurable_ttcPolyVolumeQueryCost
    (atoms : A -> LinAtom n) (phi : BForm A) (eps delta : Real)
    (V : ExpectedQueryVolumeAlgorithm n) :
    let _ := V.mΩ
    Measurable (ttcPolyVolumeQueryCost atoms phi eps delta V) := by
  let _ := V.mΩ
  exact measurable_volOfExpectedAlgQueryCost V _ _ _ _ _ _

/-- Honest expected membership-query bound for all CV volume calls made by TTC.

This theorem is independent of TTC's trajectory law because the volume estimates and
their recorded costs are both fixed by the single `V.omega` before that law is sampled.
-/
theorem lintegral_ttcPolyVolumeQueryCost_le
    (atoms : A -> LinAtom n) (phi : BForm A) (eps delta : Real)
    (V : ExpectedQueryVolumeAlgorithm n) :
    (∫⁻ omega, ttcPolyVolumeQueryCost atoms phi eps delta V omega ∂V.μ)
      <= ttcPolyVolumeQueryBound atoms phi eps delta V :=
  lintegral_volOfExpectedAlgQueryCost_le V _ _ _ _ _ _

#print axioms measurable_volOfExpectedAlgQueryCost
#print axioms lintegral_volOfExpectedAlgQueryCost_le
#print axioms lintegral_ttcPolyVolumeQueryCost_le

end Ttc

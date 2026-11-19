import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.ReferenceProgram
import ttc.Analysis.ChebyshevCenter

/-! # `GetPrecision` meets its specification

The Chebyshev-centre LP of `Model/Run.lean` recovers the maximal inscribed radius
(`MaxInscribedBall_eq_inradius`), so the precision `GetPrecision` returns satisfies
`PrecisionAdequate` (`getPrecisionChoice`). -/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace ttc

/-- A precision together with its adequacy certificate. -/
structure PrecisionChoice {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) where
  value : Nat
  adequate : PrecisionAdequate D value p.precisionEta

/-- The Chebyshev-centre LP recovers the maximal inscribed radius: its optimum value is the
component's `inradius`. -/
theorem PolytopeData.MaxInscribedBall_eq_inradius {n : Nat} (P : PolytopeData n) :
    P.presentation.MaxInscribedBall = P.inradius := rfl

/-- `GetPrecision(F_d, M, ε / 96)` (line `line:getprec`) together with the proof that the
returned precision meets the specification of `getprec`. -/
noncomputable def getPrecisionChoice {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : PrecisionChoice D p where
  value := GetPrecision D p.precisionEta
  adequate := by
    intro i
    have hγ := (D.component i).inradius_pos
    rw [← (D.component i).MaxInscribedBall_eq_inradius] at hγ ⊢
    have hratio1 : (1 : Real) ≤ getPrecisionRatio D p.precisionEta := le_max_left _ _
    have hterm : latticeRadiusRequirement D p.precisionEta / (D.component i).presentation.MaxInscribedBall ≤
        getPrecisionRatio D p.precisionEta := by
      refine (Real.le_coe_toNNReal _).trans (le_trans ?_ (le_max_right _ _))
      exact NNReal.coe_le_coe.mpr (Finset.le_sup
        (f := fun i : Fin D.componentCount => Real.toNNReal
          (latticeRadiusRequirement D p.precisionEta / (D.component i).presentation.MaxInscribedBall))
        (Finset.mem_univ i))
    have hpow : getPrecisionRatio D p.precisionEta ≤
        (10 : Real) ^ GetPrecision D p.precisionEta := by
      have hpos : 0 < getPrecisionRatio D p.precisionEta := by linarith
      calc getPrecisionRatio D p.precisionEta
          = (10 : Real) ^ Real.logb 10 (getPrecisionRatio D p.precisionEta) :=
            (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
        _ ≤ (10 : Real) ^ (GetPrecision D p.precisionEta : Real) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
        _ = (10 : Real) ^ GetPrecision D p.precisionEta := Real.rpow_natCast _ _
    have := (div_le_iff₀ hγ).mp (hterm.trans hpow)
    linarith


/-! ## Line `line:volume`: `ComputeVolume` is CV18 on the normalized component -/

/-- TTC's precision stage with its certificate; its `value` is the `choosePrecision` slot of
`ttcSubroutines` (definitionally). -/
noncomputable def TTCPreprocessor.choosePrecision {n k : Nat}
    (_prep : TTCPreprocessor n k) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) : PrecisionChoice D p :=
  getPrecisionChoice D p

end ttc

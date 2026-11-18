import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.ReferenceProgram

/-! # `GetPrecision` meets its specification

The Chebyshev-centre LP of `Model/Run.lean` recovers the maximal inscribed radius
(`MaxInscribedBall_eq_inradius`), so the precision `GetPrecision` returns satisfies
`PrecisionAdequate` (`getPrecisionChoice`). -/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Kr25Ssmxt

/-- A precision together with its adequacy certificate. -/
structure PrecisionChoice {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) where
  value : Nat
  adequate : PrecisionAdequate D value p.precisionEta

/-- An `ℓ₂` ball of radius `t ≥ 0` lies in the carrier exactly when `(c, t)` is LP-feasible. -/
theorem euclideanBall_subset_iff_chebyshevFeasible {n : Nat} (H : HalfspacePresentation n)
    (c : Point n) {t : Real} (ht : 0 ≤ t) :
    euclideanBall c t ⊆ H.carrier ↔ H.chebyshevFeasible c t := by
  constructor
  · intro hsub j
    by_cases ha : toEuclidean (H.normal j) = 0
    · have hc : c ∈ euclideanBall c t := by simpa [euclideanBall] using ht
      have := hsub hc j
      rw [ha, norm_zero, mul_zero, add_zero]
      exact this
    · set a := toEuclidean (H.normal j)
      have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
      let x : Point n := c + (t / ‖a‖) • H.normal j
      have hx : x ∈ euclideanBall c t := by
        change ‖(WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))‖ ≤ t
        have hxc : x - c = (t / ‖a‖) • H.normal j := by simp [x]
        rw [hxc, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg ht hpos.le)]
        change t / ‖a‖ * ‖a‖ ≤ t
        rw [div_mul_cancel₀ _ hpos.ne']
      have hdot := hsub hx j
      have hself : dotProduct (H.normal j) (H.normal j) = ‖a‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        change dotProduct (H.normal j) (H.normal j) =
          dotProduct (H.normal j) (H.normal j)
        rfl
      have hexp : dotProduct (H.normal j) x =
          dotProduct (H.normal j) c + t * ‖a‖ := by
        simp only [x, dotProduct_add, dotProduct_smul, smul_eq_mul, hself]
        field_simp
      change dotProduct (H.normal j) x ≤ H.offset j at hdot
      linarith
  · intro hfeas x hx j
    change dotProduct (H.normal j) x ≤ H.offset j
    have hx' : ‖(WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))‖ ≤ t := hx
    have hcs : dotProduct (H.normal j) (x - c) ≤
        ‖toEuclidean (H.normal j)‖ * ‖(WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))‖ := by
      have := real_inner_le_norm (toEuclidean (H.normal j))
        (WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))
      have heq : ⟪toEuclidean (H.normal j),
          (WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))⟫_Real =
          dotProduct (H.normal j) (x - c) := by
        change dotProduct (x - c) (H.normal j) = _
        exact dotProduct_comm _ _
      linarith
    have hsplit : dotProduct (H.normal j) x =
        dotProduct (H.normal j) c + dotProduct (H.normal j) (x - c) := by
      rw [dotProduct_sub]; ring
    have hnorm := norm_nonneg (toEuclidean (H.normal j))
    have := hfeas j
    nlinarith

/-- The Chebyshev-centre LP recovers the maximal inscribed radius: its optimum value is the
component's `inradius`. -/
theorem PolytopeData.MaxInscribedBall_eq_inradius {n : Nat} (P : PolytopeData n) :
    P.presentation.MaxInscribedBall = P.inradius := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨P.incenter, (euclideanBall_subset_iff_chebyshevFeasible _ _
    P.inradius_pos.le).mp P.inball⟩, ?_⟩
  rintro t ⟨c, hc⟩
  by_cases ht : t < 0
  · linarith [P.inradius_pos]
  · push_neg at ht
    exact P.inradius_max c t
      ((euclideanBall_subset_iff_chebyshevFeasible _ _ ht).mpr hc)

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

end Kr25Ssmxt

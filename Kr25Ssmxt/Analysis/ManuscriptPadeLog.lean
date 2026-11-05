import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! A scalar logarithm inequality used by the Poisson Chernoff bound. Keeping
it in this analysis module avoids importing a second Hit-and-Run hierarchy. -/

namespace Kr25Ssmxt

private theorem hasDerivAt_manuscriptPadeAux {t : Real} (ht : t ≠ 0) :
    HasDerivAt (fun s : Real => (s + 1) * Real.log s - 2 * (s - 1))
      (Real.log t + 1 / t - 1) t := by
  have h1 : HasDerivAt (fun s : Real => s + 1) 1 t :=
    (hasDerivAt_id t).add_const 1
  have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht
  have h3 : HasDerivAt (fun s : Real => (s + 1) * Real.log s)
      (1 * Real.log t + (t + 1) * t⁻¹) t := h1.mul h2
  have h4 : HasDerivAt (fun s : Real => 2 * (s - 1)) 2 t := by
    simpa using HasDerivAt.const_mul (2 : Real) ((hasDerivAt_id t).sub_const 1)
  have h5 := h3.sub h4
  have he : 1 * Real.log t + (t + 1) * t⁻¹ - 2 =
      Real.log t + 1 / t - 1 := by
    field_simp
    ring
  rwa [he] at h5

private theorem monotoneOn_manuscriptPadeAux :
    MonotoneOn (fun s : Real => (s + 1) * Real.log s - 2 * (s - 1))
      (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro s hs
    exact (hasDerivAt_manuscriptPadeAux (ne_of_gt hs)).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    exact (hasDerivAt_manuscriptPadeAux (ne_of_gt hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    rw [(hasDerivAt_manuscriptPadeAux (ne_of_gt hs)).deriv]
    have hlog := Real.one_sub_inv_le_log_of_pos hs
    rw [one_div]
    linarith

theorem manuscript_pade_log_bound {t : Real} (ht : 1 ≤ t) :
    2 * (t - 1) ≤ (t + 1) * Real.log t := by
  have h := monotoneOn_manuscriptPadeAux
    (Set.mem_Ioi.mpr one_pos)
    (Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos ht)) ht
  simp only [Real.log_one, mul_zero, sub_self] at h
  linarith

end Kr25Ssmxt

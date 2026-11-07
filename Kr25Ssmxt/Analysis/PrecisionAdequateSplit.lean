import Kr25Ssmxt.Model.Prelude

/-! The single `GetPrecision` radius at `η = ε / 96` covers both geometric uses
of the precision: the finite-union lattice comparison at `ε / 8` and the
pointwise lattice sampler at `ε' = ε / 12`.  The sampler half is the paper's
identity `(64 n / θ) √(log (4 r / θ)) = (512 n / ε') √(log (32 r / ε'))` at
`θ = ε' / 8 = ε / 96`, together with `m ≥ 1` and `r_i ≤ r`. -/

noncomputable section

namespace Kr25Ssmxt

theorem Decomposition.facetCount_le_totalFacets {n k : Nat}
    {F : LRAFormula n k} (D : Decomposition F) (i : Fin D.componentCount) :
    (D.component i).presentation.facetCount ≤ D.totalFacets := by
  unfold Decomposition.totalFacets
  exact Finset.single_le_sum
    (f := fun j => (D.component j).presentation.facetCount)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The sampler radius at `ε / 12` is at most the `GetPrecision` radius at `ε / 96`. -/
theorem samplerRadiusRequirement_le_precisionEta {n k : Nat}
    {F : LRAFormula n k} (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) :
    samplerRadiusRequirement (D.component i) p.epsilonPrime ≤
      latticeRadiusRequirement D p.precisionEta := by
  have hε := p.epsilon_pos
  have hm : (1 : Real) ≤ D.componentCount := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne'
  have hr : (1 : Real) ≤ (D.component i).presentation.facetCount := by
    exact_mod_cast (D.component i).facets_pos
  have hrR : ((D.component i).presentation.facetCount : Real) ≤ D.totalFacets := by
    exact_mod_cast D.facetCount_le_totalFacets i
  have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
  unfold samplerRadiusRequirement latticeRadiusRequirement
    ApproxParams.epsilonPrime ApproxParams.precisionEta
  simp only [div_div_eq_mul_div]
  apply mul_le_mul
  · apply div_le_div_of_nonneg_right _ hε.le
    nlinarith
  · apply Real.sqrt_le_sqrt
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right _ hε.le
    nlinarith
  · exact Real.sqrt_nonneg _
  · positivity

/-- The union lattice radius at `ε / 8` is at most the one at `ε / 96`. -/
theorem latticeRadiusRequirement_latticeEta_le_precisionEta {n k : Nat}
    {F : LRAFormula n k} (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) :
    latticeRadiusRequirement D p.latticeEta ≤
      latticeRadiusRequirement D p.precisionEta := by
  have hε := p.epsilon_pos
  have hr : (1 : Real) ≤ (D.component i).presentation.facetCount := by
    exact_mod_cast (D.component i).facets_pos
  have hrR : ((D.component i).presentation.facetCount : Real) ≤ D.totalFacets := by
    exact_mod_cast D.facetCount_le_totalFacets i
  have hm : (0 : Real) ≤ D.componentCount := Nat.cast_nonneg _
  have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
  unfold latticeRadiusRequirement ApproxParams.latticeEta ApproxParams.precisionEta
  simp only [div_div_eq_mul_div]
  apply mul_le_mul
  · apply div_le_div_of_nonneg_right _ hε.le
    have : 0 ≤ 64 * (D.componentCount : Real) * n := by positivity
    nlinarith
  · apply Real.sqrt_le_sqrt
    apply Real.log_le_log (div_pos (by nlinarith) hε)
    apply div_le_div_of_nonneg_right _ hε.le
    nlinarith
  · exact Real.sqrt_nonneg _
  · positivity

/-- A `GetPrecision` certificate at `ε / 96` meets both geometric requirements. -/
theorem PrecisionAdequate.split {n k : Nat} {F : LRAFormula n k}
    {D : Decomposition F} {b : Nat} {p : ApproxParams}
    (h : PrecisionAdequate D b p.precisionEta) (i : Fin D.componentCount) :
    max (latticeRadiusRequirement D p.latticeEta)
        (samplerRadiusRequirement (D.component i) p.epsilonPrime) ≤
      (10 : Real) ^ b * (D.component i).inradius :=
  max_le ((latticeRadiusRequirement_latticeEta_le_precisionEta D p i).trans (h i))
    ((samplerRadiusRequirement_le_precisionEta D p i).trans (h i))

end Kr25Ssmxt

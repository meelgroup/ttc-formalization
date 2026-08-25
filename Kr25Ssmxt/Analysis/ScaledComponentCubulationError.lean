import Kr25Ssmxt.Analysis.IntegerCubulation
import Kr25Ssmxt.Analysis.FinitePolytopeFamilyCubulationError

/-!
# Boundary-layer error for scaled components

This specializes the set-level geometric boundary estimate for finite polytope families
to the components of a certified decomposition.  The global radius requirement spends an
`η / componentCount` error budget on every component.
-/

open scoped ENNReal symmDiff

namespace Kr25Ssmxt

/--
Each scaled component differs from its integer cubulation by at most its share of the
global relative-error budget; the symmetric difference also has finite volume.

INTERNAL: set-level boundary-layer estimate needed before overlapping components can be united
-/
lemma scaled_component_cubulation_error
    {n k : Nat}
    (hn : 0 < n)
    {F : LRAFormula n k}
    (D : Decomposition F)
    (b : Nat)
    (η : Real)
    (hηpos : 0 < η)
    (hηle : η ≤ 1)
    (hm : 0 < D.componentCount)
    (hradius : ∀ i,
      latticeRadiusRequirement D η ≤
        (10 : Real) ^ b * (D.component i).inradius) :
    ∀ i,
      let A :=
        (fun x : Point n => (10 : Real) ^ b • x) '' (D.component i).carrier
      MeasureTheory.volume (A ∆ integerCubulation A) ≠ ∞ ∧
        (MeasureTheory.volume (A ∆ integerCubulation A)).toReal ≤
          (η / (D.componentCount : Real)) *
            (MeasureTheory.volume (integerCubulation A)).toReal := by
  simpa only [latticeRadiusRequirement, Decomposition.totalFacets] using
    (finite_polytope_family_cubulation_error
      hn hm D.component b η hηpos hηle hradius)

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · reduced · specialized the finite-family boundary-layer theorem; the scalar comparison was too weak
-/

end Kr25Ssmxt

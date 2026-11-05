import Kr25Ssmxt.Analysis.ManuscriptConcreteComponentStep

/-! Every coded lattice point in the union is covered by a deleted-and-
replaced component coordinate in the fixed-level prefix process. -/

namespace Kr25Ssmxt

open Classical

noncomputable def componentDeletedCodes {n : Nat}
    (S : Finset (LatticePoint n)) (P : PolytopeData n) : Finset S :=
  Finset.univ.filter (fun x : S => x.1.toPoint ∈ P.carrier)

noncomputable def fixedLevelComponentSteps
    {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (S : Finset (LatticePoint n))
    (incoming : Fin D.componentCount → S → NNReal) :
    List (FixedLevelStep S) :=
  List.ofFn fun i =>
    { deleted := componentDeletedCodes S (D.component i)
      incoming := incoming i }

theorem fixedLevelCoverage_mem_iff {ι : Type*} [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) (covered : Finset ι) (x : ι) :
    x ∈ fixedLevelCoverage steps covered ↔
      x ∈ covered ∨ ∃ step ∈ steps, x ∈ step.deleted := by
  induction steps generalizing covered with
  | nil => simp [fixedLevelCoverage]
  | cons step rest ih =>
      simp only [fixedLevelCoverage]
      rw [ih]
      simp only [Finset.mem_union, List.mem_cons]
      constructor
      · rintro ((hcovered | hdeleted) | ⟨item, hitem, hx⟩)
        · exact Or.inl hcovered
        · exact Or.inr ⟨step, Or.inl rfl, hdeleted⟩
        · exact Or.inr ⟨item, Or.inr hitem, hx⟩
      · rintro (hcovered | ⟨item, hitem, hx⟩)
        · exact Or.inl (Or.inl hcovered)
        · rcases hitem with rfl | hrest
          · exact Or.inl (Or.inr hx)
          · exact Or.inr ⟨item, hrest, hx⟩

/-- The list of all component replacement steps covers exactly the finite
set of coded lattice points in the union. -/
theorem fixedLevelComponentSteps_coverage_univ
    {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat)
    (hfinite : (D.codedUnionLatticePoints b).Finite)
    (incoming : Fin D.componentCount →
      hfinite.toFinset → NNReal) :
    fixedLevelCoverage
      (fixedLevelComponentSteps D hfinite.toFinset incoming) ∅ =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  rw [fixedLevelCoverage_mem_iff]
  right
  have hx : x.1 ∈ D.codedUnionLatticePoints b := by
    simpa only [Set.Finite.mem_toFinset] using x.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx.2
  let step : FixedLevelStep hfinite.toFinset :=
    { deleted := componentDeletedCodes hfinite.toFinset (D.component i)
      incoming := incoming i }
  refine ⟨step, ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · simp [step, componentDeletedCodes, hi]

end Kr25Ssmxt

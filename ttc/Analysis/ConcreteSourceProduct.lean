import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.OracleContracts
import ttc.Analysis.AbsolutePoissonTape
import ttc.Analysis.ConcreteFixedLevelBounds
import ttc.Analysis.PoissonPreDraw

/-! The concrete normalized sampler and the independent component Poisson
sources give the exact product of incoming point-count vectors at each fixed
dyadic level. -/

namespace ttc

open Classical MeasureTheory

theorem communityPointLaw_support_codedUnion
    {n k : Nat} (hn : 3 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    (communityPointLaw hn D p b hprecision i)
      (S : Set (LatticePoint n))ᶜ = 0 := by
  dsimp only
  let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
  have halmost :=
    communityPointLaw_almostUniform hn D p b hprecision i
  have hsubset : codedLatticePoints (D.component i) b ⊆
      (S : Set (LatticePoint n)) := by
    intro x hx
    have hmem : x ∈ D.codedUnionLatticePoints b := by
      rw [D.codedUnion_eq_iUnion b]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    change x ∈ (D.codedUnion_finite (by omega) p b hprecision).toFinset
    simpa only [Set.Finite.mem_toFinset] using hmem
  have hsmall : (S : Set (LatticePoint n))ᶜ ⊆
      (codedLatticePoints (D.component i) b)ᶜ :=
    Set.compl_subset_compl.mpr hsubset
  exact nonpos_iff_eq_zero.mp ((measure_mono hsmall).trans_eq
    (by simpa using halmost.2.2.2.1))

theorem community_source_product_fixedLevel_incoming
    {n k : Nat} (hn : 3 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (level : Nat) :
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let threshold := p.Thresh D.componentCount
    let pointLaw := communityPointLaw hn D p b hprecision
    let sourceLaw : Fin D.componentCount → Measure (PoissonTape n) :=
      fun i => poissonTapeLaw
        (ttcReference.t b n threshold (volumeEstimate i)) (pointLaw i)
    (Measure.pi sourceLaw).map
      (fun sources i => poissonTapePointCounts S 0 level (sources i)) =
    Measure.pi (fun i : Fin D.componentCount =>
      Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
        (Real.toNNReal ((pointLaw i).real {(x.1 : LatticePoint n)} *
          ((ttcReference.t b n threshold (volumeEstimate i) *
            (1 / (2 : NNReal) ^ level) : NNReal) : Real))))) := by
  dsimp only
  let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
  let pointLaw := communityPointLaw hn D p b hprecision
  have halmost (i : Fin D.componentCount) :
      AlmostUniformPointwise (pointLaw i)
        (codedLatticePoints (D.component i) b) p.ε' :=
    communityPointLaw_almostUniform hn D p b hprecision i
  have hsupport (i : Fin D.componentCount) :
      (pointLaw i) (S : Set (LatticePoint n))ᶜ = 0 := by
    exact communityPointLaw_support_codedUnion
      hn D p b hprecision i
  have hprod := poissonTape_product_fixedLevel_pointCounts
    (fun i => ttcReference.t b n (p.Thresh D.componentCount)
      (volumeEstimate i)) pointLaw (fun i => (halmost i).1)
    S hsupport (fun _ => 0) level
  calc
    _ = Measure.pi (fun i : Fin D.componentCount =>
        Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
          (Real.toNNReal ((pointLaw i).real {(x.1 : LatticePoint n)} *
            ((unitInterval.toNNReal (survivalProbability level) *
              ttcReference.t b n (p.Thresh D.componentCount)
                (volumeEstimate i) : NNReal) : Real))))) := hprod
    _ = _ := by
      congr 1
      funext i
      congr 1
      funext x
      congr 1
      rw [survivalProbability_toNNReal]
      rw [show (1 / 2 : NNReal) ^ level =
        1 / (2 : NNReal) ^ level by simp [one_div, inv_pow]]
      dsimp only [pointLaw]
      ac_rfl

end ttc

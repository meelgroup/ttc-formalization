import ttc.Analysis.OracleContracts
import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.PrecisionAdequateSplit
import ttc.Analysis.FixedLevelCertified
import ttc.Analysis.HitAndRunSamplingOracle

/-! The reference fixed-level Poisson process with the exact normalized
Hit-and-Run/KV97 point laws executed by the paper TTC program. -/

namespace ttc

open MeasureTheory

noncomputable def communityPointLaw
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) : Measure (LatticePoint n) := by
  have hn0 : 0 < n := by omega
  have heta0 : 0 < p.ε' :=
    div_pos p.epsilon_pos (by norm_num)
  have heta1 : p.ε' ≤ 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have hset := coded_lattice_points_finite_nonempty hn0 D p b hprecision i
  have hunit : samplerRadiusRequirement (D.component i) p.ε' ≤
      decimalScale b * (D.component i).inradius :=
    (le_max_right _ _).trans (hprecision.split i)
  exact normalizedHitAndRunPointLaw hn (D.component i) b p.ε'
    hunit heta0 heta1 hset.1 hset.2

theorem communityPointLaw_almostUniform
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    AlmostUniformPointwise
      (communityPointLaw hn D p b hprecision i)
      (codedLatticePoints (D.component i) b) p.ε' := by
  unfold communityPointLaw
  exact (D.component i).normalizedHitAndRun_latticePointLaw hn b _ _ _ _ _

/-- For every successful concrete CV18 outcome vector, each admissible
fixed dyadic level has the paper's explicit concentration bound. -/
theorem communityFixedLevel_error_bound
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount)
    (outcomes : Fin D.componentCount → VolumeOutcome)
    (hgood : ∀ i, (outcomes i).1 = true ∧
      ((outcomes i).2 : Real) ∈ Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (level : Nat)
    (hlevel : level ≤ dyadicCutoff (D.latticePoints b).ncard - 1) :
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let rate : NNReal := 1 / (2 : NNReal) ^ level
    let steps := certifiedFixedLevelSteps D b S
      (p.Thresh D.componentCount) (fun i => (outcomes i).2)
      (communityPointLaw hn D p b hprecision) rate
    let lower := Real.toNNReal (p.Thresh D.componentCount *
      (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate)
    let upper := Real.toNNReal (p.Thresh D.componentCount *
      (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)
    let a := (1 - p.ε') * p.ε' ^ 2 *
      p.Thresh D.componentCount / 24
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : S → Nat => ∑ x, counts x)).real
          {count : Nat |
            (count : Real) < (1 - p.ε') *
              ((D.latticePoints b).ncard : Real) * lower ∨
            (1 + p.ε') *
              ((D.latticePoints b).ncard : Real) * upper < count} ≤
      2 * Real.exp (-a * (2 : Real) ^
        (dyadicCutoff (D.latticePoints b).ncard - 1 - level)) := by
  exact certifiedFixedLevel_error_bound (by omega) D p b hprecision
    hcomponents (fun i => (outcomes i).2)
    (communityPointLaw hn D p b hprecision)
    (fun i => (hgood i).2)
    (communityPointLaw_almostUniform hn D p b hprecision)
    level hlevel

/-- The fixed-level process using the actual normalized sampler also has
the paper's per-prefix cutoff tail budget. -/
theorem communityFixedLevel_cutoff_prefix_budget
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount)
    (outcomes : Fin D.componentCount → VolumeOutcome)
    (hgood : ∀ i, (outcomes i).1 = true ∧
      ((outcomes i).2 : Real) ∈ Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal) :
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let rate : NNReal := 1 /
      (2 : NNReal) ^ (dyadicCutoff (D.latticePoints b).ncard - 1)
    let full := certifiedFixedLevelSteps D b S
      (p.Thresh D.componentCount) (fun i => (outcomes i).2)
      (communityPointLaw hn D p b hprecision) rate
    ∀ pfx : List (FixedLevelStep S),
      (∀ step ∈ pfx, step ∈ full) →
      ((fixedLevelLaw pfx
        (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))).map
          (fun counts : S → Nat => ∑ x, counts x)).real
            {k : Nat | p.Thresh D.componentCount ≤ (k : Real)} ≤
        p.delta / (6 * D.componentCount) := by
  exact certifiedFixedLevel_cutoff_prefix_budget (by omega) D p b
    hprecision hcomponents (fun i => (outcomes i).2)
    (communityPointLaw hn D p b hprecision)
    (fun i => (hgood i).2)
    (communityPointLaw_almostUniform hn D p b hprecision)

end ttc

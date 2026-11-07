import Kr25Ssmxt.Analysis.PrecisionAdequateSplit
import Kr25Ssmxt.Analysis.ManuscriptFixedLevelCertified
import Kr25Ssmxt.Analysis.HitAndRunSamplingOracle

/-! The reference fixed-level Poisson process with the exact normalized
Hit-and-Run/KV97 point laws executed by the manuscript TTC program. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def communityManuscriptPointLaw
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) : Measure (LatticePoint n) := by
  have hn0 : 0 < n := by omega
  have heta0 : 0 < p.epsilonPrime :=
    div_pos p.epsilon_pos (by norm_num)
  have heta1 : p.epsilonPrime ≤ 1 := by
    dsimp [ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  have hset := coded_lattice_points_finite_nonempty hn0 D p b hprecision i
  have hunit : 1 ≤ decimalScale b * (D.component i).inradius :=
    (one_le_samplerRadiusRequirement hn0 (D.component i) heta0 heta1).trans
      ((le_max_right _ _).trans (hprecision.split i))
  exact normalizedHitAndRunPointLaw hn (D.component i) b hunit
    p.epsilonPrime heta0 heta1 hset.1 hset.2

theorem communityManuscriptPointLaw_almostUniform
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    AlmostUniformPointwise
      (communityManuscriptPointLaw hn D p b hprecision i)
      (codedLatticePoints (D.component i) b) p.epsilonPrime := by
  unfold communityManuscriptPointLaw
  exact (D.component i).normalizedHitAndRun_latticePointLaw hn b _ _ _ _ _

/-- For every successful concrete CV18 outcome vector, each admissible
fixed dyadic level has the manuscript's explicit concentration bound. -/
theorem communityManuscriptFixedLevel_error_bound
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount)
    (outcomes : Fin D.componentCount → VolumeOutcome)
    (hgood : ∀ i, (outcomes i).1 = true ∧
      ((outcomes i).2 : Real) ∈ Arlib.relErr p.epsilonPrime
        (volume (D.component i).carrier).toReal)
    (level : Nat)
    (hlevel : level ≤ manuscriptDyadicCutoff (D.latticePoints b).ncard - 1) :
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let rate : NNReal := 1 / (2 : NNReal) ^ level
    let steps := manuscriptCertifiedFixedLevelSteps D b S
      (p.threshold D.componentCount) (fun i => (outcomes i).2)
      (communityManuscriptPointLaw hn D p b hprecision) rate
    let lower := Real.toNNReal (p.threshold D.componentCount *
      (1 - p.epsilonPrime) ^ 2 * (1 - p.latticeEta) * rate)
    let upper := Real.toNNReal (p.threshold D.componentCount *
      (1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta) * rate)
    let a := (1 - p.epsilonPrime) * p.epsilonPrime ^ 2 *
      p.threshold D.componentCount / 24
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : S → Nat => ∑ x, counts x)).real
          {count : Nat |
            (count : Real) < (1 - p.epsilonPrime) *
              ((D.latticePoints b).ncard : Real) * lower ∨
            (1 + p.epsilonPrime) *
              ((D.latticePoints b).ncard : Real) * upper < count} ≤
      2 * Real.exp (-a * (2 : Real) ^
        (manuscriptDyadicCutoff (D.latticePoints b).ncard - 1 - level)) := by
  exact manuscriptCertifiedFixedLevel_error_bound (by omega) D p b hprecision
    hcomponents (fun i => (outcomes i).2)
    (communityManuscriptPointLaw hn D p b hprecision)
    (fun i => (hgood i).2)
    (communityManuscriptPointLaw_almostUniform hn D p b hprecision)
    level hlevel

/-- The fixed-level process using the actual normalized sampler also has
the manuscript's per-prefix cutoff tail budget. -/
theorem communityManuscriptFixedLevel_cutoff_prefix_budget
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount)
    (outcomes : Fin D.componentCount → VolumeOutcome)
    (hgood : ∀ i, (outcomes i).1 = true ∧
      ((outcomes i).2 : Real) ∈ Arlib.relErr p.epsilonPrime
        (volume (D.component i).carrier).toReal) :
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let rate : NNReal := 1 /
      (2 : NNReal) ^ (manuscriptDyadicCutoff (D.latticePoints b).ncard - 1)
    let full := manuscriptCertifiedFixedLevelSteps D b S
      (p.threshold D.componentCount) (fun i => (outcomes i).2)
      (communityManuscriptPointLaw hn D p b hprecision) rate
    ∀ pfx : List (FixedLevelStep S),
      (∀ step ∈ pfx, step ∈ full) →
      ((fixedLevelLaw pfx
        (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))).map
          (fun counts : S → Nat => ∑ x, counts x)).real
            {k : Nat | p.threshold D.componentCount ≤ (k : Real)} ≤
        p.delta / (6 * D.componentCount) := by
  exact manuscriptCertifiedFixedLevel_cutoff_prefix_budget (by omega) D p b
    hprecision hcomponents (fun i => (outcomes i).2)
    (communityManuscriptPointLaw hn D p b hprecision)
    (fun i => (hgood i).2)
    (communityManuscriptPointLaw_almostUniform hn D p b hprecision)

end Kr25Ssmxt

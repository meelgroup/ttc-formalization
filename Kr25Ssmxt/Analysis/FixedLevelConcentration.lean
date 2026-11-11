import Kr25Ssmxt.Analysis.FixedLevelIntensity

/-! Concentration for the fixed-level union prefix in the paper's
pointwise rate envelope. -/

namespace Kr25Ssmxt

open MeasureTheory

/-- A fixed-level prefix count lies in the paper's deterministic
lower/upper envelope except with the Poisson Chernoff failure probability. -/
theorem fixedLevelLaw_envelope_failure_bound
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι))
    (lower upper : NNReal)
    (hsteps : ∀ step ∈ steps, step.RateEnvelope lower upper)
    (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1) :
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : ι → Nat => ∑ i, counts i)).real
          {count : Nat |
            (count : Real) < (1 - epsilon) *
              ((fixedLevelCoverage steps ∅).card : Real) * lower ∨
            (1 + epsilon) *
              ((fixedLevelCoverage steps ∅).card : Real) * upper < count} ≤
      2 * Real.exp (-
        ((∑ i, fixedLevelRates steps (fun _ => 0) i : NNReal) : Real) *
          epsilon ^ 2 / 3) := by
  let covered := fixedLevelCoverage steps ∅
  let mean : NNReal := ∑ i, fixedLevelRates steps (fun _ => 0) i
  have hbounds := fixedLevelRates_total_mean_bounds ι steps lower upper hsteps
  have hlow : (covered.card : Real) * lower ≤ (mean : Real) := by
    have hcast : (((covered.card • lower : NNReal) : Real)) ≤ mean := by
      exact_mod_cast hbounds.1
    simpa only [NNReal.coe_nsmul, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_natCast] using hcast
  have hupp : (mean : Real) ≤ (covered.card : Real) * upper := by
    have hcast : (mean : Real) ≤ ((covered.card • upper : NNReal) : Real) := by
      exact_mod_cast hbounds.2
    simpa only [NNReal.coe_nsmul, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_natCast] using hcast
  have hfactor : 0 ≤ 1 - epsilon := by linarith
  have hsubset :
      {count : Nat |
        (count : Real) < (1 - epsilon) *
          (covered.card : Real) * lower ∨
        (1 + epsilon) * (covered.card : Real) * upper < count} ⊆
      {count : Nat | ¬ ((count : Real) ∈ Arlib.relErr epsilon (mean : Real))} := by
    intro count hcount hgood
    rw [Arlib.mem_relErr] at hgood
    rcases hcount with hsmall | hlarge
    · have hmul := mul_le_mul_of_nonneg_left hlow hfactor
      nlinarith
    · have hmul := mul_le_mul_of_nonneg_left hupp (by linarith : 0 ≤ 1 + epsilon)
      nlinarith
  have hmono :
      (ProbabilityTheory.poissonMeasure mean).real
        {count : Nat |
          (count : Real) < (1 - epsilon) *
            (covered.card : Real) * lower ∨
          (1 + epsilon) * (covered.card : Real) * upper < count} ≤
      (ProbabilityTheory.poissonMeasure mean).real
        {count : Nat | ¬ ((count : Real) ∈
          Arlib.relErr epsilon (mean : Real))} :=
    measureReal_mono hsubset
  rw [fixedLevelLaw_total_poisson]
  exact hmono.trans (process_components_lattice_count_accuracy_poisson_concentration_chernoff_failure_bound
    mean epsilon hepsilon hepsilon_le_one)

/-- A lower bound on the total Poisson mean gives the corresponding explicit
Chernoff exponent for the paper's deterministic count window. -/
theorem fixedLevelLaw_envelope_failure_bound_of_mean_lower
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι))
    (lower upper : NNReal)
    (hsteps : ∀ step ∈ steps, step.RateEnvelope lower upper)
    (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (minimumMean : Real)
    (hmean : minimumMean ≤
      ((∑ i, fixedLevelRates steps (fun _ => 0) i : NNReal) : Real)) :
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : ι → Nat => ∑ i, counts i)).real
          {count : Nat |
            (count : Real) < (1 - epsilon) *
              ((fixedLevelCoverage steps ∅).card : Real) * lower ∨
            (1 + epsilon) *
              ((fixedLevelCoverage steps ∅).card : Real) * upper < count} ≤
      2 * Real.exp (-minimumMean * epsilon ^ 2 / 3) := by
  have hbase := fixedLevelLaw_envelope_failure_bound ι steps lower upper
    hsteps epsilon hepsilon hepsilon_le_one
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : Real) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hfactor : 0 ≤ epsilon ^ 2 / 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hmean hfactor]

end Kr25Ssmxt

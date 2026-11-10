import Kr25Ssmxt.Analysis.ManuscriptPoissonUpperCutoff

/-! The manuscript threshold pays for a union bound over all components
at the dyadic cutoff. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem ApproxParams.cutoff_poisson_tail_budget
    (p : ApproxParams) (m : Nat) (hm : 0 < m) :
    Real.exp (-p.Thresh m / 15) ≤ p.delta / (6 * m) := by
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  have hratio : (0 : Real) < 6 / p.delta :=
    div_pos (by norm_num) p.delta_pos
  have hthreshold :
      15 * (Real.log (6 / p.delta) + Real.log m) ≤ p.Thresh m := by
    exact le_max_right _ _
  have hle : -p.Thresh m / 15 ≤
      -(Real.log (6 / p.delta) + Real.log m) := by
    linarith
  have hexp : Real.exp (Real.log (6 / p.delta) + Real.log m) =
      (6 / p.delta) * m := by
    rw [Real.exp_add, Real.exp_log hratio, Real.exp_log hmR]
  calc
    Real.exp (-p.Thresh m / 15) ≤
        Real.exp (-(Real.log (6 / p.delta) + Real.log m)) :=
      Real.exp_le_exp.mpr hle
    _ = 1 / ((6 / p.delta) * m) := by
      rw [Real.exp_neg, hexp]
      ring
    _ = p.delta / (6 * m) := by
      field_simp

/-- Each fixed-level component prefix uses at most its allotted share of
the cutoff failure budget. -/
theorem fixedLevelLaw_dyadic_cutoff_budget
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι))
    (count : Nat) (hcount : 0 < count)
    (hcovered : (fixedLevelCoverage steps ∅).card ≤ count)
    (p : ApproxParams) (m : Nat) (hm : 0 < m)
    (upper : NNReal)
    (hupper : (upper : Real) ≤
      (4 / 3) * p.Thresh m /
        (2 : Real) ^ (manuscriptDyadicCutoff count - 1))
    (hsteps : ∀ step ∈ steps, step.RateEnvelope 0 upper) :
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : ι → Nat => ∑ i, counts i)).real
          {k : Nat | p.Thresh m ≤ (k : Real)} ≤
      p.delta / (6 * m) := by
  exact (fixedLevelLaw_dyadic_cutoff_upper_tail ι steps count hcount
    hcovered (p.Thresh m) (p.threshold_pos m) upper hupper hsteps).trans
      (p.cutoff_poisson_tail_budget m hm)

/-- The other term in the manuscript threshold pays for the geometric sum
of two-sided Poisson concentration failures over admissible dyadic levels. -/
theorem ApproxParams.concentration_tail_budget
    (p : ApproxParams) (m : Nat) :
    4 * Real.exp (-
      (1 - p.ε') * p.ε' ^ 2 * p.Thresh m / 24) ≤
      p.delta / 6 := by
  have heps0 : 0 < p.ε' :=
    div_pos p.epsilon_pos (by norm_num)
  have heps1 : p.ε' < 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have hdenom : 0 < (1 - p.ε') * p.ε' ^ 2 :=
    mul_pos (by linarith) (sq_pos_of_pos heps0)
  have hratio : (0 : Real) < 24 / p.delta :=
    div_pos (by norm_num) p.delta_pos
  have hthreshold :
      24 * Real.log (24 / p.delta) /
        ((1 - p.ε') * p.ε' ^ 2) ≤
        p.Thresh m := by exact le_max_left _ _
  have hlog : Real.log (24 / p.delta) ≤
      (1 - p.ε') * p.ε' ^ 2 * p.Thresh m / 24 := by
    have h := (div_le_iff₀ hdenom).mp hthreshold
    nlinarith
  have htail : Real.exp (-
      (1 - p.ε') * p.ε' ^ 2 * p.Thresh m / 24) ≤
      p.delta / 24 := by
    calc
      Real.exp (-
          (1 - p.ε') * p.ε' ^ 2 * p.Thresh m / 24) ≤
          Real.exp (-Real.log (24 / p.delta)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = p.delta / 24 := by
        rw [Real.exp_neg, Real.exp_log hratio]
        field_simp
  nlinarith

end Kr25Ssmxt

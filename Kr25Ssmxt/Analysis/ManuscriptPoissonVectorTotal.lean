import Kr25Ssmxt.Analysis.ManuscriptFixedLevelPrefix
import Kr25Ssmxt.Analysis.ProcessComponentsLatticeCountAccuracyPoissonConcentrationChernoffFailureBound

/-! The total count of a finite independent Poisson point-count vector is
Poisson with mean equal to the sum of its point rates. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem poisson_vector_finset_total_law
    (ι : Type*) [Fintype ι] (r : ι → NNReal) (s : Finset ι) :
    HasLaw (fun counts : ι → Nat => ∑ i ∈ s, counts i)
      (ProbabilityTheory.poissonMeasure (∑ i ∈ s, r i))
      (Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (r i))) := by
  classical
  let μ : ι → Measure Nat := fun i => ProbabilityTheory.poissonMeasure (r i)
  let P : Measure (ι → Nat) := Measure.pi μ
  have hindep : iIndepFun (fun i (counts : ι → Nat) => counts i) P :=
    iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hcoord (i : ι) :
      HasLaw (fun counts : ι → Nat => counts i)
        (ProbabilityTheory.poissonMeasure (r i)) P :=
    (measurePreserving_eval μ i).hasLaw
  change HasLaw (fun counts : ι → Nat => ∑ i ∈ s, counts i)
    (ProbabilityTheory.poissonMeasure (∑ i ∈ s, r i)) P
  induction s using Finset.induction_on with
  | empty =>
      refine HasLaw.mk (by fun_prop) ?_
      simp [P, Measure.map_const, poissonMeasure_zero_eq_dirac]
  | @insert i s hi ih =>
      have hXY : IndepFun
          (fun counts : ι → Nat => ∑ j ∈ s, counts j)
          (fun counts : ι → Nat => counts i) P :=
        by
          have hfun : (∑ j ∈ s, fun counts : ι → Nat => counts j) =
              (fun counts : ι → Nat => ∑ j ∈ s, counts j) := by
            funext counts
            simp
          rw [← hfun]
          exact hindep.indepFun_finsetSum_of_notMem
            (fun _ => by fun_prop) hi
      have hadd := hXY.hasLaw_add_poissonMeasure ih (hcoord i)
      have hfun :
          ((fun counts : ι → Nat => ∑ j ∈ s, counts j) +
            (fun counts : ι → Nat => counts i)) =
          (fun counts : ι → Nat => counts i + ∑ j ∈ s, counts j) := by
        funext counts
        simp [add_comm]
      rw [hfun] at hadd
      simpa [Finset.sum_insert hi, add_comm] using hadd

theorem poisson_vector_total_law
    (ι : Type*) [Fintype ι] (r : ι → NNReal) :
    (Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (r i))).map
      (fun counts : ι → Nat => ∑ i, counts i) =
    ProbabilityTheory.poissonMeasure (∑ i, r i) := by
  simpa using (poisson_vector_finset_total_law ι r Finset.univ).map_eq

/-- The total count after any fixed-level union prefix is Poisson with mean
equal to the sum of its current point intensities. -/
theorem fixedLevelLaw_total_poisson
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) :
    (fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : ι → Nat => ∑ i, counts i) =
      ProbabilityTheory.poissonMeasure
        (∑ i, fixedLevelRates steps (fun _ => 0) i) := by
  rw [fixedLevelLaw_zero_poisson_prefix]
  exact poisson_vector_total_law ι (fixedLevelRates steps (fun _ => 0))

theorem fixedLevelLaw_total_chernoff_failure_bound
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) (epsilon : Real)
    (hepsilon : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1) :
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : ι → Nat => ∑ i, counts i)).real
          {count | ¬ ((count : Real) ∈ Arlib.relErr epsilon
            ((∑ i, fixedLevelRates steps (fun _ => 0) i : NNReal) : Real))} ≤
      2 * Real.exp (-
        ((∑ i, fixedLevelRates steps (fun _ => 0) i : NNReal) : Real) *
          epsilon ^ 2 / 3) := by
  rw [fixedLevelLaw_total_poisson]
  exact process_components_lattice_count_accuracy_poisson_concentration_chernoff_failure_bound
    (∑ i, fixedLevelRates steps (fun _ => 0) i) epsilon
    hepsilon hepsilon_le_one

end Kr25Ssmxt

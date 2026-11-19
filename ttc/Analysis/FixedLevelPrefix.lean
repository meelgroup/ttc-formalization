import ttc.Analysis.PoissonVectorDeletion

/-! A fixed-dyadic-level finite-union process obtained by deleting overlap
and appending independent Poisson point-count batches. Its prefix law is an
independent Poisson vector with explicitly updated point rates. -/

namespace ttc

open MeasureTheory

structure FixedLevelStep (ι : Type*) where
  deleted : Finset ι
  incoming : ι → NNReal

def fixedLevelRates {ι : Type*} [DecidableEq ι] :
    List (FixedLevelStep ι) → (ι → NNReal) → (ι → NNReal)
  | [], r => r
  | step :: rest, r =>
      fixedLevelRates rest (fun x =>
        (if x ∈ step.deleted then 0 else r x) + step.incoming x)

noncomputable def fixedLevelLaw {ι : Type*} [Fintype ι] [DecidableEq ι] :
    List (FixedLevelStep ι) → Measure (ι → Nat) → Measure (ι → Nat)
  | [], μ => μ
  | step :: rest, μ =>
      fixedLevelLaw rest
        ((μ.prod (Measure.pi (fun x : ι =>
            ProbabilityTheory.poissonMeasure (step.incoming x)))).map
          (fun pair : (ι → Nat) × (ι → Nat) =>
            fun x => (if x ∈ step.deleted then 0 else pair.1 x) + pair.2 x))

/-- Every prefix of the fixed-level process has the pointwise independent
Poisson law specified by its deletion-and-append rate recurrence. -/
theorem fixedLevelLaw_poisson_prefix
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι))
    (μ : Measure (ι → Nat)) (r : ι → NNReal)
    (hμ : μ = Measure.pi (fun x : ι =>
      ProbabilityTheory.poissonMeasure (r x))) :
    fixedLevelLaw steps μ =
      Measure.pi (fun x : ι =>
        ProbabilityTheory.poissonMeasure (fixedLevelRates steps r x)) := by
  induction steps generalizing μ r with
  | nil => simpa [fixedLevelLaw, fixedLevelRates] using hμ
  | cons step rest ih =>
      change fixedLevelLaw rest
        ((μ.prod (Measure.pi (fun x : ι =>
            ProbabilityTheory.poissonMeasure (step.incoming x)))).map
          (fun pair : (ι → Nat) × (ι → Nat) =>
            fun x => (if x ∈ step.deleted then 0 else pair.1 x) + pair.2 x)) =
        Measure.pi (fun x : ι => ProbabilityTheory.poissonMeasure
          (fixedLevelRates rest (fun x =>
            (if x ∈ step.deleted then 0 else r x) + step.incoming x) x))
      apply ih
      rw [hμ]
      exact poisson_vector_delete_then_add ι step.deleted r step.incoming

theorem fixedLevelLaw_zero_poisson_prefix
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) :
    fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0)) =
      Measure.pi (fun x : ι => ProbabilityTheory.poissonMeasure
        (fixedLevelRates steps (fun _ => 0) x)) := by
  exact fixedLevelLaw_poisson_prefix ι steps _ (fun _ => 0) rfl

end ttc

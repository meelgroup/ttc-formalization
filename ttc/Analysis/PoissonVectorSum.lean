import ttc.Analysis.BernoulliCount

/-! The union-prefix invariant combines independently generated Poisson
point-count vectors. This file gives the finite-dimensional convolution law. -/

namespace ttc

open MeasureTheory

theorem poisson_vector_pointwise_sum
    (ι : Type*) [Fintype ι] (r t : ι → NNReal) :
    ((Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (r i))).prod
      (Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (t i)))).map
        (fun pair : (ι → Nat) × (ι → Nat) =>
          fun i => pair.1 i + pair.2 i) =
      Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (r i + t i)) := by
  let μ : ι → Measure Nat := fun i => ProbabilityTheory.poissonMeasure (r i)
  let ν : ι → Measure Nat := fun i => ProbabilityTheory.poissonMeasure (t i)
  let e := MeasurableEquiv.arrowProdEquivProdArrow Nat Nat ι
  have hproduct :
      (Measure.pi (fun i => (μ i).prod (ν i))).map e =
      (Measure.pi μ).prod (Measure.pi ν) :=
    (measurePreserving_arrowProdEquivProdArrow Nat Nat ι μ ν).map_eq
  change ((Measure.pi μ).prod (Measure.pi ν)).map
    (fun pair : (ι → Nat) × (ι → Nat) =>
      fun i => pair.1 i + pair.2 i) = _
  calc
    ((Measure.pi μ).prod (Measure.pi ν)).map
        (fun pair : (ι → Nat) × (ι → Nat) =>
          fun i => pair.1 i + pair.2 i) =
      ((Measure.pi (fun i => (μ i).prod (ν i))).map e).map
        (fun pair : (ι → Nat) × (ι → Nat) =>
          fun i => pair.1 i + pair.2 i) := by rw [hproduct]
    _ = (Measure.pi (fun i => (μ i).prod (ν i))).map
        (fun pairs : ι → Nat × Nat => fun i => (pairs i).1 + (pairs i).2) := by
          rw [Measure.map_map (by fun_prop) e.measurable]
          rfl
    _ = Measure.pi (fun i : ι =>
        ((μ i).prod (ν i)).map (fun pair : Nat × Nat => pair.1 + pair.2)) := by
          exact Measure.pi_map_pi
            (f := fun _ : ι => fun pair : Nat × Nat => pair.1 + pair.2)
            (fun _ => (by fun_prop : Measurable
              (fun pair : Nat × Nat => pair.1 + pair.2)).aemeasurable)
    _ = _ := by
      congr 1
      funext i
      exact ProbabilityTheory.poissonMeasure_conv_poissonMeasure (r i) (t i)

end ttc

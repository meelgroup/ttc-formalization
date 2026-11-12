import Kr25Ssmxt.Analysis.StatePointCounts
import Kr25Ssmxt.Analysis.CostedMeasureMonad

/-! Poisson marking expressed through the actual labelled TTC state after
its `addBatch` operation, rather than through a detached count vector. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory Arlib.Probability
open Classical

theorem poisson_append_pointCounts_law
    {n : Nat} (s : TTCState n) (hs : s.LabelsFresh)
    (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n))
    (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (mean : NNReal) :
    ((poissonMeasure mean).bind fun count =>
      (iidSampleBatchLaw (count := count) pointLaw).map
        (fun batch => (s.addBatch batch).pointCounts S)) =
      (Measure.pi (fun x : S => poissonMeasure (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} * (mean : Real))))).map
        (fun fresh x => s.pointCounts S x + fresh x) := by
  let shift : (S → Nat) → (S → Nat) :=
    fun fresh x => s.pointCounts S x + fresh x
  have hshift : Measurable shift := by
    unfold shift
    fun_prop
  let counts : (count : Nat) → SampleBatch n count → (S → Nat) :=
    fun _ batch x => colourCount batch x.1
  have hcounts (count : Nat) : Measurable (counts count) := by
    exact Measurable.of_discrete
  have hstep : AEMeasurable
      (fun count : Nat =>
        (iidSampleBatchLaw (count := count) pointLaw).map (counts count))
      (poissonMeasure mean) :=
    Measurable.of_discrete.aemeasurable
  calc
    ((poissonMeasure mean).bind fun count =>
        (iidSampleBatchLaw (count := count) pointLaw).map
          (fun batch => (s.addBatch batch).pointCounts S)) =
      (poissonMeasure mean).bind (fun count =>
        ((iidSampleBatchLaw (count := count) pointLaw).map
          (counts count)).map shift) := by
            congr 1
            funext count
            rw [Measure.map_map hshift (hcounts count)]
            congr 1
            funext batch
            exact s.pointCounts_addBatch batch S hs
    _ = ((poissonMeasure mean).bind fun count =>
        (iidSampleBatchLaw (count := count) pointLaw).map
          (counts count)).map shift := by
            exact (map_bind_measure (poissonMeasure mean)
              (fun count =>
                (iidSampleBatchLaw (count := count) pointLaw).map
                  (counts count)) shift hstep hshift).symm
    _ = (Measure.pi (fun x : S => poissonMeasure (Real.toNNReal
          (pointLaw.real {(x : LatticePoint n)} * (mean : Real))))).map
            (fun fresh x => s.pointCounts S x + fresh x) := by
              rw [iid_batch_poisson_count_law pointLaw S hsupport mean]

/-- The executable component's delete-then-append operations have the exact
count-vector law obtained by zeroing the component coordinates and adding
independent Poisson marked counts. -/
theorem poisson_delete_append_pointCounts_law
    {n : Nat} (s : TTCState n) (hs : s.LabelsFresh)
    (P : PolytopeData n)
    (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n))
    (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (mean : NNReal) :
    ((poissonMeasure mean).bind fun count =>
      (iidSampleBatchLaw (count := count) pointLaw).map
        (fun batch => ((s.removeComponent P).addBatch batch).pointCounts S)) =
      (Measure.pi (fun x : S => poissonMeasure (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} * (mean : Real))))).map
        (fun fresh x =>
          (if x.1.toPoint ∈ P.carrier then 0 else s.pointCounts S x) + fresh x) := by
  rw [poisson_append_pointCounts_law (s.removeComponent P)
    (s.labelsFresh_removeComponent P hs) pointLaw S hsupport mean]
  congr 1
  funext fresh x
  rw [s.pointCounts_removeComponent P S]

end Kr25Ssmxt

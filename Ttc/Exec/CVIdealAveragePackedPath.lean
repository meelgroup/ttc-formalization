import Ttc.Exec.CVIdealAveragePathTelescope

/-! Packed `Fin k` estimator specialization of the ideal-average path telescope. -/

namespace Ttc.CVIdealAveragePackedPath

open MeasureTheory ProbabilityTheory Finset Set
open Arlib Arlib.Probability
open scoped ENNReal BigOperators

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]
variable {k t : Nat}

/-- The average of the `k` score coordinates at one phase of a finite augmented path. -/
noncomputable def packedHistoryPhaseAvg
    (g : Fin (t + 1) → Fin k → Score → Real) (i : Fin (t + 1))
    (h : Finset.Iic t → Fin k → Score × Seed) : Real :=
  (∑ l : Fin k, g i l ((h ⟨i.1, Finset.mem_Iic.2 (Nat.le_of_lt_succ i.2)⟩ l).1)) / k

/-- Complete packed product read from states `0,...,t`. -/
noncomputable def packedHistoryProduct
    (g : Fin (t + 1) → Fin k → Score → Real)
    (h : Finset.Iic t → Fin k → Score × Seed) : Real :=
  ∏ i : Fin (t + 1), packedHistoryPhaseAvg g i h

theorem measurable_packedHistoryPhaseAvg
    {g : Fin (t + 1) → Fin k → Score → Real}
    (hg : ∀ i l, Measurable (g i l)) (i : Fin (t + 1)) :
    Measurable (packedHistoryPhaseAvg (Seed := Seed) g i) := by
  unfold packedHistoryPhaseAvg
  exact (Finset.measurable_fun_sum _ fun l _ ↦
    (hg i l).comp (measurable_fst.comp
      ((measurable_pi_apply l).comp (measurable_pi_apply _)))).div measurable_const

theorem measurable_packedHistoryProduct
    {g : Fin (t + 1) → Fin k → Score → Real}
    (hg : ∀ i l, Measurable (g i l)) :
    Measurable (packedHistoryProduct (Seed := Seed) g) := by
  unfold packedHistoryProduct
  exact Finset.measurable_fun_prod _ fun i _ ↦
    measurable_packedHistoryPhaseAvg (Seed := Seed) hg i

/-- Concrete finite-path TV statement for the packed augmented estimator.  The phase
replacement premise is averaged only under the exact ideal prefix law. -/
theorem tvLe_packedHistoryProduct_of_idealAverage
    (P Q : Nat → Kernel (Fin k → Score × Seed) (Fin k → Score × Seed))
    [∀ i, IsMarkovKernel (P i)] [∀ i, IsMarkovKernel (Q i)]
    (mu nu : Measure (Fin k → Score × Seed))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d : ENNReal} (e : Nat → ENNReal) (hinit : TVLe mu nu d)
    (haverage : ∀ i,
      TVLe
        ((Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure Q nu)) ⊗ₘ
          inhomogeneousHistoryKernel P i)
        ((Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure Q nu)) ⊗ₘ
          inhomogeneousHistoryKernel Q i)
        (e i))
    (g : Fin (t + 1) → Fin k → Score → Real)
    (hg : ∀ i l, Measurable (g i l)) :
    TVLe
      (Measure.map (packedHistoryProduct (Seed := Seed) g ∘ Preorder.frestrictLe t)
        (inhomogeneousPathMeasure P mu))
      (Measure.map (packedHistoryProduct (Seed := Seed) g ∘ Preorder.frestrictLe t)
        (inhomogeneousPathMeasure Q nu))
      (d + ∑ i ∈ Finset.range t, e i) :=
  Ttc.CVIdealAveragePathTelescope.tvLe_map_frestrictLe_statistic_of_idealAverage
    P Q mu nu e hinit haverage t (packedHistoryProduct (Seed := Seed) g)
      (measurable_packedHistoryProduct (Seed := Seed) hg)

/-- Exact ideal one-run success `4/5` and one total path-TV budget `1/20` give the
operational capped run success `3/4`.  This is the signature consumed by the existing
outer median/cutoff amplification. -/
theorem three_fourths_packedHistoryProduct_of_idealAverage
    (P Q : Nat → Kernel (Fin k → Score × Seed) (Fin k → Score × Seed))
    [∀ i, IsMarkovKernel (P i)] [∀ i, IsMarkovKernel (Q i)]
    (mu nu : Measure (Fin k → Score × Seed))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d : ENNReal} (e : Nat → ENNReal) (hinit : TVLe mu nu d)
    (haverage : ∀ i,
      TVLe
        ((Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure Q nu)) ⊗ₘ
          inhomogeneousHistoryKernel P i)
        ((Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure Q nu)) ⊗ₘ
          inhomogeneousHistoryKernel Q i)
        (e i))
    (g : Fin (t + 1) → Fin k → Score → Real)
    (hg : ∀ i l, Measurable (g i l))
    {L U : Real}
    (hideal : 4 / 5 ≤
      (inhomogeneousPathMeasure Q nu).real
        {ω | packedHistoryProduct (Seed := Seed) g (Preorder.frestrictLe t ω) ∈ Set.Icc L U})
    (htop : d + ∑ i ∈ Finset.range t, e i ≠ ⊤)
    (hbudget : (d + ∑ i ∈ Finset.range t, e i).toReal ≤ 1 / 20) :
    3 / 4 ≤
      (inhomogeneousPathMeasure P mu).real
        {ω | packedHistoryProduct (Seed := Seed) g (Preorder.frestrictLe t ω) ∈ Set.Icc L U} := by
  have htv := tvLe_packedHistoryProduct_of_idealAverage P Q mu nu e hinit haverage g hg
  have hset : MeasurableSet (Set.Icc L U) := measurableSet_Icc
  have hdist := htv.abs_measureReal_sub_le htop hset
  rw [abs_sub_le_iff] at hdist
  let f : (Nat → Fin k → Score × Seed) → Real :=
    packedHistoryProduct (Seed := Seed) g ∘ Preorder.frestrictLe t
  have hf : Measurable f :=
    (measurable_packedHistoryProduct (Seed := Seed) hg).comp
      (Preorder.measurable_frestrictLe t)
  have hactualMap :
      (Measure.map f (inhomogeneousPathMeasure P mu)).real (Set.Icc L U) =
        (inhomogeneousPathMeasure P mu).real (f ⁻¹' Set.Icc L U) := by
    have hmap : (Measure.map f (inhomogeneousPathMeasure P mu)) (Set.Icc L U) =
        (inhomogeneousPathMeasure P mu) (f ⁻¹' Set.Icc L U) :=
      Measure.map_apply hf hset
    exact congrArg ENNReal.toReal hmap
  have hidealMap :
      (Measure.map f (inhomogeneousPathMeasure Q nu)).real (Set.Icc L U) =
        (inhomogeneousPathMeasure Q nu).real (f ⁻¹' Set.Icc L U) := by
    have hmap : (Measure.map f (inhomogeneousPathMeasure Q nu)) (Set.Icc L U) =
        (inhomogeneousPathMeasure Q nu) (f ⁻¹' Set.Icc L U) :=
      Measure.map_apply hf hset
    exact congrArg ENNReal.toReal hmap
  change TVLe (Measure.map f (inhomogeneousPathMeasure P mu))
      (Measure.map f (inhomogeneousPathMeasure Q nu)) _ at htv
  change 4 / 5 ≤ (inhomogeneousPathMeasure Q nu).real (f ⁻¹' Set.Icc L U) at hideal
  rw [hactualMap, hidealMap] at hdist
  change 3 / 4 ≤ (inhomogeneousPathMeasure P mu).real (f ⁻¹' Set.Icc L U)
  linarith

#print axioms tvLe_packedHistoryProduct_of_idealAverage
#print axioms three_fourths_packedHistoryProduct_of_idealAverage

end Ttc.CVIdealAveragePackedPath

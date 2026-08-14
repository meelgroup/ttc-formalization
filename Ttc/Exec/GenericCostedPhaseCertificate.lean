import Ttc.Exec.SequentialCostedPathLumping
import Ttc.Exec.CVSourcePolynomialCutoffCapstone

/-! State-generic operational phase certificates.

Unlike the older CV adapter, this file does not fix the phase state to Euclidean space.
It therefore supports augmented states such as `(scoreSample, nextWarmSeed)`.
-/

namespace Ttc.GenericCostedPhaseCertificate

open MeasureTheory ProbabilityTheory Set
open Arlib.Probability
open Ttc.CVSourcePolynomialCutoffCapstone
open scoped ENNReal Classical

variable {E : Type*} [MeasurableSpace E]
variable {n : Nat}

abbrev CostedPath (E : Type*) := Nat → ENNReal × E
abbrev StatePath (E : Type*) := Nat → E

noncomputable def oneRunLaw
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) : Measure (CostedPath E) :=
  Ttc.SequentialCost.execution Q mu0

noncomputable def queryCost (m : Nat) (omega : CostedPath E) : ENNReal :=
  Ttc.SequentialCost.totalCost m omega

def statePath (omega : CostedPath E) : StatePath E :=
  Ttc.SequentialCostedPathLumping.pathMap Prod.snd omega

def value (est : StatePath E → Real) (omega : CostedPath E) : Real :=
  est (statePath omega)

noncomputable def stateMarginal
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) (i : Nat) : Measure E :=
  Measure.map (fun omega ↦ (omega i).2) (oneRunLaw Q mu0)

structure Refinement
    (P : Nat → Kernel E E)
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) (m : Nat) (phaseBound : Nat → ENNReal) : Prop where
  forgetCost : ∀ i x, Measure.map Prod.snd (Q i x) = P i x
  phaseMean : ∀ i, i < m →
    (∫⁻ x, Ttc.SequentialCost.stepMean Q i x ∂stateMarginal Q mu0 i) ≤ phaseBound i

theorem expected_queryCost_le
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (hphase : ∀ i, i < m →
      (∫⁻ x, Ttc.SequentialCost.stepMean Q i x ∂stateMarginal Q mu0 i) ≤ phaseBound i) :
    (∫⁻ omega, queryCost m omega ∂oneRunLaw Q mu0) ≤
      ∑ i ∈ Finset.range m, phaseBound i := by
  unfold queryCost oneRunLaw stateMarginal at *
  rw [Ttc.SequentialCost.lintegral_totalCost_eq_sum_stateMeans]
  apply Finset.sum_le_sum
  intro i hi
  exact hphase i (Finset.mem_range.1 hi)

theorem measurable_queryCost (m : Nat) :
    Measurable (queryCost (E := E) m) :=
  Ttc.SequentialCost.measurable_totalCost m

theorem measurable_value {est : StatePath E → Real} (hest : Measurable est) :
    Measurable (value est) :=
  hest.comp (Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd)

/-- A generic fixed-input one-run certificate.  It is the direct adapter to the public
cutoff/median capstone and permits an augmented phase state `E`. -/
theorem sourceOneRunCertificate_of_refinement
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (hop : Refinement P Q mu0 m phaseBound)
    (est : StatePath E → Real) (hest : Measurable est)
    {runtimeConstant R eps lo hi : Real}
    (hsum : (∑ i ∈ Finset.range m, phaseBound i) ≤
      sourceOneRunQueryBudget runtimeConstant n R eps)
    (haccuracy : 4 / 5 ≤
      (inhomogeneousPathMeasure P mu0).real {omega | est omega ∈ Icc lo hi}) :
    SourceOneRunCertificate (oneRunLaw Q mu0) (queryCost m) (value est)
      runtimeConstant n R eps lo hi := by
  letI : IsProbabilityMeasure (oneRunLaw Q mu0) := by
    unfold oneRunLaw
    infer_instance
  refine
    { probability := inferInstance
      cost_measurable := measurable_queryCost m
      value_measurable := measurable_value hest
      expected_queries := (expected_queryCost_le Q mu0 m phaseBound hop.phaseMean).trans hsum
      accuracy := ?_ }
  have hpath : Measure.map statePath (oneRunLaw Q mu0) =
      inhomogeneousPathMeasure P mu0 := by
    exact Ttc.SequentialCostedPathLumping.map_statePath_execution Q P mu0 hop.forgetCost
  let G : Set (StatePath E) := {omega | est omega ∈ Icc lo hi}
  have hG : MeasurableSet G := measurableSet_Icc.preimage hest
  change Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
      (oneRunLaw Q mu0) = inhomogeneousPathMeasure P mu0 at hpath
  have heq : (oneRunLaw Q mu0).real (statePath ⁻¹' G) =
      (inhomogeneousPathMeasure P mu0).real G := by
    change ((oneRunLaw Q mu0)
      (Ttc.SequentialCostedPathLumping.pathMap Prod.snd ⁻¹' G)).toReal = _
    rw [← Measure.map_apply
      (Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd) hG, hpath]
    rfl
  change 4 / 5 ≤ (oneRunLaw Q mu0).real (statePath ⁻¹' G)
  rw [heq]
  exact haccuracy

#print axioms expected_queryCost_le
#print axioms sourceOneRunCertificate_of_refinement

end Ttc.GenericCostedPhaseCertificate

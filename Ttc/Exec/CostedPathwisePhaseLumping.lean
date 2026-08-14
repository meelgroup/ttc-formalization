import Ttc.Exec.SequentialCostedPathLumping
import Ttc.Volume.CVPathwisePhaseKernel

/-! Exact operational seam for shrink/rescale/final-rejection phase kernels. -/

namespace Ttc.CostedPathwisePhaseLumping

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVPathwisePhaseKernel
open Ttc.SequentialCostedPathLumping
open Ttc.CostedStatefulSpeedyPhases
open scoped ENNReal Classical

variable {n : Nat}
abbrev State := EuclideanSpace Real (Fin n)

/-- The complete source-style state transition schedule: lazy speedy execution, rejection
into the shrunken body, rescaling, and final speedy accept/restart. -/
noncomputable def pathwiseSourcePhaseSchedule
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (steps : Nat → Nat) :
    Nat → Kernel (State (n := n)) (State (n := n)) :=
  fun i => pathwisePhaseKernel K hK (delta i) (sigmaSq i) (steps i)

theorem isMarkovKernel_pathwiseSourcePhaseSchedule
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (steps : Nat → Nat)
    (hsigma : ∀ i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) (i : Nat) :
    IsMarkovKernel (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i) := by
  unfold pathwiseSourcePhaseSchedule
  exact isMarkovKernel_pathwisePhaseKernel K hK (delta i) (steps i) (hsigma i) hc2

/-- Once an honest costed phase kernel has the source-style pointwise state marginal, the
entire recorded-query execution projects exactly to the source state trajectory.  This is
the precise interface needed by corrected `lem:accuracy`; it preserves all history/next
factorizations, not only individual phase marginals. -/
theorem map_statePath_costedPathwisePhaseExecution
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (steps : Nat → Nat)
    (hsigma : ∀ i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (Q : Nat → Kernel (State (n := n)) (ENNReal × State (n := n)))
    [∀ i, IsMarkovKernel (Q i)]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) =
      pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i x)
    (mu : Measure (State (n := n))) [IsProbabilityMeasure mu] :
    Measure.map (statePath (n := n)) (Ttc.SequentialCost.execution Q mu) =
      @inhomogeneousPathMeasure _ _
        (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
        (fun i => isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
          hsigma hc2 i) mu := by
  letI hP : ∀ i, IsMarkovKernel
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i) :=
    fun i => isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
      hsigma hc2 i
  change Measure.map (pathMap Prod.snd) (Ttc.SequentialCost.execution Q mu) = _
  exact map_statePath_execution Q
    (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps) mu hforget

/-- Measurable state events have exactly the same probability in the actual costed run and
the source-style path law. -/
theorem measureReal_stateEvent_eq_costedPathwisePhaseExecution
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (steps : Nat → Nat)
    (hsigma : ∀ i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (Q : Nat → Kernel (State (n := n)) (ENNReal × State (n := n)))
    [∀ i, IsMarkovKernel (Q i)]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) =
      pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i x)
    (mu : Measure (State (n := n))) [IsProbabilityMeasure mu]
    (G : Set (Nat → State (n := n))) (hG : MeasurableSet G) :
    (Ttc.SequentialCost.execution Q mu).real (statePath ⁻¹' G) =
      (@inhomogeneousPathMeasure _ _
        (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
        (fun i => isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
          hsigma hc2 i) mu).real G := by
  letI hP : ∀ i, IsMarkovKernel
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i) :=
    fun i => isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
      hsigma hc2 i
  apply measureReal_stateEvent_eq_of_path_lumping Q
    (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps) mu
  · exact map_statePath_costedPathwisePhaseExecution K hK delta sigmaSq steps
      hsigma hc2 Q hforget mu
  · exact hG

#print axioms map_statePath_costedPathwisePhaseExecution
#print axioms measureReal_stateEvent_eq_costedPathwisePhaseExecution

end Ttc.CostedPathwisePhaseLumping

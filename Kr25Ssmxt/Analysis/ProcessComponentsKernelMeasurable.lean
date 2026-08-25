import Kr25Ssmxt.Analysis.ProcessComponentKernelMeasurable

/-!
# Measurability of the TTC component fold

The recursive bind over a fixed component list is a measurable measure-valued kernel in its
incoming state.
-/

namespace Kr25Ssmxt

/--
For fixed algorithm data and component list, `processComponents` is measurable in the
incoming TTC state.

INTERNAL: Giry-monad bookkeeping for the recursive TTC component fold.
-/
lemma processComponents_kernel_measurable {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (Ps : List (PolytopeData n)) :
    Measurable (fun s => processComponents O b epsilonPrime deltaPrime threshold Ps s) := by
  induction Ps with
  | nil =>
      simpa [processComponents] using
        (MeasureTheory.Measure.measurable_dirac :
          Measurable (fun s : TTCState n => MeasureTheory.Measure.dirac s))
  | cons P rest ih =>
      simp only [processComponents]
      exact (MeasureTheory.Measure.measurable_bind' ih).comp
        (processComponent_kernel_measurable O b epsilonPrime deltaPrime threshold P)

end Kr25Ssmxt

import Kr25Ssmxt.Model.Program
import Kr25Ssmxt.Analysis.PoissonUnitNotHalfAccurate

/-!
# Accuracy of the stochastic component-processing core

This module isolates the substantive probabilistic obligation in the lattice-count
analysis from the outer empty-decomposition branch and final `TTCState.estimate` map in
`ttc`.  A proof must establish the component-prefix multiplicity invariant and the
concentration bound at the adaptively selected thinning level.

The model uses the required multiplicative mean `volumeOutcome.2 * state.rate`.  The paper's
concentration split does not cover `j* = 0`; `ttc` therefore handles low scaled lattice
volume exactly, and this lemma is used only under the displayed high-intensity premise.

The high-intensity Poissonized streaming result is the sole field of `Prior`.  This module
checks that the borrowed statement has exactly the measure-level form required downstream.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory unitInterval
open MeasureTheory

namespace Kr25Ssmxt

/-- The measure-level stochastic core of the paper's lattice-count lemma, before it is
wrapped by the nonempty branch of `ttc`.

PAPER: sections/analysis.tex:201-311
-/
lemma process_components_lattice_count_accuracy
    (hprior : Prior)
    {n k : Nat}
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (O : TTCOracles n k)
    (hvolume : ComputeVolumeContract O F hbounded params)
    (hsamples : GenerateSamplesContract O F hbounded params)
    (hnonempty : (O.preprocessing.run F hbounded).componentCount ≠ 0)
    (hcomponentLattice :
      let D := O.preprocessing.run F hbounded
      let b := (O.preprocessing.choosePrecision D params).value
      ∀ i,
        (volume (D.component i).carrier).toReal ∈
          Arlib.relErr params.latticeEta
            (((D.component i).carrier ∩ decimalLattice b n).ncard /
              (10 : Real) ^ (b * n)))
    (hlarge :
      let D := O.preprocessing.run F hbounded
      let b := (O.preprocessing.choosePrecision D params).value
      params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real)) :
    let D := O.preprocessing.run F hbounded
    let b := (O.preprocessing.choosePrecision D params).value
    let core := processComponents O b params.epsilonPrime
      (params.deltaPrime D.componentCount) (params.threshold D.componentCount)
      (List.ofFn D.component) (TTCState.initial n)
    (core.map TTCState.estimate).real
        {estimate | (estimate : Real) ∈
          Arlib.relErr (params.epsilon / 2)
            ((D.latticePoints b).ncard / (10 : Real) ^ (b * n))} >=
      1 - params.delta := by
  have hstream := hprior.streamingCoreAccuracy F hbounded params O
    hvolume hsamples hnonempty hcomponentLattice hlarge
  simpa [scaledLatticeVolume, NNReal.coe_div, NNReal.coe_pow] using hstream

end Kr25Ssmxt

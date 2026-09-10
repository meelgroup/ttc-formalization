import Kr25Ssmxt.Analysis.ProcessComponentsLatticeCountAccuracy

/-!
# Stochastic lattice-count accuracy for TTC

This module isolates the probabilistic content of the paper's lattice-count lemma.  Its
proof must establish the component-prefix Poisson invariant, almost-sure termination of
both thinning loops, and concentration at the adaptively selected dyadic rate.

The substantive prefix invariant and adaptive concentration estimate are isolated in
`process_components_lattice_count_accuracy`; this file checks that its measure-level
conclusion is exactly the nonempty branch exposed by `ttc`.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory unitInterval
open MeasureTheory

namespace Kr25Ssmxt

/-- The stochastic core of the TTC analysis: under the componentwise lattice comparison,
the returned estimate has relative error at most `epsilon / 2` from the scaled lattice
count, except with probability `delta`.

PAPER: sections/analysis.tex:218-311
-/
lemma ttc_lattice_count_accuracy
    (hprior : Prior)
    {n k : Nat}
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (O : TTCOracles n k)
    (hvolume : ComputeVolumeContract O F hbounded params)
    (hsamples : GenerateSamplesContract O F hbounded params)
    (hnonempty : (O.preprocessing.run F hbounded).componentCount ≠ 0)
    (hlarge :
      let D := O.preprocessing.run F hbounded
      let b := (O.preprocessing.choosePrecision D params).value
      params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real))
    (hcomponentLattice :
      let D := O.preprocessing.run F hbounded
      let b := (O.preprocessing.choosePrecision D params).value
      ∀ i,
        (volume (D.component i).carrier).toReal ∈
          Arlib.relErr params.latticeEta
            (((D.component i).carrier ∩ decimalLattice b n).ncard /
              (10 : Real) ^ (b * n))) :
    let D := O.preprocessing.run F hbounded
    let b := (O.preprocessing.choosePrecision D params).value
    (ttc F hbounded params O).real
        {estimate | (estimate : Real) ∈
          Arlib.relErr (params.epsilon / 2)
            ((D.latticePoints b).ncard / (10 : Real) ^ (b * n))} >=
      1 - params.delta := by
  let D := O.preprocessing.run F hbounded
  let b := (O.preprocessing.choosePrecision D params).value
  let q := scaledLatticeVolume D b
  let core := processComponents O b params.epsilonPrime
    (params.deltaPrime D.componentCount) (params.threshold D.componentCount)
    (List.ofFn D.component) (TTCState.initial n)
  have htcc : ttc F hbounded params O = core.map TTCState.estimate := by
    simp [ttc, D, hnonempty, b, core]
  rw [htcc]
  simpa [D, b, q, core, scaledLatticeVolume, NNReal.coe_div,
    NNReal.coe_pow] using
      process_components_lattice_count_accuracy hprior F hbounded params O hvolume hsamples
        hnonempty hcomponentLattice hlarge

end Kr25Ssmxt

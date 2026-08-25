import Kr25Ssmxt.Model.Pseudocode
import Kr25Ssmxt.Analysis.PoissonUnitNotHalfAccurate

/-!
# Accuracy of the stochastic component-processing core

This module isolates the substantive probabilistic obligation in the lattice-count
analysis from the outer empty-decomposition branch and final `TTCState.estimate` map in
`ttc`.  A proof must establish the component-prefix multiplicity invariant and the
concentration bound at the adaptively selected thinning level.

The modeled fresh-copy mean is currently `volumeOutcome.2 / withoutDuplicates.rate`.
The paper's invariant instead requires multiplication by the current rate.  In addition,
the paper's concentration split does not cover its `j* = 0` case: at unit intensity the
desired half-relative-error event has probability `exp (-1) < 1/2`, as formalized by
`poisson_unit_not_half_accurate`.  Thus correcting the rate convention alone is not enough;
a positive lower bound on the relevant Poisson mean or a separate low-volume estimator is
also required.

MODEL: `processComponent` — replace the fresh Poisson mean
`volumeOutcome.2 / withoutDuplicates.rate` by
`volumeOutcome.2 * withoutDuplicates.rate`.

PRESERVES: `∀ {n k} (O : TTCOracles n k) b e d threshold P state,
  IsProbabilityMeasure (O.computeVolume P e d) →
  (∀ count, IsProbabilityMeasure (O.generateSamples P count b e d)) →
  IsProbabilityMeasure (processComponent O b e d threshold P state)`.
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
              (10 : Real) ^ (b * n))) :
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
  -- The available component-intensity lemma is deliberately stated for the paper's
  -- multiplicative mean.  It cannot be applied to `processComponent`, whose definition
  -- still uses `volumeOutcome.2 / withoutDuplicates.rate`.  Independently, the present
  -- assumptions give no lower bound on the final Poisson mean, so the threshold-sized
  -- concentration lemma does not cover the `j* = 0` branch.
  sorry

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r7 · blocked · reconfirmed from the elaborated `processComponent` definition that
  fresh copies use the divisive mean `t / p`, differing from the invariant's `t * p`
  by `p⁻²` after later thinning; the independent unit-Poisson obstruction still leaves
  the `j* = 0` branch false without a low-intensity repair
* r6 · blocked · the new point-intensity and finite-sum lemmas concern the paper's
  corrected multiplicative mean and therefore do not apply to the modeled divisive mean;
  the proposed unit-Poisson disproof also needs `delta = 1/2` (not `delta = 1`, whose
  conclusion is the trivial lower bound zero) and a concrete exact-oracle instance
* r5 · blocked · the new coded-cardinality, parameter-envelope, and high-intensity
  Poisson lemmas do not supply either missing model feature; author decisions are still
  required on the corrected fresh mean and the shape-preserving low-intensity branch
* r4 · blocked · the prescribed proof needs two model-level design decisions: correct
  the fresh mean `t / p` to `t * p`, and add a low-count branch or a threshold-sized
  lattice-count premise; no theorem-local lemma follows from the present assumptions
* r3 · blocked · formalized the low-intensity `j* = 0` obstruction in
  `poisson_unit_not_half_accurate`; the assumptions provide no lower mean bound
* r2 · reduced · isolated the exact `processComponents` invariant/concentration theorem;
  blocked by the modeled fresh Poisson mean `t / p` versus the paper's `t * p`
-/

end Kr25Ssmxt

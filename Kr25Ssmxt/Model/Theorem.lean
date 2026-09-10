import Kr25Ssmxt.Model.Prior
import Kr25Ssmxt.Model.Pseudocode
import Kr25Ssmxt.Analysis.TheoremProof
import Kr25Ssmxt.Analysis.GeometricOracleDischarge

namespace Kr25Ssmxt

/-!
The headline is stated for the measure-valued law of the on-disk algorithm.  The model
repairs two defects exposed by formalization: fresh Poisson counts use the multiplicative
mean `t * p`, and the invalid low-count concentration step is excluded by a public
high-intensity premise.

`Prior` exposes the remaining high-intensity Poissonized streaming theorem as a hypothesis.
The deterministic preprocessing, oracle contracts, empty case, lattice
comparison, measure normalization, and final error composition are proved in this project.
-/

/--
TTC returns a probability law on single nonnegative estimates, and its estimate is within
relative error `ε` of the Lebesgue volume of the existentially projected real solution set
with probability at least `1 - δ`.  This is an accuracy statement only; it makes no runtime
claim.

PAPER: sections/analysis.tex:314-326
-/
theorem ttc_volume_accuracy
    (hprior : Prior)
    {n k : Nat}
    (hn : 0 < n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (O : TTCOracles n k)
    (hvolume : ComputeVolumeContract O F hbounded params)
    (hsamples : GenerateSamplesContract O F hbounded params)
    (hregime :
      let D := O.preprocessing.run F hbounded
      let b := (O.preprocessing.choosePrecision D params).value
      D.componentCount = 0 ∨
        params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real)) :
    MeasureTheory.IsProbabilityMeasure (ttc F hbounded params O) ∧
      (ttc F hbounded params O).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr params.epsilon
              (MeasureTheory.volume (solutionSet F)).toReal} ≥
        1 - params.delta := by
  exact ttc_volume_accuracy_proof hprior hn F hbounded params O hvolume hsamples hregime

/--
A specialization of the headline accuracy theorem to exact semantic oracles.  The canonical
laws return exact Lebesgue volume and an IID uniform batch on the coded lattice, and their
contracts are proved.  This is not a refinement proof for finite-step implementations of
CV18 or Hit-and-Run.

This theorem makes no runtime claim about evaluating the canonical laws.
-/
theorem ttc_volume_accuracy_exact_semantic_oracles
    (hprior : Prior)
    {n k : Nat}
    (hn : 0 < n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (prep : TTCPreprocessor n k)
    (hregime :
      let D := prep.run F hbounded
      let b := (prep.choosePrecision D params).value
      D.componentCount = 0 ∨
        params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real)) :
    MeasureTheory.IsProbabilityMeasure
        (ttc F hbounded params (exactSemanticOracles prep)) ∧
      (ttc F hbounded params (exactSemanticOracles prep)).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr params.epsilon
              (MeasureTheory.volume (solutionSet F)).toReal} ≥
        1 - params.delta := by
  exact ttc_volume_accuracy hprior hn F hbounded params (exactSemanticOracles prep)
    (exact_volume_contract prep F hbounded params)
    (exact_samples_contract hn prep F hbounded params) hregime

#modelClosureOfType ttc_volume_accuracy
#print axioms ttc_volume_accuracy
#print axioms ttc_volume_accuracy_exact_semantic_oracles

end Kr25Ssmxt

import Kr25Ssmxt.Model.Prior
import Kr25Ssmxt.Model.Pseudocode
import Kr25Ssmxt.Analysis.TtcVolumeAccuracyLatticeComparison
import Kr25Ssmxt.Analysis.TtcVolumeAccuracyLatticeEstimate
import Kr25Ssmxt.Analysis.TtcLatticeCountAccuracy

/-!
# Assembly of the TTC volume-accuracy theorem

The empty decomposition is handled completely here.  The nonempty branch combines the
component and union lattice comparisons with `ttc_lattice_count_accuracy`; that theorem
invokes the explicit `Prior` field under the public high-intensity premise.

The algebraic lemmas below retain the original divisive-rate diagnosis as a regression
check and record the multiplicative cancellation used by the repaired model.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory unitInterval
open MeasureTheory

namespace Kr25Ssmxt

/--
After thinning a coded `t / p` Poisson batch by `2ʳ` and updating the stored rate in the
same way, its expected contribution to `TTCState.estimate` is `t / p²`.

INTERNAL: Algebraic diagnosis of the rate convention in `processComponent`.
-/
lemma divided_poisson_rate_estimator (t p : NNReal) (hp : p ≠ 0) (r : Nat) :
    (t / (p * (2 : NNReal) ^ r)) / (p / (2 : NNReal) ^ r) = t / p ^ 2 := by
  field_simp

/--
With the paper's `t * p` Poisson mean, common thinning and division by the updated rate
cancel and the expected estimator contribution is exactly `t`.

PAPER: sections/algo.tex:32-43
-/
lemma multiplied_poisson_rate_estimator (t p : NNReal) (hp : p ≠ 0) (r : Nat) :
    (t * p / (2 : NNReal) ^ r) / (p / (2 : NNReal) ^ r) = t := by
  field_simp

/--
The headline accuracy conclusion in the exact zero-volume branch.

INTERNAL: Exact zero-volume branch of the total algorithm.
-/
lemma ttc_volume_accuracy_empty
    {n k : Nat}
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (O : TTCOracles n k)
    (hempty : (O.preprocessing.run F hbounded).componentCount = 0) :
    IsProbabilityMeasure (ttc F hbounded params O) ∧
      (ttc F hbounded params O).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr params.epsilon
              (volume (solutionSet F)).toReal} ≥
        1 - params.delta := by
  let D := O.preprocessing.run F hbounded
  have hD : D.componentCount = 0 := hempty
  have hunion : D.union = ∅ := by
    ext x
    constructor
    · intro hx
      simp only [Decomposition.union, Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      have : i.val < 0 := by simpa [hD] using i.isLt
      omega
    · simp
  have hvolume : volume (solutionSet F) = 0 := by
    rw [← D.volume_eq_solutionSet, hunion]
    simp
  have hzero : (0 : Real) ∈ Arlib.relErr params.epsilon 0 := by
    simp [Arlib.relErr]
  have hset : MeasurableSet
      {estimate : NNReal | (estimate : Real) ∈ Arlib.relErr params.epsilon 0} := by
    exact measurableSet_Icc.preimage (by fun_prop)
  simp only [ttc, hempty, if_pos, hvolume]
  constructor
  · infer_instance
  · simp only [ENNReal.toReal_zero]
    have hmem : (0 : NNReal) ∈
        {estimate : NNReal | (estimate : Real) ∈ Arlib.relErr params.epsilon 0} := by
      exact hzero
    rw [Measure.real, Measure.dirac_apply' 0 hset, Set.indicator_of_mem hmem]
    simp
    exact params.delta_pos.le

/--
TTC returns a probability law and an `ε`-relative volume estimate with probability at
least `1 - δ`.

PAPER: sections/analysis.tex:314-326
-/
theorem ttc_volume_accuracy_proof
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
    IsProbabilityMeasure (ttc F hbounded params O) ∧
      (ttc F hbounded params O).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr params.epsilon
              (volume (solutionSet F)).toReal} ≥
        1 - params.delta := by
  let D := O.preprocessing.run F hbounded
  by_cases hempty : D.componentCount = 0
  · exact ttc_volume_accuracy_empty F hbounded params O hempty
  · let b := (O.preprocessing.choosePrecision D params).value
    have hlarge :
        params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real) := by
      change D.componentCount = 0 ∨
        params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real) at hregime
      exact hregime.resolve_left hempty
    have hcomparison := ttc_volume_accuracy_lattice_comparison hn D params b
      (O.preprocessing.choosePrecision D params).adequate
    have hlatticeEstimate := ttc_lattice_count_accuracy hprior F hbounded params O hvolume
      hsamples hempty hlarge hcomparison.1
    have haccuracy := ttc_volume_accuracy_lattice_estimate hn F hbounded params O hvolume
      hsamples hcomparison.2 hlatticeEstimate
    have hvolumeEq : volume D.union = volume (solutionSet F) := D.volume_eq_solutionSet
    rw [← hvolumeEq]
    exact ⟨ttc_volume_accuracy_probability_measure F hbounded params O hvolume hsamples,
      haccuracy⟩

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · reduced · closed the headline assembly through `ttc_lattice_count_accuracy`
* r1 · diagnosed · isolated the original nonempty `t / p` rate mismatch
-/

end Kr25Ssmxt

import Kr25Ssmxt.Analysis.TtcVolumeAccuracyProbabilityMeasure

/-!
# Deterministic assembly of TTC's lattice estimate

This file proves that a stochastic relative-error estimate of the scaled lattice count,
together with the union lattice comparison, implies the desired relative-error estimate of
the union's volume.  The oracle contracts are used to ensure that the output law is finite,
which is required when passing from event inclusion to monotonicity of `Measure.real`.

The substantive stochastic premise is supplied by `ttc_lattice_count_accuracy` under the
headline theorem's high-intensity premise.
-/

namespace Kr25Ssmxt

/-- If the stochastic core supplies the paper's intermediate lattice-count estimate, the
deterministic lattice comparison converts that event into the headline volume event.

INTERNAL: Deterministic assembly of the lattice estimate and lattice comparison bounds. -/
lemma ttc_volume_accuracy_lattice_estimate
    {n k : Nat}
    (hn : 0 < n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (O : TTCOracles n k)
    (hvolume : ComputeVolumeContract O F hbounded params)
    (hsamples : GenerateSamplesContract O F hbounded params)
    (hunionLattice :
      let D := O.preprocessing.run F hbounded
      let b := (O.preprocessing.choosePrecision D params).value
      (MeasureTheory.volume D.union).toReal ∈
        Arlib.relErr params.latticeEta
          ((D.latticePoints b).ncard / (10 : Real) ^ (b * n)))
    (hlatticeEstimate :
      let D := O.preprocessing.run F hbounded
      let b := (O.preprocessing.choosePrecision D params).value
      (ttc F hbounded params O).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr (params.epsilon / 2)
              ((D.latticePoints b).ncard / (10 : Real) ^ (b * n))} ≥
        1 - params.delta) :
    let D := O.preprocessing.run F hbounded
    let b := (O.preprocessing.choosePrecision D params).value
    (ttc F hbounded params O).real
        {estimate | (estimate : Real) ∈
          Arlib.relErr params.epsilon
            (MeasureTheory.volume D.union).toReal} ≥
      1 - params.delta := by
  let D := O.preprocessing.run F hbounded
  let b := (O.preprocessing.choosePrecision D params).value
  let q : Real := (D.latticePoints b).ncard / (10 : Real) ^ (b * n)
  let V : Real := (MeasureTheory.volume D.union).toReal
  let μ := ttc F hbounded params O
  have hprob : MeasureTheory.IsProbabilityMeasure μ :=
    ttc_volume_accuracy_probability_measure F hbounded params O hvolume hsamples
  letI := hprob
  change μ.real {estimate | (estimate : Real) ∈ Arlib.relErr params.epsilon V} ≥
    1 - params.delta
  change V ∈ Arlib.relErr params.latticeEta q at hunionLattice
  change μ.real
      {estimate | (estimate : Real) ∈ Arlib.relErr (params.epsilon / 2) q} ≥
    1 - params.delta at hlatticeEstimate
  apply hlatticeEstimate.trans
  refine MeasureTheory.measureReal_mono ?_ (MeasureTheory.measure_ne_top μ _)
  intro estimate hestimate
  rw [show params.latticeEta = params.epsilon / 8 by rfl] at hunionLattice
  change (1 - params.epsilon / 2) * q ≤ (estimate : Real) ∧
    (estimate : Real) ≤ (1 + params.epsilon / 2) * q at hestimate
  change (1 - params.epsilon) * V ≤ (estimate : Real) ∧
    (estimate : Real) ≤ (1 + params.epsilon) * V
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hone_sub : 0 ≤ 1 - params.epsilon := sub_nonneg.mpr params.epsilon_le_one
  have hone_add : 0 ≤ 1 + params.epsilon := by nlinarith [params.epsilon_pos]
  constructor
  · calc
      (1 - params.epsilon) * V ≤
          (1 - params.epsilon) * ((1 + params.epsilon / 8) * q) :=
        mul_le_mul_of_nonneg_left hunionLattice.2 hone_sub
      _ ≤ (1 - params.epsilon / 2) * q := by
        nlinarith [params.epsilon_pos, params.epsilon_le_one]
      _ ≤ (estimate : Real) := hestimate.1
  · calc
      (estimate : Real) ≤ (1 + params.epsilon / 2) * q := hestimate.2
      _ ≤ (1 + params.epsilon) * ((1 - params.epsilon / 8) * q) := by
        nlinarith [params.epsilon_pos, params.epsilon_le_one]
      _ ≤ (1 + params.epsilon) * V :=
        mul_le_mul_of_nonneg_left hunionLattice.1 hone_add

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · repaired · closed the conditional deterministic assembly; restored the oracle
  contracts needed to make `Measure.real` monotone on the containing event
* r1 · reduced · exposed the stochastic lattice estimate as a premise
-/

end Kr25Ssmxt

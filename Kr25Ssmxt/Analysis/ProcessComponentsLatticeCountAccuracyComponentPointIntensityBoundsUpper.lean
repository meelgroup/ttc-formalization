import Kr25Ssmxt.Model.Prelude

/-!
# Upper per-point intensity bound for one component

This module isolates the upper scalar chain in the paper's component-prefix invariant.
It combines the upper sides of the volume-estimation, lattice-comparison, and
almost-uniform point-mass guarantees, including cancellation of the positive component
cardinality.
-/

noncomputable section

namespace Kr25Ssmxt

/-- A relative-error volume estimate, lattice comparison, and point-mass guarantee give
the paper's upper bound for the fresh-copy intensity at a nonnegative sampling rate.

INTERNAL: upper scalar half of
`process_components_lattice_count_accuracy_component_point_intensity_bounds`.
-/
lemma process_components_lattice_count_accuracy_component_point_intensity_bounds_upper
    (volumeEstimate componentVolume pointMass rate scale epsilonPrime latticeEta : Real)
    (cardinality : Nat)
    (hcardinality : 0 < cardinality)
    (hrate : 0 ≤ rate) (hscale : 0 < scale)
    (hepsilonPrime : 0 ≤ epsilonPrime)
    (hepsilonPrime_le_one : epsilonPrime ≤ 1)
    (hlatticeEta : 0 ≤ latticeEta) (hlatticeEta_le_one : latticeEta ≤ 1)
    (hvolumeEstimate : volumeEstimate ∈ Arlib.relErr epsilonPrime componentVolume)
    (hcomponentVolume : componentVolume ∈
      Arlib.relErr latticeEta ((cardinality : Real) / scale))
    (hpointMass : pointMass ∈
      Arlib.relErr epsilonPrime (1 / (cardinality : Real))) :
    volumeEstimate * rate * pointMass ≤
      (1 + epsilonPrime) ^ 2 * (1 + latticeEta) * (rate / scale) := by
  have hC : 0 < (cardinality : Real) := by
    exact_mod_cast hcardinality
  have hC0 : (cardinality : Real) ≠ 0 := ne_of_gt hC
  have hscale0 : scale ≠ 0 := ne_of_gt hscale

  have hvolumeUpper := Arlib.relErr.upper hvolumeEstimate
  have hcomponentUpper := Arlib.relErr.upper hcomponentVolume
  have hpointLower := Arlib.relErr.lower hpointMass
  have hpointUpper := Arlib.relErr.upper hpointMass

  have hepsilonMinus : 0 ≤ 1 - epsilonPrime := by linarith
  have hepsilonPlus : 0 ≤ 1 + epsilonPrime := by linarith
  have hlatticePlus : 0 ≤ 1 + latticeEta := by linarith
  have hcardinalityScale : 0 ≤ (cardinality : Real) / scale :=
    div_nonneg (le_of_lt hC) (le_of_lt hscale)
  have hcardinalityInv : 0 ≤ 1 / (cardinality : Real) :=
    div_nonneg zero_le_one (le_of_lt hC)
  have hpointMassNonneg : 0 ≤ pointMass := by
    exact le_trans (mul_nonneg hepsilonMinus hcardinalityInv) hpointLower

  have hvolumeEstimateUpper :
      volumeEstimate ≤
        (1 + epsilonPrime) *
          ((1 + latticeEta) * ((cardinality : Real) / scale)) := by
    calc
      volumeEstimate ≤ (1 + epsilonPrime) * componentVolume := hvolumeUpper
      _ ≤
          (1 + epsilonPrime) *
            ((1 + latticeEta) * ((cardinality : Real) / scale)) :=
        mul_le_mul_of_nonneg_left hcomponentUpper hepsilonPlus

  have hupperMultiplierNonneg :
      0 ≤
        (1 + epsilonPrime) *
            ((1 + latticeEta) * ((cardinality : Real) / scale)) * rate :=
    mul_nonneg
      (mul_nonneg hepsilonPlus (mul_nonneg hlatticePlus hcardinalityScale)) hrate

  have hupperProduct :
      volumeEstimate * rate * pointMass ≤
        ((1 + epsilonPrime) *
            ((1 + latticeEta) * ((cardinality : Real) / scale))) * rate *
          ((1 + epsilonPrime) * (1 / (cardinality : Real))) := by
    calc
      volumeEstimate * rate * pointMass ≤
          ((1 + epsilonPrime) *
              ((1 + latticeEta) * ((cardinality : Real) / scale))) * rate *
            pointMass := by
        apply mul_le_mul_of_nonneg_right _ hpointMassNonneg
        exact mul_le_mul_of_nonneg_right hvolumeEstimateUpper hrate
      _ ≤
          ((1 + epsilonPrime) *
              ((1 + latticeEta) * ((cardinality : Real) / scale))) * rate *
            ((1 + epsilonPrime) * (1 / (cardinality : Real))) :=
        mul_le_mul_of_nonneg_left hpointUpper hupperMultiplierNonneg

  have hupperIdentity :
      ((1 + epsilonPrime) *
            ((1 + latticeEta) * ((cardinality : Real) / scale))) * rate *
          ((1 + epsilonPrime) * (1 / (cardinality : Real))) =
        (1 + epsilonPrime) ^ 2 * (1 + latticeEta) * (rate / scale) := by
    field_simp [hC0, hscale0]

  rw [← hupperIdentity]
  exact hupperProduct

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · chained the three upper relative-error bounds and cancelled the
  positive component cardinality
-/

end Kr25Ssmxt

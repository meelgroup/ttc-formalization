import Kr25Ssmxt.Model.Pseudocode

/-!
# Lower per-point intensity bound for one component

This module isolates the lower scalar chain in the paper's component-prefix invariant.
It combines the lower sides of the volume-estimation, lattice-comparison, and
almost-uniform point-mass guarantees, including cancellation of the positive component
cardinality.
-/

noncomputable section

namespace Kr25Ssmxt

/-- A relative-error volume estimate, lattice comparison, and point-mass guarantee give
the paper's lower bound for the fresh-copy intensity at a nonnegative sampling rate.

INTERNAL: lower scalar half of
`process_components_lattice_count_accuracy_component_point_intensity_bounds`.
-/
lemma process_components_lattice_count_accuracy_component_point_intensity_bounds_lower
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
    (1 - epsilonPrime) ^ 2 * (1 - latticeEta) * (rate / scale) ≤
      volumeEstimate * rate * pointMass := by
  have hC : 0 < (cardinality : Real) := by
    exact_mod_cast hcardinality
  have hC0 : (cardinality : Real) ≠ 0 := ne_of_gt hC
  have hscale0 : scale ≠ 0 := ne_of_gt hscale

  have hvolumeLower := Arlib.relErr.lower hvolumeEstimate
  have hcomponentLower := Arlib.relErr.lower hcomponentVolume
  have hpointLower := Arlib.relErr.lower hpointMass

  have hepsilonMinus : 0 ≤ 1 - epsilonPrime := by linarith
  have hlatticeMinus : 0 ≤ 1 - latticeEta := by linarith
  have hcardinalityScale : 0 ≤ (cardinality : Real) / scale :=
    div_nonneg (le_of_lt hC) (le_of_lt hscale)
  have hcardinalityInv : 0 ≤ 1 / (cardinality : Real) :=
    div_nonneg zero_le_one (le_of_lt hC)

  have hvolumeEstimateLower :
      (1 - epsilonPrime) *
          ((1 - latticeEta) * ((cardinality : Real) / scale)) ≤ volumeEstimate := by
    calc
      (1 - epsilonPrime) *
          ((1 - latticeEta) * ((cardinality : Real) / scale)) ≤
          (1 - epsilonPrime) * componentVolume :=
        mul_le_mul_of_nonneg_left hcomponentLower hepsilonMinus
      _ ≤ volumeEstimate := hvolumeLower

  have hcomponentVolumeNonneg : 0 ≤ componentVolume := by
    exact le_trans (mul_nonneg hlatticeMinus hcardinalityScale) hcomponentLower
  have hvolumeEstimateNonneg : 0 ≤ volumeEstimate := by
    exact le_trans (mul_nonneg hepsilonMinus hcomponentVolumeNonneg) hvolumeLower
  have hvolumeRateNonneg : 0 ≤ volumeEstimate * rate :=
    mul_nonneg hvolumeEstimateNonneg hrate
  have hpointLowerNonneg :
      0 ≤ (1 - epsilonPrime) * (1 / (cardinality : Real)) :=
    mul_nonneg hepsilonMinus hcardinalityInv

  have hlowerProduct :
      ((1 - epsilonPrime) *
            ((1 - latticeEta) * ((cardinality : Real) / scale))) * rate *
          ((1 - epsilonPrime) * (1 / (cardinality : Real))) ≤
        volumeEstimate * rate * pointMass := by
    calc
      ((1 - epsilonPrime) *
            ((1 - latticeEta) * ((cardinality : Real) / scale))) * rate *
          ((1 - epsilonPrime) * (1 / (cardinality : Real))) ≤
          volumeEstimate * rate *
            ((1 - epsilonPrime) * (1 / (cardinality : Real))) := by
        apply mul_le_mul_of_nonneg_right _ hpointLowerNonneg
        exact mul_le_mul_of_nonneg_right hvolumeEstimateLower hrate
      _ ≤ volumeEstimate * rate * pointMass :=
        mul_le_mul_of_nonneg_left hpointLower hvolumeRateNonneg

  have hlowerIdentity :
      ((1 - epsilonPrime) *
            ((1 - latticeEta) * ((cardinality : Real) / scale))) * rate *
          ((1 - epsilonPrime) * (1 / (cardinality : Real))) =
        (1 - epsilonPrime) ^ 2 * (1 - latticeEta) * (rate / scale) := by
    field_simp [hC0, hscale0]

  rw [← hlowerIdentity]
  exact hlowerProduct

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · chained the three lower relative-error bounds and cancelled the
  positive component cardinality
-/

end Kr25Ssmxt

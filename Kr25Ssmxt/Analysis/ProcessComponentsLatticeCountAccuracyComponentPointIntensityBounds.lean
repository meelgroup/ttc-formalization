import Kr25Ssmxt.Model.Program

/-!
# Per-point intensity bounds for one component

This is the scalar part of the component-prefix invariant.  It combines a relative-error
volume estimate, the lattice comparison, and an almost-uniform point mass.  The mean is
written with the paper's multiplication by the current sampling rate.
-/

noncomputable section

namespace Kr25Ssmxt

/-- With the paper's corrected fresh-copy mean, every point of a nonempty component has
intensity within the product of the volume, lattice, and point-mass error factors.

PAPER: sections/analysis.tex:215-229
-/
lemma process_components_lattice_count_accuracy_component_point_intensity_bounds
    (volumeEstimate componentVolume pointMass rate scale epsilonPrime latticeEta : Real)
    (cardinality : Nat)
    (hcardinality : 0 < cardinality)
    (hrate : 0 ≤ rate) (hscale : 0 < scale)
    (hepsilonPrime : 0 ≤ epsilonPrime) (hepsilonPrime_le_one : epsilonPrime ≤ 1)
    (hlatticeEta : 0 ≤ latticeEta) (hlatticeEta_le_one : latticeEta ≤ 1)
    (hvolumeEstimate : volumeEstimate ∈ Arlib.relErr epsilonPrime componentVolume)
    (hcomponentVolume : componentVolume ∈
      Arlib.relErr latticeEta ((cardinality : Real) / scale))
    (hpointMass : pointMass ∈
      Arlib.relErr epsilonPrime (1 / (cardinality : Real))) :
    (1 - epsilonPrime) ^ 2 * (1 - latticeEta) * (rate / scale) ≤
        volumeEstimate * rate * pointMass ∧
      volumeEstimate * rate * pointMass ≤
        (1 + epsilonPrime) ^ 2 * (1 + latticeEta) * (rate / scale) := by
  have hC : 0 < (cardinality : Real) := by
    exact_mod_cast hcardinality
  have hC0 : (cardinality : Real) ≠ 0 := ne_of_gt hC
  have hscale0 : scale ≠ 0 := ne_of_gt hscale

  have hvolumeLower := Arlib.relErr.lower hvolumeEstimate
  have hvolumeUpper := Arlib.relErr.upper hvolumeEstimate
  have hcomponentLower := Arlib.relErr.lower hcomponentVolume
  have hcomponentUpper := Arlib.relErr.upper hcomponentVolume
  have hpointLower := Arlib.relErr.lower hpointMass
  have hpointUpper := Arlib.relErr.upper hpointMass

  have hepsilonMinus : 0 ≤ 1 - epsilonPrime := by linarith
  have hepsilonPlus : 0 ≤ 1 + epsilonPrime := by linarith
  have hlatticeMinus : 0 ≤ 1 - latticeEta := by linarith
  have hlatticePlus : 0 ≤ 1 + latticeEta := by linarith
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

  have hcomponentVolumeNonneg : 0 ≤ componentVolume := by
    exact le_trans (mul_nonneg hlatticeMinus hcardinalityScale) hcomponentLower
  have hvolumeEstimateNonneg : 0 ≤ volumeEstimate := by
    exact le_trans (mul_nonneg hepsilonMinus hcomponentVolumeNonneg) hvolumeLower
  have hvolumeRateNonneg : 0 ≤ volumeEstimate * rate :=
    mul_nonneg hvolumeEstimateNonneg hrate
  have hpointLowerNonneg :
      0 ≤ (1 - epsilonPrime) * (1 / (cardinality : Real)) :=
    mul_nonneg hepsilonMinus hcardinalityInv
  have hpointUpperNonneg :
      0 ≤ (1 + epsilonPrime) * (1 / (cardinality : Real)) :=
    mul_nonneg hepsilonPlus hcardinalityInv

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
  have hupperProduct :
      volumeEstimate * rate * pointMass ≤
        ((1 + epsilonPrime) *
            ((1 + latticeEta) * ((cardinality : Real) / scale))) * rate *
          ((1 + epsilonPrime) * (1 / (cardinality : Real))) := by
    calc
      volumeEstimate * rate * pointMass ≤
          volumeEstimate * rate *
            ((1 + epsilonPrime) * (1 / (cardinality : Real))) :=
        mul_le_mul_of_nonneg_left hpointUpper hvolumeRateNonneg
      _ ≤
          ((1 + epsilonPrime) *
              ((1 + latticeEta) * ((cardinality : Real) / scale))) * rate *
            ((1 + epsilonPrime) * (1 / (cardinality : Real))) := by
        apply mul_le_mul_of_nonneg_right _ hpointUpperNonneg
        exact mul_le_mul_of_nonneg_right hvolumeEstimateUpper hrate

  have hlowerIdentity :
      ((1 - epsilonPrime) *
            ((1 - latticeEta) * ((cardinality : Real) / scale))) * rate *
          ((1 - epsilonPrime) * (1 / (cardinality : Real))) =
        (1 - epsilonPrime) ^ 2 * (1 - latticeEta) * (rate / scale) := by
    field_simp [hC0, hscale0]
  have hupperIdentity :
      ((1 + epsilonPrime) *
            ((1 + latticeEta) * ((cardinality : Real) / scale))) * rate *
          ((1 + epsilonPrime) * (1 / (cardinality : Real))) =
        (1 + epsilonPrime) ^ 2 * (1 + latticeEta) * (rate / scale) := by
    field_simp [hC0, hscale0]

  constructor
  · rw [← hlowerIdentity]
    exact hlowerProduct
  · rw [← hupperIdentity]
    exact hupperProduct

end Kr25Ssmxt

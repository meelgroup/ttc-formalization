import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.ProcessComponentsLatticeCountAccuracyComponentPointIntensityBounds
import Kr25Ssmxt.Analysis.ThinningCosts

/-! The scaled paper intensity gives a nearly constant Poisson mean per
lattice point. This is the numerical input to the prefix invariant. -/

namespace Kr25Ssmxt

theorem ApproxParams.upper_intensity_factor (p : ApproxParams) :
    (1 + p.ε') ^ 2 * (1 + p.latticeEta) ≤ (4 / 3 : Real) := by
  have he : 1 + p.ε' ≤ (13 / 12 : Real) := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have heta : 1 + p.latticeEta ≤ (9 / 8 : Real) := by
    dsimp [ApproxParams.latticeEta]
    linarith [p.epsilon_le_one]
  calc
    (1 + p.ε') ^ 2 * (1 + p.latticeEta) ≤
        (13 / 12 : Real) ^ 2 * (9 / 8 : Real) := by
          gcongr
          all_goals dsimp [ApproxParams.ε', ApproxParams.latticeEta]
          all_goals linarith [p.epsilon_pos]
    _ ≤ (4 / 3 : Real) := by norm_num

theorem point_intensity_bounds
    (n b : Nat) (threshold : Real) (hthreshold : 0 ≤ threshold)
    (volumeEstimate : NNReal) (componentVolume pointMass : Real)
    (rate : NNReal) (cardinality : Nat) (hcardinality : 0 < cardinality)
    (ε' latticeEta : Real)
    (hepsilonPrime : 0 ≤ ε') (hepsilonPrime_le_one : ε' ≤ 1)
    (hlatticeEta : 0 ≤ latticeEta) (hlatticeEta_le_one : latticeEta ≤ 1)
    (hvolumeEstimate : (volumeEstimate : Real) ∈
      Arlib.relErr ε' componentVolume)
    (hcomponentVolume : componentVolume ∈
      Arlib.relErr latticeEta
        ((cardinality : Real) / (10 : Real) ^ (b * n)))
    (hpointMass : pointMass ∈
      Arlib.relErr ε' (1 / (cardinality : Real))) :
    threshold * (1 - ε') ^ 2 * (1 - latticeEta) * (rate : Real) ≤
      (ttcReference.t b n threshold volumeEstimate : Real) * rate * pointMass ∧
    (ttcReference.t b n threshold volumeEstimate : Real) * rate * pointMass ≤
      threshold * (1 + ε') ^ 2 * (1 + latticeEta) * (rate : Real) := by
  let scale : Real := (10 : Real) ^ (b * n)
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hbase := process_components_lattice_count_accuracy_component_point_intensity_bounds
    (volumeEstimate : Real) componentVolume pointMass (rate : Real) scale
    ε' latticeEta cardinality hcardinality
    rate.coe_nonneg hscale hepsilonPrime hepsilonPrime_le_one
    hlatticeEta hlatticeEta_le_one hvolumeEstimate hcomponentVolume hpointMass
  have hintensity : (ttcReference.t b n threshold volumeEstimate : Real) =
      threshold * scale * volumeEstimate := by
    simp [ttcReference.t, scale, Real.coe_toNNReal threshold hthreshold]
  have hfactor : 0 ≤ threshold * scale := mul_nonneg hthreshold hscale.le
  constructor
  · have h := mul_le_mul_of_nonneg_left hbase.1 hfactor
    rw [hintensity]
    calc
      threshold * (1 - ε') ^ 2 * (1 - latticeEta) * (rate : Real) =
          (threshold * scale) *
            ((1 - ε') ^ 2 * (1 - latticeEta) *
              ((rate : Real) / scale)) := by
            field_simp
      _ ≤ (threshold * scale) *
          ((volumeEstimate : Real) * rate * pointMass) := h
      _ = (threshold * scale * volumeEstimate) * rate * pointMass := by ring
  · have h := mul_le_mul_of_nonneg_left hbase.2 hfactor
    rw [hintensity]
    calc
      (threshold * scale * volumeEstimate) * rate * pointMass =
          (threshold * scale) *
            ((volumeEstimate : Real) * rate * pointMass) := by ring
      _ ≤ (threshold * scale) *
          ((1 + ε') ^ 2 * (1 + latticeEta) *
            ((rate : Real) / scale)) := h
      _ = threshold * (1 + ε') ^ 2 * (1 + latticeEta) *
          (rate : Real) := by
            field_simp

/-- A successful volume estimate cannot push the first while-loop
past the dyadic cutoff determined by the union's lattice count. -/
theorem intensity_le_four_thirds
    (n b : Nat) (p : ApproxParams) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (volumeEstimate : NNReal) (trueVolume : Real)
    (componentCount totalCount : Nat) (hcount : componentCount ≤ totalCount)
    (hestimate : (volumeEstimate : Real) ∈
      Arlib.relErr p.ε' trueVolume)
    (hlattice : trueVolume ∈ Arlib.relErr p.latticeEta
      ((componentCount : Real) / (10 : Real) ^ (b * n))) :
    (ttcReference.t b n threshold volumeEstimate : Real) ≤
      (4 / 3) * threshold * totalCount := by
  let scale : Real := (10 : Real) ^ (b * n)
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have heps : 0 ≤ 1 + p.ε' := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_pos]
  have hfactor : (1 + p.ε') * (1 + p.latticeEta) ≤
      (4 / 3 : Real) := by
    have hepssq : p.epsilon ^ 2 ≤ p.epsilon := by
      nlinarith [mul_nonneg p.epsilon_pos.le
        (sub_nonneg.mpr p.epsilon_le_one)]
    dsimp [ApproxParams.ε', ApproxParams.latticeEta]
    nlinarith [p.epsilon_pos, p.epsilon_le_one]
  have hscaled : scale * volumeEstimate ≤
      (1 + p.ε') * (1 + p.latticeEta) * componentCount := by
    calc
      scale * volumeEstimate ≤ scale * ((1 + p.ε') * trueVolume) :=
        mul_le_mul_of_nonneg_left hestimate.2 hscale.le
      _ ≤ scale * ((1 + p.ε') *
          ((1 + p.latticeEta) * (componentCount / scale))) := by
        apply mul_le_mul_of_nonneg_left _ hscale.le
        exact mul_le_mul_of_nonneg_left hlattice.2 heps
      _ = (1 + p.ε') * (1 + p.latticeEta) * componentCount := by
        field_simp
  have hcountR : (componentCount : Real) ≤ totalCount := by exact_mod_cast hcount
  have hnonneg : 0 ≤ (componentCount : Real) := Nat.cast_nonneg _
  have hintensity : (ttcReference.t b n threshold volumeEstimate : Real) =
      threshold * scale * volumeEstimate := by
    simp [ttcReference.t, scale, Real.coe_toNNReal threshold hthreshold]
  rw [hintensity]
  calc
    threshold * scale * volumeEstimate = threshold * (scale * volumeEstimate) := by ring
    _ ≤ threshold * ((1 + p.ε') * (1 + p.latticeEta) *
        componentCount) := mul_le_mul_of_nonneg_left hscaled hthreshold
    _ ≤ threshold * ((4 / 3 : Real) * componentCount) := by
      gcongr
    _ ≤ threshold * ((4 / 3 : Real) * totalCount) := by
      gcongr
    _ = (4 / 3 : Real) * threshold * totalCount := by ring

end Kr25Ssmxt

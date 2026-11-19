import ttc.Analysis.OracleContracts
import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.CodedUnion
import ttc.Analysis.ComponentStep
import ttc.Analysis.TtcVolumeAccuracyLatticeComparison

/-! The fixed-level rate envelope for a real component of the certified
decomposition, using a successful CV18 estimate and the sampler's pointwise
almost-uniform law. -/

namespace ttc

open Classical MeasureTheory

theorem concrete_component_step_envelope
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount)
    (pointLaw : Measure (LatticePoint n))
    (halmost : AlmostUniformPointwise pointLaw
      (codedLatticePoints (D.component i) b) p.ε')
    (volumeEstimate : NNReal)
    (hvolume : (volumeEstimate : Real) ∈
      Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (rate : NNReal) :
    let S := (D.codedUnion_finite hn p b hprecision).toFinset
    let T : Finset S := Finset.univ.filter
      (fun x : S => x.1.toPoint ∈ (D.component i).carrier)
    (componentFixedLevelStep S T pointLaw b
      (p.Thresh D.componentCount) volumeEstimate rate).RateEnvelope
        (Real.toNNReal (p.Thresh D.componentCount *
          (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate))
        (Real.toNNReal (p.Thresh D.componentCount *
          (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)) := by
  let S := (D.codedUnion_finite hn p b hprecision).toFinset
  let T : Finset S := Finset.univ.filter
    (fun x : S => x.1.toPoint ∈ (D.component i).carrier)
  have hT : ∀ x : S, x ∈ T ↔
      x.1 ∈ codedLatticePoints (D.component i) b := by
    intro x
    have hx : x.1 ∈ D.codedUnionLatticePoints b := by
      simpa only [S, Set.Finite.mem_toFinset] using x.2
    have hb : x.1.1 = b := hx.1
    simp [T, codedLatticePoints, hb]
  have hlattice : (volume (D.component i).carrier).toReal ∈
      Arlib.relErr p.latticeEta
        (((codedLatticePoints (D.component i) b).ncard : Real) /
          (10 : Real) ^ (b * n)) := by
    rw [process_components_lattice_count_accuracy_coded_card]
    exact (ttc_volume_accuracy_lattice_comparison hn D p b hprecision).1 i
  have heps0 : 0 ≤ p.ε' :=
    (div_pos p.epsilon_pos (by norm_num)).le
  have heps1 : p.ε' ≤ 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have heta0 : 0 ≤ p.latticeEta :=
    (div_pos p.epsilon_pos (by norm_num)).le
  have heta1 : p.latticeEta ≤ 1 := by
    dsimp [ApproxParams.latticeEta]
    linarith [p.epsilon_le_one]
  exact componentFixedLevelStep_envelope_of_almostUniform
    S T pointLaw (codedLatticePoints (D.component i) b)
    b (p.Thresh D.componentCount) (p.threshold_pos D.componentCount).le
    volumeEstimate rate (volume (D.component i).carrier).toReal
    p.ε' p.latticeEta heps0 heps1 heta0 heta1
    hvolume hlattice halmost hT

/-- Instantiate the component envelope with the normalized finite-step
Hit-and-Run/KV97 point law used by `ttcRef`. -/
theorem normalized_component_step_envelope
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount)
    (hunit : samplerRadiusRequirement (D.component i) p.ε' ≤ decimalScale b * (D.component i).inradius)
    (hfinite : (codedLatticePoints (D.component i) b).Finite)
    (hnonempty : (codedLatticePoints (D.component i) b).Nonempty)
    (volumeEstimate : NNReal)
    (hvolume : (volumeEstimate : Real) ∈
      Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (rate : NNReal) :
    let pointLaw := normalizedHitAndRunPointLaw hn (D.component i) b p.ε'
      hunit
      (div_pos p.epsilon_pos (by norm_num))
      (by dsimp [ApproxParams.ε']; linarith [p.epsilon_le_one])
      hfinite hnonempty
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let T : Finset S := Finset.univ.filter
      (fun x : S => x.1.toPoint ∈ (D.component i).carrier)
    (componentFixedLevelStep S T pointLaw b
      (p.Thresh D.componentCount) volumeEstimate rate).RateEnvelope
        (Real.toNNReal (p.Thresh D.componentCount *
          (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate))
        (Real.toNNReal (p.Thresh D.componentCount *
          (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)) := by
  have heta0 : 0 < p.ε' :=
    div_pos p.epsilon_pos (by norm_num)
  have heta1 : p.ε' ≤ 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  let pointLaw := normalizedHitAndRunPointLaw hn (D.component i) b p.ε'
    hunit heta0 heta1 hfinite hnonempty
  have halmost : AlmostUniformPointwise pointLaw
      (codedLatticePoints (D.component i) b) p.ε' :=
    (D.component i).normalizedHitAndRun_latticePointLaw hn b hunit
      heta0 heta1 hfinite hnonempty
  exact concrete_component_step_envelope
    (lt_of_lt_of_le (by norm_num) hn) D p b hprecision i
    pointLaw halmost volumeEstimate hvolume rate

/-- The concrete paper sampler's certified branch is exactly an IID
batch from the normalized Hit-and-Run/KV97 point law. -/
theorem community_generateSamples_eq_iid
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty) :
    (ttcSubroutines hn prep).GenerateSamples
      P count b eta =
    iidSampleBatchLaw (normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2) := by
  simp only [ttcSubroutines, dif_pos hroute]

end ttc

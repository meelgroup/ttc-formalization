import Kr25Ssmxt.Analysis.ManuscriptCodedUnion
import Kr25Ssmxt.Analysis.ManuscriptComponentStep
import Kr25Ssmxt.Analysis.TtcVolumeAccuracyLatticeComparison

/-! The fixed-level rate envelope for a real component of the certified
decomposition, using a successful CV18 estimate and the sampler's pointwise
almost-uniform law. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

theorem manuscript_concrete_component_step_envelope
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (i : Fin D.componentCount)
    (pointLaw : Measure (LatticePoint n))
    (halmost : AlmostUniformPointwise pointLaw
      (codedLatticePoints (D.component i) b) p.epsilonPrime)
    (volumeEstimate : NNReal)
    (hvolume : (volumeEstimate : Real) ∈
      Arlib.relErr p.epsilonPrime
        (volume (D.component i).carrier).toReal)
    (rate : NNReal) :
    let S := (D.codedUnion_finite hn p b hprecision).toFinset
    let T : Finset S := Finset.univ.filter
      (fun x : S => x.1.toPoint ∈ (D.component i).carrier)
    (manuscriptComponentFixedLevelStep S T pointLaw b
      (p.threshold D.componentCount) volumeEstimate rate).RateEnvelope
        (Real.toNNReal (p.threshold D.componentCount *
          (1 - p.epsilonPrime) ^ 2 * (1 - p.latticeEta) * rate))
        (Real.toNNReal (p.threshold D.componentCount *
          (1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta) * rate)) := by
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
  have heps0 : 0 ≤ p.epsilonPrime :=
    (div_pos p.epsilon_pos (by norm_num)).le
  have heps1 : p.epsilonPrime ≤ 1 := by
    dsimp [ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  have heta0 : 0 ≤ p.latticeEta :=
    (div_pos p.epsilon_pos (by norm_num)).le
  have heta1 : p.latticeEta ≤ 1 := by
    dsimp [ApproxParams.latticeEta]
    linarith [p.epsilon_le_one]
  exact manuscriptComponentFixedLevelStep_envelope_of_almostUniform
    S T pointLaw (codedLatticePoints (D.component i) b)
    b (p.threshold D.componentCount) (p.threshold_pos D.componentCount).le
    volumeEstimate rate (volume (D.component i).carrier).toReal
    p.epsilonPrime p.latticeEta heps0 heps1 heta0 heta1
    hvolume hlattice halmost hT

/-- Instantiate the component envelope with the normalized finite-step
Hit-and-Run/KV97 point law used by `communityManuscriptTTC`. -/
theorem manuscript_normalized_component_step_envelope
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (i : Fin D.componentCount)
    (hunit : 1 ≤ decimalScale b * (D.component i).inradius)
    (hfinite : (codedLatticePoints (D.component i) b).Finite)
    (hnonempty : (codedLatticePoints (D.component i) b).Nonempty)
    (volumeEstimate : NNReal)
    (hvolume : (volumeEstimate : Real) ∈
      Arlib.relErr p.epsilonPrime
        (volume (D.component i).carrier).toReal)
    (rate : NNReal) :
    let pointLaw := normalizedHitAndRunPointLaw hn (D.component i) b hunit
      p.epsilonPrime
      (div_pos p.epsilon_pos (by norm_num))
      (by dsimp [ApproxParams.epsilonPrime]; linarith [p.epsilon_le_one])
      hfinite hnonempty
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let T : Finset S := Finset.univ.filter
      (fun x : S => x.1.toPoint ∈ (D.component i).carrier)
    (manuscriptComponentFixedLevelStep S T pointLaw b
      (p.threshold D.componentCount) volumeEstimate rate).RateEnvelope
        (Real.toNNReal (p.threshold D.componentCount *
          (1 - p.epsilonPrime) ^ 2 * (1 - p.latticeEta) * rate))
        (Real.toNNReal (p.threshold D.componentCount *
          (1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta) * rate)) := by
  have heta0 : 0 < p.epsilonPrime :=
    div_pos p.epsilon_pos (by norm_num)
  have heta1 : p.epsilonPrime ≤ 1 := by
    dsimp [ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  let pointLaw := normalizedHitAndRunPointLaw hn (D.component i) b hunit
    p.epsilonPrime heta0 heta1 hfinite hnonempty
  have halmost : AlmostUniformPointwise pointLaw
      (codedLatticePoints (D.component i) b) p.epsilonPrime :=
    (D.component i).normalizedHitAndRun_latticePointLaw hn b hunit
      heta0 heta1 hfinite hnonempty
  exact manuscript_concrete_component_step_envelope
    (lt_of_lt_of_le (by norm_num) hn) D p b hprecision i
    pointLaw halmost volumeEstimate hvolume rate

/-- The concrete manuscript sampler's certified branch is exactly an IID
batch from the normalized Hit-and-Run/KV97 point law. -/
theorem communityManuscript_generateSamples_eq_iid
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty) :
    (communityManuscriptOracles hn prep).generateSamples
      P count b eta delta =
    iidSampleBatchLaw (normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2) := by
  simp only [communityManuscriptOracles, dif_pos hroute]

end Kr25Ssmxt

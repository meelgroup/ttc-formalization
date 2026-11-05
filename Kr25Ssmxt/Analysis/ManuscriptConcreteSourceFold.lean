import Kr25Ssmxt.Analysis.ManuscriptFixedLevelProductFold

/-! A single product of the concrete component Poisson tapes yields every
certified fixed-level delete-and-append prefix law. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

theorem manuscriptCertifiedFixedLevelSteps_length
    {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) (S : Finset (LatticePoint n))
    (threshold : Real) (volumeEstimate : Fin D.componentCount → NNReal)
    (pointLaw : Fin D.componentCount → Measure (LatticePoint n))
    (rate : NNReal) :
    (manuscriptCertifiedFixedLevelSteps D b S threshold volumeEstimate
      pointLaw rate).length = D.componentCount := by
  simp [manuscriptCertifiedFixedLevelSteps, fixedLevelComponentSteps]

theorem communityManuscript_source_fixedLevel_fold
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (level : Nat) :
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let pointLaw := communityManuscriptPointLaw hn D p b hprecision
    let steps := manuscriptCertifiedFixedLevelSteps D b S
      (p.threshold D.componentCount) volumeEstimate pointLaw
        (1 / (2 : NNReal) ^ level)
    let sourceLaw : Fin D.componentCount → Measure (ManuscriptPoissonTape n) :=
      fun i => manuscriptPoissonTapeLaw
        (manuscriptIntensity b n (p.threshold D.componentCount)
          (volumeEstimate i)) (pointLaw i)
    (Measure.pi sourceLaw).map
      (fun sources => fixedLevelFold steps (fun _ => 0)
        (fun i => manuscriptPoissonTapePointCounts S 0 level
          (sources (Fin.cast (by
            exact manuscriptCertifiedFixedLevelSteps_length D b S
              (p.threshold D.componentCount) volumeEstimate pointLaw
                (1 / (2 : NNReal) ^ level)) i)))) =
      fixedLevelLaw steps
        (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0)) := by
  classical
  dsimp only
  let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
  let pointLaw := communityManuscriptPointLaw hn D p b hprecision
  let steps := manuscriptCertifiedFixedLevelSteps D b S
    (p.threshold D.componentCount) volumeEstimate pointLaw
      (1 / (2 : NNReal) ^ level)
  let sourceLaw : Fin D.componentCount → Measure (ManuscriptPoissonTape n) :=
    fun i => manuscriptPoissonTapeLaw
      (manuscriptIntensity b n (p.threshold D.componentCount)
        (volumeEstimate i)) (pointLaw i)
  have hlength : steps.length = D.componentCount := by
    simp [steps, manuscriptCertifiedFixedLevelSteps, fixedLevelComponentSteps]
  let e : Fin D.componentCount ≃ Fin steps.length := finCongr hlength.symm
  let sourceLaw' : Fin steps.length → Measure (ManuscriptPoissonTape n) :=
    fun i => sourceLaw (e.symm i)
  have hprob (i : Fin D.componentCount) : IsProbabilityMeasure (pointLaw i) := by
    exact (communityManuscriptPointLaw_almostUniform
      hn D p b hprecision i).1
  have hsourceProb (i : Fin D.componentCount) :
      IsProbabilityMeasure (sourceLaw i) := by
    exact manuscriptPoissonTapeLaw_isProbabilityMeasure _ (pointLaw i)
  letI : ∀ i : Fin steps.length, SigmaFinite (sourceLaw' i) :=
    fun i => by letI := hsourceProb (e.symm i); infer_instance
  have hreindex : (Measure.pi sourceLaw).map
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin steps.length => ManuscriptPoissonTape n) e) =
      Measure.pi sourceLaw' := by
    have h := Measure.pi_map_piCongrLeft e
      (fun i : Fin steps.length => sourceLaw' i)
    simpa [sourceLaw', e] using h
  have hdraw (i : Fin steps.length) :
      (sourceLaw' i).map (manuscriptPoissonTapePointCounts S 0 level) =
      fixedLevelIncomingLaw (steps.get i) := by
    have hsupport := communityManuscriptPointLaw_support_codedUnion
      hn D p b hprecision (e.symm i)
    letI : IsProbabilityMeasure (pointLaw (e.symm i)) := hprob (e.symm i)
    have h := manuscriptPoissonTapeLaw_fixedLevel_pointCounts
      (manuscriptIntensity b n (p.threshold D.componentCount)
        (volumeEstimate (e.symm i)))
      (pointLaw (e.symm i)) S hsupport 0 level
    change (sourceLaw (e.symm i)).map
      (manuscriptPoissonTapePointCounts S 0 level) = _
    rw [h]
    unfold fixedLevelIncomingLaw
    congr 1
    funext x
    congr 1
    have hget := List.get_ofFn
      (fun j : Fin D.componentCount =>
        ({ deleted := componentDeletedCodes S (D.component j)
           incoming := fun y : S => Real.toNNReal
             ((pointLaw j).real {(y.1 : LatticePoint n)} *
               ((manuscriptIntensity b n (p.threshold D.componentCount)
                 (volumeEstimate j) *
                 (1 / (2 : NNReal) ^ level) : NNReal) : Real)) } :
          FixedLevelStep S)) i
    change _ = ((List.ofFn fun j : Fin D.componentCount =>
        ({ deleted := componentDeletedCodes S (D.component j)
           incoming := fun y : S => Real.toNNReal
             ((pointLaw j).real {(y.1 : LatticePoint n)} *
               ((manuscriptIntensity b n (p.threshold D.componentCount)
                 (volumeEstimate j) *
                 (1 / (2 : NNReal) ^ level) : NNReal) : Real)) } :
          FixedLevelStep S)).get i).incoming x
    rw [hget]
    change Real.toNNReal
        ((pointLaw (e.symm i)).real {(x.1 : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            manuscriptIntensity b n (p.threshold D.componentCount)
              (volumeEstimate (e.symm i)) : NNReal) : Real)) =
      Real.toNNReal
        ((pointLaw (Fin.cast hlength i)).real {(x.1 : LatticePoint n)} *
          ((manuscriptIntensity b n (p.threshold D.componentCount)
              (volumeEstimate (Fin.cast hlength i)) *
              (1 / (2 : NNReal) ^ level) : NNReal) : Real))
    have hindex : e.symm i = Fin.cast hlength i := Fin.ext rfl
    rw [hindex, survivalProbability_toNNReal]
    rw [show (1 / 2 : NNReal) ^ level =
      1 / (2 : NNReal) ^ level by simp [one_div, inv_pow]]
    rw [mul_comm (1 / (2 : NNReal) ^ level)]
  have hfold := fixedLevelFold_source_pi_eq_fixedLevelLaw steps
    (fun _ : S => 0) sourceLaw'
    (fun _ => manuscriptPoissonTapePointCounts S 0 level)
    (fun _ => measurable_manuscriptPoissonTapePointCounts S 0 level)
    hdraw
  rw [pointCountVector_pi_poisson_zero_eq_dirac S]
  have hpath (sources : Fin D.componentCount → ManuscriptPoissonTape n) :
      fixedLevelFold steps (fun _ : S => 0)
        (fun i => manuscriptPoissonTapePointCounts S 0 level
          (sources (Fin.cast hlength i))) =
      fixedLevelFold steps (fun _ : S => 0)
        (fun i => manuscriptPoissonTapePointCounts S 0 level
          ((MeasurableEquiv.piCongrLeft
            (fun _ : Fin steps.length => ManuscriptPoissonTape n) e sources) i)) := by
    funext i
    congr 1
  change (Measure.pi sourceLaw).map
    (fun sources => fixedLevelFold steps (fun _ : S => 0)
      (fun i => manuscriptPoissonTapePointCounts S 0 level
        (sources (Fin.cast hlength i)))) = _
  have hfunctions :
      (fun sources : Fin D.componentCount → ManuscriptPoissonTape n =>
        fixedLevelFold steps (fun _ : S => 0)
          (fun i => manuscriptPoissonTapePointCounts S 0 level
            (sources (Fin.cast hlength i)))) =
      (fun sources => fixedLevelFold steps (fun _ : S => 0)
          (fun i => manuscriptPoissonTapePointCounts S 0 level
            ((MeasurableEquiv.piCongrLeft
              (fun _ : Fin steps.length => ManuscriptPoissonTape n) e sources) i))) :=
    funext hpath
  rw [hfunctions]
  let f : (Fin steps.length → ManuscriptPoissonTape n) → (S → Nat) :=
    fun sources => fixedLevelFold steps (fun _ => 0)
      (fun i => manuscriptPoissonTapePointCounts S 0 level (sources i))
  have hf : Measurable f :=
    (measurable_fixedLevelFold steps (fun _ : S => 0)).comp
      (Measurable.of_eval (fun i =>
        (measurable_manuscriptPoissonTapePointCounts S 0 level).comp
          (measurable_pi_apply i)))
  change (Measure.pi sourceLaw).map
    (f ∘ (MeasurableEquiv.piCongrLeft
      (fun _ : Fin steps.length => ManuscriptPoissonTape n) e)) = _
  rw [← Measure.map_map hf
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin steps.length => ManuscriptPoissonTape n) e).measurable]
  rw [hreindex]
  exact hfold

/-- At any fixed level, the total stored count derived from the shared
component source has exactly the concrete certified prefix count law. -/
theorem communityManuscript_source_fixedLevel_total_law
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (level : Nat) :
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let pointLaw := communityManuscriptPointLaw hn D p b hprecision
    let steps := manuscriptCertifiedFixedLevelSteps D b S
      (p.threshold D.componentCount) volumeEstimate pointLaw
        (1 / (2 : NNReal) ^ level)
    let sourceLaw : Fin D.componentCount → Measure (ManuscriptPoissonTape n) :=
      fun i => manuscriptPoissonTapeLaw
        (manuscriptIntensity b n (p.threshold D.componentCount)
          (volumeEstimate i)) (pointLaw i)
    (Measure.pi sourceLaw).map
      (fun sources => ∑ x : S, fixedLevelFold steps (fun _ => 0)
        (fun i => manuscriptPoissonTapePointCounts S 0 level
          (sources (Fin.cast (by
            exact manuscriptCertifiedFixedLevelSteps_length D b S
              (p.threshold D.componentCount) volumeEstimate pointLaw
                (1 / (2 : NNReal) ^ level)) i))) x) =
      (fixedLevelLaw steps
        (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))).map
          (fun counts : S → Nat => ∑ x, counts x) := by
  classical
  let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
  let pointLaw := communityManuscriptPointLaw hn D p b hprecision
  let steps := manuscriptCertifiedFixedLevelSteps D b S
    (p.threshold D.componentCount) volumeEstimate pointLaw
      (1 / (2 : NNReal) ^ level)
  let sourceLaw : Fin D.componentCount → Measure (ManuscriptPoissonTape n) :=
    fun i => manuscriptPoissonTapeLaw
      (manuscriptIntensity b n (p.threshold D.componentCount)
        (volumeEstimate i)) (pointLaw i)
  let hlength := manuscriptCertifiedFixedLevelSteps_length D b S
    (p.threshold D.componentCount) volumeEstimate pointLaw
      (1 / (2 : NNReal) ^ level)
  let counts : (Fin D.componentCount → ManuscriptPoissonTape n) → (S → Nat) :=
    fun sources => fixedLevelFold steps (fun _ => 0)
      (fun i => manuscriptPoissonTapePointCounts S 0 level
        (sources (Fin.cast hlength i)))
  have hcounts : Measurable counts :=
    (measurable_fixedLevelFold steps (fun _ : S => 0)).comp
      (Measurable.of_eval (fun i =>
        (measurable_manuscriptPoissonTapePointCounts S 0 level).comp
          (measurable_pi_apply (Fin.cast hlength i))))
  have hsum : Measurable (fun v : S → Nat => ∑ x, v x) :=
    Measurable.of_discrete
  change (Measure.pi sourceLaw).map
    ((fun v : S → Nat => ∑ x, v x) ∘ counts) = _
  rw [← Measure.map_map hsum hcounts]
  rw [communityManuscript_source_fixedLevel_fold hn D p b hprecision
    volumeEstimate level]

/-- The manuscript's dyadic Chernoff estimate now holds for the same source
space at every level, ready for a finite stopped-level union bound. -/
theorem communityManuscript_source_fixedLevel_error_bound
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (hcomponents : 0 < D.componentCount)
    (outcomes : Fin D.componentCount → VolumeOutcome)
    (hgood : ∀ i, (outcomes i).1 = true ∧
      ((outcomes i).2 : Real) ∈ Arlib.relErr p.epsilonPrime
        (volume (D.component i).carrier).toReal)
    (level : Nat)
    (hlevel : level ≤ manuscriptDyadicCutoff (D.latticePoints b).ncard - 1) :
    let S := (D.codedUnion_finite (by omega) p b hprecision).toFinset
    let pointLaw := communityManuscriptPointLaw hn D p b hprecision
    let volumeEstimate := fun i : Fin D.componentCount => (outcomes i).2
    let steps := manuscriptCertifiedFixedLevelSteps D b S
      (p.threshold D.componentCount) volumeEstimate pointLaw
        (1 / (2 : NNReal) ^ level)
    let sourceLaw : Fin D.componentCount → Measure (ManuscriptPoissonTape n) :=
      fun i => manuscriptPoissonTapeLaw
        (manuscriptIntensity b n (p.threshold D.componentCount)
          (volumeEstimate i)) (pointLaw i)
    let lower := Real.toNNReal (p.threshold D.componentCount *
      (1 - p.epsilonPrime) ^ 2 * (1 - p.latticeEta) *
      (1 / (2 : NNReal) ^ level))
    let upper := Real.toNNReal (p.threshold D.componentCount *
      (1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta) *
      (1 / (2 : NNReal) ^ level))
    let a := (1 - p.epsilonPrime) * p.epsilonPrime ^ 2 *
      p.threshold D.componentCount / 24
    ((Measure.pi sourceLaw).map
      (fun sources => ∑ x : S, fixedLevelFold steps (fun _ => 0)
        (fun i => manuscriptPoissonTapePointCounts S 0 level
          (sources (Fin.cast (by
            exact manuscriptCertifiedFixedLevelSteps_length D b S
              (p.threshold D.componentCount) volumeEstimate pointLaw
                (1 / (2 : NNReal) ^ level)) i))) x)).real
      {count : Nat |
        (count : Real) < (1 - p.epsilonPrime) *
          ((D.latticePoints b).ncard : Real) * lower ∨
        (1 + p.epsilonPrime) *
          ((D.latticePoints b).ncard : Real) * upper < count} ≤
      2 * Real.exp (-a * (2 : Real) ^
        (manuscriptDyadicCutoff (D.latticePoints b).ncard - 1 - level)) := by
  dsimp only
  rw [communityManuscript_source_fixedLevel_total_law hn D p b hprecision
    (fun i => (outcomes i).2) level]
  exact communityManuscriptFixedLevel_error_bound hn D p b hprecision
    hcomponents outcomes hgood level hlevel

end Kr25Ssmxt

import ttc.Analysis.OracleContracts
import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.FixedLevelCoverage
import ttc.Analysis.FixedLevelConcentration
import ttc.Analysis.DyadicMean
import ttc.Analysis.FixedLevelCutoff

/-! A fixed-level prefix process built from the actual component geometry,
successful component volume outcomes, and pointwise sampler laws. -/

namespace ttc

open Classical MeasureTheory

noncomputable def certifiedFixedLevelSteps
    {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat)
    (S : Finset (LatticePoint n))
    (threshold : Real)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (pointLaw : Fin D.componentCount → Measure (LatticePoint n))
    (rate : NNReal) : List (FixedLevelStep S) :=
  fixedLevelComponentSteps D S (fun i x => Real.toNNReal
    ((pointLaw i).real {(x.1 : LatticePoint n)} *
      ((ttcReference.t b n threshold (volumeEstimate i) * rate : NNReal) : Real)))

theorem certifiedFixedLevelSteps_coverage
    {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat)
    (hfinite : (D.codedUnionLatticePoints b).Finite)
    (threshold : Real)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (pointLaw : Fin D.componentCount → Measure (LatticePoint n))
    (rate : NNReal) :
    fixedLevelCoverage
      (certifiedFixedLevelSteps D b hfinite.toFinset
        threshold volumeEstimate pointLaw rate) ∅ = Finset.univ := by
  exact fixedLevelComponentSteps_coverage_univ D b hfinite _

theorem certifiedFixedLevelSteps_envelope
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (pointLaw : Fin D.componentCount → Measure (LatticePoint n))
    (hvolume : ∀ i,
      (volumeEstimate i : Real) ∈ Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (halmost : ∀ i,
      AlmostUniformPointwise (pointLaw i)
        (codedLatticePoints (D.component i) b) p.ε')
    (rate : NNReal) :
    let S := (D.codedUnion_finite hn p b hprecision).toFinset
    ∀ step ∈ certifiedFixedLevelSteps D b S
      (p.Thresh D.componentCount) volumeEstimate pointLaw rate,
      step.RateEnvelope
        (Real.toNNReal (p.Thresh D.componentCount *
          (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate))
        (Real.toNNReal (p.Thresh D.componentCount *
          (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)) := by
  let S := (D.codedUnion_finite hn p b hprecision).toFinset
  dsimp only
  intro step hstep
  change step ∈ fixedLevelComponentSteps D S
    (fun i x => Real.toNNReal
      ((pointLaw i).real {(x.1 : LatticePoint n)} *
        ((ttcReference.t b n (p.Thresh D.componentCount)
          (volumeEstimate i) * rate : NNReal) : Real))) at hstep
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hstep
  exact concrete_component_step_envelope hn D p b hprecision
    i (pointLaw i) (halmost i) (volumeEstimate i) (hvolume i) rate

/-- Conditioned on successful per-component volume outcomes and the certified
point laws, the complete fixed-level union count obeys the paper's
two-sided Poisson concentration estimate. -/
theorem certifiedFixedLevel_concentration
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (pointLaw : Fin D.componentCount → Measure (LatticePoint n))
    (hvolume : ∀ i,
      (volumeEstimate i : Real) ∈ Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (halmost : ∀ i,
      AlmostUniformPointwise (pointLaw i)
        (codedLatticePoints (D.component i) b) p.ε')
    (rate : NNReal) :
    let S := (D.codedUnion_finite hn p b hprecision).toFinset
    let steps := certifiedFixedLevelSteps D b S
      (p.Thresh D.componentCount) volumeEstimate pointLaw rate
    let lower := Real.toNNReal (p.Thresh D.componentCount *
      (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate)
    let upper := Real.toNNReal (p.Thresh D.componentCount *
      (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : S → Nat => ∑ x, counts x)).real
          {count : Nat |
            (count : Real) < (1 - p.ε') *
              ((D.latticePoints b).ncard : Real) * lower ∨
            (1 + p.ε') *
              ((D.latticePoints b).ncard : Real) * upper < count} ≤
      2 * Real.exp (-
        ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) *
          p.ε' ^ 2 / 3) := by
  let S := (D.codedUnion_finite hn p b hprecision).toFinset
  let steps := certifiedFixedLevelSteps D b S
    (p.Thresh D.componentCount) volumeEstimate pointLaw rate
  let lower := Real.toNNReal (p.Thresh D.componentCount *
    (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate)
  let upper := Real.toNNReal (p.Thresh D.componentCount *
    (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)
  have hcoverage : fixedLevelCoverage steps ∅ = Finset.univ :=
    certifiedFixedLevelSteps_coverage D b
      (D.codedUnion_finite hn p b hprecision)
      (p.Thresh D.componentCount) volumeEstimate pointLaw rate
  have hcard : S.card = (D.latticePoints b).ncard := by
    rw [← D.codedUnion_ncard_eq_latticePoints b]
    exact (Set.ncard_eq_toFinset_card (D.codedUnionLatticePoints b)
      (D.codedUnion_finite hn p b hprecision)).symm
  have heps0 : 0 < p.ε' :=
    div_pos p.epsilon_pos (by norm_num)
  have heps1 : p.ε' ≤ 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have hsteps : ∀ step ∈ steps, step.RateEnvelope lower upper :=
    certifiedFixedLevelSteps_envelope hn D p b hprecision
      volumeEstimate pointLaw hvolume halmost rate
  simpa only [hcoverage, Finset.card_univ, Fintype.card_coe, hcard] using
    fixedLevelLaw_envelope_failure_bound S steps lower upper hsteps
      p.ε' heps0 heps1

/-- Every admissible fixed-level union prefix has enough Poisson mean for
the paper's dyadic Chernoff summation. -/
theorem certifiedFixedLevel_mean_lower
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (pointLaw : Fin D.componentCount → Measure (LatticePoint n))
    (hvolume : ∀ i,
      (volumeEstimate i : Real) ∈ Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (halmost : ∀ i,
      AlmostUniformPointwise (pointLaw i)
        (codedLatticePoints (D.component i) b) p.ε')
    (level : Nat)
    (hlevel : level ≤ dyadicCutoff (D.latticePoints b).ncard - 1) :
    let S := (D.codedUnion_finite hn p b hprecision).toFinset
    let rate := (1 / (2 : NNReal) ^ level)
    let steps := certifiedFixedLevelSteps D b S
      (p.Thresh D.componentCount) volumeEstimate pointLaw rate
    ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) ≥
      (1 - p.ε') * p.Thresh D.componentCount / 8 *
        (2 : Real) ^
          (dyadicCutoff (D.latticePoints b).ncard - 1 - level) := by
  let S := (D.codedUnion_finite hn p b hprecision).toFinset
  let rate : NNReal := 1 / (2 : NNReal) ^ level
  let steps := certifiedFixedLevelSteps D b S
    (p.Thresh D.componentCount) volumeEstimate pointLaw rate
  let lower := Real.toNNReal (p.Thresh D.componentCount *
    (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate)
  let upper := Real.toNNReal (p.Thresh D.componentCount *
    (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)
  have hcoverage : fixedLevelCoverage steps ∅ = Finset.univ :=
    certifiedFixedLevelSteps_coverage D b
      (D.codedUnion_finite hn p b hprecision)
      (p.Thresh D.componentCount) volumeEstimate pointLaw rate
  have hcard : S.card = (D.latticePoints b).ncard := by
    rw [← D.codedUnion_ncard_eq_latticePoints b]
    exact (Set.ncard_eq_toFinset_card (D.codedUnionLatticePoints b)
      (D.codedUnion_finite hn p b hprecision)).symm
  have hsteps : ∀ step ∈ steps, step.RateEnvelope lower upper :=
    certifiedFixedLevelSteps_envelope hn D p b hprecision
      volumeEstimate pointLaw hvolume halmost rate
  have hmeanNN :=
    (fixedLevelRates_total_mean_bounds S steps lower upper hsteps).1
  have hmeanR : (S.card : Real) * lower ≤
      ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) := by
    rw [hcoverage] at hmeanNN
    have hmeanNN' : S.card • lower ≤
        ∑ x, fixedLevelRates steps (fun _ => 0) x := by
      simpa only [Finset.card_univ, Fintype.card_coe] using hmeanNN
    have hcast : ((S.card • lower : NNReal) : Real) ≤
        ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) := by
      exact_mod_cast hmeanNN'
    simpa only [NNReal.coe_nsmul, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_natCast] using hcast
  have heps : 0 ≤ 1 - p.ε' := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have heta : 0 ≤ 1 - p.latticeEta := by
    dsimp [ApproxParams.latticeEta]
    linarith [p.epsilon_le_one]
  have hlowerNonneg : 0 ≤ p.Thresh D.componentCount *
      (1 - p.ε') ^ 2 * (1 - p.latticeEta) * (rate : Real) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (p.threshold_pos D.componentCount).le (sq_nonneg _)) heta)
      rate.coe_nonneg
  have hlowerR : (lower : Real) =
      p.Thresh D.componentCount * (1 - p.ε') ^ 2 *
        (1 - p.latticeEta) / (2 : Real) ^ level := by
    change ((Real.toNNReal (p.Thresh D.componentCount *
      (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate) : NNReal) : Real) = _
    rw [Real.coe_toNNReal _ hlowerNonneg]
    simp only [rate, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow,
      NNReal.coe_ofNat]
    ring
  have hcount := union_lattice_ncard_pos hn D p b hprecision
    hcomponents
  have hscalar := dyadic_mean_lower p D.componentCount
    (D.latticePoints b).ncard hcount level hlevel
  rw [hcard, hlowerR] at hmeanR
  calc
    (1 - p.ε') * p.Thresh D.componentCount / 8 *
        (2 : Real) ^
          (dyadicCutoff (D.latticePoints b).ncard - 1 - level) ≤
      ((D.latticePoints b).ncard : Real) *
        (p.Thresh D.componentCount * (1 - p.ε') ^ 2 *
          (1 - p.latticeEta) / (2 : Real) ^ level) := by
            calc
              _ ≤ ((D.latticePoints b).ncard : Real) *
                  p.Thresh D.componentCount *
                  (1 - p.ε') ^ 2 *
                  (1 - p.latticeEta) / (2 : Real) ^ level := hscalar
              _ = _ := by ring
    _ ≤ ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) :=
      hmeanR

/-- The exact levelwise error term used in the paper's finite dyadic
union bound, for certified fixed-level component outcomes. -/
theorem certifiedFixedLevel_error_bound
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (pointLaw : Fin D.componentCount → Measure (LatticePoint n))
    (hvolume : ∀ i,
      (volumeEstimate i : Real) ∈ Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (halmost : ∀ i,
      AlmostUniformPointwise (pointLaw i)
        (codedLatticePoints (D.component i) b) p.ε')
    (level : Nat)
    (hlevel : level ≤ dyadicCutoff (D.latticePoints b).ncard - 1) :
    let S := (D.codedUnion_finite hn p b hprecision).toFinset
    let rate := (1 / (2 : NNReal) ^ level)
    let steps := certifiedFixedLevelSteps D b S
      (p.Thresh D.componentCount) volumeEstimate pointLaw rate
    let lower := Real.toNNReal (p.Thresh D.componentCount *
      (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate)
    let upper := Real.toNNReal (p.Thresh D.componentCount *
      (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)
    let a := (1 - p.ε') * p.ε' ^ 2 *
      p.Thresh D.componentCount / 24
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : S → Nat => ∑ x, counts x)).real
          {count : Nat |
            (count : Real) < (1 - p.ε') *
              ((D.latticePoints b).ncard : Real) * lower ∨
            (1 + p.ε') *
              ((D.latticePoints b).ncard : Real) * upper < count} ≤
      2 * Real.exp (-a * (2 : Real) ^
        (dyadicCutoff (D.latticePoints b).ncard - 1 - level)) := by
  let S := (D.codedUnion_finite hn p b hprecision).toFinset
  let rate : NNReal := 1 / (2 : NNReal) ^ level
  let steps := certifiedFixedLevelSteps D b S
    (p.Thresh D.componentCount) volumeEstimate pointLaw rate
  let lower := Real.toNNReal (p.Thresh D.componentCount *
    (1 - p.ε') ^ 2 * (1 - p.latticeEta) * rate)
  let upper := Real.toNNReal (p.Thresh D.componentCount *
    (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)
  let a := (1 - p.ε') * p.ε' ^ 2 *
    p.Thresh D.componentCount / 24
  have hconc := certifiedFixedLevel_concentration hn D p b
    hprecision volumeEstimate pointLaw hvolume halmost rate
  have hmean := certifiedFixedLevel_mean_lower hn D p b
    hprecision hcomponents volumeEstimate pointLaw hvolume halmost
    level hlevel
  change ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) ≥
    (1 - p.ε') * p.Thresh D.componentCount / 8 *
      (2 : Real) ^
        (dyadicCutoff (D.latticePoints b).ncard - 1 - level) at hmean
  have hfactor : 0 ≤ p.ε' ^ 2 / 3 := by positivity
  have hExp :
      2 * Real.exp (-
        ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) *
          p.ε' ^ 2 / 3) ≤
      2 * Real.exp (-a * (2 : Real) ^
        (dyadicCutoff (D.latticePoints b).ncard - 1 - level)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : Real) ≤ 2)
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hmean hfactor
    have harg : -
        ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) *
          p.ε' ^ 2 / 3 ≤
        -a * (2 : Real) ^
          (dyadicCutoff (D.latticePoints b).ncard - 1 - level) := by
      have hpos : a * (2 : Real) ^
          (dyadicCutoff (D.latticePoints b).ncard - 1 - level) ≤
          ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) *
            p.ε' ^ 2 / 3 := by
        calc
          a * (2 : Real) ^
              (dyadicCutoff (D.latticePoints b).ncard - 1 - level) =
            ((1 - p.ε') * p.Thresh D.componentCount / 8 *
              (2 : Real) ^
                (dyadicCutoff (D.latticePoints b).ncard - 1 - level)) *
              (p.ε' ^ 2 / 3) := by
                dsimp only [a]
                ring
          _ ≤ ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) *
              (p.ε' ^ 2 / 3) := hmul
          _ = ((∑ x, fixedLevelRates steps (fun _ => 0) x : NNReal) : Real) *
              p.ε' ^ 2 / 3 := by ring
      linarith
    exact harg
  exact hconc.trans hExp

/-- Every successful fixed-level component prefix has the cutoff upper tail
allocated to one of the paper's `m` component tests. -/
theorem certifiedFixedLevel_cutoff_prefix_budget
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount)
    (volumeEstimate : Fin D.componentCount → NNReal)
    (pointLaw : Fin D.componentCount → Measure (LatticePoint n))
    (hvolume : ∀ i,
      (volumeEstimate i : Real) ∈ Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (halmost : ∀ i,
      AlmostUniformPointwise (pointLaw i)
        (codedLatticePoints (D.component i) b) p.ε') :
    let S := (D.codedUnion_finite hn p b hprecision).toFinset
    let rate : NNReal := 1 /
      (2 : NNReal) ^ (dyadicCutoff (D.latticePoints b).ncard - 1)
    let full := certifiedFixedLevelSteps D b S
      (p.Thresh D.componentCount) volumeEstimate pointLaw rate
    ∀ pfx : List (FixedLevelStep S),
      (∀ step ∈ pfx, step ∈ full) →
      ((fixedLevelLaw pfx
        (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))).map
          (fun counts : S → Nat => ∑ x, counts x)).real
            {k : Nat | p.Thresh D.componentCount ≤ (k : Real)} ≤
        p.delta / (6 * D.componentCount) := by
  let S := (D.codedUnion_finite hn p b hprecision).toFinset
  let d := dyadicCutoff (D.latticePoints b).ncard - 1
  let rate : NNReal := 1 / (2 : NNReal) ^ d
  let full := certifiedFixedLevelSteps D b S
    (p.Thresh D.componentCount) volumeEstimate pointLaw rate
  dsimp only
  intro pfx hpfx
  have hcard : Fintype.card S ≤ (D.latticePoints b).ncard := by
    rw [Fintype.card_coe]
    rw [← D.codedUnion_ncard_eq_latticePoints b]
    exact (Set.ncard_eq_toFinset_card (D.codedUnionLatticePoints b)
      (D.codedUnion_finite hn p b hprecision)).symm.le
  have hfull : ∀ step ∈ full,
      step.RateEnvelope 0
        (Real.toNNReal (p.Thresh D.componentCount *
          (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate)) := by
    have henv := certifiedFixedLevelSteps_envelope hn D p b
      hprecision volumeEstimate pointLaw hvolume halmost rate
    intro step hstep
    have h := henv step hstep
    exact ⟨fun x hx => ⟨zero_le, (h.1 x hx).2⟩, h.2⟩
  have hupperEq :
      Real.toNNReal (p.Thresh D.componentCount *
        (1 + p.ε') ^ 2 * (1 + p.latticeEta) * rate) =
      Real.toNNReal (p.Thresh D.componentCount *
        (1 + p.ε') ^ 2 * (1 + p.latticeEta) /
          (2 : Real) ^ d) := by
    congr 1
    simp only [rate, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow,
      NNReal.coe_ofNat]
    ring
  have hsteps : ∀ step ∈ pfx,
      step.RateEnvelope 0
        (Real.toNNReal (p.Thresh D.componentCount *
          (1 + p.ε') ^ 2 * (1 + p.latticeEta) /
          (2 : Real) ^ d)) := by
    intro step hs
    rw [← hupperEq]
    exact hfull step (hpfx step hs)
  exact fixed_level_prefix_cutoff_budget S pfx p
    D.componentCount (D.latticePoints b).ncard hcomponents
    (union_lattice_ncard_pos hn D p b hprecision hcomponents)
    hcard hsteps

end ttc

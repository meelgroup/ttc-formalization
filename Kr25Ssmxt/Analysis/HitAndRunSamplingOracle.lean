import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.GeometricOracleDischarge
import Kr25Ssmxt.Analysis.KV97HitAndRunSampling
import Kr25Ssmxt.Analysis.NormalizedHitAndRunGeometry

/-!
# A TTC sampling oracle implemented by Hit-and-Run and KV97 rounding

This file packages the finite-step continuous sampler and randomized-rounding theorem into
TTC's batch interface.  On calls covered by `PrecisionAdequate` (and in the dimension range
of the unconditional Arlib Hit-and-Run theorem), every coordinate is an independent restart
of the proved point law.  The volume field is deliberately left as the semantic law: this
module discharges only `GenerateSamplesContract`.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory
open MeasureTheory

namespace Kr25Ssmxt

/-- The paper's sampler-radius expression is at least one in its intended parameter range. -/
lemma one_le_samplerRadiusRequirement {n : Nat} (hn : 0 < n) (P : PolytopeData n)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    1 ≤ samplerRadiusRequirement P eta := by
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
  have hf1 : (1 : Real) ≤ P.presentation.facetCount := by
    exact_mod_cast P.facets_pos
  have hratio : (4 : Real) ≤ 32 * P.presentation.facetCount / eta := by
    rw [le_div_iff₀ heta0]
    nlinarith [mul_nonneg (show (0 : Real) ≤ P.presentation.facetCount by positivity)
      (sub_nonneg.mpr heta1)]
  have hsqrt :
      (1 : Real) ≤ Real.sqrt (Real.log (32 * P.presentation.facetCount / eta)) := by
    rw [Real.one_le_sqrt]
    have hlog4 : (1 : Real) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact Real.exp_one_lt_three.le.trans (by norm_num)
    exact hlog4.trans (Real.log_le_log (by norm_num) hratio)
  have hbase : (1 : Real) ≤ 512 * n / eta := by
    rw [le_div_iff₀ heta0]
    nlinarith
  rw [samplerRadiusRequirement]
  exact hbase.trans (le_mul_of_one_le_right (by positivity) hsqrt)

/-- A convenient existential form of the single-point capstone theorem. -/
theorem PolytopeData.exists_hitAndRun_pointLaw {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat)
    (hunit : 1 ≤ decimalScale b * P.inradius)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty) :
    ∃ pointLaw : Measure (LatticePoint n),
      AlmostUniformPointwise pointLaw (codedLatticePoints P b) eta := by
  obtain ⟨D, m, _hD, _hdeadline, _hmceil, hpoint⟩ :=
    P.exists_hitAndRun_latticePointLaw hn b hunit heta0 heta1 hfinite hnonempty
  exact ⟨acceptedRoundedLatticeLaw
    (Arlib.MarkovChains.iterate
      (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun
        (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
          (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))))
      (Arlib.uniformOn volume
        (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)) m)
    P b, hpoint⟩

lemma hitAndRunPointLaw_spec {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n) (b : Nat)
    (hunit : 1 ≤ decimalScale b * P.inradius)
    (eta : Real) (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty) :
    AlmostUniformPointwise
      (hitAndRunPointLaw hn P b hunit eta heta0 heta1 hfinite hnonempty)
      (codedLatticePoints P b) eta :=
  P.direct_hitAndRun_latticePointLaw hn b hunit heta0 heta1 hfinite hnonempty

lemma iidSampleBatchLaw_isProbabilityMeasure {n count : Nat}
    (pointLaw : Measure (LatticePoint n)) [IsProbabilityMeasure pointLaw] :
    IsProbabilityMeasure (iidSampleBatchLaw (count := count) pointLaw) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

lemma iidSampleBatchLaw_false {n count : Nat} (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw] :
    (iidSampleBatchLaw (count := count) pointLaw) {o | o.1 = false} = 0 := by
  rw [iidSampleBatchLaw, Measure.map_apply (by fun_prop) (by measurability)]
  simp

lemma iidSampleBatchLaw_iid {n count : Nat} (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw] :
    IIDBatchOnGood (iidSampleBatchLaw (count := count) pointLaw) pointLaw := by
  let productLaw : Measure (Fin count → LatticePoint n) :=
    Measure.pi (fun _ : Fin count => pointLaw)
  letI : IsProbabilityMeasure productLaw := by
    dsimp only [productLaw]
    infer_instance
  let tag : (Fin count → LatticePoint n) → SampleBatch n count :=
    fun samples => (true, samples)
  have htag : Measurable tag := by fun_prop
  have hgood : (productLaw.map tag) {o | o.1 = true} = 1 := by
    rw [Measure.map_apply htag (by measurability)]
    simp [tag]
  have hae : ∀ᵐ o ∂productLaw.map tag, o ∈ {o | o.1 = true} := by
    rw [MeasureTheory.ae_map_iff htag.aemeasurable (by measurability)]
    simp [tag]
  change ((ProbabilityTheory.cond (productLaw.map tag) {o | o.1 = true}).map Prod.snd) =
    Measure.pi (fun _ : Fin count => pointLaw)
  rw [ProbabilityTheory.cond, hgood, inv_one, one_smul,
    Measure.restrict_eq_self_of_ae_mem hae]
  rw [Measure.map_map measurable_snd htag]
  simpa [Function.comp_def, tag, productLaw] using (Measure.map_id productLaw)

/-- `PrecisionAdequate` routes every sampling call through finite-step Hit-and-Run, KV97
rounding/rejection, and independent restarts. -/
theorem hitAndRun_samples_contract {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams) :
    GenerateSamplesContract (hitAndRunSamplingOracles hn prep) F hbounded params := by
  let D := prep.run F hbounded
  let choice := prep.choosePrecision D params
  let b := choice.value
  intro i count
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have heta0 : 0 < params.epsilonPrime :=
    div_pos params.epsilon_pos (by norm_num)
  have heta1 : params.epsilonPrime ≤ 1 := by
    dsimp only [ApproxParams.epsilonPrime]
    linarith [params.epsilon_le_one]
  have hset := coded_lattice_points_finite_nonempty hn0 D params b choice.adequate i
  have hunit : 1 ≤ decimalScale b * (D.component i).inradius :=
    (one_le_samplerRadiusRequirement hn0 (D.component i) heta0 heta1).trans
      ((le_max_right _ _).trans (choice.adequate i))
  let pointLaw := hitAndRunPointLaw hn (D.component i) b hunit params.epsilonPrime
    heta0 heta1 hset.1 hset.2
  have halmost : AlmostUniformPointwise pointLaw
      (codedLatticePoints (D.component i) b) params.epsilonPrime := by
    exact hitAndRunPointLaw_spec hn (D.component i) b hunit params.epsilonPrime
      heta0 heta1 hset.1 hset.2
  letI : IsProbabilityMeasure pointLaw := halmost.1
  have hroute : 1 ≤ decimalScale b * (D.component i).inradius ∧
      0 < params.epsilonPrime ∧ params.epsilonPrime ≤ 1 ∧
      (codedLatticePoints (D.component i) b).Finite ∧
      (codedLatticePoints (D.component i) b).Nonempty :=
    ⟨hunit, heta0, heta1, hset.1, hset.2⟩
  have hmain : IsProbabilityMeasure (iidSampleBatchLaw (count := count) pointLaw) ∧
      (iidSampleBatchLaw (count := count) pointLaw).real {o | o.1 = false} ≤
        params.deltaPrime D.componentCount ∧
      ∃ pointLaw' : Measure (LatticePoint n),
        AlmostUniformPointwise pointLaw'
            (codedLatticePoints (D.component i) b) params.epsilonPrime ∧
          IIDBatchOnGood (iidSampleBatchLaw (count := count) pointLaw) pointLaw' := by
    refine ⟨iidSampleBatchLaw_isProbabilityMeasure pointLaw, ?_,
      ⟨pointLaw, halmost, iidSampleBatchLaw_iid pointLaw⟩⟩
    have hdelta : 0 ≤ params.deltaPrime D.componentCount := by
      exact div_nonneg params.delta_pos.le (by positivity)
    simp [Measure.real, iidSampleBatchLaw_false pointLaw, hdelta]
  simpa only [hitAndRunSamplingOracles, D, choice, b, dif_pos hroute, pointLaw]
    using hmain

/-- The manuscript run uses the normalized walk, with the same batch contract. -/
theorem manuscript_hitAndRun_samples_contract {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams) :
    GenerateSamplesContract (communityManuscriptOracles hn prep) F hbounded params := by
  let D := prep.run F hbounded
  let choice := prep.choosePrecision D params
  let b := choice.value
  intro i count
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have heta0 : 0 < params.epsilonPrime :=
    div_pos params.epsilon_pos (by norm_num)
  have heta1 : params.epsilonPrime ≤ 1 := by
    dsimp only [ApproxParams.epsilonPrime]
    linarith [params.epsilon_le_one]
  have hset := coded_lattice_points_finite_nonempty hn0 D params b choice.adequate i
  have hunit : 1 ≤ decimalScale b * (D.component i).inradius :=
    (one_le_samplerRadiusRequirement hn0 (D.component i) heta0 heta1).trans
      ((le_max_right _ _).trans (choice.adequate i))
  let pointLaw := normalizedHitAndRunPointLaw hn (D.component i) b hunit
    params.epsilonPrime heta0 heta1 hset.1 hset.2
  have halmost : AlmostUniformPointwise pointLaw
      (codedLatticePoints (D.component i) b) params.epsilonPrime := by
    exact (D.component i).normalizedHitAndRun_latticePointLaw hn b hunit
      heta0 heta1 hset.1 hset.2
  letI : IsProbabilityMeasure pointLaw := halmost.1
  have hroute : 1 ≤ decimalScale b * (D.component i).inradius ∧
      0 < params.epsilonPrime ∧ params.epsilonPrime ≤ 1 ∧
      (codedLatticePoints (D.component i) b).Finite ∧
      (codedLatticePoints (D.component i) b).Nonempty :=
    ⟨hunit, heta0, heta1, hset.1, hset.2⟩
  have hmain : IsProbabilityMeasure (iidSampleBatchLaw (count := count) pointLaw) ∧
      (iidSampleBatchLaw (count := count) pointLaw).real {o | o.1 = false} ≤
        params.deltaPrime D.componentCount ∧
      ∃ pointLaw' : Measure (LatticePoint n),
        AlmostUniformPointwise pointLaw'
            (codedLatticePoints (D.component i) b) params.epsilonPrime ∧
          IIDBatchOnGood (iidSampleBatchLaw (count := count) pointLaw) pointLaw' := by
    refine ⟨iidSampleBatchLaw_isProbabilityMeasure pointLaw, ?_,
      ⟨pointLaw, halmost, iidSampleBatchLaw_iid pointLaw⟩⟩
    have hdelta : 0 ≤ params.deltaPrime D.componentCount := by
      exact div_nonneg params.delta_pos.le (by positivity)
    simp [Measure.real, iidSampleBatchLaw_false pointLaw, hdelta]
  simpa only [communityManuscriptOracles, communityCV18HitAndRunOracles,
    hitAndRunSamplingOracles, D, choice, b, dif_pos hroute, pointLaw]
    using hmain

end Kr25Ssmxt

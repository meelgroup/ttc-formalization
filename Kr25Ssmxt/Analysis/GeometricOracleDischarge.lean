import Kr25Ssmxt.Analysis.OracleContracts
import Kr25Ssmxt.Analysis.PrecisionChoice
import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.PrecisionAdequateSplit
import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.EuclideanInball
import Kr25Ssmxt.Analysis.DecimalLatticeComponentComparison
import Kr25Ssmxt.Analysis.ProcessComponentsLatticeCountAccuracyCodedCard
import Kr25Ssmxt.Analysis.PolytopeCarrierMeasurable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.UniformOn

/-!
# A kernel-checked discharge of the geometric oracle contracts

The accuracy development only observes the output laws of the volume and sampling
subroutines.  This file supplies canonical laws with the required specifications: exact
Lebesgue volume and independent uniform draws from the finite coded lattice set.

This is an accuracy-level construction.  It discharges the abstract contracts without
claiming that either cited algorithm's finite-step implementation or runtime has been
formalized.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory
open MeasureTheory

namespace Kr25Ssmxt

/-- Exact volume, tagged as an unconditional successful call. -/
def exactVolumeLaw {n : Nat} (P : PolytopeData n) : Measure VolumeOutcome :=
  Measure.dirac (true, ⟨(volume P.carrier).toReal, ENNReal.toReal_nonneg⟩)

/-- The exact uniform point law on the coded lattice points of `P`. -/
def exactLatticePointLaw {n : Nat} (P : PolytopeData n) (b : Nat) :
    Measure (LatticePoint n) :=
  ProbabilityTheory.uniformOn (codedLatticePoints P b)

/-- An independently generated batch, with an always-successful tag. -/
def exactSampleBatchLaw {n count : Nat} (P : PolytopeData n) (b : Nat) :
    Measure (SampleBatch n count) :=
  (Measure.pi (fun _ : Fin count => exactLatticePointLaw P b)).map
    (fun samples => (true, samples))

/-- Canonical accuracy-level geometric oracles attached to certified preprocessing. -/
def exactSemanticOracles {n k : Nat} (prep : TTCPreprocessor n k) : TTCOracles n k where
  preprocessing := prep
  choosePrecision := fun D p => GetPrecision D p.precisionEta
  ComputeVolume := fun P _ _ => exactVolumeLaw P
  GenerateSamples := fun P count b _ _ => exactSampleBatchLaw P b

set_option maxHeartbeats 800000 in
lemma exact_volume_law_specification {n : Nat} (P : PolytopeData n) (eta delta : Real)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta) :
    IsProbabilityMeasure (exactVolumeLaw P) ∧
      (exactVolumeLaw P).real {o | o.1 = false} ≤ delta ∧
      ∀ᵐ o ∂exactVolumeLaw P, o.1 = true →
        (o.2 : Real) ∈ Arlib.relErr eta (volume P.carrier).toReal := by
  refine ⟨?_, ?_, ?_⟩
  · change IsProbabilityMeasure (Measure.dirac _)
    infer_instance
  · simpa [exactVolumeLaw, Measure.real] using hdelta
  · have hmeas : MeasurableSet {o : VolumeOutcome | o.1 = true →
        (o.2 : Real) ∈ Arlib.relErr eta (volume P.carrier).toReal} := by
      measurability
    let v : NNReal := ⟨(volume P.carrier).toReal, ENNReal.toReal_nonneg⟩
    let a : VolumeOutcome := (true, v)
    have hpoint : a.1 = true → (a.2 : Real) ∈
        Arlib.relErr eta (volume P.carrier).toReal := by
      intro _
      dsimp only [a, v]
      change (volume P.carrier).toReal ∈ Arlib.relErr eta (volume P.carrier).toReal
      rw [Arlib.mem_relErr]
      have hvolume_nonneg : 0 ≤ (volume P.carrier).toReal := ENNReal.toReal_nonneg
      constructor <;> nlinarith
    have hae : ∀ᵐ o ∂Measure.dirac a,
        o.1 = true → (o.2 : Real) ∈ Arlib.relErr eta (volume P.carrier).toReal :=
      (MeasureTheory.ae_dirac_iff hmeas).2 hpoint
    simpa only [exactVolumeLaw, a, v] using hae

lemma exact_volume_contract {n k : Nat} (prep : TTCPreprocessor n k)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams) :
    ComputeVolumeContract (exactSemanticOracles prep) F hbounded params := by
  intro i
  have heta : 0 ≤ params.ε' :=
    (div_pos params.epsilon_pos (by norm_num)).le
  have hdelta : 0 ≤ params.δ' (prep.run F hbounded).componentCount := by
    exact div_nonneg params.delta_pos.le (by positivity)
  simpa [exactSemanticOracles] using
    exact_volume_law_specification ((prep.run F hbounded).component i)
      params.ε' (params.δ' (prep.run F hbounded).componentCount)
      heta hdelta

lemma polytope_volume_toReal_pos {n : Nat} (P : PolytopeData n) :
    0 < (volume P.carrier).toReal := by
  have hvolume : 0 < volume P.carrier := P.volume_carrier_pos
  exact ENNReal.toReal_pos hvolume.ne' P.bounded.measure_lt_top.ne

/-- Adequate precision makes every component's coded lattice set finite and nonempty. -/
lemma coded_lattice_points_finite_nonempty
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k} (D : Decomposition F)
    (params : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b params.precisionEta)
    (i : Fin D.componentCount) :
    (codedLatticePoints (D.component i) b).Finite ∧
      (codedLatticePoints (D.component i) b).Nonempty := by
  have heta_pos : 0 < params.latticeEta := by
    exact div_pos params.epsilon_pos (by norm_num)
  have heta_le : params.latticeEta ≤ 1 := by
    dsimp only [ApproxParams.latticeEta]
    linarith [params.epsilon_le_one]
  have hradius : ∀ j,
      latticeRadiusRequirement D params.latticeEta ≤
        (10 : Real) ^ b * (D.component j).inradius := by
    intro j
    exact (le_max_left _ _).trans (hprecision.split j)
  have hcomparison := decimal_lattice_component_comparison hn D b params.latticeEta
    heta_pos heta_le hradius i
  have hgeometric_ne :
      ((D.component i).carrier ∩ decimalLattice b n).ncard ≠ 0 := by
    intro hzero
    have hupper := Arlib.relErr.upper hcomparison
    rw [hzero] at hupper
    norm_num at hupper
    exact (not_le_of_gt (polytope_volume_toReal_pos (D.component i))) hupper
  have hcoded_ne : (codedLatticePoints (D.component i) b).ncard ≠ 0 := by
    rw [process_components_lattice_count_accuracy_coded_card]
    exact hgeometric_ne
  exact ⟨Set.finite_of_ncard_ne_zero hcoded_ne,
    Set.nonempty_of_ncard_ne_zero hcoded_ne⟩

lemma exact_lattice_point_law_almost_uniform {n : Nat} (P : PolytopeData n) (b : Nat)
    (eta : Real) (heta : 0 ≤ eta)
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty) :
    AlmostUniformPointwise (exactLatticePointLaw P b) (codedLatticePoints P b) eta := by
  let S := codedLatticePoints P b
  have hprob : IsProbabilityMeasure (ProbabilityTheory.uniformOn S) :=
    ProbabilityTheory.isProbabilityMeasure_uniformOn hfinite hnonempty
  refine ⟨hprob, hfinite, hnonempty, ?_, ?_⟩
  · change ProbabilityTheory.uniformOn S Sᶜ = 0
    exact (ProbabilityTheory.uniformOn_eq_zero_iff hfinite).mpr (Set.inter_compl_self S)
  · intro x hx
    have hmassENN : ProbabilityTheory.uniformOn S {x} = (S.ncard : ENNReal)⁻¹ := by
      simpa [S, hfinite.mem_toFinset, hx, Set.ncard_eq_toFinset_card S hfinite] using
        (ProbabilityTheory.uniformOn_apply_finset
          (s := hfinite.toFinset) (t := ({x} : Finset (LatticePoint n))))
    have hmass : (ProbabilityTheory.uniformOn S).real {x} = (1 : Real) / S.ncard := by
      rw [Measure.real, hmassENN, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      simp [one_div]
    change (ProbabilityTheory.uniformOn S).real {x} ∈ Arlib.relErr eta (1 / S.ncard)
    rw [hmass]
    rw [Arlib.mem_relErr]
    have hcenter : 0 ≤ (1 : Real) / S.ncard := by positivity
    constructor <;> nlinarith

lemma exact_sample_batch_isProbabilityMeasure {n count : Nat} (P : PolytopeData n) (b : Nat)
    (hprob : IsProbabilityMeasure (exactLatticePointLaw P b)) :
    IsProbabilityMeasure (exactSampleBatchLaw (count := count) P b) := by
  letI : IsProbabilityMeasure (exactLatticePointLaw P b) := hprob
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end Kr25Ssmxt

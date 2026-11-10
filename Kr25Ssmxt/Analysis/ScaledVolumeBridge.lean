import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.PrecisionAdequateSplit
import Kr25Ssmxt.Analysis.AcceptanceBudget
import Kr25Ssmxt.Analysis.PolytopeCarrierMeasurable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Kr25Ssmxt.Analysis.IntegerLatticePolytopeComparison
import Kr25Ssmxt.Analysis.GeometricOracleDischarge
import Kr25Ssmxt.Analysis.ManuscriptCostedOracles
import Kr25Ssmxt.Analysis.HitAndRunSamplingOracle

/-! Volume and lattice-count representation bridges for acceptance. -/

namespace Kr25Ssmxt

open MeasureTheory Set

theorem scaledBody_preimage_toEuclidean {n : Nat} (P : PolytopeData n)
    (b : Nat) :
    toEuclidean ⁻¹' P.scaledBody b =
      (fun x : Point n => decimalScale b • x) '' P.carrier := by
  let A : Set (Point n) :=
    (fun x : Point n => decimalScale b • x) '' P.carrier
  rw [← P.image_decimalScale_eq_scaledBody b]
  ext x
  simp only [Set.mem_preimage, Set.mem_image, A]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    have h := congrArg
      (WithLp.ofLp : EuclideanSpace Real (Fin n) → Point n) hxy.symm
    simpa [toEuclidean] using h.symm
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [toEuclidean]⟩

theorem scaledBody_volume_eq_point_image {n : Nat} (P : PolytopeData n)
    (b : Nat) :
    volume (P.scaledBody b) =
      volume (((fun x : Point n => decimalScale b • x) '' P.carrier)) := by
  have hmeas : MeasurableSet (P.scaledBody b) := by
    unfold PolytopeData.scaledBody
    exact Arlib.Polytope.measurableSet_body _ _
  have hmeasure := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    hmeas.nullMeasurableSet
  change volume (toEuclidean ⁻¹' P.scaledBody b) = volume (P.scaledBody b) at hmeasure
  simpa only [scaledBody_preimage_toEuclidean] using hmeasure.symm

theorem acceptedIntegers_ncard_eq_point_lattice {n : Nat}
    (P : PolytopeData n) (b : Nat) :
    (acceptedIntegers P b).ncard =
      (((fun x : Point n => decimalScale b • x) '' P.carrier) ∩
        {x : Point n | ∀ i, ∃ z : Int, x i = (z : Real)}).ncard := by
  apply Set.ncard_congr (fun z (_ : z ∈ acceptedIntegers P b) =>
    (fun i : Fin n => (z i : Real)))
  · intro z hz
    constructor
    · rw [← scaledBody_preimage_toEuclidean P b]
      simpa [acceptedIntegers, toEuclidean, kv97LatEmb] using hz
    · intro i
      exact ⟨z i, rfl⟩
  · intro z w _ _ hzw
    funext i
    exact Int.cast_injective (congrFun hzw i)
  · intro x hx
    choose z hz using hx.2
    refine ⟨z, ?_, ?_⟩
    · change kv97LatEmb n z ∈ P.scaledBody b
      rw [← scaledBody_preimage_toEuclidean P b] at hx
      have heq : (fun i : Fin n => (z i : Real)) = x := by
        funext i
        exact (hz i).symm
      simpa [toEuclidean, kv97LatEmb, heq] using hx.1
    · funext i
      exact (hz i).symm

theorem scaledBody_volume_le_lattice_count {n k : Nat} (hn : 0 < n)
    {F : LRAFormula n k} (D : Decomposition F) (b : Nat) (η : Real)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hradius : ∀ i,
      latticeRadiusRequirement D η ≤
        (10 : Real) ^ b * (D.component i).inradius)
    (i : Fin D.componentCount) :
    (volume ((D.component i).scaledBody b)).toReal ≤
      (1 + η) * ((acceptedIntegers (D.component i) b).ncard : Real) := by
  have hcomp := integer_lattice_polytope_comparison hn D b η hη0 hη1 hradius i
  rw [Arlib.mem_relErr] at hcomp
  have hvolume := scaledBody_volume_eq_point_image (D.component i) b
  have hcount := acceptedIntegers_ncard_eq_point_lattice (D.component i) b
  rw [hvolume, hcount]
  exact hcomp.2

/-- The manuscript precision choice supplies the rejection probability
needed to bound independent retry costs, with no extra acceptance hypothesis. -/
theorem certified_normalizedHitAndRun_acceptance_ge_half {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    (1 / 2 : Real) ≤
      (roundedAcceptanceProbability
        (normalizedHitAndRunContinuousLaw (D.component i) b p.ε')
        (D.component i) b : Real) := by
  have hn0 : 0 < n := by omega
  have hsample0 : 0 < p.ε' := by
    dsimp [ApproxParams.ε']
    exact div_pos p.epsilon_pos (by norm_num)
  have hsample8 : p.ε' ≤ 1 / 8 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have hlattice0 : 0 ≤ p.latticeEta := by
    dsimp [ApproxParams.latticeEta]
    exact (div_pos p.epsilon_pos (by norm_num)).le
  have hlattice8 : p.latticeEta ≤ 1 / 8 := by
    dsimp [ApproxParams.latticeEta]
    linarith [p.epsilon_le_one]
  have hradius : ∀ j,
      latticeRadiusRequirement D p.latticeEta ≤
        (10 : Real) ^ b * (D.component j).inradius := by
    intro j
    exact (le_max_left _ _).trans (hprecision.split j)
  have hbase := scaledBody_volume_le_lattice_count hn0 D b p.latticeEta
    (by dsimp [ApproxParams.latticeEta]; exact div_pos p.epsilon_pos (by norm_num))
    (by linarith) hradius i
  have hfinite := (coded_lattice_points_finite_nonempty hn0 D p b hprecision i).1
  have hsampler : samplerRadiusRequirement (D.component i) p.ε' ≤
      decimalScale b * (D.component i).inradius := by
    simpa only [decimalScale] using (le_max_right _ _).trans (hprecision.split i)
  exact normalizedHitAndRun_acceptance_ge_half_of_base_comparison hn
    (D.component i) b hsample0 hsample8 p.latticeEta hlattice0 hlattice8
    hfinite hsampler hbase

theorem certified_community_sampler_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor count : Nat)
    (delta : Real) (i : Fin D.componentCount) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      (communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
        (D.component i) count b p.ε' delta ≤
      count * (2 * TTCRuntime.samplingAttemptOperations n
        (D.component i).presentation.facetCount
        (normalizedHitAndRunSteps (D.component i) b p.ε')) := by
  have hn0 : 0 < n := by omega
  have hset := coded_lattice_points_finite_nonempty hn0 D p b hprecision i
  have hunit : 1 ≤ decimalScale b * (D.component i).inradius :=
    (one_le_samplerRadiusRequirement hn0 (D.component i)
      (by dsimp [ApproxParams.ε']; exact div_pos p.epsilon_pos (by norm_num))
      (by dsimp [ApproxParams.ε']; linarith [p.epsilon_le_one])).trans
      ((le_max_right _ _).trans (hprecision.split i))
  have hsample0 : 0 < p.ε' := by
    dsimp [ApproxParams.ε']
    exact div_pos p.epsilon_pos (by norm_num)
  have hsample1 : p.ε' ≤ 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  exact communityManuscriptCosted_samples_expected_cost hn prep factor
    (D.component i) count b p.ε' delta
    ⟨hunit, hsample0, hsample1, hset.1, hset.2⟩
    (certified_normalizedHitAndRun_acceptance_ge_half hn D p b hprecision i)

theorem certified_community_sampler_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor count : Nat)
    (delta : Real) (i : Fin D.componentCount) :
    ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
      (D.component i) count b p.ε' delta) Set.univ ≤ 1 := by
  have hn0 : 0 < n := by omega
  have hset := coded_lattice_points_finite_nonempty hn0 D p b hprecision i
  have hunit : 1 ≤ decimalScale b * (D.component i).inradius :=
    (one_le_samplerRadiusRequirement hn0 (D.component i)
      (by dsimp [ApproxParams.ε']; exact div_pos p.epsilon_pos (by norm_num))
      (by dsimp [ApproxParams.ε']; linarith [p.epsilon_le_one])).trans
      ((le_max_right _ _).trans (hprecision.split i))
  have hsample0 : 0 < p.ε' := by
    dsimp [ApproxParams.ε']
    exact div_pos p.epsilon_pos (by norm_num)
  have hsample1 : p.ε' ≤ 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  exact communityManuscriptCosted_samples_mass_le_one hn prep factor
    (D.component i) count b p.ε' delta
    ⟨hunit, hsample0, hsample1, hset.1, hset.2⟩

end Kr25Ssmxt

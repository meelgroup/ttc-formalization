import Kr25Ssmxt.Analysis.ManuscriptVolumeClipAccuracy
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Geometric validity of the manuscript's volume-clipping interval. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem PolytopeData.volume_le_outerCube {n : Nat} (P : PolytopeData n) :
    (volume P.carrier).toReal ≤ (2 * P.outerRadius) ^ n := by
  let box : Set (Point n) :=
    Set.Icc (fun _ => -P.outerRadius) (fun _ => P.outerRadius)
  have hsubset : P.carrier ⊆ box := by
    intro x hx
    change (fun _ => -P.outerRadius) ≤ x ∧
      x ≤ (fun _ => P.outerRadius)
    constructor
    · intro i
      have hcoord := PiLp.norm_apply_le (WithLp.toLp 2 x) i
      have hbound := P.outer_bound x hx
      have habs : |x i| ≤ P.outerRadius := by
        simpa [Real.norm_eq_abs] using hcoord.trans hbound
      exact (abs_le.mp habs).1
    · intro i
      have hcoord := PiLp.norm_apply_le (WithLp.toLp 2 x) i
      have hbound := P.outer_bound x hx
      have habs : |x i| ≤ P.outerRadius := by
        simpa [Real.norm_eq_abs] using hcoord.trans hbound
      exact (abs_le.mp habs).2
  have hbox : (volume box).toReal = (2 * P.outerRadius) ^ n := by
    change (volume (Set.Icc (fun _ : Fin n => -P.outerRadius)
      (fun _ => P.outerRadius))).toReal = _
    rw [Real.volume_Icc_pi_toReal (by intro i; dsimp; linarith [P.outerRadius_nonneg])]
    simp [Finset.prod_const]
    congr 1
    ring
  have hboxTop : volume box ≠ ⊤ := by
    dsimp [box]
    rw [Real.volume_Icc_pi]
    simp
  exact (ENNReal.toReal_mono hboxTop (measure_mono hsubset)).trans_eq hbox

theorem PolytopeData.innerCube_le_volume {n : Nat} (hn : 0 < n)
    (P : PolytopeData n) :
    (2 * P.inradius / Real.sqrt n) ^ n ≤
      (volume P.carrier).toReal := by
  let r : Real := P.inradius / Real.sqrt n
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hone : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have hr : 0 ≤ r := (div_pos P.inradius_pos hsqrt).le
  have hrle : r ≤ P.inradius := by
    dsimp [r]
    exact div_le_self P.inradius_pos.le hone
  let box : Set (Point n) :=
    Set.Icc (fun i => P.incenter i - r) (fun i => P.incenter i + r)
  have hsubset : box ⊆ P.carrier := by
    intro x hx
    apply P.inball
    rw [Metric.mem_closedBall, dist_pi_le_iff P.inradius_pos.le]
    intro i
    have hlow := hx.1 i
    have hhigh := hx.2 i
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hbox : (volume box).toReal = (2 * r) ^ n := by
    change (volume (Set.Icc (fun i : Fin n => P.incenter i - r)
      (fun i => P.incenter i + r))).toReal = _
    rw [Real.volume_Icc_pi_toReal (by intro i; dsimp; linarith)]
    simp [Finset.prod_const]
    congr 1
    ring
  have hcarrierTop : volume P.carrier ≠ ⊤ := P.bounded.measure_lt_top.ne
  have hvolume := ENNReal.toReal_mono hcarrierTop (measure_mono hsubset)
  calc
    (2 * P.inradius / Real.sqrt n) ^ n = (2 * r) ^ n := by
      dsimp [r]
      congr 1
      ring
    _ = (volume box).toReal := hbox.symm
    _ ≤ (volume P.carrier).toReal := hvolume

theorem PolytopeData.manuscriptVolume_bounds {n : Nat}
    (hn : 0 < n) (P : PolytopeData n) (eta : Real)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    (P.manuscriptVolumeLower eta : Real) ≤
      (volume P.carrier).toReal ∧
    (volume P.carrier).toReal ≤
      (P.manuscriptVolumeUpper eta : Real) := by
  have hbaseLower := P.innerCube_le_volume hn
  have hbaseUpper := P.volume_le_outerCube
  have hlowFactor : 0 ≤ 1 - eta := by linarith
  have hhighFactor : 0 ≤ 1 + eta := by linarith
  have hlowPower : 0 ≤ (2 * P.inradius / Real.sqrt n) ^ n := by
    exact pow_nonneg (div_nonneg
      (mul_nonneg (by norm_num) P.inradius_pos.le)
      (Real.sqrt_nonneg _)) _
  have hhighPower : 0 ≤ (2 * P.outerRadius) ^ n := by
    exact pow_nonneg (mul_nonneg (by norm_num) P.outerRadius_nonneg) _
  constructor
  · unfold PolytopeData.manuscriptVolumeLower
    rw [Real.coe_toNNReal _ (mul_nonneg hlowFactor hlowPower)]
    nlinarith
  · unfold PolytopeData.manuscriptVolumeUpper
    rw [Real.coe_toNNReal _ (mul_nonneg hhighFactor hhighPower)]
    nlinarith

theorem community_manuscript_volume_contract
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams) :
    ComputeVolumeContract (communityManuscriptOracles hn prep)
      F hbounded p := by
  apply community_manuscript_volume_contract_of_bounds hn prep F hbounded p
  dsimp only
  intro i
  have heta0 : 0 ≤ p.epsilonPrime :=
    (div_pos p.epsilon_pos (by norm_num)).le
  have heta1 : p.epsilonPrime ≤ 1 := by
    dsimp only [ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  exact ((prep.run F hbounded).component i).manuscriptVolume_bounds
    (by omega : 0 < n) p.epsilonPrime heta0 heta1

end Kr25Ssmxt

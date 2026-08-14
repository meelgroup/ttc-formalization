import Mathlib

/-!
# Deterministic arithmetic behind `sections/analysis.tex`, `thm:runtime`

The paper first sums, over the `m` decomposed polytopes, the two per-cube costs

`rᵢ * max (n^3 * (Rᵢ / γᵢ)^2) n^4 / eps^2`

and

`rᵢ * n^5 * (Rᵢ / γᵢ)^2 * Threshold`.

It then replaces every `Rᵢ / γᵢ` by `rho` and every `rᵢ` by `rMax`.  This file
machine-checks exactly that deterministic comparison.  It deliberately does not hide
`eps^-2` or `Threshold`: the last `O(m*n^5*rho^2*rMax)` in the paper suppresses them.

The final two lemmas connect the arithmetic expression to the current operational TTC
envelopes.  Their premises state the remaining semantic bridges explicitly: converting
recorded volume membership queries and hybrid-sampler inspections to the two per-cube
paper prices.
-/

namespace Ttc.TTCRuntimePaperArithmetic

open scoped BigOperators ENNReal

/-- The volume contribution displayed in the proof of `thm:runtime`, after replacing
the per-cube ratio `Rᵢ / γᵢ` by the uniform upper bound `rho`. -/
noncomputable def paperVolumeFactor (n : Nat) (rho eps : Real) : Real :=
  max ((n : Real) ^ 3 * rho ^ 2) ((n : Real) ^ 4) / eps ^ 2

/-- The sampling contribution displayed in the proof of `thm:runtime`, after replacing
the per-cube ratio by `rho` and bounding the number of samples by `threshold`. -/
noncomputable def paperSamplingFactor (n : Nat) (rho threshold : Real) : Real :=
  (n : Real) ^ 5 * rho ^ 2 * threshold

/-- The unsuppressed deterministic runtime expression immediately before the last
big-O equality in `sections/analysis.tex`. -/
noncomputable def paperRuntimeEnvelope
    (m n : Nat) (rho rMax eps threshold : Real) : Real :=
  (m : Real) * rMax *
    (paperVolumeFactor n rho eps + paperSamplingFactor n rho threshold)

theorem paperVolumeFactor_nonneg (n : Nat) {rho eps : Real} :
    0 ≤ paperVolumeFactor n rho eps := by
  unfold paperVolumeFactor
  positivity

theorem paperSamplingFactor_nonneg (n : Nat) {rho threshold : Real}
    (hthreshold : 0 ≤ threshold) :
    0 ≤ paperSamplingFactor n rho threshold := by
  unfold paperSamplingFactor
  positivity

/-- With `n ≥ 1` and `rho ≥ 1`, both alternatives in the volume maximum are at
most `n^5*rho^2`.  This is the deterministic polynomial comparison used by the
paper's last equality. -/
theorem paperVolumeFactor_le_quintic
    {n : Nat} {rho eps : Real} (hn : 1 ≤ n) (hrho : 1 ≤ rho) (heps : 0 < eps) :
    paperVolumeFactor n rho eps ≤ (n : Real) ^ 5 * rho ^ 2 / eps ^ 2 := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : Real) ≤ n := le_trans zero_le_one hnR
  have hrho0 : (0 : Real) ≤ rho := le_trans zero_le_one hrho
  have hn3le5 : (n : Real) ^ 3 ≤ (n : Real) ^ 5 := by
    have hs : 0 ≤ (n : Real) ^ 2 - 1 := by nlinarith
    have h : 0 ≤ (n : Real) ^ 3 * ((n : Real) ^ 2 - 1) :=
      mul_nonneg (by positivity) hs
    nlinarith
  have hn4le5 : (n : Real) ^ 4 ≤ (n : Real) ^ 5 := by
    have h : 0 ≤ (n : Real) ^ 4 * ((n : Real) - 1) := by positivity
    nlinarith
  have hrhoSq : (1 : Real) ≤ rho ^ 2 := by nlinarith
  have hfirst : (n : Real) ^ 3 * rho ^ 2 ≤ (n : Real) ^ 5 * rho ^ 2 :=
    mul_le_mul_of_nonneg_right hn3le5 (sq_nonneg rho)
  have hsecond : (n : Real) ^ 4 ≤ (n : Real) ^ 5 * rho ^ 2 :=
    calc
      (n : Real) ^ 4 ≤ (n : Real) ^ 5 := hn4le5
      _ ≤ (n : Real) ^ 5 * rho ^ 2 := by
        nlinarith [show 0 ≤ (n : Real) ^ 5 by positivity]
  unfold paperVolumeFactor
  exact div_le_div_of_nonneg_right (max_le hfirst hsecond) (sq_nonneg eps)

/-- Exact version of the paper's final suppression step.  The factor
`eps^-2 + threshold` remains visible; treating it (and its hidden logarithmic/warm-start
factors) as suppressed yields the advertised `O(m*n^5*rho^2*rMax)` shape. -/
theorem paperRuntimeEnvelope_le_quintic
    {m n : Nat} {rho rMax eps threshold : Real}
    (hn : 1 ≤ n) (hrho : 1 ≤ rho) (hrMax : 0 ≤ rMax)
    (heps : 0 < eps) (hthreshold : 0 ≤ threshold) :
    paperRuntimeEnvelope m n rho rMax eps threshold ≤
      (m : Real) * rMax * ((n : Real) ^ 5 * rho ^ 2 *
        (1 / eps ^ 2 + threshold)) := by
  have hV := paperVolumeFactor_le_quintic hn hrho heps
  have hS : paperSamplingFactor n rho threshold =
      (n : Real) ^ 5 * rho ^ 2 * threshold := rfl
  have houter : 0 ≤ (m : Real) * rMax := mul_nonneg (by positivity) hrMax
  unfold paperRuntimeEnvelope
  apply mul_le_mul_of_nonneg_left _ houter
  rw [hS]
  calc
    paperVolumeFactor n rho eps + (n : Real) ^ 5 * rho ^ 2 * threshold ≤
        ((n : Real) ^ 5 * rho ^ 2 / eps ^ 2) +
          (n : Real) ^ 5 * rho ^ 2 * threshold := add_le_add hV le_rfl
    _ = (n : Real) ^ 5 * rho ^ 2 * (1 / eps ^ 2 + threshold) := by
      field_simp
      <;> ring

/-- Uniformize one cube's volume price using `Rᵢ / γᵢ ≤ rho`. -/
theorem perCubeVolumeFactor_le
    (n : Nat) {ratio rho eps : Real}
    (hratio0 : 0 ≤ ratio) (hratio : ratio ≤ rho) :
    max ((n : Real) ^ 3 * ratio ^ 2) ((n : Real) ^ 4) / eps ^ 2 ≤
      paperVolumeFactor n rho eps := by
  have hsquare : ratio ^ 2 ≤ rho ^ 2 := by nlinarith
  have hn3 : 0 ≤ (n : Real) ^ 3 := by positivity
  have hfirst : (n : Real) ^ 3 * ratio ^ 2 ≤ (n : Real) ^ 3 * rho ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare hn3
  unfold paperVolumeFactor
  exact div_le_div_of_nonneg_right (max_le_max hfirst le_rfl) (sq_nonneg eps)

/-- Uniformize one cube's total sampling price, including its sample count. -/
theorem perCubeSamplingFactor_le
    (n : Nat) {ratio rho samples threshold : Real}
    (hratio0 : 0 ≤ ratio) (hratio : ratio ≤ rho)
    (hsamples0 : 0 ≤ samples) (hsamples : samples ≤ threshold) :
    (n : Real) ^ 5 * ratio ^ 2 * samples ≤
      paperSamplingFactor n rho threshold := by
  have hrho0 : 0 ≤ rho := le_trans hratio0 hratio
  have hsquare : ratio ^ 2 ≤ rho ^ 2 := by nlinarith
  have hn5 : 0 ≤ (n : Real) ^ 5 := by positivity
  have hratioTerm :
      (n : Real) ^ 5 * ratio ^ 2 ≤ (n : Real) ^ 5 * rho ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare hn5
  unfold paperSamplingFactor
  exact mul_le_mul hratioTerm hsamples hsamples0 (mul_nonneg hn5 (sq_nonneg rho))

/-- Per-cube facet and geometry comparisons imply the paper's uniform per-cube price.

`volumeCost` and `samplingCost` may be any deterministic costs.  The last two premises
are precisely where an operational implementation must show that its recorded counters
are bounded by the paper's membership/facet accounting. -/
theorem perCubeTotalCost_le
    (n : Nat) {ratio facets volumeCost samplingCost rho rMax eps samples threshold : Real}
    (hratio0 : 0 ≤ ratio) (hratio : ratio ≤ rho)
    (hfacets0 : 0 ≤ facets) (hfacets : facets ≤ rMax)
    (hsamples0 : 0 ≤ samples) (hsamples : samples ≤ threshold)
    (hvolumeCost : volumeCost ≤ facets *
      (max ((n : Real) ^ 3 * ratio ^ 2) ((n : Real) ^ 4) / eps ^ 2))
    (hsamplingCost : samplingCost ≤ facets *
      ((n : Real) ^ 5 * ratio ^ 2 * samples)) :
    volumeCost + samplingCost ≤
      rMax * (paperVolumeFactor n rho eps +
        paperSamplingFactor n rho threshold) := by
  have hV := perCubeVolumeFactor_le n (eps := eps) hratio0 hratio
  have hS := perCubeSamplingFactor_le n hratio0 hratio hsamples0 hsamples
  have hpaperV0 := paperVolumeFactor_nonneg n (rho := rho) (eps := eps)
  have hpaperS0 := paperSamplingFactor_nonneg n (rho := rho)
    (le_trans hsamples0 hsamples)
  calc
    volumeCost + samplingCost ≤
        facets * (max ((n : Real) ^ 3 * ratio ^ 2) ((n : Real) ^ 4) / eps ^ 2) +
          facets * ((n : Real) ^ 5 * ratio ^ 2 * samples) :=
      add_le_add hvolumeCost hsamplingCost
    _ ≤ facets * paperVolumeFactor n rho eps +
          facets * paperSamplingFactor n rho threshold :=
      add_le_add (mul_le_mul_of_nonneg_left hV hfacets0)
        (mul_le_mul_of_nonneg_left hS hfacets0)
    _ = facets * (paperVolumeFactor n rho eps +
          paperSamplingFactor n rho threshold) := by ring
    _ ≤ rMax * (paperVolumeFactor n rho eps +
          paperSamplingFactor n rho threshold) :=
      mul_le_mul_of_nonneg_right hfacets (add_nonneg hpaperV0 hpaperS0)

/-- Sum the paper's per-cube prices over exactly `m = card I` cubes. -/
theorem sum_perCubeTotalCost_le
    {I : Type*} [Fintype I]
    (n : Nat) (ratio facets volumeCost samplingCost samples : I → Real)
    (rho rMax eps threshold : Real)
    (hratio0 : ∀ i, 0 ≤ ratio i) (hratio : ∀ i, ratio i ≤ rho)
    (hfacets0 : ∀ i, 0 ≤ facets i) (hfacets : ∀ i, facets i ≤ rMax)
    (hsamples0 : ∀ i, 0 ≤ samples i) (hsamples : ∀ i, samples i ≤ threshold)
    (hvolumeCost : ∀ i, volumeCost i ≤ facets i *
      (max ((n : Real) ^ 3 * (ratio i) ^ 2) ((n : Real) ^ 4) / eps ^ 2))
    (hsamplingCost : ∀ i, samplingCost i ≤ facets i *
      ((n : Real) ^ 5 * (ratio i) ^ 2 * samples i)) :
    (∑ i, (volumeCost i + samplingCost i)) ≤
      paperRuntimeEnvelope (Fintype.card I) n rho rMax eps threshold := by
  calc
    (∑ i, (volumeCost i + samplingCost i)) ≤
        ∑ _i : I, rMax * (paperVolumeFactor n rho eps +
          paperSamplingFactor n rho threshold) := by
      apply Finset.sum_le_sum
      intro i hi
      exact perCubeTotalCost_le n (hratio0 i) (hratio i)
        (hfacets0 i) (hfacets i) (hsamples0 i) (hsamples i)
        (hvolumeCost i) (hsamplingCost i)
    _ = paperRuntimeEnvelope (Fintype.card I) n rho rMax eps threshold := by
      simp [paperRuntimeEnvelope]
      <;> ring

/-- Direct ENNReal bridge from the current two operational TTC envelopes to the
unsuppressed expression in the paper.  `hvolume` and `hsampling` are intentionally
premises: they are the two implementation-specific comparisons not supplied by pure
arithmetic. -/
theorem operationalEnvelopes_le_paperRuntime
    {n m : Nat} (volumeEnvelope samplingEnvelope : ENNReal)
    (eps rho rMax threshold : Real)
    (hrMax : 0 ≤ rMax) (hthreshold : 0 ≤ threshold)
    (hvolume : volumeEnvelope ≤
      ENNReal.ofReal ((m : Real) * rMax * paperVolumeFactor n rho eps))
    (hsampling : samplingEnvelope ≤
      ENNReal.ofReal ((m : Real) * rMax * paperSamplingFactor n rho threshold)) :
    volumeEnvelope + samplingEnvelope ≤
      ENNReal.ofReal (paperRuntimeEnvelope m n rho rMax eps threshold) := by
  calc
    _ ≤ ENNReal.ofReal ((m : Real) * rMax * paperVolumeFactor n rho eps) +
          ENNReal.ofReal ((m : Real) * rMax * paperSamplingFactor n rho threshold) :=
      add_le_add hvolume hsampling
    _ = ENNReal.ofReal (paperRuntimeEnvelope m n rho rMax eps threshold) := by
      rw [← ENNReal.ofReal_add]
      · congr 1
        unfold paperRuntimeEnvelope
        ring
      · exact mul_nonneg (mul_nonneg (by positivity) hrMax)
          (paperVolumeFactor_nonneg n)
      · exact mul_nonneg (mul_nonneg (by positivity) hrMax)
          (paperSamplingFactor_nonneg n hthreshold)

/-!
The theorem above proves the exact displayed, unsuppressed expression.  Passing from it
to `O(m*n^5*rho^2*rMax)` additionally treats `eps^-2`, `threshold`, logarithmic confidence
terms, and warm-start costs as suppressed factors, exactly as stated in the prose of
`thm:runtime`; that asymptotic convention is not an inequality between fixed reals.
-/

#print axioms perCubeVolumeFactor_le
#print axioms perCubeSamplingFactor_le
#print axioms paperVolumeFactor_le_quintic
#print axioms paperRuntimeEnvelope_le_quintic
#print axioms perCubeTotalCost_le
#print axioms sum_perCubeTotalCost_le
#print axioms operationalEnvelopes_le_paperRuntime

end Ttc.TTCRuntimePaperArithmetic

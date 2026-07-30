/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.ProdKernel
import Ttc.Analysis.PiLintegral
import Mathlib.Probability.Independence.Basic

/-!
# The law of the product kernel's displacement

`Ttc.prodKernel` is given by a **density**; `Ttc.rounding_tail_bound` needs the
displacement's coordinates to be **independent**, which is a statement about
measures. This file bridges the two.

The displacement map `p ↦ (pᵢ − xᵢ)ᵢ` carries `Ttc.RoundingKernel.dispLaw` of the
product kernel onto `Measure.pi (fun _ => Ttc.tentProb)`
(`Ttc.map_dispEquiv_dispLaw`) — a genuine product measure — whence independence.
The two ingredients are `Ttc.pi_withDensity` (a product of `withDensity` measures
is the `withDensity` of the product density) and the fact that the displacement
map is volume preserving.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Pushing a density forward along a measurable equivalence. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun b => f (e.symm b)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.measurable hs,
    lintegral_map (f := fun b => f (e.symm b)) (g := ⇑e)
      (hf.comp e.symm.measurable) e.measurable]
  simp

/-- **The one-dimensional displacement law**: the tent density against Lebesgue. -/
noncomputable def tentProb : Measure ℝ := volume.withDensity (fun u => ENNReal.ofReal (tent u))

instance isProbabilityMeasure_tentProb : IsProbabilityMeasure tentProb := by
  constructor
  rw [tentProb, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_tent
      (Filter.Eventually.of_forall tent_nonneg), integral_tent, ENNReal.ofReal_one]

/-- The product of the one-dimensional laws, as a density against Lebesgue. -/
theorem pi_tentProb_eq (n : ℕ) :
    Measure.pi (fun _ : Fin n => tentProb)
      = (volume : Measure (Fin n → ℝ)).withDensity
          (fun q => ENNReal.ofReal (∏ i, tent (q i))) := by
  rw [tentProb, pi_withDensity (fun _ : Fin n => fun u => ENNReal.ofReal (tent u))
    (fun _ => continuous_tent.measurable.ennreal_ofReal), volume_pi]
  congr 1
  funext q
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => tent_nonneg _]

/-- **The displacement map** `p ↦ (pᵢ − xᵢ)ᵢ`, as a measurable equivalence. -/
noncomputable def dispEquiv {n : ℕ} (x : Space n) : Space n ≃ᵐ (Fin n → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.trans
    (MeasurableEquiv.subRight (WithLp.ofLp x))

@[simp] theorem dispEquiv_apply {n : ℕ} (x p : Space n) (i : Fin n) :
    dispEquiv x p i = p i - x i := rfl

theorem dispEquiv_symm_apply {n : ℕ} (x : Space n) (q : Fin n → ℝ) (i : Fin n) :
    ((dispEquiv x).symm q) i = q i + x i := rfl

theorem measurePreserving_dispEquiv {n : ℕ} (x : Space n) :
    MeasurePreserving (dispEquiv x) (volume : Measure (Space n)) volume :=
  (measurePreserving_sub_right (volume : Measure (Fin n → ℝ)) (WithLp.ofLp x)).comp
    (PiLp.volume_preserving_ofLp (Fin n))

/-- **The displacement of the product kernel is a product measure.**

This is what makes the coordinates independent: pushing `dispLaw` forward along
`p ↦ (pᵢ − xᵢ)ᵢ` gives exactly `Measure.pi` of the one-dimensional tent laws. -/
theorem map_dispEquiv_dispLaw {n : ℕ} (x : Space n) :
    ((prodKernel n).dispLaw x).map (dispEquiv x)
      = Measure.pi (fun _ : Fin n => tentProb) := by
  have hmeas : Measurable (fun p : Space n => ENNReal.ofReal (∏ i, tent (p i - x i))) :=
    (continuous_prod_tent x).measurable.ennreal_ofReal
  have hcoord : ∀ (q : Fin n → ℝ) (i : Fin n), ((dispEquiv x).symm q) i - x i = q i := by
    intro q i
    show q i + x i - x i = q i
    ring
  have hd : (prodKernel n).dispLaw x
      = volume.withDensity (fun p : Space n => ENNReal.ofReal (∏ i, tent (p i - x i))) := rfl
  rw [hd, map_withDensity_equiv _ _ _ hmeas,
    (measurePreserving_dispEquiv x).map_eq, pi_tentProb_eq]
  congr 1
  funext q
  exact congrArg ENNReal.ofReal (Finset.prod_congr rfl fun i _ => by rw [hcoord q i])

/-- The displacement law gives no mass outside the kernel's support. -/
theorem dispLaw_compl_supp {n : ℕ} (K : RoundingKernel n) (x : Space n) :
    K.dispLaw x (K.supp x)ᶜ = 0 := by
  have hzero : ∫ p in (K.supp x)ᶜ, K.k p x = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun p hp => K.vanishes x p hp
  rw [K.dispLaw_apply x (K.supp_meas x).compl, hzero, ENNReal.ofReal_zero]

/-- **`hbdd`**: the displacement lies in `[−1,1]` in each coordinate, almost
surely — because the density vanishes off the box. -/
theorem ae_disp_mem_Icc {n : ℕ} (x : Space n) (k : Fin n) :
    ∀ᵐ p ∂((prodKernel n).dispLaw x), p k - x k ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsub : {p : Space n | ¬ (p k - x k ∈ Set.Icc (-1 : ℝ) 1)}
      ⊆ ((prodKernel n).supp x)ᶜ := by
    intro p hp hbox
    exact hp (Set.mem_Icc.mpr (abs_le.mp (hbox k)))
  exact measure_mono_null hsub (dispLaw_compl_supp (prodKernel n) x)

/-- **`hindep`**: the displacement's coordinates are independent under the
product kernel's law — immediate from `Ttc.map_dispEquiv_dispLaw`, since a
product measure is exactly what independence asserts. -/
theorem iIndepFun_disp {n : ℕ} (x : Space n) :
    iIndepFun (fun (k : Fin n) (p : Space n) => p k - x k) ((prodKernel n).dispLaw x) := by
  haveI := (prodKernel n).isProbabilityMeasure_dispLaw x
  have hfun : (fun (p : Space n) (k : Fin n) => p k - x k) = ⇑(dispEquiv x) := by
    funext p; funext k; rfl
  have hae : ∀ k : Fin n,
      AEMeasurable (fun p : Space n => p k - x k) ((prodKernel n).dispLaw x) :=
    fun k => ((measurable_coord k).sub measurable_const).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hae, hfun, map_dispEquiv_dispLaw]
  congr 1
  funext k
  have hmk : ((prodKernel n).dispLaw x).map (fun p : Space n => p k - x k)
      = (Measure.pi (fun _ : Fin n => tentProb)).map (Function.eval k) := by
    rw [← map_dispEquiv_dispLaw x,
      Measure.map_map (measurable_pi_apply k) (dispEquiv x).measurable]
    rfl
  rw [hmk, Measure.pi_map_eval]
  simp

/-- The one-dimensional displacement has mean zero. -/
theorem integral_tentProb_id : ∫ u, u ∂tentProb = 0 := by
  rw [tentProb, integral_withDensity_eq_integral_toReal_smul
    continuous_tent.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (tent_nonneg _), smul_eq_mul]
  have h : (fun x : ℝ => tent x * x) = fun x => x * tent x := by funext x; ring
  rw [h]; exact integral_id_mul_tent

/-- **`hmean`**: each coordinate of the displacement has mean zero. -/
theorem integral_disp_eq_zero {n : ℕ} (x : Space n) (k : Fin n) :
    ∫ p, (p k - x k) ∂((prodKernel n).dispLaw x) = 0 := by
  have hmarg : (Measure.pi (fun _ : Fin n => tentProb)).map (Function.eval k) = tentProb := by
    rw [Measure.pi_map_eval]; simp
  have h1 : ∫ p, (p k - x k) ∂((prodKernel n).dispLaw x)
      = ∫ q : Fin n → ℝ, q k ∂(Measure.pi (fun _ : Fin n => tentProb)) := by
    rw [← map_dispEquiv_dispLaw x,
      integral_map (dispEquiv x).measurable.aemeasurable
        (measurable_pi_apply k).aestronglyMeasurable]
    rfl
  have h2 : ∫ q : Fin n → ℝ, q k ∂(Measure.pi (fun _ : Fin n => tentProb))
      = ∫ u, u ∂tentProb := by
    have h := integral_map (μ := Measure.pi (fun _ : Fin n => tentProb))
      (φ := Function.eval k) (f := fun u : ℝ => u)
      (measurable_pi_apply k).aemeasurable measurable_id.aestronglyMeasurable
    rw [hmarg] at h
    exact h.symm
  rw [h1, h2, integral_tentProb_id]

/-! ## The tail bound, for the product kernel

All four hypotheses of `Ttc.rounding_tail_bound` are now theorems about
`Ttc.prodKernel`, so the bound applies with nothing assumed.
-/

/-- The scaled displacement coordinates are independent. -/
theorem iIndepFun_disp_smul {n : ℕ} (x : Space n) (A : Fin n → ℝ) :
    iIndepFun (fun (k : Fin n) (p : Space n) => A k * (p k - x k))
      ((prodKernel n).dispLaw x) :=
  (iIndepFun_disp x).comp (fun k u => A k * u)
    (fun _ => measurable_const.mul measurable_id)

set_option maxHeartbeats 1000000 in
/-- **The facet-crossing tail bound for the actual rounding.** -/
theorem prodKernel_tail_bound {n : ℕ} (x : Space n) (A : Fin n → ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 < ∑ k, A k ^ 2) :
    ((prodKernel n).dispLaw x).real
        {p | κ * coeffNorm A ≤ ∑ k, A k * (p k - x k)} ≤ Real.exp (-κ ^ 2 / 2) := by
  haveI := (prodKernel n).isProbabilityMeasure_dispLaw x
  exact rounding_tail_bound (fun (k : Fin n) (p : Space n) => p k - x k) A
    (fun k => ((measurable_coord k).sub measurable_const).aemeasurable)
    (iIndepFun_disp_smul x A)
    (fun k => ae_disp_mem_Icc x k) (fun k => integral_disp_eq_zero x k) hκ hA

set_option maxHeartbeats 1000000 in
/-- **The tail bound at the paper's `κ`**: at most `η/(4r)` per facet. -/
theorem prodKernel_tail_bound_kappa {n : ℕ} (x : Space n) (A : Fin n → ℝ)
    {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r) (hA : 0 < ∑ k, A k ^ 2) :
    ((prodKernel n).dispLaw x).real
        {p | (Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r)) * coeffNorm A
              ≤ ∑ k, A k * (p k - x k)} ≤ η / (4 * r) := by
  haveI := (prodKernel n).isProbabilityMeasure_dispLaw x
  exact rounding_tail_bound_kappa (fun (k : Fin n) (p : Space n) => p k - x k) A
    (fun k => ((measurable_coord k).sub measurable_const).aemeasurable)
    (iIndepFun_disp_smul x A)
    (fun k => ae_disp_mem_Icc x k) (fun k => integral_disp_eq_zero x k) hη hη1 hr hA

/-! ## `claim:cl`(a), with nothing assumed

`Ttc.claim_cl_a` takes the escape mass as the hypothesis `hesc`. For the actual
rounding it is now a theorem: the covering puts every escaping point on the wrong
side of some facet, the tail bound gives each facet `η/(4r)`, and the union bound
over the `r` facets gives `η/4`.
-/

/-- **The escape bound, discharged for the product kernel.** This is `hesc` of
`Ttc.claim_cl_a`, proved rather than assumed. -/
theorem prodKernel_escape_bound {n : ℕ} (x : Space n) {S : Set (Space n)}
    (hS : MeasurableSet S) {ι : Type*} (T : Finset ι) (Aof : ι → Fin n → ℝ)
    {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r) (hcard : (T.card : ℝ) ≤ r)
    (hA : ∀ j ∈ T, 0 < ∑ k, (Aof j) k ^ 2)
    (hcover : (prodKernel n).supp x \ S ⊆ ⋃ j ∈ T,
      {p | (Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r)) * coeffNorm (Aof j)
            ≤ ∑ k, Aof j k * (p k - x k)}) :
    ∫ p in (prodKernel n).supp x \ S, (prodKernel n).k p x ≤ η / 4 := by
  refine escape_of_cover T _ hS hcover ?_
  refine rounding_union_bound T _ (by linarith) hcard ?_ (le_of_lt hη)
  intro j hj
  exact prodKernel_tail_bound_kappa x (Aof j) hη hη1 hr (hA j hj)

/-- **`claim:cl`(a) for the actual rounding, with no residual hypothesis.**

Every input is now proved: the kernel is the product of tent densities
(`Ttc.prodKernel`), its coordinates are independent (`Ttc.iIndepFun_disp`), and
the escape bound follows from the tail bound
(`Ttc.prodKernel_escape_bound`). -/
theorem prodKernel_claim_cl_a {n : ℕ} (x : Space n) {S : Set (Space n)}
    (hS : MeasurableSet S) {ι : Type*} (T : Finset ι) (Aof : ι → Fin n → ℝ)
    {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r) (hcard : (T.card : ℝ) ≤ r)
    (hvol : 0 ≤ (volume S).toReal)
    (hA : ∀ j ∈ T, 0 < ∑ k, (Aof j) k ^ 2)
    (hcover : (prodKernel n).supp x \ S ⊆ ⋃ j ∈ T,
      {p | (Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r)) * coeffNorm (Aof j)
            ≤ ∑ k, Aof j k * (p k - x k)}) :
    (1 - η / 4) / (volume S).toReal ≤ roundProb (prodKernel n) S x :=
  claim_cl_a (prodKernel n) hS x hvol
    (prodKernel_escape_bound x hS T Aof hη hη1 hr hcard hA hcover)

end Ttc

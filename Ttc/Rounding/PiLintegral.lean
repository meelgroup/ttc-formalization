/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Tonelli for a product of one-variable functions

Mathlib proves that on a finite product of measure spaces the **Bochner** integral
of `∏ᵢ fᵢ(xᵢ)` factors as `∏ᵢ ∫ fᵢ`
(`MeasureTheory.integral_fintype_prod_eq_prod`). It has no `ℝ≥0∞` counterpart.

This file supplies it. The proof mirrors Mathlib's Bochner one: induct on the
number of coordinates, split `Measure.pi` over `Fin (n+1)` into
`μ 0 ×ˢ Measure.pi (μ ∘ succ)` via `measurePreserving_piFinSuccAbove`, and apply
`MeasureTheory.lintegral_prod_mul` (Tonelli) at each step.

It is needed because the rounding kernel of `Rounding/ProdKernel` is given by a
**density**, while independence of its coordinates is a statement about
**measures**; bridging the two means identifying a product of `withDensity`
measures with the `withDensity` of the product density, and that identification is
tested on measurable boxes — which is exactly this lemma.
-/

namespace Ttc

open Fintype MeasureTheory MeasureTheory.Measure
open scoped ENNReal

/-- **Tonelli's theorem for a product of one-variable functions**, in `n`
variables. The `ℝ≥0∞` analogue of `MeasureTheory.integral_fin_nat_prod_eq_prod`. -/
theorem lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          have hm : Measurable (fun x : (i : Fin (n + 1)) → E i => ∏ i, f i (x i)) :=
            Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp hm]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
          rfl
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          have hm2 : Measurable (fun x : (i : Fin n) → E i.succ => ∏ i, f i.succ (x i)) :=
            Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)
          rw [← n_ih (fun i => f i.succ) (fun i => hf _),
            ← lintegral_prod_mul (hf 0).aemeasurable hm2.aemeasurable]
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- **A product of `withDensity` measures is the `withDensity` of the product
density.** Tested on measurable boxes via `MeasureTheory.Measure.pi_eq`, where the
box restriction becomes a product of indicators and `Ttc.lintegral_fin_nat_prod`
applies.

This is the bridge the rounding kernel needs: `Ttc.prodKernel` is given by a
density, while independence of its coordinates is a statement about measures. -/
theorem pi_withDensity {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i))
      = (Measure.pi μ).withDensity (fun q => ∏ i, f i (q i)) := by
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : (Set.univ.pi s).indicator (fun q : (i : Fin n) → E i => ∏ i, f i (q i))
      = fun q => ∏ i, (s i).indicator (f i) (q i) := by
    funext q
    by_cases hq : q ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hq]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (Set.mem_univ_pi.mp hq i) _).symm
    · rw [Set.indicator_of_notMem hq]
      simp only [Set.mem_univ_pi, not_forall] at hq
      obtain ⟨i, hi⟩ := hq
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox, hind,
    lintegral_fin_nat_prod (fun i => (s i).indicator (f i))
      (fun i => (hf i).indicator (hs i))]
  exact Finset.prod_congr rfl fun i _ => by
    rw [lintegral_indicator (hs i), ← withDensity_apply _ (hs i)]

end Ttc

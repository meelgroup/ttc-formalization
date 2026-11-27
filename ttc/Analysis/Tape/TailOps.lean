/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.RuntimeBudget
import ttc.Analysis.Tape.HalveOps
import ttc.Analysis.Tape.SamplerOps
import ttc.Analysis.Tape.StepCap

/-! # Arithmetic budget after the rate check -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open ttc.RuntimeBudget

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {d : ℕ}

theorem Eops_tailT_le (hd : 0 < d) (f b : ℕ) (K : Params) (L : Loaded d)
    (t : Num ℝ) (sc : Fin L.facets → Num ℝ) (q : Num ℝ × List (Fin d → Num ℤ) × Num ℕ)
    (hTh : 0 ≤ K.thresh.get) (hp : 0 ≤ q.1.get)
    (hsize : q.2.2.get = q.2.1.length)
    (hX : (q.2.1.length : ℝ) ≤ K.thresh.get) (hr : t.get * q.1.get ≤ K.thresh.get)
    (hacc : vlaw (sampleTryT L (walkConstantsProg L K.scale K.epsPrime K.dim).val sc K.dimN) b
      {some none} ≤ (2 : ENNReal)⁻¹) :
    Eops (tailT f K L t sc q) b ≤ tailOpsBudget K L := by
  let cap := Nat.floor K.thresh.get
  let r := (A.mul t q.1).val
  let P := (poissonT r).bind (halveT K f q.1 q.2.1 q.2.2)
  let S := sampleT f K L sc
  let c := walkConstantsProg L K.scale K.epsPrime K.dim
  let B := sampleTryOps d L.facets c.val.steps.get
  have hmP : MeasFam fun _ : Unit => P :=
    MeasFam.poissonT (rate := fun _ => r) (k := fun _ => halveT K f q.1 q.2.1 q.2.2)
      measurable_const (mf_halve K f (p := fun _ => q.1) (X := fun _ => q.2.1)
        (size := fun _ => q.2.2) (N := Prod.snd)
        measurable_const measurable_const measurable_const measurable_snd)
  have hmS : MeasFam S := mf_sampleT f K L sc measurable_id
  have hm : MeasFam fun _ : Unit => P.bind S :=
    MeasFam.bind' hmP (hmS.comp measurable_snd)
  rw [tailT_eq]
  change Eops ((compute (A.mul t q.1)).bind fun _ => P.bind S) b ≤ _
  rw [Eops_compute_bind _ _ _ (hm.outcome () b), opsTotal_mul, Nat.cast_one]
  have hcap := Nat.le_floor hX
  have hnext : Post P fun h => h.2.2.2.get ≤ cap := by
    refine Post.bind (post_of_forall (fun N => ?_) _)
    refine (post_halveT_capped K f q.1 q.2.1 q.2.2 N hsize).mono fun h hh => ?_
    have hhle := Nat.le_floor hh.2
    exact (Nat.le_add_left _ _).trans hhle
  have hQ : MeasurableSet {h : Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ |
      h.2.2.2.get ≤ cap} :=
    measurableSet_Iic.preimage (Num.measurable_get.comp measurable_snd.snd.snd)
  have hsample : ∀ h, h.2.2.2.get ≤ cap →
      Eops (S h) b ≤ (opsTotal c.cost : ENNReal) + (1 + cap * (2 * B + 3)) := by
    intro h hh
    refine (Eops_sampleT_le hd f K L sc b h hacc).trans ?_
    exact add_le_add le_rfl (add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr hh) le_rfl))
  have hp' := Eops_poisson_halveT_le K f b q.1 r q.2.1 q.2.2 hTh hp hsize
  have hr' : (Real.toNNReal r.get : ℝ) ≤ K.thresh.get := by
    rw [Real.coe_toNNReal']
    exact max_le (by simpa [r, A.mul] using hr) hTh
  have hpopReal : (q.2.1.length : ℝ) + (Real.toNNReal r.get : ℝ) ≤ 2 * (cap + 1 : ℝ) := by
    have hf := Nat.lt_floor_add_one K.thresh.get
    change K.thresh.get < (cap : ℝ) + 1 at hf
    linarith
  have hpop : (q.2.1.length : ENNReal) + (Real.toNNReal r.get : ENNReal) ≤ 2 * (cap + 1 : ENNReal) := by
    exact_mod_cast hpopReal
  have hden : (cap + 1 : ENNReal) ≠ 0 := by simp
  have hratio : ((q.2.1.length + (Real.toNNReal r.get : ENNReal)) / (cap + 1 : ENNReal)) ≤ 2 :=
    (ENNReal.div_le_iff hden (by simp)).2 hpop
  have hcount : Eops P b ≤ (1 + (8 + 4 * cap) * 5 : ENNReal) := by
    change Eops P b ≤ _
    refine hp'.trans ?_
    push_cast
    refine add_le_add le_rfl (mul_le_mul' (by gcongr) ?_)
    calc _ ≤ 1 + 2 * (2 : ENNReal) := add_le_add le_rfl (mul_le_mul' le_rfl hratio)
      _ = 5 := by norm_num
  have hB := Eops_bind_le_of_post hnext hQ hmS (fun h => Free.capFirst (free_sampleT f K L sc h))
    b b (hmP.outcome () b) _ hsample
  refine (add_le_add le_rfl (hB.trans (add_le_add hcount le_rfl))).trans_eq ?_
  unfold tailOpsBudget
  push_cast
  ring

end ttc.Tape

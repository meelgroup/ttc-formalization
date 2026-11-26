/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.RuntimeBudget
import ttc.Analysis.Tape.CV18Ops
import ttc.Analysis.Tape.RateOps
import ttc.Analysis.Tape.TailOps

/-! # Cost of a complete sealed TTC component -/

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

private theorem opsTotal_tProg (K : Params) (L : Loaded d) (v : Num ℝ) :
    opsTotal (tProg K L v).cost = 8 := by
  simp [tProg, powHeld, A.cast, A.log, opsTotal_add, opsTotal_one]

private theorem mp_tProg (K : Params) (L : Loaded d) :
    MP (tProg K L) :=
  MP.bind' (MP.const _) (MP.bind' (mp_max measurable_snd (by fun_prop))
    (MP.bind' (MP.const _) (MP.bind' (mp_mul measurable_snd measurable_fst.snd)
      (mp_mul measurable_const measurable_snd))))

private def rateTailT (f : ℕ) (K : Params) (L : Loaded d) (sc : Fin L.facets → Num ℝ) (s : State d)
    (t : Num ℝ) : Tree d (State d) :=
  (rateT K.thresh L sc t s).bind (tailT f K L t sc)

private theorem mf_rateTailT (f : ℕ) (K : Params) (L : Loaded d) (sc : Fin L.facets → Num ℝ)
    (s : State d) : MeasFam (rateTailT f K L sc s) :=
  MeasFam.bind' (mf_rateT _ _ _ measurable_id s)
    (mf_tailT _ _ _ _ measurable_fst measurable_snd)

private def componentRestT (f : ℕ) (K : Params) (L : Loaded d) (s : State d)
    (v : Num ℝ) : Tree d (State d) :=
  (compute (tProg K L v)).bind fun t =>
  (compute (scaledOffsets L K.scale)).bind fun sc =>
  rateTailT f K L sc s t

private theorem mf_componentRestT (f : ℕ) (K : Params) (L : Loaded d) (s : State d) :
    MeasFam (componentRestT f K L s) :=
  MeasFam.compute (mp_tProg K L)
    (MeasFam.computeConst _ ((mf_rateTailT f K L (scaledOffsets L K.scale).val s).comp measurable_snd))

/-- The input to a component is capped by the preceding halving and sampling
step. The scalar rate is nonnegative. -/
def ComponentStateOk (K : Params) (s : State d) : Prop :=
  0 ≤ s.p.get ∧ (s.X.length : ℝ) ≤ K.thresh.get

theorem measurableSet_componentStateOk (K : Params) :
    MeasurableSet {s : State d | ComponentStateOk K s} :=
  (measurableSet_Ici.preimage (Num.measurable_get.comp State.measurable_p)).inter
    (measurableSet_Iic.preimage
      ((measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp
        (List.measurable_length.comp State.measurable_X)))

theorem post_stepT_componentStateOk (f : ℕ) (K : Params) (L : Loaded d) (s : State d)
    (hs : ComponentStateOk K s) :
    Post (stepT (cv18T d) f K L s) (ComponentStateOk K) :=
  ((post_stepT f K L s hs.1).and (post_stepT_capped f K L s hs.1)).mono fun _ h => ⟨h.1.1, h.2⟩

set_option maxHeartbeats 400000 in
private theorem Eops_componentRestT_le (hd0 : 0 < d) (f b : ℕ) (K : Params) (L : Loaded d)
    (s : State d) (hTh : 0 < K.thresh.get) (hs : ComponentStateOk K s)
    (hacc : vlaw (sampleTryT L (walkConstantsProg L K.scale K.epsPrime K.dim).val
      (scaledOffsets L K.scale).val K.dimN) b {some none} ≤ (2 : ENNReal)⁻¹) (v : Num ℝ) :
    let S := scaledOffsets L K.scale
    let cap := Nat.floor K.thresh.get
    let B := 19 + cap * (d + 2 * d * L.facets + 8)
    Eops (componentRestT f K L s v) b ≤ (8 : ENNReal) + opsTotal S.cost + B + tailOpsBudget K L := by
  let S := scaledOffsets L K.scale
  let cap := Nat.floor K.thresh.get
  let B := 19 + cap * (d + 2 * d * L.facets + 8)
  let t := (tProg K L v).val
  have hmr := mf_rateTailT f K L S.val s
  have hmr' : MeasFam fun _ : Unit => (compute S).bind fun sc => rateTailT f K L sc s t :=
    MeasFam.computeConst _ (hmr.comp (φ := fun _ : Unit => t) measurable_const)
  change Eops ((compute (tProg K L v)).bind fun z =>
    (compute S).bind fun sc => rateTailT f K L sc s z) b ≤ _
  rw [Eops_compute_bind (tProg K L v) (fun z => (compute S).bind fun sc =>
        rateTailT f K L sc s z) b (hmr'.outcome () b),
    Eops_compute_bind S (fun sc => rateTailT f K L sc s t) b (hmr.outcome t b), opsTotal_tProg]
  have hr : MeasFam fun _ : Unit => rateT K.thresh L S.val t s :=
    mf_rateT _ _ _ (t := fun _ => t) measurable_const s
  have ht : MeasFam (tailT f K L t S.val) := mf_tailT _ _ _ _ measurable_const measurable_id
  have hrN : maxOps (rateT K.thresh L S.val t s) ≤ (B : ℕ∞) := by
    refine (maxOps_rateT_le hd0 K.thresh L S.val t s).trans ?_
    unfold B
    push_cast
    exact add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr (Nat.le_floor hs.2)) le_rfl)
  have hrate : Eops (rateT K.thresh L S.val t s) b ≤ (B : ENNReal) :=
    (Eops_le_maxOps _ _ (hr.outcome () b)).trans (ENat.toENNReal_le_natCast.mpr hrN)
  let good := fun q : Num ℝ × List (Fin d → Num ℤ) × Num ℕ =>
    0 ≤ q.1.get ∧ q.2.2.get = q.2.1.length ∧ q.2.1.length ≤ s.X.length ∧ t.get * q.1.get ≤ K.thresh.get
  have hgood : MeasurableSet {q | good q} := by
    have hm1 := (Num.measurable_get (α := ℝ)).comp (measurable_fst :
      Measurable (Prod.fst : (Num ℝ × List (Fin d → Num ℤ) × Num ℕ) → Num ℝ))
    have hm2 := (Num.measurable_get (α := ℕ)).comp (measurable_snd.snd :
      Measurable fun q : (Num ℝ × List (Fin d → Num ℤ) × Num ℕ) => q.2.2)
    have hm3 := (List.measurable_length.comp measurable_snd.fst :
      Measurable fun q : (Num ℝ × List (Fin d → Num ℤ) × Num ℕ) => q.2.1.length)
    exact (measurableSet_Ici.preimage hm1).inter ((measurableSet_eq_fun hm2 hm3).inter
      ((measurableSet_Iic.preimage hm3).inter
        (measurableSet_Iic.preimage (measurable_const.mul hm1))))
  have hbound := Eops_bind_le_of_post (post_rateT_bounded K.thresh L S.val t s hTh hs.1)
    hgood ht (fun q => Free.capFirst (free_tailT f K L t S.val q)) b b (hr.outcome () b)
    (tailOpsBudget K L) (fun q hq => Eops_tailT_le hd0 f b K L t S.val q hTh.le hq.1
      hq.2.1 ((Nat.cast_le.mpr hq.2.2.1).trans hs.2) hq.2.2.2 hacc)
  refine (add_le_add le_rfl (add_le_add le_rfl (hbound.trans (add_le_add hrate le_rfl)))).trans_eq ?_
  dsimp only [S, B, cap]
  push_cast
  ring

set_option maxHeartbeats 400000 in
/-- A uniform expected-cost bound for one actual execution of the sealed
component, conditional only on the certified sampling acceptance bound. -/
theorem Eops_stepT_le (hd : 3 ≤ d) (f b : ℕ) (K : Params) (L : Loaded d) (s : State d)
    (hTh : 0 < K.thresh.get) (hs : ComponentStateOk K s)
    (hacc : vlaw (sampleTryT L (walkConstantsProg L K.scale K.epsPrime K.dim).val
      (scaledOffsets L K.scale).val K.dimN) b {some none} ≤ (2 : ENNReal)⁻¹) :
    Eops (stepT (cv18T d) f K L s) b ≤ componentOpsBudget K L := by
  have hd0 : 0 < d := by omega
  let C := cv18Offsets L
  let V := cv18ParamsProg K L
  let vol := cv18T d (allFacets L.facets L.normal C.val) V.val.1 V.val.2.2 V.val.2.1
  let rest := componentRestT f K L s
  have hR : MeasFam rest := mf_componentRestT f K L s
  have hVol : MeasFam fun _ : Unit => vol :=
    mf_cv18T (memberMP_allFacets L.facets L.normal C.val) V.val.1 V.val.2.2 V.val.2.1
  have hVr : MeasFam fun _ : Unit => vol.bind rest :=
    MeasFam.bind' hVol (hR.comp measurable_snd)
  have hcf : ∀ v, CapFirst (rest v) := by
    intro v
    exact Free.capFirst (Free.bind (free_compute _) fun t => Free.bind (free_compute _) fun _ =>
      Free.bind (free_rateT _ _ _ _ _) fun q => free_tailT _ _ _ _ _ _)
  have hrest := Eops_componentRestT_le hd0 f b K L s hTh hs hacc
  let q : ArlibCommunity.Algorithms.CV18.VolumeParams :=
    ⟨d, hd, 1/2, by constructor <;> norm_num, 1/2, by constructor <;> norm_num, 1, by norm_num⟩
  have hv := Eops_cv18T_allFacets_le q L.facets L.normal C.val V.val.1 V.val.2.2 V.val.2.1 b
  let ccont := fun off : Fin L.facets → Num ℝ => (compute V).bind fun x =>
    (cv18T d (allFacets L.facets L.normal off) x.1 x.2.2 x.2.1).bind rest
  let vcont := fun x : Num ℝ × Num ℝ × Num ℝ =>
    (cv18T d (allFacets L.facets L.normal C.val) x.1 x.2.2 x.2.1).bind rest
  have hmeas : MeasFam fun _ : Unit => ccont C.val :=
    MeasFam.computeConst _ hVr
  rw [stepT_eq]
  change Eops ((compute C).bind ccont) b ≤ _
  rw [Eops_compute_bind C ccont b (hmeas.outcome () b)]
  change (opsTotal C.cost : ENNReal) + Eops ((compute V).bind vcont) b ≤ _
  rw [Eops_compute_bind V vcont b (hVr.outcome () b)]
  have hbudget := Eops_bind_le_of_post (post_of_forall (Q := fun _ => True) (fun _ => trivial) _)
    (by simp) hR hcf b b (hVol.outcome () b) _ (fun v _ => hrest v)
  refine (add_le_add le_rfl (add_le_add le_rfl (hbudget.trans (add_le_add hv le_rfl)))).trans_eq ?_
  unfold componentOpsBudget
  push_cast
  ring

end ttc.Tape

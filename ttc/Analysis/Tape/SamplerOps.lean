/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.OpsExp
import ttc.Analysis.Tape.WalkOps

/-! # Expected arithmetic for the retry loop -/

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
variable (L : Loaded d) (W : WalkConstants d L.facets) (scaled : Fin L.facets → Num ℝ)
  (dimN : Num ℕ) (b : ℕ)

/-- The rejected attempt is the only branch that can spend on another attempt. -/
theorem Eops_sampleUntilAccepted_succ (f : ℕ) :
    Eops (sampleUntilAcceptedT L W scaled dimN (f + 1)) b =
      Eops (sampleTryT L W scaled dimN) b +
        Eops (sampleUntilAcceptedT L W scaled dimN f) b *
          vlaw (sampleTryT L W scaled dimN) b {some none} := by
  have hM := (mf_sampleTry (Q := Unit) L W scaled dimN).outcome () b
  have hC : ∀ r : Option (Fin d → Num ℤ),
      CapFirst (r.elim (sampleUntilAcceptedT L W scaled dimN f) Tree.pure) := by
    rintro (_ | z)
    · exact Free.capFirst (free_sampleUntilAcceptedT L W scaled dimN f)
    · trivial
  rw [sampleUntilAcceptedT, Eops_bind_capFirst (mf_retryCont L W scaled dimN f) hC _ b hM b]
  congr 1
  have hf : ∀ o : Option (Option (Fin d → Num ℤ)),
      o.elim 0 (fun r => Eops (r.elim (sampleUntilAcceptedT L W scaled dimN f) Tree.pure) b) =
        ({some none} : Set (Option (Option (Fin d → Num ℤ)))).indicator
          (fun _ => Eops (sampleUntilAcceptedT L W scaled dimN f) b) o := by
    rintro (_ | _ | z) <;> simp
  simp_rw [hf, lintegral_indicator_const (measurableSet_singleton _)]

/-- Acceptance probability at least one half bounds the cost uniformly in fuel by
twice the bound on one attempt. -/
theorem Eops_sampleUntilAccepted_le (B : ENNReal)
    (hB : Eops (sampleTryT L W scaled dimN) b ≤ B)
    (hprob : vlaw (sampleTryT L W scaled dimN) b {some none} ≤ (2 : ENNReal)⁻¹) :
    ∀ f, Eops (sampleUntilAcceptedT L W scaled dimN f) b ≤ B + B
  | 0 => by simp [sampleUntilAcceptedT]
  | f + 1 => by
      rw [Eops_sampleUntilAccepted_succ]
      refine (add_le_add hB (mul_le_mul' (Eops_sampleUntilAccepted_le B hB hprob f) hprob)).trans ?_
      rw [← two_mul B, mul_comm (2 : ENNReal) B, mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by simp), mul_one]
      exact (mul_two B).symm.le

/-- Rejecting the first attempt forces the sampler with fuel one to stop. -/
theorem sampleTry_none_le_oneFuel_none :
    vlaw (sampleTryT L W scaled dimN) b {some none} ≤
      ((vlaw (sampleUntilAcceptedT L W scaled dimN 1) b).map (Option.map getZ)) {none} := by
  have hTry := (mf_sampleTry (Q := Unit) L W scaled dimN).outcome () b
  have hRetry := (mf_sampleUntilAccepted (Q := Unit) L W scaled dimN 1).outcome () b
  have hm := measurable_optionMap (measurable_getZ (k := d))
  rw [vlaw, vlaw, ← tapeLaw_map_exec _ _ hTry, ← tapeLaw_map_exec _ _ hRetry,
    Measure.map_map measurable_fst hTry, Measure.map_map measurable_fst hRetry,
    Measure.map_map hm (measurable_fst.comp hRetry),
    Measure.map_apply (measurable_fst.comp hTry) (measurableSet_singleton _),
    Measure.map_apply (hm.comp (measurable_fst.comp hRetry)) measurableSet_none]
  refine measure_mono fun t ht => ?_
  change (exec (sampleTryT L W scaled dimN) b t).1 = some none at ht
  change (exec (sampleUntilAcceptedT L W scaled dimN 1) b t).1.map getZ = none
  rw [sampleUntilAcceptedT, exec_bind]
  rcases ht' : exec (sampleTryT L W scaled dimN) b t with ⟨r, j, b', t'⟩
  rw [ht'] at ht
  simp only at ht
  subst r
  rfl

section Certified

variable {k : ℕ} {F : ttc.LRAFormula d k}

/-- The actual sealed sampler retries with probability at most one half on every
certified component. -/
theorem certified_sampleTry_rejection_le (hn : 21 ≤ d) (D : ttc.Decomposition F)
    (p : ttc.ApproxParams) (i : Fin D.componentCount) (b' : ℕ) :
    let K := paramsOf D p
    let P := D.component i
    vlaw (sampleTryT (loaded P) (walkC P K.scale K.epsPrime K.dim)
      (scaledOffsets (loaded P) K.scale).val K.dimN) b' {some none} ≤ (2 : ENNReal)⁻¹ := by
  dsimp only
  have hm : 0 < D.componentCount := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn0 : 0 < d := by omega
  have : NeZero d := ⟨ne_of_gt hn0⟩
  obtain ⟨hdimN, hdim, he, -, -, hs, -⟩ := paramsProg_val D p hm
  let P := D.component i
  let bp := ttc.GetPrecision D p.precisionEta
  have hK : Bornology.IsBounded (ttc.HitAndRunLaw.body (P.hitAndRunPresentation bp p.ε')) := by
    rw [body_eq]
    exact P.normalizedHitAndRun_bounded bp p.ε'
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆
      ttc.HitAndRunLaw.body (P.hitAndRunPresentation bp p.ε') := by
    rw [body_eq]
    exact Metric.ball_subset_closedBall.trans (P.normalizedHitAndRun_unitBall bp p.ε')
  let K := paramsOf D p
  refine (sampleTry_none_le_oneFuel_none (loaded P) (walkC P K.scale K.epsPrime K.dim)
    (scaledOffsets (loaded P) K.scale).val K.dimN b').trans ?_
  rw [sampler_eq_old P bp p.ε' K.scale K.epsPrime K.dim hs he hdim K.dimN hdimN hK hball b' 1,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply ArlibCommunity.Algorithms.CV18.measurable_some measurableSet_none]
  let μ := ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw P bp p.ε')
  let A := ttc.acceptedIntegers P bp
  have : IsProbabilityMeasure (ttc.normalizedHitAndRunContinuousLaw P bp p.ε') :=
    ttc.normalizedHitAndRunContinuousLaw_isProbabilityMeasure hn0 P bp p.ε'
  have : IsProbabilityMeasure μ := Arlib.KV97.isProbabilityMeasure_roundedMeasureLaw _
  have hpre : (some : (Fin d → ℤ) → Option (Fin d → ℤ)) ⁻¹' {none} = ∅ := by
    ext z
    simp
  simp only [hpre, measure_empty, smul_eq_mul, mul_zero, zero_add, pow_one,
    Measure.dirac_apply' _ measurableSet_none, Set.indicator_of_mem (Set.mem_singleton none),
    Pi.one_apply, mul_one]
  change μ Aᶜ ≤ _
  have h := ttc.certified_normalizedHitAndRun_acceptance_ge_half hn D p bp
    (ttc.getPrecisionChoice D p).adequate i
  rw [ttc.roundedAcceptanceProbability_val_eq, Measure.real] at h
  have hhalf : (2 : ENNReal)⁻¹ ≤ μ A := by
    apply (ENNReal.toReal_le_toReal (by simp) (measure_ne_top μ A)).mp
    simpa [one_div, ENNReal.toReal_inv] using h
  rw [measure_compl (Set.to_countable A).measurableSet (measure_ne_top μ A), measure_univ]
  exact (tsub_le_tsub_left hhalf 1).trans_eq (by norm_num)

end Certified

/-- The sampling loop charges at most one sampler cost, one append, one literal
and one increment for each pending copy. -/
theorem Eops_loopRounds_sampleBody_le (S : Tree d (Fin d → Num ℤ))
    (hm : ∀ (Q : Type) [MeasurableSpace Q], MeasFam fun _ : Q => S)
    (hS : Tree.Free S) (b : ℕ) (B : ENNReal) (hB : Eops S b ≤ B)
    (n : ℕ) (acc : List (Fin d → Num ℤ) × Num ℕ) :
    Eops (loopRounds (sampleBody S) n acc) b ≤ n * (B + 3) := by
  have hmf : MeasFam (sampleBody S) :=
    (mf_sampleBody (Q := Unit) S hm).comp
      (φ := fun a : List (Fin d → Num ℤ) × Num ℕ => ((), a))
      (measurable_const.prodMk measurable_id)
  have hcap (a : List (Fin d → Num ℤ) × Num ℕ) : CapFirst (sampleBody S a) :=
    Free.capFirst (Tree.Free.bind hS fun _ => Tree.Free.bind (free_compute _) fun _ =>
      Tree.Free.bind (free_compute _) fun _ => free_pure _)
  apply Eops_loopRounds_le hmf hcap b (B + 3) ?_ n acc
  intro a
  unfold sampleBody
  refine (Eops_bind_le_of_post (post_of_forall (Q := fun _ => True) (fun _ => trivial) _)
    (by simp) ?_ ?_ b b ((hm Unit).outcome () b) 3 ?_).trans (add_le_add hB le_rfl)
  · refine MeasFam.compute (mp_push measurable_const measurable_id) ?_
    refine MeasFam.compute (MP.const _) ?_
    exact MeasFam.pure (measurable_inl.comp (measurable_fst.snd.prodMk measurable_snd))
  · intro z
    exact Free.capFirst (Tree.Free.bind (free_compute _) fun _ =>
      Tree.Free.bind (free_compute _) fun _ => free_pure _)
  · intro z _
    apply Eops_le_of_exec_ops_le
    · exact (MeasFam.computeConst _ (MeasFam.computeConst _
        (MeasFam.pure measurable_const)) : MeasFam fun _ : Unit =>
          (compute (A.push a.1 z)).bind fun ys =>
            (compute (do let one ← A.lit (1 : ℕ); A.add a.2 one)).bind fun c =>
            Tree.pure (Sum.inl (ys, c) : (List (Fin d → Num ℤ) × Num ℕ) ⊕ Empty)).outcome () b
    · intro t
      simp [compute, Tree.bind, exec, opsTotal_add]

/-- Sampling after the halving loop pays for its walk constants, loop entry,
and all attempts, rounding, membership tests and appends for the pending copies. -/
theorem Eops_sampleT_le (hd : 0 < d) (f : ℕ) (K : Params) (L : Loaded d)
    (sc : Fin L.facets → Num ℝ) (b : ℕ)
    (h : Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ)
    (hc : vlaw (sampleTryT L (walkConstantsProg L K.scale K.epsPrime K.dim).val sc K.dimN) b
      {some none} ≤ (2 : ENNReal)⁻¹) :
    let c := walkConstantsProg L K.scale K.epsPrime K.dim
    let B := sampleTryOps d L.facets c.val.steps.get
    Eops (sampleT f K L sc h) b ≤ (opsTotal c.cost : ENNReal) +
      (1 + h.2.2.2.get * (2 * B + 3)) := by
  let c := walkConstantsProg L K.scale K.epsPrime K.dim
  let W := c.val
  let B := sampleTryOps d L.facets W.steps.get
  let S := sampleUntilAcceptedT L W sc K.dimN f
  let P := loopRounds (sampleBody S) h.2.2.2.get (h.2.1, h.2.2.1)
  let k := fun r : (List (Fin d → Num ℤ) × Num ℕ) ⊕ Empty =>
    (⟨h.1, (r.elim id Empty.elim).1, (r.elim id Empty.elim).2⟩ : State d)
  have hS : ∀ (Q : Type) [MeasurableSpace Q], MeasFam fun _ : Q => S := fun Q _ =>
    mf_sampleUntilAccepted L W sc K.dimN f
  have hfree := free_sampleUntilAcceptedT L W sc K.dimN f
  have hkm : Measurable k := State.measurable_mk measurable_const
    (measurable_fst.comp (measurable_id.sumElim measurable_from_top))
    (measurable_snd.comp (measurable_id.sumElim measurable_from_top))
  have hP : MeasFam fun _ : Unit => P :=
    (MeasFam.loopRounds (A := Unit) (body := fun _ => sampleBody S)
      (mf_sampleBody S hS) h.2.2.2.get).comp
      (φ := fun _ : Unit => ((), (h.2.1, h.2.2.1))) measurable_const
  have hPk : MeasFam fun _ : Unit => P.bind (fun r => Tree.pure (k r)) :=
    MeasFam.bind' hP (MeasFam.pure (hkm.comp measurable_snd))
  have htry := Eops_le_maxOps (sampleTryT L W sc K.dimN) b
    ((mf_sampleTry (Q := Unit) L W sc K.dimN).outcome () b)
  have htry' : Eops (sampleTryT L W sc K.dimN) b ≤ (B : ENNReal) := by
    exact htry.trans (ENat.toENNReal_le_natCast.mpr (maxOps_sampleTryT_le hd L W sc K.dimN))
  have hcost := Eops_sampleUntilAccepted_le L W sc K.dimN b (B : ENNReal) htry' hc f
  have hPcost := Eops_loopRounds_sampleBody_le S hS hfree b ((B : ENNReal) + B) hcost
    h.2.2.2.get (h.2.1, h.2.2.1)
  have hlast : Eops (P.bind (fun r => Tree.pure (k r))) b ≤ Eops P b :=
    (Eops_bind_le_of_post (post_of_forall (Q := fun _ => True) (fun _ => trivial) _)
      (by simp) (MeasFam.pure hkm) (fun _ => trivial) b b (hP.outcome () b) 0
      (fun _ _ => (Eops_pure (d := d) _ _).le)).trans_eq (add_zero _)
  let mark : Prog Unit := Charged.op (Op.num .loop) ()
  have hm : MeasFam fun _ : Unit => (compute mark).bind fun _ =>
      P.bind (fun r => Tree.pure (k r)) :=
    MeasFam.computeConst _ hPk
  change Eops ((compute c).bind fun _ => (compute mark).bind fun _ =>
    P.bind (fun r => Tree.pure (k r))) b ≤ _
  rw [Eops_compute_bind _ _ _ (hm.outcome () b), Eops_compute_bind _ _ _ (hPk.outcome () b),
    show opsTotal mark.cost = 1 from opsTotal_op _ _, Nat.cast_one]
  refine add_le_add le_rfl (add_le_add le_rfl (hlast.trans ?_))
  refine hPcost.trans_eq ?_
  ring

end ttc.Tape

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Planar.Program
import ttc.Analysis.Tape.ArithmeticOps
import ttc.Analysis.Tape.TTCTrees
import ttc.Analysis.Tape.CV18Component
import ttc.Analysis.MembershipCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCappedDominance
import ttc.Analysis.PlanarAreaLaw

/-! The planar estimator's charged tape execution and operation bound. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace ttc.Tape

open ttc.SealedRun (roundLaw tapeLaw)

open Arlib.Computation (Num Charged NumOp)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

def planarSquarePointT (K : PlanarConstants) : Tree 2 (NumPoint 2) :=
  unitT.bind fun u =>
  unitT.bind fun v =>
  (compute (planarCoordinateProg K u)).bind fun x =>
  (compute (planarCoordinateProg K v)).bind fun y =>
  .pure (Fin.cons x fun _ => y)

theorem agree_planarSquarePoint (K : PlanarConstants) :
    Agree (planarSquarePoint K) (interp (planarSquarePointT K)) :=
  Agree.bindT agree_unit fun _ => Agree.bindT agree_unit fun _ =>
    Agree.bindT (agree_run _) fun _ => Agree.bindT (agree_run _) fun _ => agree_pure _

def planarTrialT (K : PlanarConstants) (member : NumPoint 2 → Prog Bool) (count : Num ℕ) :
    Tree 2 (Num ℕ ⊕ Empty) :=
  (planarSquarePointT K).bind fun x =>
  (compute (member x)).bind fun inside =>
  if inside then
    (compute (A.lit (1 : ℕ))).bind fun one =>
    (compute (A.add count one)).bind fun count' =>
    .pure (.inl count')
  else .pure (.inl count)

theorem agree_planarTrial (K : PlanarConstants) (member : NumPoint 2 → Prog Bool) (count : Num ℕ) :
    Agree (planarTrial K member count) (interp (planarTrialT K member count)) :=
  Agree.bindT (agree_planarSquarePoint K) fun _ => Agree.bindT (agree_run _) fun inside =>
    agree_ite inside
      (Agree.bindT (agree_run _) fun _ => Agree.bindT (agree_run _) fun _ => agree_pure _)
      (agree_pure _)

def planarAreaT (member : NumPoint 2 → Prog Bool) (eps roundness p : Num ℝ) : Tree 2 (Num ℝ) :=
  (compute (planarConstantsProg eps roundness p)).bind fun K =>
  (compute (A.lit (0 : ℕ))).bind fun zero =>
  (loopTree K.trials (planarTrialT K member) zero).bind fun c =>
  compute (planarEstimateProg K (c.elim id Empty.elim))

theorem agree_planarArea (member : NumPoint 2 → Prog Bool) (eps roundness p : Num ℝ) :
    Agree (planarArea member eps roundness p) (interp (planarAreaT member eps roundness p)) :=
  Agree.bindT (agree_run _) fun K => Agree.bindT (agree_run _) fun zero =>
    Agree.bindT (agree_loop K.trials (agree_planarTrial K member) zero) fun _ => agree_run _

/-- The held point computed by two successive unit draws. -/
def planarHeldPoint (K : PlanarConstants) (u v : ℝ) : NumPoint 2 :=
  Fin.cons (planarCoordinateProg K (sealDraw u).val).val
    (fun _ => (planarCoordinateProg K (sealDraw v).val).val)

theorem exec_planarSquarePointT (K : PlanarConstants) (b : ℕ) (t : Tape 2) :
    exec (planarSquarePointT K) b t =
      (some (planarHeldPoint K (t 0).2.2 (t.tail 0).2.2), 6, b, t.tail.tail) := by
  simp [planarSquarePointT, planarHeldPoint, planarCoordinateProg, unitT, compute, Tree.bind, exec, opsTotal_add]

theorem exec_planarTrialT (K : PlanarConstants) (member : NumPoint 2 → Prog Bool)
    (acc : Num ℕ) (b : ℕ) (t : Tape 2) :
    let x := planarHeldPoint K (t 0).2.2 (t.tail 0).2.2
    let hit := (member x).val
    exec (planarTrialT K member acc) b t =
      (some (.inl (if hit then (A.add acc (A.lit (1 : ℕ)).val).val else acc)),
        6 + opsTotal (member x).cost + (if hit then 2 else 0), b, t.tail.tail) := by
  dsimp only [planarTrialT]
  rw [exec_bind, exec_planarSquarePointT]
  dsimp only
  split <;> simp [compute, Tree.bind, exec, *, Nat.add_assoc]

private theorem opsTotal_planarConstantsProg (eps roundness p : Num ℝ) :
    opsTotal (planarConstantsProg eps roundness p).cost = 16 := by
  simp [planarConstantsProg, A.mulLit, A.litDiv, A.ceil, A.log, Num.cost_ceil, Num.log,
    opsTotal_add, opsTotal_one]

private theorem opsTotal_planarEstimateProg (K : PlanarConstants) (acc : Num ℕ) :
    opsTotal (planarEstimateProg K acc).cost = 4 := by
  simp [planarEstimateProg, A.cast, Num.cast, opsTotal_add, opsTotal_one]

/-- Every run of the area estimator costs at most its fixed overhead plus
two draws, four coordinate operations, a membership test and two increment
operations per point. The membership routine supplies its own cost bound. -/
theorem exec_ops_planarAreaT (member : NumPoint 2 → Prog Bool) (eps roundness p : Num ℝ)
    (B : ℕ) (hB : ∀ x, opsTotal (member x).cost ≤ B) (b : ℕ) (t : Tape 2) :
    (exec (planarAreaT member eps roundness p) b t).2.1 ≤
      22 + (planarConstantsProg eps roundness p).val.trials.get * (8 + B) := by
  let K := (planarConstantsProg eps roundness p).val
  let z := (A.lit (0 : ℕ)).val
  have hb (acc : Num ℕ) (b' : ℕ) (t' : Tape 2) :
      (exec (planarTrialT K member acc) b' t').2.1 ≤ 8 + B := by
    rw [exec_planarTrialT]
    dsimp only
    have := hB (planarHeldPoint K (t' 0).2.2 (t'.tail 0).2.2)
    split <;> omega
  have hrs : ∀ k acc b' t',
      (exec (loopRounds (planarTrialT K member) k acc) b' t').2.1 ≤ k * (8 + B) := by
    intro k
    induction k with
    | zero => intros; simp [loopRounds, exec]
    | succ k ih =>
      intro acc b' t'
      rw [loopRounds, exec_bind, exec_planarTrialT]
      dsimp only
      rw [Nat.succ_mul]
      have hnext := ih (if (member (planarHeldPoint K (t' 0).2.2 (t'.tail 0).2.2)).val
        then (A.add acc (A.lit (1 : ℕ)).val).val else acc) b' t'.tail.tail
      have hcur := hb acc b' t'
      rw [exec_planarTrialT] at hcur
      dsimp only at hcur
      exact (Nat.add_le_add hcur hnext).trans_eq (Nat.add_comm _ _)
  have h := hrs K.trials.get z b t
  change _ ≤ 22 + K.trials.get * (8 + B)
  simp only [planarAreaT, compute, Tree.bind]
  change opsTotal (planarConstantsProg eps roundness p).cost +
      (opsTotal (A.lit (0 : ℕ)).cost +
       (opsTotal (Charged.op (Op.num .loop) () : Prog Unit).cost +
        (exec ((loopRounds (planarTrialT K member) K.trials.get z).bind
          fun c => Tree.step (planarEstimateProg K (c.elim id Empty.elim)) Tree.pure) b t).2.1)) ≤ _
  rw [opsTotal_planarConstantsProg, opsTotal_lit, opsTotal_op, exec_bind]
  rcases hr : exec (loopRounds (planarTrialT K member) K.trials.get z) b t with ⟨r, j, b', t'⟩
  rw [hr] at h
  dsimp only at h
  cases r <;> simp [exec, opsTotal_planarEstimateProg] <;> omega

theorem exec_ops_planarAreaT_allFacets (r : ℕ) (a : Fin r → NumPoint 2) (o : Fin r → Num ℝ)
    (eps roundness p : Num ℝ) (b : ℕ) (t : Tape 2) :
    (exec (planarAreaT (allFacets r a o) eps roundness p) b t).2.1 ≤
      22 + (planarConstantsProg eps roundness p).val.trials.get * (8 + 4 * r) :=
  exec_ops_planarAreaT _ _ _ _ (4 * r)
    (fun x => (opsTotal_allFacets (by decide) r a o x).le) b t

/-! ## Measurability and budget independence -/

theorem mf_planarCoordinate (K : PlanarConstants) : MP (planarCoordinateProg K) := by
  unfold planarCoordinateProg
  exact MP.bind' (mp_mul measurable_const measurable_id) (mp_sub measurable_snd measurable_const)

theorem mf_planarSquarePoint (K : PlanarConstants) :
    MeasFam (fun _ : Unit => planarSquarePointT K) := by
  unfold planarSquarePointT
  refine MeasFam.unitT (MeasFam.unitT ?_)
  refine MeasFam.compute ((mf_planarCoordinate K).comp measurable_fst.snd) ?_
  refine MeasFam.compute ((mf_planarCoordinate K).comp measurable_fst.snd) ?_
  exact MeasFam.pure (measurable_fin_cons.comp
    (measurable_fst.snd.prodMk (measurable_pi_iff.mpr fun _ => measurable_snd)))

theorem mf_planarTrial (K : PlanarConstants) {member : NumPoint 2 → Prog Bool}
    (hmember : MP member) :
    MeasFam (planarTrialT K member) := by
  unfold planarTrialT
  have hpt : MeasFam (fun _ : Num ℕ => planarSquarePointT K) :=
    (mf_planarSquarePoint K).comp (measurable_const (a := ()))
  refine MeasFam.bind' hpt ?_
  refine MeasFam.compute (hmember.comp measurable_snd) ?_
  refine MeasFam.iteB measurable_snd ?_ (MeasFam.pure (measurable_inl.comp measurable_fst.fst))
  refine MeasFam.computeConst (A.lit (1 : ℕ)) ?_
  have hInc : MP (fun a : (Num ℕ × NumPoint 2) × Bool =>
      A.add a.1.1 (A.lit (1 : ℕ)).val) := mp_addN measurable_fst.fst measurable_const
  exact MeasFam.compute hInc (k := fun _ c => Tree.pure (Sum.inl c : Num ℕ ⊕ Empty))
    (MeasFam.pure (measurable_inl.comp measurable_snd))

theorem mf_planarEstimate (K : PlanarConstants) : MP (planarEstimateProg K) := by
  unfold planarEstimateProg
  refine MP.bind' (mp_cast measurable_id) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (mp_div measurable_fst.snd measurable_snd) ?_
  exact mp_mul measurable_const measurable_snd

theorem mf_planarArea {member : NumPoint 2 → Prog Bool} (hmember : MP member)
    (eps roundness p : Num ℝ) : MeasFam fun _ : Unit => planarAreaT member eps roundness p := by
  unfold planarAreaT
  let K := (planarConstantsProg eps roundness p).val
  let z := (A.lit (0 : ℕ)).val
  refine MeasFam.computeConst (planarConstantsProg eps roundness p) ?_
  refine MeasFam.computeConst (A.lit (0 : ℕ)) ?_
  have hloop : MeasFam (fun _ : Unit => loopTree K.trials (planarTrialT K member) z) :=
    MeasFam.loopTree (count := fun _ : Unit => K.trials) measurable_const
      (body := fun _ => planarTrialT K member)
      ((mf_planarTrial K hmember).comp measurable_snd) (init := fun _ => z) measurable_const
  refine MeasFam.bind' hloop ?_
  apply MeasFam.computeEnd
  apply (mf_planarEstimate K).comp
  exact (measurable_id.sumElim (measurable_of_countable (Empty.elim : Empty → Num ℕ))).comp
    measurable_snd

theorem free_planarArea (member : NumPoint 2 → Prog Bool) (eps roundness p : Num ℝ) :
    Free (planarAreaT member eps roundness p) := by
  unfold planarAreaT
  refine Free.bind (free_compute _) fun K => Free.bind (free_compute _) fun z => ?_
  apply Free.bind _ (fun _ => free_compute _)
  exact free_loopRounds (fun acc =>
    Free.bind (Free.bind free_unitT fun _ => Free.bind free_unitT fun _ =>
      Free.bind (free_compute _) fun _ => Free.bind (free_compute _) fun _ => free_pure _) fun _ =>
      Free.bind (free_compute _) fun inside =>
        free_ite inside (Free.bind (free_compute _) fun _ =>
          Free.bind (free_compute _) fun _ => free_pure _) (free_pure _)) _ _

/-! ## The count and the output of the loop -/

private def planarFlags (test : ℝ × ℝ → Bool) : (n : ℕ) → Tape 2 → Fin n → Bool
  | 0, _ => Fin.elim0
  | n + 1, t => Fin.cons (test ((t 0).2.2, (t.tail 0).2.2)) (planarFlags test n t.tail.tail)

private theorem hits_cons {n : ℕ} (b : Bool) (v : Fin n → Bool) :
    Planar.hits (Fin.cons b v) = (if b then 1 else 0) + Planar.hits v := by
  have hs {m : ℕ} (f : Fin m → Bool) :
      Planar.hits f = ∑ i, (if f i = true then 1 else 0 : ℕ) := by
    simpa only [Planar.hits, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun i => f i = true) Finset.univ).symm
  simp only [hs, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

private theorem exec_value_planarLoop (K : PlanarConstants) (member : NumPoint 2 → Prog Bool)
    (test : ℝ × ℝ → Bool)
    (htest : ∀ u v, (member (planarHeldPoint K u v)).val = test (u, v)) :
    ∀ n (acc : Num ℕ) b t,
    ((exec (loopRounds (planarTrialT K member) n acc) b t).1.map
      (fun c => (c.elim id Empty.elim).get)) =
      some (acc.get + Planar.hits (planarFlags test n t))
  | 0, acc, b, t => by simp [loopRounds, exec, Planar.hits]
  | n + 1, acc, b, t => by
    rw [loopRounds, exec_bind, exec_planarTrialT]
    dsimp only
    rw [htest, Sum.elim_inl, exec_value_planarLoop K member test htest, planarFlags, hits_cons]
    split <;> simp [A.add, A.lit, Num.get_add, Num.get_lit, Nat.add_assoc]

private theorem val_planarEstimateProg (K : PlanarConstants) (acc : Num ℕ) :
    (planarEstimateProg K acc).val.get =
      K.boxArea.get * ((acc.get : ℝ) / (K.trials.get : ℝ)) := by
  simp [planarEstimateProg, Charged.val_bind, A.cast, A.div, A.mul,
    Num.get_cast, Num.get_div, Num.get_mul]

private theorem exec_value_planarAreaT (member : NumPoint 2 → Prog Bool)
    (eps roundness p : Num ℝ) (test : ℝ × ℝ → Bool)
    (htest : ∀ u v,
      (member (planarHeldPoint (planarConstantsProg eps roundness p).val u v)).val = test (u, v))
    (b : ℕ) (t : Tape 2) :
    ((exec (planarAreaT member eps roundness p) b t).1.map Num.get) =
      some (Planar.estimateFromHits (planarConstantsProg eps roundness p).val.boxArea.get
        (planarFlags test (planarConstantsProg eps roundness p).val.trials.get t)) := by
  let K := (planarConstantsProg eps roundness p).val
  let z := (A.lit (0 : ℕ)).val
  have h := exec_value_planarLoop K member test htest K.trials.get z b t
  change (exec ((loopRounds (planarTrialT K member) K.trials.get z).bind
    fun c => compute (planarEstimateProg K (c.elim id Empty.elim))) b t).1.map Num.get = _
  rw [exec_bind]
  rcases hr : exec (loopRounds (planarTrialT K member) K.trials.get z) b t with ⟨r, j, b', t'⟩
  rw [hr] at h
  dsimp only at h
  rcases r with _ | a
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    have hz : z.get = 0 := rfl
    rw [hz, zero_add] at h
    simp only [compute, exec, Option.map_some, val_planarEstimateProg, h,
      Planar.estimateFromHits, K]

private theorem measurable_planarFlags {test : ℝ × ℝ → Bool} (ht : Measurable test) :
    ∀ n, Measurable (planarFlags test n)
  | 0 => measurable_const
  | n + 1 => by
    have hu : Measurable (fun t : Tape 2 => (t 0).2.2) :=
      (measurable_snd.comp measurable_snd).comp (measurable_pi_apply 0)
    apply measurable_pi_iff.mpr
    refine Fin.cases ?_ (fun i => ?_)
    · simpa [planarFlags, Function.comp_def] using ht.comp (hu.prodMk (hu.comp measurable_tape_tail))
    · simpa [planarFlags, Function.comp_def] using (measurable_pi_apply i).comp
        ((measurable_planarFlags ht n).comp (measurable_tape_tail.comp measurable_tape_tail))

/-- The two uniforms used for a point are independent of the next trial's tape. -/
private theorem map_unit_pair_and_tail {Y : Type} [MeasurableSpace Y]
    {g : Tape 2 → Y} (hg : Measurable g) :
    (tapeLaw 2).map (fun t => (((t 0).2.2, (t.tail 0).2.2), g t.tail.tail)) =
      (uniformUnit.prod uniformUnit).prod ((tapeLaw 2).map g) := by
  let u : Round 2 → ℝ := fun r => r.2.2
  have hu : Measurable u := measurable_snd.comp measurable_snd
  let h : Tape 2 → ℝ × Y := fun t => (u (t 0), g t.tail)
  have hh : Measurable h := (hu.comp (measurable_pi_apply 0)).prodMk
    (hg.comp measurable_tape_tail)
  let e : (ℝ × ℝ) × Y ≃ᵐ ℝ × ℝ × Y := MeasurableEquiv.prodAssoc
  change (tapeLaw 2).map (e.symm ∘ fun t => (u (t 0), h t.tail)) = _
  have hh' : Measurable (fun t : Tape 2 => (u (t 0), h t.tail)) :=
    (hu.comp (measurable_pi_apply 0)).prodMk (hh.comp measurable_tape_tail)
  rw [← Measure.map_map e.symm.measurable hh',
    tapeLaw_map_head_tail hu hh, show (tapeLaw 2).map h = _ from tapeLaw_map_head_tail hu hg,
    roundLaw_map_unit]
  exact (measurePreserving_prodAssoc uniformUnit uniformUnit ((tapeLaw 2).map g)).symm.map_eq

private theorem tapeLaw_map_planarFlags (P : PolytopeData 2) :
    ∀ n, (tapeLaw 2).map (planarFlags (Planar.hit P) n) =
      Measure.pi fun _ : Fin n => bernoulliMeasure true false (Planar.hitProbability P)
  | 0 => by
    rw [Measure.pi_of_empty (x := fun i => i.elim0)]
    simp [planarFlags, Measure.map_const]
  | n + 1 => by
    let μ := bernoulliMeasure true false (Planar.hitProbability P)
    let f := Planar.hit P
    let g := planarFlags f n
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Bool) 0).symm
    have hf : Measurable f := Planar.measurable_hit P
    have hg : Measurable g := measurable_planarFlags hf n
    have hu : Measurable (fun t : Tape 2 => (t 0).2.2) :=
      (measurable_snd.comp measurable_snd).comp (measurable_pi_apply 0)
    have hpair : Measurable (fun t : Tape 2 => (((t 0).2.2, (t.tail 0).2.2), g t.tail.tail)) :=
      (hu.prodMk (hu.comp measurable_tape_tail)).prodMk
        (hg.comp (measurable_tape_tail.comp measurable_tape_tail))
    have heq : planarFlags f (n + 1) =
        e ∘ Prod.map f id ∘ fun (t : Tape 2) => (((t 0).2.2, (t.tail 0).2.2), g t.tail.tail) := by
      funext t i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [planarFlags, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      · simp [planarFlags, e, MeasurableEquiv.piFinSuccAbove_symm_apply, g]
    rw [heq, ← Measure.map_map e.measurable ((hf.prodMap measurable_id).comp hpair),
      ← Measure.map_map (hf.prodMap measurable_id) hpair]
    -- Push the law through the test and the insertion at index zero.
    rw [map_unit_pair_and_tail hg, ← Measure.map_prod_map _ _ hf measurable_id,
      Planar.map_hit P, Measure.map_id, tapeLaw_map_planarFlags P n]
    exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm.map_eq

private theorem planarConstants_get (P : PolytopeData 2) (eps roundness p : Num ℝ)
    (hr : roundness.get = CommunityCV18.roundness P) :
    let K := (planarConstantsProg eps roundness p).val
    K.radius.get = Planar.radius P ∧ K.width.get = 2 * Planar.radius P ∧
      K.boxArea.get = Planar.boxArea P ∧
      K.trials.get = Planar.trialCount (Planar.boxArea P) eps.get p.get := by
  have h : 2 * roundness.get = Planar.radius P ^ 2 := by
    rw [hr, CommunityCV18.roundness, Planar.radius]
    push_cast
    ring
  have hs : Real.sqrt (Planar.radius P * Planar.radius P) = Planar.radius P := by
    rw [← pow_two, Real.sqrt_sq ((by norm_num : (0 : ℝ) ≤ 1).trans (Planar.radius_one_le P))]
  simp only [planarConstantsProg, A.mulLit, A.litDiv, A.lit, A.div, A.mul, A.sqrt, A.log, A.ceil,
    Charged.val_bind, Charged.val_pure, Num.get_mul, Num.get_div, Num.get_sqrt, Num.get_log,
    Num.get_ceil, Num.get_lit, h, Planar.boxArea, Planar.trialCount, pow_two, hs, and_self]

private theorem planarHeldPoint_get (K : PlanarConstants) (R : ℝ)
    (hR : K.radius.get = R) (hW : K.width.get = 2 * R) (u v : ℝ) :
    (WithLp.toLp 2 (fun i => (planarHeldPoint K u v i).get) : Planar.Point) =
      Planar.pointFromUnits R (u, v) := by
  apply WithLp.ofLp_injective
  funext i
  have hget (x : ℝ) : (planarCoordinateProg K (sealDraw x).val).val.get =
      Planar.coordinate R x := by
    simp [planarCoordinateProg, A.mul, A.sub, Num.get_mul, Num.get_sub,
      Charged.val_bind, get_sealDraw, hW, hR, Planar.coordinate]
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hget u
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    exact hget v

/-- On TTC's actual random tape the charged planar estimator has the direct
area estimator law. There is no tape adapter or CV18 call in this branch. -/
theorem planarArea_component_map (P : PolytopeData 2) (eps roundness p : Num ℝ)
    (hr : roundness.get = CommunityCV18.roundness P) (b : ℕ) :
    (tapeLaw 2).map
      (fun t => (runFrom (planarArea
        (allFacets P.presentation.facetCount (loaded P).normal (cv18Off P)) eps roundness p)
        (Oracle.withBudget t b)).val.1.map Num.get) =
      (Planar.areaLaw P eps.get p.get).map some := by
  classical
  let K := (planarConstantsProg eps roundness p).val
  let member := allFacets P.presentation.facetCount (loaded P).normal (cv18Off P)
  obtain ⟨hR, hW, hB, hn⟩ := planarConstants_get P eps roundness p hr
  have htest (u v : ℝ) : (member (planarHeldPoint K u v)).val = Planar.hit P (u, v) := by
    have hm := congrFun (memberOracle_cv18 P)
      (WithLp.toLp 2 (fun i => (planarHeldPoint K u v i).get))
    apply Bool.eq_iff_iff.mpr
    rw [Planar.hit, decide_eq_true_eq, ← CommunityCV18.query_eq_true_iff,
      ← planarHeldPoint_get K _ hR hW, ← hm]
    simp only [memberOracle, val_allFacets_iff, ofPt, get_sealVector, member]
  have hfun : (fun t => (runFrom (planarArea member eps roundness p)
      (Oracle.withBudget t b)).val.1.map Num.get) =
      (fun v => some (Planar.estimateFromHits (Planar.boxArea P) v)) ∘
        planarFlags (Planar.hit P) (Planar.trialCount (Planar.boxArea P) eps.get p.get) := by
    funext t
    rw [(agree_planarArea member eps roundness p).run b t |>.1]
    have he := exec_value_planarAreaT member eps roundness p (Planar.hit P) htest b t
    rw [hB, hn] at he
    exact he
  change (tapeLaw 2).map (fun t => (runFrom (planarArea member eps roundness p)
    (Oracle.withBudget t b)).val.1.map Num.get) = _
  rw [hfun, ← Measure.map_map (measurable_of_countable _)
    (measurable_planarFlags (Planar.measurable_hit P) _), tapeLaw_map_planarFlags, Planar.areaLaw]
  exact (Measure.map_map (ArlibCommunity.Algorithms.CV18.measurable_some (α := ℝ))
    (measurable_of_countable _)).symm

/-- The planar call's result law in the form used in the component-step proof. -/
theorem vlaw_planarArea_component (P : PolytopeData 2) (eps roundness p : Num ℝ)
    (hr : roundness.get = CommunityCV18.roundness P) (b : ℕ) :
    (vlaw (planarAreaT (allFacets P.presentation.facetCount (loaded P).normal (cv18Off P))
        eps roundness p) b).map (Option.map Num.get) =
      (Planar.areaLaw P eps.get p.get).map some := by
  let member := allFacets P.presentation.facetCount (loaded P).normal (cv18Off P)
  let tr := planarAreaT member eps roundness p
  have hmem : MP member := mp_allFacets _ _ _ measurable_id
  have hm : Measurable fun t => outcome (exec tr b t) :=
    (mf_planarArea hmem eps roundness p).outcome () b
  have hg : Measurable (Option.map (Num.get : Num ℝ → ℝ)) :=
    measurable_optionMap Num.measurable_get
  have hfun : (fun t => Option.map Num.get (outcome (exec tr b t)).1) =
      fun t => (runFrom (planarArea member eps roundness p) (Oracle.withBudget t b)).val.1.map
        Num.get := by
    funext t
    rw [(agree_planarArea member eps roundness p).run b t |>.1]
    rfl
  change ((law tr b).map Prod.fst).map (Option.map Num.get) = _
  rw [← tapeLaw_map_exec tr b hm, Measure.map_map measurable_fst hm,
    Measure.map_map hg (measurable_fst.comp hm)]
  exact congrArg ((tapeLaw 2).map) hfun |>.trans (planarArea_component_map P eps roundness p hr b)

/-- The charged program on a normalized component, with every facet test included.
The expression on the right reads only the certified input geometry and tolerances. -/
theorem planarArea_component_ops_le (P : PolytopeData 2) (eps roundness p : Num ℝ)
    (hr : roundness.get = CommunityCV18.roundness P) (b : ℕ) (t : Tape 2) :
    opsTotal (runFrom (planarArea
      (allFacets P.presentation.facetCount (loaded P).normal (cv18Off P)) eps roundness p)
      (Oracle.withBudget t b)).cost ≤
      22 + Planar.trialCount (Planar.boxArea P) eps.get p.get *
        (8 + 4 * P.presentation.facetCount) := by
  rw [(agree_planarArea _ _ _ _).run b t |>.2]
  have h := exec_ops_planarAreaT_allFacets P.presentation.facetCount (loaded P).normal
    (cv18Off P) eps roundness p b t
  rw [(planarConstants_get P eps roundness p hr).2.2.2] at h
  exact h

/-- Relative-error accuracy of the actual charged planar computation. -/
theorem planarArea_component_accuracy (P : PolytopeData 2) (eps roundness p : Num ℝ)
    (hr : roundness.get = CommunityCV18.roundness P)
    (he : 0 < eps.get) (he1 : eps.get ≤ 1) (hp : 0 < p.get) (hp1 : p.get ≤ 1) (b : ℕ) :
    ((tapeLaw 2).map
      (fun t => (runFrom (planarArea
        (allFacets P.presentation.facetCount (loaded P).normal (cv18Off P)) eps roundness p)
        (Oracle.withBudget t b)).val.1.map Num.get)).real
      (ArlibCommunity.Algorithms.CV18.optionSomeEvent
        (Arlib.relErr eps.get (volume P.cv18Body).toReal)) ≥ 1 - p.get := by
  have hm := ArlibCommunity.Algorithms.CV18.measurable_some (α := ℝ)
  have hset := ArlibCommunity.Algorithms.CV18.measurableSet_optionSomeEvent
    (measurableSet_Icc (a := (1 - eps.get) * (volume P.cv18Body).toReal)
      (b := (1 + eps.get) * (volume P.cv18Body).toReal))
  rw [planarArea_component_map P eps roundness p hr b, measureReal_def, Measure.map_apply hm hset,
    ← measureReal_def]
  exact Planar.areaLaw_accuracy P he he1 hp hp1

end ttc.Tape

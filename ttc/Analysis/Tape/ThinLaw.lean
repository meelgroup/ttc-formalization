/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.RetryLaw
import ttc.Analysis.CoinBlockLaw

/-!
# Thinning keeps each copy independently

`filterCopiesT keep X` asks `keep` about each copy of `X` in turn.  When every answer is read
from one round of the tape (a fair coin, or a uniform number below a threshold), the copies
kept are an independent selection (`vlaw_filterCopiesT`): copy `i` is kept with the law of
one answer, independently.

* with fair coins (the halving loop), each copy is kept with probability `1/2`
  (`vlaw_filterCopiesT_coin`);
* with a uniform number below `q` (the rate check), with probability `q`
  (`vlaw_filterCopiesT_below`); at `q = 2^{-k}` this is the old model's survival of `k` fair
  rounds (`bernoulli_survivalProbability`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc.SealedRun (roundLaw tapeLaw)
open ArlibCommunity.Algorithms.CV18 (measurable_some)

variable {d : ℕ}

/-! ## Selections -/

/-- The entries of `l` whose flag is set, in order. -/
def selectBy {α : Type} : (l : List α) → (Fin l.length → Bool) → List α
  | [], _ => []
  | x :: xs, c => if c 0 then x :: selectBy xs (Fin.tail c) else selectBy xs (Fin.tail c)

/-! ## What the filter computes -/

/-- One copy's step of the filter. -/
def filterStep (keep : (Fin d → Num ℤ) → Tree d Bool) (one : Num ℕ)
    (acc : List (Fin d → Num ℤ) × Num ℕ) (x : Fin d → Num ℤ) :
    Tree d (List (Fin d → Num ℤ) × Num ℕ) :=
  (compute (A.cell x)).bind fun x =>
    (keep x).bind fun k =>
      if k then
        (compute (A.push acc.1 x)).bind fun ys =>
          (compute (A.add acc.2 one)).bind fun c => .pure (ys, c)
      else .pure acc

theorem filterCopiesT_eq (keep : (Fin d → Num ℤ) → Tree d Bool) (X : List (Fin d → Num ℤ)) :
    filterCopiesT keep X =
      Tree.step (A.lit (0 : ℕ)) fun zero => Tree.step (A.lit (1 : ℕ)) fun one =>
        X.foldlM (filterStep keep one) ([], zero) := rfl

/-- **The fold, on a tape where each answer is read from one round**: the copies kept are
those whose round's answer `κ` is `true`. -/
theorem exec_foldlM_filterStep {keep : (Fin d → Num ℤ) → Tree d Bool} {κ : Round d → Bool}
    (hkeep : ∀ x b t, ∃ j, exec (keep x) b t = (some (κ (t 0)), j, b, t.tail))
    (one : Num ℕ) (hone : one.get = 1) :
    ∀ (X : List (Fin d → Num ℤ)) (acc : List (Fin d → Num ℤ) × Num ℕ) (b : ℕ) (t : Tape d),
      Option.map (fun r : List (Fin d → Num ℤ) × Num ℕ => (r.1, r.2.get))
          (exec (X.foldlM (filterStep keep one) acc) b t).1 =
        some (acc.1 ++ selectBy X (fun i => κ (t i)),
          acc.2.get + (selectBy X (fun i => κ (t i))).length)
  | [], acc, b, t => by simp [selectBy, exec]
  | x :: xs, acc, b, t => by
      obtain ⟨j, hj⟩ := hkeep x b t
      rw [List.foldlM_cons]
      show Option.map _ (exec ((filterStep keep one acc x).bind _) b t).1 = _
      rw [exec_bind]
      have hstep : exec (filterStep keep one acc x) b t =
          ((some (if κ (t 0) then (acc.1 ++ [x], (A.add acc.2 one).val) else acc)),
            (exec (filterStep keep one acc x) b t).2.1, b, t.tail) := by
        obtain ⟨j', hj'⟩ := hkeep (A.cell x).val b t
        simp only [filterStep, compute, Tree.bind, exec]
        rw [exec_bind, hj']
        cases κ (t 0) <;> simp [exec, A.cell, ttc.Model.Operations.cell, A.push,
          ttc.Model.Operations.push]
      rw [hstep]
      simp only
      have ih := exec_foldlM_filterStep hkeep one hone xs
        (if κ (t 0) then (acc.1 ++ [x], (A.add acc.2 one).val) else acc) b t.tail
      rw [ih]
      have htail : (Fin.tail fun i : Fin (xs.length + 1) => κ (t i)) =
          fun i : Fin xs.length => κ (t.tail i) := rfl
      cases h : κ (t 0)
      · simp only [selectBy, Fin.val_zero, h, Bool.false_eq_true, ite_false, htail]
        rfl
      · simp only [selectBy, Fin.val_zero, h, ite_true, List.length_cons, htail, A.add, Num.get_add, hone,
          List.append_assoc, List.singleton_append]
        congr 2
        omega


theorem measurable_vecRounds {X : Type} [MeasurableSpace X] {κ : Round d → X} (hκ : Measurable κ)
    (k : ℕ) : Measurable fun t : Tape d => fun i : Fin k => κ (t i) :=
  measurable_pi_iff.mpr fun _ => hκ.comp (measurable_pi_apply _)

/-- **The filter's law**: copy `i` is kept with the law of one answer, independently. -/
theorem vlaw_filterCopiesT {keep : (Fin d → Num ℤ) → Tree d Bool} {κ : Round d → Bool}
    (hκ : Measurable κ) (hkeep : ∀ x b t, ∃ j, exec (keep x) b t = (some (κ (t 0)), j, b, t.tail))
    (X : List (Fin d → Num ℤ)) (b : ℕ)
    (hm : Measurable fun t => outcome (exec (filterCopiesT keep X) b t)) :
    (vlaw (filterCopiesT keep X) b).map (Option.map fun r => (r.1, r.2.get)) =
      (Measure.pi fun _ : Fin X.length => (roundLaw d).map κ).map
        fun c => some (selectBy X c, (selectBy X c).length) := by
  have hv : Measurable (Option.map fun r : List (Fin d → Num ℤ) × Num ℕ => (r.1, r.2.get)) :=
    measurable_optionMap (measurable_fst.prodMk (Num.measurable_get.comp measurable_snd))
  have hsel : Measurable fun c : Fin X.length → Bool =>
      (some (selectBy X c, (selectBy X c).length) : Option (List (Fin d → Num ℤ) × ℕ)) :=
    measurable_of_countable _
  have hfun : (fun t => Option.map (fun r : List (Fin d → Num ℤ) × Num ℕ => (r.1, r.2.get))
      (outcome (exec (filterCopiesT keep X) b t)).1) =
      (fun c => some (selectBy X c, (selectBy X c).length)) ∘
        fun t : Tape d => fun i : Fin X.length => κ (t i) := by
    funext t
    have := exec_foldlM_filterStep hkeep (A.lit (1 : ℕ)).val rfl X ([], (A.lit (0 : ℕ)).val) b t
    simp only [List.nil_append, A.lit, Num.get_lit, zero_add] at this
    exact this
  rw [vlaw, ← tapeLaw_map_exec _ b hm, Measure.map_map measurable_fst hm,
    Measure.map_map hv (measurable_fst.comp hm)]
  change (tapeLaw d).map (fun t => Option.map (fun r : List (Fin d → Num ℤ) × Num ℕ =>
    (r.1, r.2.get)) (outcome (exec (filterCopiesT keep X) b t)).1) = _
  rw [hfun, ← Measure.map_map hsel (measurable_vecRounds hκ _), tapeLaw_map_vec hκ]

/-! ## Fair coins -/

theorem exec_coinT_keep (x : Fin d → Num ℤ) (b : ℕ) (t : Tape d) :
    ∃ j, exec ((fun _ => coinT) x : Tree d Bool) b t = (some ((t 0).1), j, b, t.tail) :=
  ⟨1, rfl⟩

/-- **The halving loop's filter keeps each copy with probability `1/2`, independently.** -/
theorem vlaw_filterCopiesT_coin (X : List (Fin d → Num ℤ)) (b : ℕ) :
    (vlaw (filterCopiesT (fun _ => coinT) X) b).map (Option.map fun r => (r.1, r.2.get)) =
      (Measure.pi fun _ : Fin X.length => fairCoinLaw).map
        fun c => some (selectBy X c, (selectBy X c).length) := by
  have hm : Measurable fun t => outcome (exec (filterCopiesT (d := d) (fun _ => coinT) X) b t) :=
    (mf_filterCopies (Q := Unit) (keep := fun _ _ => coinT) (MeasFam.coinT (MeasFam.pure
      measurable_snd)) (X := fun _ => X) measurable_const).outcome () b
  rw [vlaw_filterCopiesT measurable_fst exec_coinT_keep X b hm, roundLaw_map_coin]

/-! ## A uniform number below a threshold -/

theorem measurable_decide_lt_const (q : ℝ) : Measurable fun u : ℝ => decide (u < q) :=
  measurable_to_countable' fun c => by
    cases c
    · convert (measurableSet_Iio (a := q)).compl using 1
      ext u; simp
    · convert measurableSet_Iio (a := q) using 1
      ext u; simp

/-- `u < q` for a uniform `u`: a coin showing `true` with probability `q`. -/
theorem uniformUnit_map_lt {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    uniformUnit.map (fun u => decide (u < q)) = bernoulliMeasure true false ⟨q, h0, h1⟩ := by
  have hm := measurable_decide_lt_const q
  have htrue : uniformUnit.map (fun u => decide (u < q)) {true} = ENNReal.ofReal q := by
    rw [Measure.map_apply hm (measurableSet_singleton true),
      Measure.restrict_apply' measurableSet_Icc]
    have : (fun u : ℝ => decide (u < q)) ⁻¹' {true} ∩ Icc 0 1 = Ico 0 q := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, decide_eq_true_eq, mem_Icc,
        mem_Ico]
      constructor
      · rintro ⟨hu, h0', _⟩; exact ⟨h0', hu⟩
      · rintro ⟨h0', hu⟩; exact ⟨hu, h0', (hu.trans_le h1).le⟩
    rw [this, Real.volume_Ico, sub_zero]
  refine Measure.ext_iff_singleton.mpr fun c => ?_
  have hb : bernoulliMeasure true false (⟨q, h0, h1⟩ : unitInterval) {true} = ENNReal.ofReal q := by
    rw [bernoulliMeasure_apply _ (measurableSet_singleton true)]
    simp only [Set.mem_singleton_iff, Bool.false_eq_true, ite_false, ite_true, ENNReal.ofReal,
      Real.toNNReal_of_nonneg h0]
    rfl
  have hprob : IsProbabilityMeasure (uniformUnit.map fun u => decide (u < q)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  cases c
  · have hc : ({false} : Set Bool) = {true}ᶜ := by ext x; cases x <;> simp
    rw [hc, prob_compl_eq_one_sub (measurableSet_singleton true),
      prob_compl_eq_one_sub (measurableSet_singleton true), htrue, hb]
  · rw [htrue, hb]

theorem exec_below_keep (q : Num ℝ) (x : Fin d → Num ℤ) (b : ℕ) (t : Tape d) :
    ∃ j, exec ((fun _ => unitT.bind fun u => compute (A.lt u q)) x : Tree d Bool) b t =
      (some (decide ((t 0).2.2 < q.get)), j, b, t.tail) := by
  refine ⟨1 + (opsTotal (A.lt (sealDraw (t 0).2.2).val q).cost + 0), ?_⟩
  show (some (A.lt (sealDraw (t 0).2.2).val q).val, _, b, t.tail) = _
  rw [val_Alt, get_sealDraw]
  rfl

/-- **The rate check's filter keeps each copy with probability `q`, independently.** -/
theorem vlaw_filterCopiesT_below (q : Num ℝ) (h0 : 0 ≤ q.get) (h1 : q.get ≤ 1)
    (X : List (Fin d → Num ℤ)) (b : ℕ) :
    (vlaw (filterCopiesT (fun _ => unitT.bind fun u => compute (A.lt u q)) X) b).map
        (Option.map fun r => (r.1, r.2.get)) =
      (Measure.pi fun _ : Fin X.length => bernoulliMeasure true false ⟨q.get, h0, h1⟩).map
        fun c => some (selectBy X c, (selectBy X c).length) := by
  have hκ : Measurable fun r : Round d => decide (r.2.2 < q.get) :=
    (measurable_decide_lt_const q.get).comp (measurable_snd.comp measurable_snd)
  have hm : Measurable fun t =>
      outcome (exec (filterCopiesT (d := d) (fun _ => unitT.bind fun u => compute (A.lt u q)) X) b t) :=
    (mf_filterCopies (Q := Unit) (keep := fun _ _ => unitT.bind fun u => compute (A.lt u q))
      (MeasFam.unitT (MeasFam.computeEnd (mp_lt measurable_snd measurable_const)))
      (X := fun _ => X) measurable_const).outcome () b
  rw [vlaw_filterCopiesT hκ (exec_below_keep q) X b hm]
  congr 2
  funext _
  rw [show (fun r : Round d => decide (r.2.2 < q.get)) = (fun u => decide (u < q.get)) ∘
    (fun r : Round d => r.2.2) from rfl, ← Measure.map_map (g := fun u => decide (u < q.get))
    (f := fun r : Round d => r.2.2) (measurable_decide_lt_const q.get)
    (measurable_snd.comp measurable_snd), roundLaw_map_unit, uniformUnit_map_lt h0 h1]

/-- **At `q = 2^{-k}`, keeping a copy is the old model's survival of `k` fair rounds.** -/
theorem bernoulli_survivalProbability (k : ℕ) (h0 : 0 ≤ ((1 : ℝ) / 2) ^ k)
    (h1 : ((1 : ℝ) / 2) ^ k ≤ 1) :
    bernoulliMeasure true false (⟨((1 : ℝ) / 2) ^ k, h0, h1⟩ : unitInterval) =
      bernoulliMeasure true false (survivalProbability k) := by
  congr 1


/-! ## The halving loop, one round at a time -/

theorem free_filterCopiesT {keep : (Fin d → Num ℤ) → Tree d Bool} (hkeep : ∀ x, Free (keep x))
    (X : List (Fin d → Num ℤ)) : Free (filterCopiesT keep X) :=
  free_foldlM (fun _ _ => Free.bind (free_compute _) fun x' => Free.bind (hkeep x') fun k =>
    free_ite k (Free.bind (free_compute _) fun _ => Free.bind (free_compute _) fun _ =>
      free_pure _) (free_pure _)) X _

/-- The halving filter's result, held. -/
theorem vlaw_filterCopiesT_coin' (X : List (Fin d → Num ℤ)) (b : ℕ) :
    vlaw (filterCopiesT (fun _ => coinT) X) b =
      ((Measure.pi fun _ : Fin X.length => fairCoinLaw).map
        fun c => (selectBy X c, (sealDraw (selectBy X c).length).val)).map some := by
  rw [Measure.map_map measurable_some (measurable_of_countable _)]
  have hv : Measurable (Option.map fun r : List (Fin d → Num ℤ) × Num ℕ => (r.1, r.2.get)) :=
    measurable_optionMap (measurable_fst.prodMk (Num.measurable_get.comp measurable_snd))
  have hw : Measurable (Option.map fun r : List (Fin d → Num ℤ) × ℕ => (r.1, (sealDraw r.2).val)) :=
    measurable_optionMap (measurable_fst.prodMk (measurable_sealDraw.comp measurable_snd))
  have h := congrArg (Measure.map (Option.map fun r : List (Fin d → Num ℤ) × ℕ =>
    (r.1, (sealDraw r.2).val))) (vlaw_filterCopiesT_coin X b)
  rw [Measure.map_map hw hv, Measure.map_map hw (measurable_of_countable _)] at h
  have hid : (Option.map fun r : List (Fin d → Num ℤ) × ℕ => (r.1, (sealDraw r.2).val)) ∘
      (Option.map fun r : List (Fin d → Num ℤ) × Num ℕ => (r.1, r.2.get)) = id := by
    funext o
    rcases o with _ | ⟨ys, c⟩
    · rfl
    · simp [sealDraw_get]
  rw [hid, Measure.map_id] at h
  rw [h]
  rfl

/-- **One round of the halving loop**: if the population is at most `Thresh`, stop;
otherwise keep each stored copy with a fair coin, draw the pending count from
`Binomial(N, 1/2)`, halve `p`, and go on. -/
theorem vlaw_halveT_succ (K : Params) (f : ℕ) (p : Num ℝ) (X : List (Fin d → Num ℤ))
    (size N : Num ℕ) (b : ℕ) :
    vlaw (halveT K (f + 1) p X size N) b =
      if (((size.get + N.get : ℕ) : ℝ) ≤ K.thresh.get) then Measure.dirac (some (p, X, size, N))
      else (Measure.pi fun _ : Fin X.length => fairCoinLaw).bind fun c =>
        (binomial N.get half).bind fun N' =>
          vlaw (halveT K f (A.divLit p 2).val (selectBy X c)
            (sealDraw (selectBy X c).length).val (sealDraw N').val) b := by
  -- the continuation after the filter, and after the binomial draw
  have hK2 : MeasFam fun q : (List (Fin d → Num ℤ) × Num ℕ) × Num ℕ =>
      (compute (A.divLit p 2)).bind fun p' => halveT K f p' q.1.1 q.1.2 q.2 :=
    MeasFam.compute (mp_divLit 2 measurable_const)
      (mf_halve K f (Q := ((List (Fin d → Num ℤ) × Num ℕ) × Num ℕ) × Num ℝ)
        (p := fun x => x.2) (X := fun x => x.1.1.1) (size := fun x => x.1.1.2)
        (N := fun x => x.1.2) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
  have hK1 : MeasFam fun r : List (Fin d → Num ℤ) × Num ℕ =>
      (binomT N).bind fun N' => (compute (A.divLit p 2)).bind fun p' => halveT K f p' r.1 r.2 N' :=
    MeasFam.binomT measurable_const hK2
  have hstop : (do
      let total ← A.add size N
      let totalR ← A.cast total
      A.le totalR K.thresh : Prog Bool).val =
      decide (((size.get + N.get : ℕ) : ℝ) ≤ K.thresh.get) := by
    simp [A.add, A.cast, A.le]
  show vlaw (Tree.step _ _) b = _
  rw [vlaw_step, pure_bindT, hstop]
  by_cases h : (((size.get + N.get : ℕ) : ℝ) ≤ K.thresh.get)
  · simp only [h, decide_true, ite_true]
    exact vlaw_pure _ b
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    have hmf : Measurable fun t => outcome (exec (filterCopiesT (d := d) (fun _ => coinT) X) b t) :=
      (mf_filterCopies (Q := Unit) (keep := fun _ _ => coinT) (MeasFam.coinT (MeasFam.pure
        measurable_snd)) (X := fun _ => X) measurable_const).outcome () b
    have hmb : Measurable fun t => outcome (exec (binomT (n := d) N) b t) :=
      (MeasFam.binomT (A := Unit) (N := fun _ => N) measurable_const (k := fun _ k => Tree.pure k)
        (MeasFam.pure (g := fun q : Unit × Num ℕ => q.2) measurable_snd)).outcome () b
    have hbin : vlaw (binomT (n := d) N) b =
        ((binomial N.get half).map fun k => (sealDraw k).val).map some := by
      rw [vlaw_binomT, Measure.map_map measurable_some measurable_sealDraw]
      rfl
    rw [vlaw_bind_of_some hK1 (free_filterCopiesT (fun _ => free_coinT) X) b hmf
      (vlaw_filterCopiesT_coin' X b), Measure.bind_map (measurable_of_countable _).aemeasurable
      (hK1.measurable_vlaw b).aemeasurable]
    congr 1
    funext c
    have hK2' : MeasFam fun N' : Num ℕ => (compute (A.divLit p 2)).bind fun p' =>
        halveT K f p' (selectBy X c) (sealDraw (selectBy X c).length).val N' :=
      hK2.comp (φ := fun N' => (((selectBy X c), (sealDraw (selectBy X c).length).val), N'))
        (measurable_const.prodMk measurable_id)
    show vlaw ((binomT N).bind _) b = _
    rw [vlaw_bind_of_some hK2' (free_binomT N) b hmb hbin, Measure.bind_map
      measurable_sealDraw.aemeasurable (hK2'.measurable_vlaw b).aemeasurable]
    congr 1
    funext k
    show vlaw (Tree.step _ _) b = _
    rw [vlaw_step, pure_bindT]

end ttc.Tape

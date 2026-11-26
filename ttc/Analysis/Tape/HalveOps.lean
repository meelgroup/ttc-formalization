/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.FilterOps
import ttc.Analysis.Tape.UntilOps

/-! # Charging the sealed halving loop -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc (TTCState fairCoinStreamLaw)

variable {d : ℕ}

private abbrev HalveState (d : ℕ) := Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ

private def halveRound (K : Params) (a : HalveState d) :
    Tree d (HalveState d ⊕ HalveState d) :=
  (compute (do
    let total ← A.add a.2.2.1 a.2.2.2
    let totalR ← A.cast total
    A.le totalR K.thresh)).bind fun stop =>
    if stop then .pure (.inr a) else
      (filterCopiesT (fun _ => coinT) a.2.1).bind fun r =>
      (binomT a.2.2.2).bind fun N' =>
      (compute (A.divLit a.1 2)).bind fun p' => .pure (.inl (p', r.1, r.2, N'))

private theorem halveT_eq_untilFuel (K : Params) :
    ∀ (f : ℕ) (a : HalveState d),
      halveT K f a.1 a.2.1 a.2.2.1 a.2.2.2 = untilFuel (halveRound K) f a
  | 0, a => rfl
  | f + 1, a => by
      rw [halveT, untilFuel, halveRound, bind_assoc]
      congr 1
      funext stop
      cases stop
      · simp only [Bool.false_eq_true, ite_false, bind_assoc, pure_bindT, Sum.elim_inl]
        congr 1
        funext r
        congr 1
        funext N'
        congr 1
        funext p'
        exact halveT_eq_untilFuel K f (p', r.1, r.2, N')
      · rfl

private theorem post_halveRound (K : Params) (c : ℕ) (a : HalveState d)
    (ha : a.2.1.length ≤ c) :
    Post (halveRound K a) fun r => r.elim (fun a' => a'.2.1.length ≤ c) (fun _ => True) := by
  unfold halveRound
  refine post_compute_bind ?_
  split_ifs
  · trivial
  · refine Post.bind ((post_filterCopiesT_size _ a.2.1).mono fun r hr => ?_)
    refine Post.bind (post_of_forall (fun N' => ?_) _)
    exact post_compute_bind (hr.trans ha)

private theorem maxOps_halveRound_le (K : Params) (a : HalveState d) :
    maxOps (halveRound K a) ≤ (8 + 4 * a.2.1.length : ℕ) := by
  unfold halveRound
  rw [maxOps_compute_bind]
  have hguard : opsTotal (do
      let total ← A.add a.2.2.1 a.2.2.2
      let totalR ← A.cast total
      A.le totalR K.thresh : Prog Bool).cost = 3 := by
    simp [A.cast, opsTotal_add, opsTotal_one]
  rw [hguard]
  split_ifs
  · simpa only [maxOps, add_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      (add_le_add (show (3 : ℕ∞) ≤ 8 by decide) (show 0 ≤ (4 : ℕ∞) * a.2.1.length from bot_le))
  · refine (add_le_add le_rfl (maxOps_bind_le (post_of_forall (Q := fun _ => True)
        (fun _ => trivial) _) 3 (fun r _ => ?_))).trans ?_
    · simp only [binomT, Tree.bind, maxOps]
      refine (add_le_add le_rfl (iSup_le fun n => ?_)).trans (show (1 : ℕ∞) + 2 ≤ 3 by decide)
      norm_num [maxOps_compute_bind, maxOps, A.divLit, opsTotal_add]
    · refine (add_le_add le_rfl (add_le_add (maxOps_filterCopiesT_coin_le a.2.1) le_rfl)).trans ?_
      push_cast
      ring_nf
      exact le_rfl

/-- The halving part is bounded by one charged scan for every round the loop
actually reaches. In particular the bound uses the population at entry, not
the Poisson count, to price each scan. -/
theorem Eops_halveT_le_tail (K : Params) (f b : ℕ) (p : Num ℝ) (X : List (Fin d → Num ℤ))
    (size N : Num ℕ) :
    Eops (halveT K f p X size N) b ≤
      (8 + 4 * X.length : ℕ) * ∑ j ∈ Finset.range f, vlaw (halveT K j p X size N) b {none} := by
  let a : HalveState d := (p, X, size, N)
  simp_rw [show ∀ j, halveT K j p X size N = untilFuel (halveRound K) j a from
    fun j => halveT_eq_untilFuel K j a]
  refine Eops_untilFuel_le (halveRound K) (fun a' => a'.2.1.length ≤ X.length)
    (8 + 4 * X.length) (post_halveRound K X.length) ?_ b a le_rfl ?_ f
  · intro a' ha' b' t
    have h := (exec_ops_le_maxOps (halveRound K a') b' t).trans (maxOps_halveRound_le K a')
    exact Nat.cast_le.mp (h.trans (Nat.cast_le.mpr (by omega)))
  · intro j
    rw [← halveT_eq_untilFuel K]
    exact (mf_halve K j (Q := Unit) (p := fun _ => p) (X := fun _ => X)
      (size := fun _ => size) (N := fun _ => N)
      measurable_const measurable_const measurable_const measurable_const).outcome () b

private theorem oldLaw_none_le (s : TTCState d) (N j : ℕ) (Th : ℝ) (hTh : 0 ≤ Th) :
    oldLaw Th (j + 1) s N {none} ≤
      ((s.X.card + N : ENNReal) * (1 / 2 : ENNReal) ^ j) / (Nat.floor Th + 1) := by
  classical
  let U := {c : ℕ × ℕ → Bool | j < ttcPseudocode.secondLoopExitRound s N Th c}
  let Z := {c : ℕ × ℕ → Bool | ∀ r, ¬ ttcPseudocode.secondLoopExit s N Th c r}
  rw [oldLaw, Measure.map_apply (measurable_oldTrunc Th (j + 1) s N) measurableSet_none]
  have hsub : oldTrunc Th (j + 1) s N ⁻¹' ({none} : Set (Option (TTCState d × ℕ))) ⊆ U ∪ Z := by
    intro c hc
    by_cases he : ∃ r, ttcPseudocode.secondLoopExit s N Th c r
    · left
      change j < ttcPseudocode.secondLoopExitRound s N Th c
      by_contra! hj
      have hmem : ttcPseudocode.secondLoopExit s N Th c (ttcPseudocode.secondLoopExitRound s N Th c) :=
        Nat.sInf_mem (s := {r | ttcPseudocode.secondLoopExit s N Th c r}) he
      have hlt : ∃ r < j + 1, ttcPseudocode.secondLoopExit s N Th c r :=
        ⟨_, Nat.lt_succ_of_le hj, hmem⟩
      change oldTrunc Th (j + 1) s N c = none at hc
      rw [oldTrunc, ite_eq_left hlt] at hc
      cases hc
    · exact Or.inr fun r hr => he ⟨r, hr⟩
  exact (measure_mono hsub).trans ((measure_union_le U Z).trans (by
    rw [show fairCoinStreamLaw Z = 0 from ttc.never_thinningExit_null s N Th hTh, add_zero]
    exact ttc.firstExitRound_tail_floor s N j Th hTh))

/-- Uniform expected halving cost in the labelled state representation. The
entry size bounds each scan, and the expected number of extra rounds is at
most twice the entry population divided by the integer guard cutoff. -/
theorem Eops_halveT_le (K : Params) (f b : ℕ) (p : Num ℝ) (X : List (Fin d → Num ℤ))
    (size N : Num ℕ) (s : TTCState d) (Ls : List (ttc.SampleCopy d)) (hTh : 0 ≤ K.thresh.get)
    (hp : p.get = s.p) (hXL : X.map getZ = Ls.map (fun c => c.2.2)) (hsize : size.get = Ls.length)
    (hX : Ls.toFinset = s.X) (hlab : (Ls.map (·.1)).Nodup) (hbelow : ∀ c ∈ Ls, c.1 < s.nextLabel) :
    Eops (halveT K f p X size N) b ≤
      (8 + 4 * X.length : ℕ) * (1 + 2 *
        ((s.X.card + N.get : ENNReal) / (Nat.floor K.thresh.get + 1))) := by
  classical
  refine (Eops_halveT_le_tail K f b p X size N).trans (mul_le_mul' le_rfl ?_)
  have h (j : ℕ) : vlaw (halveT K j p X size N) b {none} = oldLaw K.thresh.get j s N.get {none} := by
    have he := congrArg (fun μ : Measure (Option (ℝ × ℕ × ℕ)) => μ {none})
      (halveT_eq_oldLaw K b j p X size N s Ls hp hXL hsize hX hlab hbelow)
    rw [Measure.map_apply measurable_viewNew measurableSet_none,
      Measure.map_apply measurable_viewOld measurableSet_none] at he
    have hnew : viewNew (n := d) ⁻¹' {none} = {none} := by
      ext x
      cases x <;> simp [viewNew]
    have hold : viewOld (n := d) ⁻¹' {none} = {none} := by
      ext x
      cases x <;> simp [viewOld]
    rwa [hnew, hold] at he
  simp_rw [h]
  cases f with
  | zero => simp
  | succ f =>
      rw [Finset.sum_range_succ', oldLaw_zero, Measure.dirac_apply' _ measurableSet_none]
      simp only [indicator_of_mem (mem_singleton none), Pi.one_apply]
      rw [add_comm]
      refine add_le_add le_rfl ?_
      refine (Finset.sum_le_sum (s := Finset.range f) (fun j _ =>
        oldLaw_none_le s N.get j K.thresh.get hTh)).trans ?_
      let A := (s.X.card + N.get : ENNReal) / (Nat.floor K.thresh.get + 1)
      calc _ ≤ ∑' j : ℕ, ((s.X.card + N.get : ENNReal) * (1 / 2 : ENNReal) ^ j) /
          (Nat.floor K.thresh.get + 1) := ENNReal.sum_le_tsum _
        _ = A * ∑' j : ℕ, (1 / 2 : ENNReal) ^ j := by
          have hterm (j : ℕ) : ((s.X.card + N.get : ENNReal) * (1 / 2 : ENNReal) ^ j) /
              (Nat.floor K.thresh.get + 1) = A * (1 / 2 : ENNReal) ^ j := by
            simp only [A, div_eq_mul_inv]
            ac_rfl
          simp_rw [hterm, ENNReal.tsum_mul_left]
        _ = 2 * A := by rw [ENNReal.tsum_geometric]; norm_num; ac_rfl

/-- The halving bound expressed only in the sealed state. Fresh labels for the
old law are chosen from the positions of the copies, so repetitions of a point
are counted separately. -/
theorem Eops_halveT_le_unlabelled (K : Params) (f b : ℕ) (p : Num ℝ) (X : List (Fin d → Num ℤ))
    (size N : Num ℕ) (hTh : 0 ≤ K.thresh.get) (hp : 0 ≤ p.get) (hs : size.get = X.length) :
    Eops (halveT K f p X size N) b ≤
      (8 + 4 * X.length : ℕ) * (1 + 2 *
        ((X.length + N.get : ENNReal) / (Nat.floor K.thresh.get + 1))) := by
  classical
  let Ls : List (ttc.SampleCopy d) := List.ofFn fun i : Fin X.length => (i.val, 0, getZ (X.get i))
  let s : TTCState d := ⟨⟨p.get, hp⟩, Ls.toFinset, X.length⟩
  have hXs : X.map getZ = Ls.map (·.2.2) := by
    simp only [Ls, List.map_ofFn, Function.comp_def]
    exact (List.ofFn_getElem_eq_map X getZ).symm
  have hLs : Ls.length = X.length := List.length_ofFn
  have hlabel : (Ls.map (·.1)).Nodup := by
    simp only [Ls, List.map_ofFn, Function.comp_def]
    exact List.nodup_ofFn_ofInjective Fin.val_injective
  have hbelow : ∀ c ∈ Ls, c.1 < s.nextLabel := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact i.isLt
  have hsCard : s.X.card = X.length := by
    rw [show s.X = Ls.toFinset from rfl, List.toFinset_card_of_nodup (List.Nodup.of_map _ hlabel), hLs]
  simpa only [hsCard] using Eops_halveT_le K f b p X size N s Ls hTh rfl hXs (hs.trans hLs.symm)
    rfl hlabel hbelow

/-- Averaging the halving cost over the actual Poisson draw replaces the
pending count in the bound by its mean. -/
theorem Eops_poisson_halveT_le (K : Params) (f b : ℕ) (p rate : Num ℝ)
    (X : List (Fin d → Num ℤ)) (size : Num ℕ)
    (hTh : 0 ≤ K.thresh.get) (hp : 0 ≤ p.get) (hs : size.get = X.length) :
    Eops ((poissonT rate).bind (halveT K f p X size)) b ≤
      1 + (8 + 4 * X.length : ℕ) * (1 + 2 *
        ((X.length + (Real.toNNReal rate.get : ENNReal)) / (Nat.floor K.thresh.get + 1))) := by
  have hf : MeasFam (halveT K f p X size) :=
    mf_halve K f (p := fun _ => p) (X := fun _ => X) (size := fun _ => size) (N := id)
      measurable_const measurable_const measurable_const measurable_id
  have hm : Measurable fun t => outcome (exec (poissonT (n := d) rate) b t) :=
    (MeasFam.poissonT (A := Unit) (d := d) (rate := fun _ => rate)
      (k := fun _ => Tree.pure) measurable_const
      (MeasFam.pure measurable_snd)).outcome () b
  have hcf : ∀ N, CapFirst (halveT K f p X size N) :=
    fun N => Free.capFirst (free_halveT K f p X size N)
  rw [Eops_bind_capFirst hf hcf _ b hm b, Eops_eq_tape _ _ hm, vlaw_poissonT]
  simp only [poissonT, exec, add_zero, Nat.cast_one, lintegral_const, measure_univ, mul_one]
  have hg : Measurable fun o : Option (Num ℕ) => o.elim 0 (fun N => Eops (halveT K f p X size N) b) := by
    have he : (fun o : Option (Num ℕ) => o.elim 0 (fun N => Eops (halveT K f p X size N) b)) =
        Sum.elim (fun _ : Unit => 0) (fun N => Eops (halveT K f p X size N) b) ∘
          ArlibCommunity.Algorithms.CV18.optionToSum := by
      funext o
      cases o <;> rfl
    rw [he]
    exact (measurable_const.sumElim (MeasFam.measurable_Eops hf b)).comp
      ArlibCommunity.Algorithms.CV18.measurable_optionToSum
  have hmap : Measurable (fun n : ℕ => some (sealDraw n).val) := measurable_of_countable _
  rw [lintegral_map hg hmap]
  simp only [Option.elim_some]
  apply add_le_add le_rfl
  let B : ENNReal := (8 + 4 * X.length : ℕ)
  let C : ENNReal := Nat.floor K.thresh.get + 1
  let r := Real.toNNReal rate.get
  change (∫⁻ n : ℕ, Eops (halveT K f p X size (sealDraw n).val) b ∂poissonMeasure r) ≤
    B * (1 + 2 * ((X.length + (r : ENNReal)) / C))
  calc ∫⁻ n : ℕ, Eops (halveT K f p X size (sealDraw n).val) b ∂poissonMeasure r
      ≤ ∫⁻ n : ℕ, B * (1 + 2 * ((X.length + n : ENNReal) / C)) ∂poissonMeasure r := by
        refine lintegral_mono fun n => ?_
        simpa only [B, C, get_sealDraw] using
          Eops_halveT_le_unlabelled K f b p X size (sealDraw n).val hTh hp hs
    _ = _ := by
        rw [lintegral_const_mul _ (measurable_of_countable _), lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one, lintegral_const_mul _ (measurable_of_countable _)]
        simp_rw [div_eq_mul_inv, add_mul]
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_mul_const _ (measurable_of_countable (fun n : ℕ => (n : ENNReal))),
          ttc.poissonMeasure_lintegral_count]

end ttc.Tape

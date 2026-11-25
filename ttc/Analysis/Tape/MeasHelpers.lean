/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.MeasProg

/-!
# Measurability of the program's arithmetic

`MP` for each arithmetic procedure of the program (`Model/SealedProgram.lean`) that runs on
random numbers: its value and operation count are measurable in its inputs.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ArlibCommunity.Algorithms.CV18 (measurable_some)

variable {Q : Type} [MeasurableSpace Q]

theorem measurable_fin_cons {α : Type} [MeasurableSpace α] {k : ℕ} :
    Measurable fun p : α × (Fin k → α) => (Fin.cons p.1 p.2 : Fin (k + 1) → α) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_fst
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_fin_tail {α : Type} [MeasurableSpace α] {k : ℕ} :
    Measurable fun v : Fin (k + 1) → α => Fin.tail v :=
  measurable_pi_iff.mpr fun j => measurable_pi_apply j.succ

theorem mp_forEach {α : Type} [MeasurableSpace α] :
    ∀ {k : ℕ} {f : Q → Fin k → Prog α}, (∀ i, MP fun q => f q i) →
      MP fun q => A.forEach (f q)
  | 0, f, _ => MP.const _
  | k + 1, f, h => by
      have key : MP fun q => f q 0 >>= fun first =>
          (A.forEach fun i => f q i.succ) >>= fun rest =>
            (Pure.pure (Fin.cons first rest) : Prog (Fin (k + 1) → α)) :=
        MP.bind' (h 0) (MP.bind' ((mp_forEach (f := fun q i => f q i.succ)
          fun i => (h i.succ)).comp measurable_fst)
          (MP.pure (measurable_fin_cons.comp (measurable_fst.snd.prodMk measurable_snd))))
      exact MP.congr key fun q => rfl

theorem mp_dot : ∀ (k : ℕ) {a x : Q → NumPoint k}, Measurable a → Measurable x →
    MP fun q => A.dot k (a q) (x q)
  | 0, _, _, _, _ => MP.const _
  | 1, a, x, ha, hx =>
      mp_mul ((measurable_pi_apply 0).comp ha) ((measurable_pi_apply 0).comp hx)
  | k + 2, a, x, ha, hx => by
      have key : MP fun q => A.mul (a q 0) (x q 0) >>= fun first =>
          A.dot (k + 1) (Fin.tail (a q)) (Fin.tail (x q)) >>= fun rest => A.add first rest :=
        MP.bind' (mp_mul ((measurable_pi_apply 0).comp ha) ((measurable_pi_apply 0).comp hx))
          (MP.bind' ((mp_dot (k + 1) (a := fun q => Fin.tail (a q))
              (x := fun q => Fin.tail (x q)) (measurable_fin_tail.comp ha)
              (measurable_fin_tail.comp hx)).comp measurable_fst)
            (mp_add (measurable_fst.snd) measurable_snd))
      exact MP.congr key fun q => rfl

theorem mp_normSq {k : ℕ} {x : Q → NumPoint k} (hx : Measurable x) :
    MP fun q => A.normSq (x q) :=
  mp_dot k hx hx

theorem mp_norm {k : ℕ} {x : Q → NumPoint k} (hx : Measurable x) : MP fun q => A.norm (x q) :=
  MP.bind' (mp_normSq hx) (mp_sqrt measurable_snd)

theorem mp_smul {k : ℕ} {c : Q → Num ℝ} {x : Q → NumPoint k} (hc : Measurable c)
    (hx : Measurable x) : MP fun q => A.smul (c q) (x q) :=
  mp_forEach fun i => mp_mul hc ((measurable_pi_apply i).comp hx)

theorem mp_addVec {k : ℕ} {x y : Q → NumPoint k} (hx : Measurable x) (hy : Measurable y) :
    MP fun q => A.addVec (x q) (y q) :=
  mp_forEach fun i => mp_add ((measurable_pi_apply i).comp hx) ((measurable_pi_apply i).comp hy)

theorem mp_pow {x : Q → Num ℝ} (hx : Measurable x) : ∀ k : ℕ, MP fun q => A.pow (x q) k
  | 0 => MP.const _
  | k + 1 => MP.bind' (mp_pow hx k) (mp_mul measurable_snd (hx.comp measurable_fst))

theorem mp_protectedLog {x : Q → Num ℝ} (hx : Measurable x) :
    MP fun q => A.protectedLog (x q) :=
  MP.bind' (mp_log hx) (MP.bind' (MP.const _) (mp_max measurable_snd measurable_fst.snd))

theorem mp_mulLit (c : ℝ) {x : Q → Num ℝ} (hx : Measurable x) :
    MP fun q => A.mulLit c (x q) :=
  MP.bind' (MP.const _) (mp_mul measurable_snd (hx.comp measurable_fst))

theorem mp_divLit (c : ℝ) {x : Q → Num ℝ} (hx : Measurable x) :
    MP fun q => A.divLit (x q) c :=
  MP.bind' (MP.const _) (mp_div (hx.comp measurable_fst) measurable_snd)

theorem mp_litDiv (c : ℝ) {x : Q → Num ℝ} (hx : Measurable x) :
    MP fun q => A.litDiv c (x q) :=
  MP.bind' (MP.const _) (mp_div measurable_snd (hx.comp measurable_fst))

theorem mp_litMax (c : ℝ) {x : Q → Num ℝ} (hx : Measurable x) :
    MP fun q => A.litMax c (x q) :=
  MP.bind' (MP.const _) (mp_max measurable_snd (hx.comp measurable_fst))

theorem mp_gaussianLogWeight {k : ℕ} {s : Q → Num ℝ} {x : Q → NumPoint k} (hs : Measurable s)
    (hx : Measurable x) : MP fun q => A.gaussianLogWeight (s q) (x q) := by
  unfold A.gaussianLogWeight
  refine MP.bind' (mp_normSq hx) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (mp_mul measurable_snd (by fun_prop)) ?_
  refine MP.bind' (mp_div (by fun_prop) measurable_snd) ?_
  refine MP.bind' (MP.const _) ?_
  exact mp_sub measurable_snd (by fun_prop)

theorem mp_ballStart {k : ℕ} {dim : Q → Num ℕ} {g : Q → NumPoint k} {u : Q → Num ℝ}
    (hdim : Measurable dim) (hg : Measurable g) (hu : Measurable u) :
    MP fun q => A.ballStart (dim q) (g q) (u q) := by
  unfold A.ballStart
  refine MP.bind' (mp_normSq hg) ?_
  refine MP.bind' (mp_sqrt measurable_snd) ?_
  refine MP.bind' (mp_root (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (mp_div measurable_snd (by fun_prop)) ?_
  exact mp_smul measurable_snd (by fun_prop)

theorem mp_properTestProg {k : ℕ} {rootT radius : Q → Num ℝ} {y : Q → NumPoint k}
    (h1 : Measurable rootT) (h2 : Measurable radius) (hy : Measurable y) :
    MP fun q => properTestProg (rootT q) (radius q) (y q) := by
  unfold properTestProg
  refine MP.bind' (mp_norm hy) ?_
  refine MP.bind' (mp_le measurable_snd (by fun_prop)) ?_
  refine MP.bind' (mp_le (by fun_prop) (by fun_prop)) ?_
  exact MP.pure (by fun_prop)

theorem mp_lazyTestProg {k : ℕ} {s : Q → Num ℝ} {x y : Q → NumPoint k} {coin : Q → Num ℝ}
    (hs : Measurable s) (hx : Measurable x) (hy : Measurable y) (hc : Measurable coin) :
    MP fun q => lazyTestProg (s q) (x q) (y q) (coin q) := by
  unfold lazyTestProg
  refine MP.bind' (mp_gaussianLogWeight hs hy) ?_
  refine MP.bind' (mp_gaussianLogWeight (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (mp_exp (by fun_prop)) ?_
  refine MP.bind' (mp_exp (by fun_prop)) ?_
  refine MP.bind' (mp_div (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (mp_min (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (mp_div (by fun_prop) (by fun_prop)) ?_
  exact mp_le (by fun_prop) (by fun_prop)

theorem mp_scaleAcceptTestProg {k : ℕ} {s c : Q → Num ℝ} {y : Q → NumPoint k}
    {coin : Q → Num ℝ} (hs : Measurable s) (hc : Measurable c) (hy : Measurable y)
    (hcoin : Measurable coin) :
    MP fun q => scaleAcceptTestProg (s q) (c q) (y q) (coin q) := by
  unfold scaleAcceptTestProg
  refine MP.bind' (mp_mul hc hc) ?_
  refine MP.bind' (mp_div (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (mp_gaussianLogWeight (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (mp_gaussianLogWeight (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (mp_exp (by fun_prop)) ?_
  refine MP.bind' (mp_exp (by fun_prop)) ?_
  refine MP.bind' (mp_div (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (mp_div (by fun_prop) (by fun_prop)) ?_
  exact mp_le (by fun_prop) (by fun_prop)

theorem mp_gaussianRatioWeightProg {k : ℕ} {s t : Q → Num ℝ} {x : Q → NumPoint k}
    (hs : Measurable s) (ht : Measurable t) (hx : Measurable x) :
    MP fun q => gaussianRatioWeightProg (s q) (t q) (x q) := by
  unfold gaussianRatioWeightProg
  refine MP.bind' (mp_gaussianLogWeight ht hx) ?_
  refine MP.bind' (mp_gaussianLogWeight (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (mp_exp (by fun_prop)) ?_
  refine MP.bind' (mp_exp (by fun_prop)) ?_
  exact mp_div (by fun_prop) (by fun_prop)

theorem mp_uniformRatioWeightProg {k : ℕ} {s : Q → Num ℝ} {x : Q → NumPoint k}
    (hs : Measurable s) (hx : Measurable x) :
    MP fun q => uniformRatioWeightProg (s q) (x q) := by
  unfold uniformRatioWeightProg
  refine MP.bind' (mp_normSq hx) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (mp_mul (by fun_prop) (by fun_prop)) ?_
  refine MP.bind' (mp_div (by fun_prop) (by fun_prop)) ?_
  exact mp_exp (by fun_prop)

theorem mp_ballProposalProg {k : ℕ} {dim : Q → Num ℕ} {x : Q → NumPoint k} {r : Q → Num ℝ}
    {g : Q → NumPoint k} {u : Q → Num ℝ} (hdim : Measurable dim) (hx : Measurable x)
    (hr : Measurable r) (hg : Measurable g) (hu : Measurable u) :
    MP fun q => ballProposalProg (dim q) (x q) (r q) (g q) (u q) := by
  unfold ballProposalProg
  refine MP.bind' (mp_ballStart hdim hg hu) ?_
  refine MP.bind' (mp_smul (by fun_prop) (by fun_prop)) ?_
  exact mp_addVec (by fun_prop) (by fun_prop)

theorem mp_gaussianStartProg {k : ℕ} {r : Q → Num ℝ} {g : Q → NumPoint k} (hr : Measurable r)
    (hg : Measurable g) : MP fun q => gaussianStartProg (r q) (g q) :=
  mp_smul hr hg

/-! ## Options -/

theorem measurable_optionMatch {α β : Type} [MeasurableSpace α] [MeasurableSpace β] [Inhabited α]
    {o : Q → Option α} (ho : Measurable o) {F : Q → β} {G : Q × α → β} (hF : Measurable F)
    (hG : Measurable G) :
    Measurable fun q => match o q with
      | none => F q
      | some x => G (q, x) := by
  have H := ArlibCommunity.Algorithms.CV18.Measurable.optionCases (α := α) (γ := Q) (β := β)
    default (noneValue := F) (someValue := G) hF hG
  have : (fun q => match o q with
      | none => F q
      | some x => G (q, x)) = (fun p : Q × Option α => match p.2 with
      | none => F p.1
      | some v => G (p.1, v)) ∘ fun q => (q, o q) := by
    funext q; rfl
  rw [this]
  exact H.comp (measurable_id.prodMk ho)

theorem MP.option {α β : Type} [MeasurableSpace α] [MeasurableSpace β] [Inhabited α]
    {o : Q → Option α} (ho : Measurable o) {F : Q → Prog β} {G : Q × α → Prog β} (hF : MP F)
    (hG : MP G) :
    MP fun q => match o q with
      | none => F q
      | some x => G (q, x) := by
  refine ⟨?_, ?_⟩
  · have e : (fun q => (match o q with
        | none => F q
        | some x => G (q, x)).val) = fun q => match o q with
        | none => (F q).val
        | some x => (G (q, x)).val := by
      funext q; rcases o q with _ | x <;> rfl
    rw [e]; exact measurable_optionMatch (F := fun q => (F q).val) (G := fun p => (G p).val)
      ho hF.1 hG.1
  · have e : (fun q => opsTotal (match o q with
        | none => F q
        | some x => G (q, x)).cost) = fun q => match o q with
        | none => opsTotal (F q).cost
        | some x => opsTotal (G (q, x)).cost := by
      funext q; rcases o q with _ | x <;> rfl
    rw [e]; exact measurable_optionMatch (F := fun q => opsTotal (F q).cost)
      (G := fun p => opsTotal (G p).cost) ho hF.2 hG.2

theorem measurable_bif {β : Type} [MeasurableSpace β] {c : Q → Bool} (hc : Measurable c)
    {x y : Q → β} (hx : Measurable x) (hy : Measurable y) :
    Measurable fun q => if c q = true then x q else y q :=
  Measurable.ite (hc (measurableSet_singleton true)) hx hy

theorem List.measurable_map' {α β : Type} [MeasurableSpace α] [MeasurableSpace β] [Inhabited α]
    {L : Q → List α} (hL : Measurable L) {h : Q → α → β}
    (hh : Measurable fun p : Q × α => h p.1 p.2) :
    Measurable fun q => (L q).map (h q) := by
  refine List.measurable_of ?_ fun i => ?_
  · simp only [List.length_map]; exact List.measurable_length.comp hL
  · have := measurable_optionMatch (α := α) (β := Option β) (o := fun q => (L q)[i]?)
      ((List.measurable_getElem? i).comp hL) (F := fun _ => (none : Option β))
      (G := fun p : Q × α => some (h p.1 p.2)) measurable_const (measurable_some.comp hh)
    have e : (fun q => ((L q).map (h q))[i]?) = fun q => match (L q)[i]? with
        | none => none
        | some x => some (h q x) := by
      funext q; simp only [List.getElem?_map]; rcases (L q)[i]? with _ | x <;> rfl
    rw [e]; exact this

/-! ## Lists of results -/

theorem mp_mapM_ofFn {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {g : Q × α → Prog β} (hg : MP g) :
    ∀ k : ℕ, MP fun p : Q × (Fin k → α) => (List.ofFn p.2).mapM fun x => g (p.1, x)
  | 0 => MP.congr (MP.pure (g := fun _ : Q × (Fin 0 → α) => ([] : List β)) measurable_const)
      fun p => by simp
  | k + 1 => by
      have key : MP fun p : Q × (Fin (k + 1) → α) => g (p.1, p.2 0) >>= fun b =>
          (List.ofFn fun i : Fin k => p.2 i.succ).mapM (fun x => g (p.1, x)) >>= fun bs =>
            (Pure.pure (b :: bs) : Prog (List β)) :=
        MP.bind' (hg.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)))
          (MP.bind' ((mp_mapM_ofFn hg k).comp (measurable_fst.fst.prodMk
              (measurable_fin_tail.comp measurable_fst.snd)))
            (MP.pure (List.measurable_cons measurable_fst.snd measurable_snd)))
      exact MP.congr key fun p => by simp [List.ofFn_succ, List.mapM_cons]

theorem mp_mapM {α β : Type} [MeasurableSpace α] [MeasurableSpace β] [Inhabited α]
    {L : Q → List α} (hL : Measurable L) {g : Q → α → Prog β}
    (hg : MP fun p : Q × α => g p.1 p.2) : MP fun q => (L q).mapM (g q) := by
  have h : MP fun p : Q × List α => p.2.mapM fun x => g p.1 x :=
    MP.ofList fun k => mp_mapM_ofFn (g := fun p : Q × α => g p.1 p.2) hg k
  exact h.comp (measurable_id.prodMk hL)

theorem mp_sumList_ofFn : ∀ k : ℕ, MP fun v : Fin k → Num ℕ => A.sumList (List.ofFn v)
  | 0 => MP.congr (MP.const (A.sumList [])) fun v => by simp
  | 1 => MP.congr (MP.pure (g := fun v : Fin 1 → Num ℕ => v 0) (measurable_pi_apply 0))
      fun v => rfl
  | k + 2 => by
      have key : MP fun v : Fin (k + 2) → Num ℕ =>
          A.sumList (List.ofFn (Fin.tail v)) >>= fun r => A.add (v 0) r :=
        MP.bind' ((mp_sumList_ofFn (k + 1)).comp measurable_fin_tail)
          (mp_addN ((measurable_pi_apply 0).comp measurable_fst) measurable_snd)
      refine MP.congr key fun v => ?_
      obtain ⟨b, rest, hbr⟩ : ∃ b rest, List.ofFn (Fin.tail v) = b :: rest :=
        ⟨_, _, List.ofFn_succ (f := Fin.tail v)⟩
      have h1 : List.ofFn v = v 0 :: List.ofFn (Fin.tail v) := List.ofFn_succ (f := v)
      rw [h1, hbr]
      rfl

theorem mp_sumList {L : Q → List (Num ℕ)} (hL : Measurable L) : MP fun q => A.sumList (L q) := by
  have h : MP fun p : Unit × List (Num ℕ) => A.sumList p.2 :=
    MP.ofList fun k => (mp_sumList_ofFn k).comp measurable_snd
  exact h.comp (φ := fun q => ((), L q)) (measurable_const.prodMk hL)

theorem mp_firstPassing_ofFn :
    ∀ k : ℕ, MP fun v : Fin k → Num ℝ × Bool => A.firstPassing (List.ofFn v)
  | 0 => MP.congr (MP.const (A.firstPassing [])) fun v => by simp
  | k + 1 => by
      have key : MP fun v : Fin (k + 1) → Num ℝ × Bool =>
          if (v 0).2 then A.pure (v 0).1 else A.firstPassing (List.ofFn (Fin.tail v)) :=
        MP.ite ((measurable_pi_apply 0).snd) (MP.pure ((measurable_pi_apply 0).fst))
          ((mp_firstPassing_ofFn k).comp measurable_fin_tail)
      refine MP.congr key fun v => ?_
      rw [List.ofFn_succ]
      rfl

theorem mp_firstPassing {L : Q → List (Num ℝ × Bool)} (hL : Measurable L) :
    MP fun q => A.firstPassing (L q) := by
  have h : MP fun p : Unit × List (Num ℝ × Bool) => A.firstPassing p.2 :=
    MP.ofList fun k => (mp_firstPassing_ofFn k).comp measurable_snd
  exact h.comp (φ := fun q => ((), L q)) (measurable_const.prodMk hL)

/-- The median, of a measurable list. -/
theorem mp_median {m : Q → Num ℕ} (hm : Measurable m) {v : Q → List (Num ℝ)}
    (hv : Measurable v) : MP fun q => A.median (m q) (v q) := by
  unfold A.median
  refine MP.bind' (mp_mapM hv (mp_cell measurable_snd)) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (mp_divN (by fun_prop) measurable_snd) ?_
  refine MP.bind' (mp_mapM (by fun_prop) ?_) ?_
  · refine MP.bind' (mp_mapM (by fun_prop) (mp_lt measurable_snd (by fun_prop))) ?_
    refine MP.bind' (mp_sumList ?_) ?_
    · exact List.measurable_map' (by fun_prop)
        (measurable_bif measurable_snd (by fun_prop) (by fun_prop))
    refine MP.bind' (mp_mapM (by fun_prop) (mp_le measurable_snd (by fun_prop))) ?_
    refine MP.bind' (mp_sumList ?_) ?_
    · exact List.measurable_map' (by fun_prop)
        (measurable_bif measurable_snd (by fun_prop) (by fun_prop))
    refine MP.bind' (mp_leN (by fun_prop) (by fun_prop)) ?_
    refine MP.bind' (mp_ltN (by fun_prop) (by fun_prop)) ?_
    exact MP.pure (by fun_prop)
  · exact mp_firstPassing measurable_snd

/-! ## The sampler's arithmetic -/

theorem mp_apure {β : Type} [MeasurableSpace β] {g : Q → β} (hg : Measurable g) :
    MP fun q => A.pure (g q) :=
  MP.pure hg

theorem mp_allFacets {d : ℕ} : ∀ (r : ℕ) (a : Fin r → NumPoint d) (b : Fin r → Num ℝ)
    {x : Q → NumPoint d}, Measurable x → MP fun q => allFacets r a b (x q)
  | 0, _, _, _, _ => MP.const _
  | r + 1, a, b, x, hx => by
      have key : MP fun q => A.dot d (a 0) (x q) >>= fun s => A.le s (b 0) >>= fun ok =>
          allFacets r (Fin.tail a) (Fin.tail b) (x q) >>= fun rest => A.pure (ok && rest) :=
        MP.bind' (mp_dot d measurable_const hx)
          (MP.bind' (mp_le measurable_snd measurable_const)
            (MP.bind' ((mp_allFacets r (Fin.tail a) (Fin.tail b) hx).comp
                measurable_fst.fst)
              (MP.pure (by fun_prop))))
      exact MP.congr key fun q => rfl

theorem mp_normalize {d : ℕ} {g : Q → NumPoint d} (hg : Measurable g) :
    MP fun q => Program.normalize (g q) := by
  unfold Program.normalize
  refine MP.bind' (mp_norm hg) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (mp_div measurable_snd (by fun_prop)) ?_
  exact mp_smul measurable_snd (by fun_prop)

theorem mp_facetEndpoints {d : ℕ} (a : NumPoint d) (β : Num ℝ) {x θ : Q → NumPoint d}
    (hx : Measurable x) (hθ : Measurable θ) :
    MP fun q => facetEndpoints a β (x q) (θ q) := by
  unfold facetEndpoints
  refine MP.bind' (mp_dot d measurable_const hθ) ?_
  refine MP.bind' (mp_dot d measurable_const (by fun_prop)) ?_
  refine MP.bind' (mp_sub measurable_const measurable_snd) ?_
  refine MP.bind' (mp_div measurable_snd (by fun_prop)) ?_
  refine MP.bind' (MP.const _) ?_
  refine MP.bind' (mp_lt (by fun_prop) measurable_snd) ?_
  refine MP.bind' (mp_lt (by fun_prop) (by fun_prop)) ?_
  refine MP.pure ((measurable_bif (by fun_prop) (measurable_some.comp (by fun_prop))
    measurable_const).prodMk (measurable_bif (by fun_prop) (measurable_some.comp (by fun_prop))
    measurable_const))

/-- The second case split of `maxEnd`/`minEnd`, given a first endpoint `x`. -/
def endWith (op : Num ℝ → Num ℝ → Prog (Num ℝ)) (o₂ : Option (Num ℝ)) (x : Num ℝ) :
    Prog (Option (Num ℝ)) :=
  match o₂ with
  | none => A.pure (some x)
  | some y => op x y >>= fun z => A.pure (some z)

theorem maxEnd_eq (o₁ o₂ : Option (Num ℝ)) :
    maxEnd o₁ o₂ = match o₁ with
      | none => A.pure o₂
      | some x => endWith A.max o₂ x := by
  rcases o₁ with _ | x <;> rcases o₂ with _ | y <;> rfl

theorem minEnd_eq (o₁ o₂ : Option (Num ℝ)) :
    minEnd o₁ o₂ = match o₁ with
      | none => A.pure o₂
      | some x => endWith A.min o₂ x := by
  rcases o₁ with _ | x <;> rcases o₂ with _ | y <;> rfl

theorem mp_endWith {op : Num ℝ → Num ℝ → Prog (Num ℝ)}
    (hop : ∀ {Q' : Type} [MeasurableSpace Q'] {x y : Q' → Num ℝ}, Measurable x → Measurable y →
      MP fun q => op (x q) (y q))
    {o₂ : Q → Option (Num ℝ)} (h₂ : Measurable o₂) {x : Q → Num ℝ} (hx : Measurable x) :
    MP fun q => endWith op (o₂ q) (x q) := by
  have key := MP.option (G := fun p : Q × Num ℝ => op (x p.1) p.2 >>= fun z => A.pure (some z))
    (F := fun q => A.pure (some (x q))) h₂ (mp_apure (measurable_some.comp hx))
    (MP.bind' (hop (by fun_prop) measurable_snd) (mp_apure (measurable_some.comp measurable_snd)))
  refine MP.congr key fun q => ?_
  unfold endWith; rcases o₂ q <;> rfl

theorem mp_maxEnd {o₁ o₂ : Q → Option (Num ℝ)} (h₁ : Measurable o₁) (h₂ : Measurable o₂) :
    MP fun q => maxEnd (o₁ q) (o₂ q) := by
  have key := MP.option (G := fun p : Q × Num ℝ => endWith A.max (o₂ p.1) p.2)
    (F := fun q => A.pure (o₂ q)) h₁ (mp_apure h₂)
    (mp_endWith (fun hx hy => mp_max hx hy) (h₂.comp measurable_fst) measurable_snd)
  refine MP.congr key fun q => ?_
  rw [maxEnd_eq]; rcases o₁ q <;> rfl

theorem mp_minEnd {o₁ o₂ : Q → Option (Num ℝ)} (h₁ : Measurable o₁) (h₂ : Measurable o₂) :
    MP fun q => minEnd (o₁ q) (o₂ q) := by
  have key := MP.option (G := fun p : Q × Num ℝ => endWith A.min (o₂ p.1) p.2)
    (F := fun q => A.pure (o₂ q)) h₁ (mp_apure h₂)
    (mp_endWith (fun hx hy => mp_min hx hy) (h₂.comp measurable_fst) measurable_snd)
  refine MP.congr key fun q => ?_
  rw [minEnd_eq]; rcases o₁ q <;> rfl

theorem mp_chord {d : ℕ} : ∀ (r : ℕ) (a : Fin r → NumPoint d) (β : Fin r → Num ℝ)
    {x θ : Q → NumPoint d}, Measurable x → Measurable θ → MP fun q => chord r a β (x q) (θ q)
  | 0, _, _, _, _, _, _ => MP.const _
  | r + 1, a, β, x, θ, hx, hθ => by
      have key : MP fun q => facetEndpoints (a 0) (β 0) (x q) (θ q) >>= fun first =>
          chord r (Fin.tail a) (Fin.tail β) (x q) (θ q) >>= fun rest =>
          maxEnd first.1 rest.1 >>= fun lo => minEnd first.2 rest.2 >>= fun hi =>
          A.pure (lo, hi) :=
        MP.bind' (mp_facetEndpoints _ _ hx hθ)
          (MP.bind' ((mp_chord r (Fin.tail a) (Fin.tail β) hx hθ).comp measurable_fst)
            (MP.bind' (mp_maxEnd (by fun_prop) (by fun_prop))
              (MP.bind' (mp_minEnd (by fun_prop) (by fun_prop)) (MP.pure (by fun_prop)))))
      exact MP.congr key fun q => rfl

theorem mp_latticeReal {d : ℕ} {z : Q → Fin d → Num ℤ} (hz : Measurable z) :
    MP fun q => latticeReal (z q) :=
  mp_forEach fun i => mp_intCast ((measurable_pi_apply i).comp hz)

theorem mp_latticeMember {d : ℕ} (L : Loaded d) (scaled : Fin L.facets → Num ℝ)
    {z : Q → Fin d → Num ℤ} (hz : Measurable z) : MP fun q => latticeMember L scaled (z q) :=
  MP.bind' (mp_latticeReal hz) (mp_allFacets _ _ _ measurable_snd)

theorem mp_move {d : ℕ} {lo hi u : Q → Num ℝ} {x θ : Q → NumPoint d} (hlo : Measurable lo)
    (hhi : Measurable hi) (hu : Measurable u) (hx : Measurable x) (hθ : Measurable θ) :
    MP fun q => (do
      let width ← A.sub (hi q) (lo q)
      let shift ← A.mul (u q) width
      let t ← A.add (lo q) shift
      A.forEach fun i => do
        let step ← A.mul t (θ q i)
        A.add (x q i) step : Prog (NumPoint d)) := by
  refine MP.bind' (mp_sub hhi hlo) ?_
  refine MP.bind' (mp_mul (by fun_prop) measurable_snd) ?_
  refine MP.bind' (mp_add (by fun_prop) measurable_snd) ?_
  exact mp_forEach fun i => MP.bind' (mp_mul measurable_snd (by fun_prop))
    (mp_add (by fun_prop) measurable_snd)

theorem mp_chart {d r : ℕ} (W : WalkConstants d r) {y : Q → NumPoint d} (hy : Measurable y) :
    MP fun q => (A.forEach fun i => do
      let s ← A.mul W.scaledInradius (y q i)
      A.add s (W.scaledIncenter i) : Prog (NumPoint d)) :=
  mp_forEach fun i => MP.bind' (mp_mul measurable_const (by fun_prop))
    (mp_add measurable_snd measurable_const)

theorem mp_roundStep {one : Num ℤ} {q₀ : Q → Num ℝ} {v : Q → Num ℝ} (hq : Measurable q₀)
    (hv : Measurable v) :
    MP fun q => (do
      let fl ← floor (q₀ q)
      let flR ← intCast fl
      let frac ← A.sub (q₀ q) flR
      let up ← A.lt (v q) frac
      if up then A.add fl one else A.pure fl : Prog (Num ℤ)) := by
  refine MP.bind' (mp_floor hq) ?_
  refine MP.bind' (mp_intCast measurable_snd) ?_
  refine MP.bind' (mp_sub (by fun_prop) measurable_snd) ?_
  refine MP.bind' (mp_lt (by fun_prop) measurable_snd) ?_
  exact MP.ite measurable_snd (mp_addZ (by fun_prop) measurable_const) (MP.pure (by fun_prop))

end ttc.Tape

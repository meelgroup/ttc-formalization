/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Tree
import ttc.Model.Run
import ttc.Analysis.LegacyRun

/-!
# The law of a tree on the random tape

The tape of `Model/Run.lean` is a sequence of independent rounds.  This file proves
that a tree run on it has the law of the same tree with each random number drawn from its
law when it is read (`Tree.tapeLaw_map_exec`): "every random number is fresh".  The law
records the result, the operations spent and the membership calls left (`Tree.law`).

The proof splits the tape into its first round and the rest (`tapeLaw_eq_map_cons`): the
two are independent, and the rest is again a tape.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open ttc.Model.Operations
open ttc.SealedRun (roundLaw tapeLaw)

variable {n : ℕ}

/-! ## The tape is its first round followed by a tape -/

/-- The tape with first round `r` followed by `t`. -/
def cons (r : Round n) (t : Tape n) : Tape n
  | 0 => r
  | j + 1 => t j

@[simp] theorem cons_zero (r : Round n) (t : Tape n) : cons r t 0 = r := rfl

@[simp] theorem tail_cons (r : Round n) (t : Tape n) : (cons r t).tail = t := rfl

theorem measurable_tape_cons :
    Measurable fun p : Round n × Tape n => cons p.1 p.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  cases i with
  | zero => exact measurable_fst
  | succ j => exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_tape_tail : Measurable fun t : Tape n => t.tail :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1)

/-- The uniform law on `[0, 1]`. -/
abbrev uniformUnit : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance uniformUnit_isProbabilityMeasure : IsProbabilityMeasure uniformUnit :=
  ⟨by simp⟩

instance fairCoinLaw_isProbabilityMeasure : IsProbabilityMeasure fairCoinLaw := by
  unfold fairCoinLaw
  infer_instance

instance roundLaw_isProbabilityMeasure : IsProbabilityMeasure (roundLaw n) := by
  unfold roundLaw
  infer_instance

instance tapeLaw_isProbabilityMeasure : IsProbabilityMeasure (tapeLaw n) := by
  unfold tapeLaw
  infer_instance

/-- **The tape is its first round followed by an independent tape.** -/
theorem tapeLaw_eq_map_cons :
    tapeLaw n = ((roundLaw n).prod (tapeLaw n)).map fun p => cons p.1 p.2 := by
  symm
  refine Measure.eq_infinitePi _ fun s A hA => ?_
  classical
  let s' : Finset ℕ := s.preimage Nat.succ Nat.succ_injective.injOn
  have hpre : (fun p : Round n × Tape n => cons p.1 p.2) ⁻¹' (s : Set ℕ).pi A =
      (if 0 ∈ s then A 0 else univ) ×ˢ (s' : Set ℕ).pi fun j => A (j + 1) := by
    ext ⟨r, t⟩
    simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_prod, s', Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun j hj => h (j + 1) hj⟩
      split_ifs with h0
      · exact h 0 h0
      · exact mem_univ _
    · rintro ⟨h0, ht⟩ i hi
      cases i with
      | zero => simpa [hi] using h0
      | succ j => exact ht j hi
  have hmeas : MeasurableSet ((s : Set ℕ).pi A) :=
    MeasurableSet.pi s.countable_toSet fun i _ => hA i
  rw [Measure.map_apply measurable_tape_cons hmeas, hpre, Measure.prod_prod, tapeLaw,
    Measure.infinitePi_pi _ fun j _ => hA (j + 1)]
  have hsplit : ∏ i ∈ s, roundLaw n (A i) =
      (if 0 ∈ s then roundLaw n (A 0) else 1) * ∏ j ∈ s', roundLaw n (A (j + 1)) := by
    have himage : s.erase 0 = s'.map ⟨Nat.succ, Nat.succ_injective⟩ := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_map, Function.Embedding.coeFn_mk, s',
        Finset.mem_preimage]
      constructor
      · rintro ⟨hi0, hi⟩
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        exact ⟨j, hi, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨Nat.succ_ne_zero j, hj⟩
    have hrest : ∏ i ∈ s.erase 0, roundLaw n (A i) = ∏ j ∈ s', roundLaw n (A (j + 1)) := by
      rw [himage, Finset.prod_map]
      rfl
    split_ifs with h0
    · rw [← Finset.mul_prod_erase s _ h0, hrest]
    · rw [Finset.erase_eq_of_notMem h0] at hrest
      rw [hrest, one_mul]
  rw [hsplit]
  congr 1
  split_ifs <;> simp

/-- A measure of a set of tapes: average over the first round of the measure of the
section through the rest. -/
theorem tapeLaw_apply_eq_lintegral {A : Set (Tape n)} (hA : MeasurableSet A) :
    tapeLaw n A = ∫⁻ r, tapeLaw n {t | cons r t ∈ A} ∂roundLaw n := by
  conv_lhs => rw [tapeLaw_eq_map_cons]
  rw [Measure.map_apply measurable_tape_cons hA,
    Measure.prod_apply (measurable_tape_cons hA)]
  rfl

/-! ## The components of a round -/

theorem roundLaw_map_coin : (roundLaw n).map (fun r => r.1) = fairCoinLaw := by
  simp [roundLaw, Measure.map_fst_prod]

theorem fairCoinLaw_pair : fairCoinLaw ({false, true} : Set Bool) = 1 := by
  rw [show ({false, true} : Set Bool) = univ by ext x; cases x <;> simp]
  exact measure_univ

theorem roundLaw_map_gaussian :
    (roundLaw n).map (fun r => r.2.1) =
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [show (fun r : Round n => r.2.1) = Prod.fst ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_fst measurable_snd]
  simp [roundLaw, Measure.map_snd_prod, fairCoinLaw_pair, Measure.map_fst_prod]

theorem roundLaw_map_unit : (roundLaw n).map (fun r => r.2.2) = uniformUnit := by
  rw [show (fun r : Round n => r.2.2) = Prod.snd ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_snd measurable_snd]
  simp [roundLaw, Measure.map_snd_prod, fairCoinLaw_pair]

/-! ## The law of a tree -/

namespace Tree

variable {α : Type} [MeasurableSpace α]

/-- What a run records: its result, the operations it spent, and the calls left. -/
abbrev Outcome (α : Type) := Option α × ℕ × ℕ

/-- Add `j` operations to an outcome. -/
def addOps (j : ℕ) (r : Outcome α) : Outcome α := (r.1, j + r.2.1, r.2.2)

theorem measurable_addOps (j : ℕ) : Measurable (addOps (α := α) j) :=
  measurable_fst.prodMk ((measurable_const.add measurable_snd.fst).prodMk measurable_snd.snd)

/-- The outcome of a run, without the tape left. -/
def outcome (r : Option α × ℕ × ℕ × Tape n) : Outcome α := (r.1, r.2.1, r.2.2.1)

/-- **The law of a tree when each random number is drawn from its law as it is read**: a
fair coin, a uniform number in `[0, 1]`, a standard Gaussian vector; a Poisson or binomial
number is its quantile at a uniform number.  Records the result, the operations spent and
the membership calls left. -/
def law : Tree n α → ℕ → Measure (Outcome α)
  | .pure a, b => Measure.dirac (some a, 0, b)
  | .fail, b => Measure.dirac (none, 0, b)
  | .step c k, b => (law (k c.val) b).map (addOps (opsTotal c.cost))
  | .coin k, b => fairCoinLaw.bind fun x => (law (k x) b).map (addOps 1)
  | .unit k, b => uniformUnit.bind fun v => (law (k v) b).map (addOps 1)
  | .gaussian k, b => (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).bind
      fun g => (law (k g) b).map (addOps n)
  | .poisson rate k, b => uniformUnit.bind fun u =>
      (law (k (poissonQuantile (Real.toNNReal rate.get) u)) b).map (addOps 1)
  | .binom N k, b => uniformUnit.bind fun u =>
      (law (k (binomialHalfQuantile N.get u)) b).map (addOps 1)
  | .setBudget c k, _ => (law k c.get).map (addOps 1)
  | .spend k, 0 => law (k false) 0
  | .spend k, b + 1 => law (k true) b

/-- One random read: reading a component `π` of the first round, with law `μ`, then
continuing with `k` and adding `j` operations, has the law of drawing from `μ`,
continuing, and adding `j`. -/
private theorem draw_case {X : Type} [MeasurableSpace X] (π : Round n → X) (hπ : Measurable π)
    (μ : Measure X) (hμ : (roundLaw n).map π = μ) (σ : X → Round n) (hσ : Measurable σ)
    (hσπ : ∀ x, π (σ x) = x) (j : ℕ) (b : ℕ) (k : X → Tree n α) (R : X → Measure (Outcome α))
    (hk : Measurable fun t : Tape n => addOps j (outcome (exec (k (π (t 0))) b t.tail)))
    (ih : ∀ x, Measurable (fun t => outcome (exec (k x) b t)) →
      ∀ S, MeasurableSet S → tapeLaw n ((fun t => outcome (exec (k x) b t)) ⁻¹' S) = R x S)
    {S : Set (Outcome α)} (hS : MeasurableSet S) :
    tapeLaw n ((fun t : Tape n => addOps j (outcome (exec (k (π (t 0))) b t.tail))) ⁻¹' S) =
      (μ.bind fun x => (R x).map (addOps j)) S := by
  -- the outcome before the `j` operations are added is measurable too
  have hk' : Measurable fun t : Tape n => outcome (exec (k (π (t 0))) b t.tail) := by
    have : (fun t : Tape n => outcome (exec (k (π (t 0))) b t.tail)) =
        (fun r : Outcome α => (r.1, r.2.1 - j, r.2.2)) ∘
          fun t => addOps j (outcome (exec (k (π (t 0))) b t.tail)) := by
      funext t
      simp [addOps]
    rw [this]
    exact (measurable_fst.prodMk ((measurable_snd.fst.sub_const j).prodMk
      measurable_snd.snd)).comp hk
  -- the joint map `(x, t) ↦ exec (k x) t`
  let H : X × Tape n → Outcome α := fun p => outcome (exec (k p.1) b p.2)
  have hH : Measurable H := by
    have : H = (fun t : Tape n => outcome (exec (k (π (t 0))) b t.tail)) ∘
        fun p : X × Tape n => cons (σ p.1) p.2 := by
      funext p
      simp only [H, Function.comp_apply, cons_zero, tail_cons, hσπ]
    rw [this]
    exact hk'.comp (measurable_tape_cons.comp ((hσ.comp measurable_fst).prodMk measurable_snd))
  have hsec : ∀ x, Measurable fun t : Tape n => outcome (exec (k x) b t) := fun x =>
    hH.comp (measurable_const.prodMk measurable_id)
  have hR : ∀ x S, MeasurableSet S →
      R x S = tapeLaw n (Prod.mk x ⁻¹' (H ⁻¹' S)) := fun x S hS =>
    (ih x (hsec x) S hS).symm
  have hRmeas : Measurable R := by
    refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
    simp_rw [hR _ S hS]
    exact measurable_measure_prodMk_left (hH hS)
  have hS' : MeasurableSet (addOps j ⁻¹' S) := measurable_addOps j hS
  have hRj : Measurable fun x => (R x).map (addOps j) := by
    refine Measure.measurable_of_measurable_coe _ fun T hT => ?_
    simp_rw [Measure.map_apply (measurable_addOps j) hT]
    exact Measure.measurable_coe (measurable_addOps j hT) |>.comp hRmeas
  rw [Measure.bind_apply hS hRj.aemeasurable, ← hμ]
  simp_rw [Measure.map_apply (measurable_addOps j) hS]
  rw [lintegral_map (f := fun x => R x (addOps j ⁻¹' S))
    ((Measure.measurable_coe hS').comp hRmeas) hπ,
    show (fun t : Tape n => addOps j (outcome (exec (k (π (t 0))) b t.tail))) ⁻¹' S =
      (fun t : Tape n => outcome (exec (k (π (t 0))) b t.tail)) ⁻¹' (addOps j ⁻¹' S) from rfl,
    tapeLaw_apply_eq_lintegral (hk' hS')]
  refine lintegral_congr fun r => ?_
  rw [hR _ _ hS']
  rfl

/-- **The law of a tree on the random tape** is the law of the tree that draws each random
number from its law when it is read. -/
theorem tapeLaw_preimage_exec (p : Tree n α) (b : ℕ)
    (hp : Measurable fun t => outcome (exec p b t)) {S : Set (Outcome α)}
    (hS : MeasurableSet S) :
    tapeLaw n ((fun t => outcome (exec p b t)) ⁻¹' S) = law p b S := by
  induction p generalizing b S with
  | pure a =>
      simp only [exec, outcome, law]
      by_cases ha : ((some a, 0, b) : Outcome α) ∈ S
      · rw [preimage_const_of_mem ha, measure_univ, Measure.dirac_apply_of_mem ha]
      · rw [preimage_const_of_notMem ha, measure_empty,
          Measure.dirac_apply' _ hS, indicator_of_notMem ha]
  | fail =>
      simp only [exec, outcome, law]
      by_cases ha : ((none, 0, b) : Outcome α) ∈ S
      · rw [preimage_const_of_mem ha, measure_univ, Measure.dirac_apply_of_mem ha]
      · rw [preimage_const_of_notMem ha, measure_empty,
          Measure.dirac_apply' _ hS, indicator_of_notMem ha]
  | step c k ih =>
      have heq : (fun t => outcome (exec (Tree.step c k) b t)) =
          fun t => addOps (opsTotal c.cost) (outcome (exec (k c.val) b t)) := rfl
      have hk : Measurable fun t => outcome (exec (k c.val) b t) := by
        have : (fun t => outcome (exec (k c.val) b t)) =
            (fun r : Outcome α => (r.1, r.2.1 - opsTotal c.cost, r.2.2)) ∘
              fun t => outcome (exec (Tree.step c k) b t) := by
          funext t
          simp [heq, addOps]
        rw [this]
        exact (measurable_fst.prodMk ((measurable_snd.fst.sub_const _).prodMk
          measurable_snd.snd)).comp hp
      simp only [law]
      rw [Measure.map_apply (measurable_addOps _) hS, heq,
        show (fun t => addOps (opsTotal c.cost) (outcome (exec (k c.val) b t))) ⁻¹' S =
          (fun t => outcome (exec (k c.val) b t)) ⁻¹' (addOps (opsTotal c.cost) ⁻¹' S) from rfl,
        ih c.val b hk (measurable_addOps _ hS)]
  | coin k ih =>
      exact draw_case (fun r => r.1) measurable_fst fairCoinLaw roundLaw_map_coin
        (fun x => (x, 0, 0)) (measurable_id.prodMk measurable_const) (fun _ => rfl) 1 b k _ hp
        (fun x hx S hS => ih x b hx hS) hS
  | unit k ih =>
      exact draw_case (fun r => r.2.2) (measurable_snd.comp measurable_snd) uniformUnit
        roundLaw_map_unit (fun v => (false, 0, v))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)) (fun _ => rfl)
        1 b k _ hp (fun x hx S hS => ih x b hx hS) hS
  | gaussian k ih =>
      exact draw_case (fun r => r.2.1) (measurable_fst.comp measurable_snd) _
        roundLaw_map_gaussian (fun g => (false, g, 0))
        (measurable_const.prodMk (measurable_id.prodMk measurable_const)) (fun _ => rfl)
        n b k _ hp (fun x hx S hS => ih x b hx hS) hS
  | poisson rate k ih =>
      exact draw_case (fun r => r.2.2) (measurable_snd.comp measurable_snd) uniformUnit
        roundLaw_map_unit (fun v => (false, 0, v))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)) (fun _ => rfl)
        1 b (fun u => k (poissonQuantile (Real.toNNReal rate.get) u)) _ hp
        (fun x hx S hS => ih _ b hx hS) hS
  | binom N k ih =>
      exact draw_case (fun r => r.2.2) (measurable_snd.comp measurable_snd) uniformUnit
        roundLaw_map_unit (fun v => (false, 0, v))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)) (fun _ => rfl)
        1 b (fun u => k (binomialHalfQuantile N.get u)) _ hp
        (fun x hx S hS => ih _ b hx hS) hS
  | setBudget c k ih =>
      have heq : (fun t => outcome (exec (Tree.setBudget c k) b t)) =
          fun t => addOps 1 (outcome (exec k c.get t)) := rfl
      have hk : Measurable fun t => outcome (exec k c.get t) := by
        have : (fun t => outcome (exec k c.get t)) =
            (fun r : Outcome α => (r.1, r.2.1 - 1, r.2.2)) ∘
              fun t => outcome (exec (Tree.setBudget c k) b t) := by
          funext t
          simp [heq, addOps]
        rw [this]
        exact (measurable_fst.prodMk ((measurable_snd.fst.sub_const _).prodMk
          measurable_snd.snd)).comp hp
      simp only [law]
      rw [Measure.map_apply (measurable_addOps _) hS, heq,
        show (fun t => addOps 1 (outcome (exec k c.get t))) ⁻¹' S =
          (fun t => outcome (exec k c.get t)) ⁻¹' (addOps 1 ⁻¹' S) from rfl,
        ih c.get hk (measurable_addOps _ hS)]
  | spend k ih =>
      cases b with
      | zero => exact ih false 0 hp hS
      | succ b => exact ih true b hp hS

/-- **The outcome law of a tree on the random tape**: the tape law pushed through the
outcome of `exec` is the law of the tree with fresh draws. -/
theorem tapeLaw_map_exec (p : Tree n α) (b : ℕ)
    (hp : Measurable fun t => outcome (exec p b t)) :
    (tapeLaw n).map (fun t => outcome (exec p b t)) = law p b := by
  ext S hS
  rw [Measure.map_apply hp hS, tapeLaw_preimage_exec p b hp hS]

end Tree

end ttc.Tape

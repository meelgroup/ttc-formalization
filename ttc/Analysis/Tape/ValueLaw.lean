/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.LawBind
import ttc.Analysis.Tape.QuantileLaw

/-!
# The law of a tree's result

`Tree.vlaw p b` is the law of the result of `p` alone (`none` if it stops), forgetting the
operations and the calls left.  For a tree that does not touch CV18's query cap
(`Tree.Free`), the result of `p.bind f` has the law of `p`'s result followed by `f`'s
(`Tree.vlaw_bind`), and the primitive draws have their laws (`vlaw_coinT`, `vlaw_unitT`,
`vlaw_gaussianT`, `vlaw_poissonT`, `vlaw_binomT`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.SealedRun (roundLaw tapeLaw)
open ArlibCommunity.Algorithms.CV18 (measurable_some)

namespace Tree

variable {n : ℕ} {α β γ : Type}

/-! ## Trees that leave the query cap alone -/

/-- A tree that never sets or spends CV18's query cap. -/
def Free : Tree n α → Prop
  | .pure _ => True
  | .fail => True
  | .step c k => Free (k c.val)
  | .coin k => ∀ x, Free (k x)
  | .unit k => ∀ x, Free (k x)
  | .gaussian k => ∀ x, Free (k x)
  | .poisson _ k => ∀ x, Free (k x)
  | .binom _ k => ∀ x, Free (k x)
  | .setBudget _ _ => False
  | .spend _ => False

theorem Free.bind {p : Tree n α} {f : α → Tree n β} (hp : Free p) (hf : ∀ a, Free (f a)) :
    Free (p.bind f) := by
  induction p with
  | pure a => exact hf a
  | fail => trivial
  | step c k ih => exact ih c.val hp
  | coin k ih => exact fun x => ih x (hp x)
  | unit k ih => exact fun x => ih x (hp x)
  | gaussian k ih => exact fun x => ih x (hp x)
  | poisson r k ih => exact fun x => ih x (hp x)
  | binom N k ih => exact fun x => ih x (hp x)
  | setBudget c k ih => exact hp.elim
  | spend k ih => exact hp.elim

theorem free_pure (a : α) : Free (Tree.pure (n := n) a) := trivial
theorem free_fail : Free (Tree.fail : Tree n α) := trivial
theorem free_compute (c : Prog α) : Free (compute (n := n) c) := trivial
theorem free_coinT : Free (coinT (n := n)) := fun _ => trivial
theorem free_unitT : Free (unitT (n := n)) := fun _ => trivial
theorem free_gaussianT : Free (gaussianT (n := n)) := fun _ => trivial
theorem free_poissonT (r : Num ℝ) : Free (poissonT (n := n) r) := fun _ => trivial
theorem free_binomT (N : Num ℕ) : Free (binomT (n := n) N) := fun _ => trivial

theorem free_ite (c : Bool) {p q : Tree n α} (hp : Free p) (hq : Free q) :
    Free (if c then p else q) := by
  cases c <;> assumption

theorem free_foldlM {ι : Type} {g : β → ι → Tree n β} (hg : ∀ b x, Free (g b x)) :
    ∀ (l : List ι) (b : β), Free (l.foldlM g b)
  | [], b => trivial
  | x :: l, b => by
      simp only [List.foldlM_cons]
      exact Free.bind (hg b x) fun b' => free_foldlM hg l b'

/-- A tree that leaves the cap alone ends with the calls it started with. -/
theorem exec_budget_of_free {p : Tree n α} (hp : Free p) (b : ℕ) (t : Tape n) :
    (exec p b t).2.2.1 = b := by
  induction p generalizing t with
  | pure a => rfl
  | fail => rfl
  | step c k ih => exact ih c.val hp t
  | coin k ih => exact ih _ (hp _) _
  | unit k ih => exact ih _ (hp _) _
  | gaussian k ih => exact ih _ (hp _) _
  | poisson r k ih => exact ih _ (hp _) _
  | binom N k ih => exact ih _ (hp _) _
  | setBudget c k ih => exact hp.elim
  | spend k ih => exact hp.elim

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem ae_budget {p : Tree n α} (hp : Free p) (b : ℕ)
    (hm : Measurable fun t => outcome (exec p b t)) : ∀ᵐ o ∂law p b, o.2.2 = b := by
  rw [← tapeLaw_map_exec p b hm]
  exact (ae_map_iff hm.aemeasurable (measurable_snd.snd (measurableSet_singleton b))).mpr
    (ae_of_all _ fun t => exec_budget_of_free hp b t)

/-! ## The law of the result -/

/-- **The law of a tree's result** (`none` if it stops). -/
def vlaw (p : Tree n α) (b : ℕ) : Measure (Option α) := (law p b).map Prod.fst

theorem measurable_optionKernel {f : α → Measure (Option β)} (hf : Measurable f) :
    Measurable fun o : Option α => o.elim (Measure.dirac none) f := by
  have : (fun o : Option α => o.elim (Measure.dirac none) f) =
      Sum.elim (fun _ : Unit => Measure.dirac (none : Option β)) f ∘
        ArlibCommunity.Algorithms.CV18.optionToSum := by
    funext o
    cases o <;> rfl
  rw [this]
  exact (Measurable.sumElim measurable_const hf).comp
    ArlibCommunity.Algorithms.CV18.measurable_optionToSum

theorem MeasFam.measurable_vlaw {f : α → Tree n β} (hf : MeasFam f) (b : ℕ) :
    Measurable fun a => vlaw (f a) b :=
  (Measure.measurable_map _ measurable_fst).comp
    (hf.measurable_law.comp (measurable_id.prodMk measurable_const))

/-- **The result of a sequence**: the result of `p`, then the result of `f` at it. -/
theorem vlaw_bind {f : α → Tree n β} (hf : MeasFam f) {p : Tree n α} (hp : Free p) (b : ℕ)
    (hm : Measurable fun t => outcome (exec p b t)) :
    vlaw (p.bind f) b = (vlaw p b).bind fun o => o.elim (Measure.dirac none) fun a => vlaw (f a) b := by
  have hc := measurable_cont hf
  have hK := measurable_optionKernel (hf.measurable_vlaw b)
  rw [vlaw, law_bind hf p b hm, Measure.map_bind hc.aemeasurable measurable_fst.aemeasurable,
    vlaw, Measure.bind_map measurable_fst.aemeasurable hK.aemeasurable]
  refine Measure.bind_congr_right ?_
  filter_upwards [ae_budget hp b hm] with o ho
  obtain ⟨_ | a, m, b'⟩ := o
  · simp only [cont, Option.elim]
    rw [Measure.map_dirac' measurable_fst]
  · simp only at ho
    subst ho
    simp only [cont, Option.elim, vlaw]
    rw [Measure.map_map measurable_fst (measurable_addOps m)]
    rfl

/-- A sequence whose first part always gives a result `p`'s result law is `μ.map some`. -/
theorem vlaw_bind_of_some {f : α → Tree n β} (hf : MeasFam f) {p : Tree n α} (hp : Free p)
    (b : ℕ) (hm : Measurable fun t => outcome (exec p b t)) {μ : Measure α}
    (hμ : vlaw p b = μ.map some) : vlaw (p.bind f) b = μ.bind fun a => vlaw (f a) b := by
  rw [vlaw_bind hf hp b hm, hμ, Measure.bind_map measurable_some.aemeasurable
    (measurable_optionKernel (hf.measurable_vlaw b)).aemeasurable]
  rfl

/-! ## The primitives -/

theorem vlaw_pure (a : α) (b : ℕ) : vlaw (Tree.pure (n := n) a) b = Measure.dirac (some a) := by
  simp only [vlaw, law]
  rw [Measure.map_dirac' measurable_fst]

theorem vlaw_fail (b : ℕ) : vlaw (Tree.fail : Tree n α) b = Measure.dirac none := by
  simp only [vlaw, law]
  rw [Measure.map_dirac' measurable_fst]

theorem vlaw_compute (c : Prog α) (b : ℕ) :
    vlaw (compute (n := n) c) b = Measure.dirac (some c.val) := by
  simp only [vlaw, compute, law]
  rw [Measure.map_dirac' (measurable_addOps _), Measure.map_dirac' measurable_fst]
  rfl

/-- A draw followed by a result: the result's law is the draw's law, mapped. -/
private theorem vlaw_draw {X : Type} [MeasurableSpace X] (μ : Measure X) (g : X → α)
    (hg : Measurable g) (j b : ℕ) :
    (μ.bind fun x => (law (Tree.pure (n := n) (g x)) b).map (addOps j)).map Prod.fst =
      μ.map fun x => some (g x) := by
  have : (fun x => (law (Tree.pure (n := n) (g x)) b).map (addOps j)) =
      fun x => Measure.dirac ((some (g x), j, b) : Outcome α) := by
    funext x
    simp only [law]
    rw [Measure.map_dirac' (measurable_addOps j)]
    simp [addOps]
  rw [this, Measure.bind_dirac_eq_map (f := fun x => ((some (g x), j, b) : Outcome α)) _
      ((measurable_some.comp hg).prodMk measurable_const),
    Measure.map_map (f := fun x => ((some (g x), j, b) : Outcome α)) measurable_fst
      ((measurable_some.comp hg).prodMk measurable_const)]
  rfl

theorem vlaw_coinT (b : ℕ) : vlaw (coinT (n := n)) b = fairCoinLaw.map some :=
  vlaw_draw fairCoinLaw id measurable_id 1 b

theorem vlaw_unitT (b : ℕ) :
    vlaw (unitT (n := n)) b = uniformUnit.map fun v => some (sealDraw v).val :=
  vlaw_draw uniformUnit _ measurable_sealDraw 1 b

theorem vlaw_gaussianT (b : ℕ) :
    vlaw (gaussianT (n := n)) b = (stdGaussian (EuclideanSpace ℝ (Fin n))).map
      fun g => some (sealVector n (WithLp.ofLp g)).val :=
  vlaw_draw _ _ measurable_sealVector n b

/-- **A Poisson draw** has the Poisson law. -/
theorem vlaw_poissonT (r : Num ℝ) (b : ℕ) :
    vlaw (poissonT (n := n) r) b =
      (poissonMeasure (Real.toNNReal r.get)).map fun k => some (sealDraw k).val := by
  have hq : Measurable (poissonQuantile (Real.toNNReal r.get)) :=
    measurable_poissonQuantile.comp (measurable_const.prodMk measurable_id)
  have := vlaw_draw (n := n) uniformUnit (fun u => (sealDraw (poissonQuantile
    (Real.toNNReal r.get) u)).val) (measurable_sealDraw.comp hq) 1 b
  rw [vlaw, poissonT, law, this, ← uniformUnit_map_poissonQuantile,
    Measure.map_map (g := fun k : ℕ => some (sealDraw k).val)
    (measurable_some.comp measurable_sealDraw) hq]
  rfl

/-- **A `Binomial(N, 1/2)` draw** has the binomial law. -/
theorem vlaw_binomT (N : Num ℕ) (b : ℕ) :
    vlaw (binomT (n := n) N) b = (binomial N.get half).map fun k => some (sealDraw k).val := by
  have hq : Measurable (binomialHalfQuantile N.get) :=
    measurable_binomialHalfQuantile.comp (measurable_const.prodMk measurable_id)
  have := vlaw_draw (n := n) uniformUnit (fun u => (sealDraw (binomialHalfQuantile
    N.get u)).val) (measurable_sealDraw.comp hq) 1 b
  rw [vlaw, binomT, law, this, ← uniformUnit_map_binomialHalfQuantile,
    Measure.map_map (g := fun k : ℕ => some (sealDraw k).val)
    (measurable_some.comp measurable_sealDraw) hq]
  rfl

end Tree

end ttc.Tape

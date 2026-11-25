/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.HitAndRunLaw
import ttc.Analysis.RoundPoint
import ttc.Analysis.BallStart

/-!
# One sample attempt has the old model's law

* the start point (`startT`) is the old start point: uniform on the unit ball
  (`vlaw_startT`);
* the rounding (`roundPointT`) is KV97's rounding (`vlaw_roundPointT`);
* a whole attempt (`sampleTryT`) draws the start point, walks, maps by the chart, rounds and
  tests membership (`vlaw_sampleTryT`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc.SealedRun (roundLaw tapeLaw)
open ArlibCommunity.Algorithms.CV18 (measurable_some)
open ArlibCommunity.Foundations.MarkovChainTheory (iterate)

variable {d : ℕ}

/-! ## Vectors of the tape -/

/-- **The first `k` rounds of the tape are independent.** -/
theorem tapeLaw_map_vec {X : Type} [MeasurableSpace X] {f : Round d → X} (hf : Measurable f) :
    ∀ k : ℕ, (tapeLaw d).map (fun t => fun i : Fin k => f (t i)) =
      Measure.pi fun _ : Fin k => (roundLaw d).map f
  | 0 => by
      rw [Measure.pi_of_empty (x := fun i => i.elim0)]
      have : (fun t : Tape d => fun i : Fin 0 => f (t i)) = fun _ => fun i => i.elim0 := by
        funext t i; exact i.elim0
      rw [this, Measure.map_const, measure_univ, one_smul]
  | k + 1 => by
      have hvec : ∀ m : ℕ, Measurable fun t : Tape d => fun i : Fin m => f (t i) := fun m =>
        measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply _)
      let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => X) 0).symm
      have heq : (fun t : Tape d => fun i : Fin (k + 1) => f (t i)) =
          e ∘ fun t => (f (t 0), (fun t' : Tape d => fun i : Fin k => f (t' i)) t.tail) := by
        funext t i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
          rfl
      have hF : Measurable fun t : Tape d =>
          (f (t 0), (fun t' : Tape d => fun i : Fin k => f (t' i)) t.tail) :=
        (hf.comp (measurable_pi_apply 0)).prodMk ((hvec k).comp measurable_tape_tail)
      rw [heq, ← Measure.map_map e.measurable hF,
        tapeLaw_map_head_tail hf (hvec k), tapeLaw_map_vec hf k]
      exact (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => (roundLaw d).map f) 0).symm.map_eq

/-! ## Rounding -/

/-- An integer point, held, as integers. -/
def getZ {k : ℕ} (z : Fin k → Num ℤ) : Fin k → ℤ := fun i => (z i).get

theorem measurable_getZ {k : ℕ} : Measurable (getZ (k := k)) :=
  measurable_pi_iff.mpr fun i => Num.measurable_get.comp (measurable_pi_apply i)

/-- What the rounding computes on a tape: coordinate `i` reads the uniform number of round
`i`. -/
theorem exec_roundCoordsT (one : Num ℤ) (hone : one.get = 1) :
    ∀ (k : ℕ) (q : Fin k → Num ℝ) (b : ℕ) (t : Tape d),
      Option.map (fun z i => (z i).get) (exec (roundCoordsT (d := d) one k q) b t).1 =
        some (fun i : Fin k => ⌊(q i).get⌋ + if (t i).2.2 < (q i).get - ⌊(q i).get⌋ then 1 else 0)
  | 0, q, b, t => by
      simp only [roundCoordsT, exec, Option.map_some]
      congr 1
      funext i
      exact i.elim0
  | k + 1, q, b, t => by
      have ih := exec_roundCoordsT one hone k (Fin.tail q) b t.tail
      simp only [roundCoordsT, unitT, compute, Tree.bind, exec]
      rw [exec_bind]
      rcases h : exec (roundCoordsT (d := d) one k (Fin.tail q)) b t.tail with ⟨_ | w, m, b', t'⟩
      · rw [h] at ih; simp at ih
      · rw [h] at ih
        simp only [Option.map_some, Option.some.injEq] at ih ⊢
        simp only [exec, Option.map_some, Option.some.injEq]
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          simp [floor, intCast, A.sub, A.lt, A.add, A.pure]
          by_cases hv : (t 0).2.2 < Int.fract (q 0).get
          · simp [hv, not_le.mpr hv, Num.get_add, hone]
          · simp [hv, not_lt.mp hv]
        · have := congrFun ih j
          simp only [Fin.cons_succ]
          exact this

theorem roundPointT_eq (p : NumPoint d) :
    roundPointT p = Tree.step (A.lit (1 : ℤ)) fun one => roundCoordsT one d p := rfl

/-- **The sealed rounding is KV97's rounding**, at every point. -/
theorem vlaw_roundPointT (p : NumPoint d) (b : ℕ) :
    (vlaw (roundPointT p) b).map (Option.map getZ) = (roundPointLaw (toPt p)).map some := by
  have hm : Measurable fun t => outcome (exec (roundPointT p) b t) :=
    (mf_roundPoint (Q := Unit) (p := fun _ => p) measurable_const).outcome () b
  have hR : Measurable fun v : Fin d → ℝ => fun i : Fin d =>
      ⌊(p i).get⌋ + if v i < (p i).get - ⌊(p i).get⌋ then (1 : ℤ) else 0 :=
    measurable_pi_iff.mpr fun i => (Measurable.ite (measurableSet_lt (measurable_pi_apply i)
      measurable_const) measurable_const measurable_const).const_add _
  have hv : Measurable fun t : Tape d => fun i : Fin d => (t i).2.2 :=
    measurable_pi_iff.mpr fun i => (measurable_snd.comp measurable_snd).comp (measurable_pi_apply _)
  have hfun : (fun t => Option.map getZ (outcome (exec (roundPointT p) b t)).1) =
      (some ∘ fun v : Fin d → ℝ => fun i : Fin d =>
        ⌊(p i).get⌋ + if v i < (p i).get - ⌊(p i).get⌋ then (1 : ℤ) else 0) ∘
        fun t : Tape d => fun i : Fin d => (t i).2.2 := by
    funext t
    exact exec_roundCoordsT _ rfl d p b t
  rw [vlaw, ← tapeLaw_map_exec _ b hm, Measure.map_map measurable_fst hm,
    Measure.map_map (measurable_optionMap measurable_getZ) (measurable_fst.comp hm)]
  change (tapeLaw d).map (fun t => Option.map getZ (outcome (exec (roundPointT p) b t)).1) = _
  have hold : roundPointLaw (toPt p) = (Measure.pi fun _ : Fin d => uniformUnit).map
      fun v : Fin d → ℝ => fun i : Fin d =>
        ⌊(p i).get⌋ + if v i < (p i).get - ⌊(p i).get⌋ then (1 : ℤ) else 0 := by
    rw [roundPointLaw]
    congr 1
    funext v
    rw [RoundPoint.roundPoint_value]
    rfl
  rw [hfun, ← Measure.map_map (measurable_some.comp hR) hv,
    tapeLaw_map_vec (f := fun r : Round d => r.2.2) (measurable_snd.comp measurable_snd) d, roundLaw_map_unit, hold,
    Measure.map_map measurable_some hR]

/-! ## The start point -/

/-- The start point of an attempt: a uniform point of the unit ball. -/
def startT (dimN : Num ℕ) : Tree d (NumPoint d) :=
  gaussianT.bind fun g => unitT.bind fun u => compute (A.ballStart dimN g u)

theorem toPt_ballStart (dimN : Num ℕ) (g : NumPoint d) (u : Num ℝ) :
    toPt (A.ballStart dimN g u).val = ((u.get ^ ((dimN.get : ℝ)⁻¹)) / ‖toPt g‖) • toPt g := by
  ext i
  simp [A.ballStart, A.normSq, A.sqrt, A.root, A.div, A.smul, A.mul, val_forEach, get_dot,
    EuclideanSpace.norm_eq, dotProduct, sq]

/-- **The sealed start point is the old start point**: uniform on the unit ball. -/
theorem vlaw_startT (dimN : Num ℕ) (hdim : dimN.get = d) (b : ℕ) :
    (vlaw (startT dimN) b).map (Option.map toPt) = (ballStartLaw d).map some := by
  have hm : Measurable fun t => outcome (exec (startT (d := d) dimN) b t) := by
    have : MeasFam fun _ : Unit => startT (d := d) dimN := by
      unfold startT
      refine MeasFam.gaussianT ?_
      refine MeasFam.unitT ?_
      exact MeasFam.computeEnd (mp_ballStart measurable_const measurable_fst.snd measurable_snd)
    exact this.outcome () b
  have hB : Measurable fun ω : EuclideanSpace ℝ (Fin d) × ℝ =>
      (ω.2 ^ ((d : ℝ)⁻¹) / ‖ω.1‖) • ω.1 := by fun_prop
  have h2 : Measurable fun t : Tape d => ((t 0).2.1, (t.tail 0).2.2) :=
    ((measurable_fst.comp measurable_snd).comp (measurable_pi_apply 0)).prodMk
      ((measurable_snd.comp measurable_snd).comp ((measurable_pi_apply 0).comp measurable_tape_tail))
  have hfun : (fun t => Option.map toPt (outcome (exec (startT (d := d) dimN) b t)).1) =
      (some ∘ fun ω : EuclideanSpace ℝ (Fin d) × ℝ => (ω.2 ^ ((d : ℝ)⁻¹) / ‖ω.1‖) • ω.1) ∘
        fun t : Tape d => ((t 0).2.1, (t.tail 0).2.2) := by
    funext t
    simp only [startT, gaussianT, unitT, compute, Tree.bind, exec, outcome, Function.comp_apply,
      Option.map_some]
    rw [toPt_ballStart, hdim, toPt_sealVector]
    simp
  have hlaw : (tapeLaw d).map (fun t => ((t 0).2.1, (t.tail 0).2.2)) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).prod uniformUnit := by
    rw [tapeLaw_map_head_tail (f := fun r : Round d => r.2.1) (g := fun t : Tape d => (t 0).2.2)
      (measurable_fst.comp measurable_snd)
      ((measurable_snd.comp measurable_snd).comp (measurable_pi_apply 0)),
      roundLaw_map_gaussian,
      show (fun t : Tape d => (t 0).2.2) = (fun r : Round d => r.2.2) ∘ (fun t => t 0) from rfl,
      ← Measure.map_map (g := fun r : Round d => r.2.2) (f := fun t : Tape d => t 0)
        (measurable_snd.comp measurable_snd) (measurable_pi_apply 0),
      tapeLaw_map_eval_zero, roundLaw_map_unit]
  rw [vlaw, ← tapeLaw_map_exec _ b hm, Measure.map_map measurable_fst hm,
    Measure.map_map (measurable_optionMap measurable_toPt) (measurable_fst.comp hm)]
  change (tapeLaw d).map (fun t => Option.map toPt (outcome (exec (startT (d := d) dimN) b t)).1) = _
  have hold : ballStartLaw d = ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod uniformUnit).map
      fun ω : EuclideanSpace ℝ (Fin d) × ℝ => (ω.2 ^ ((d : ℝ)⁻¹) / ‖ω.1‖) • ω.1 := by
    rw [ballStartLaw]
    congr 1
    funext ω
    exact BallStart.ballStart_value ω.1 ω.2
  rw [hfun, ← Measure.map_map (measurable_some.comp hB) h2, hlaw, hold,
    Measure.map_map measurable_some hB]

end ttc.Tape

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc.SealedRun (roundLaw tapeLaw)
open ArlibCommunity.Algorithms.CV18 (measurable_some)
open ArlibCommunity.Foundations.MarkovChainTheory (iterate)

variable {d : ℕ}

/-! ## A whole attempt -/

/-- The chart from the unit-inball chart to the scaled body. -/
def chartProg {r : ℕ} (W : WalkConstants d r) (y : NumPoint d) : Prog (NumPoint d) :=
  A.forEach fun i => do
    let s ← A.mul W.scaledInradius (y i)
    A.add s (W.scaledIncenter i)

/-- After the walk: map by the chart, round, and test membership. -/
def finishT (L : Loaded d) (W : WalkConstants d L.facets) (scaled : Fin L.facets → Num ℝ)
    (y : NumPoint d) : Tree d (Option (Fin d → Num ℤ)) :=
  (compute (chartProg W y)).bind fun p =>
    (roundPointT p).bind fun z =>
      (compute (latticeMember L scaled z)).bind fun ok => .pure (if ok then some z else none)

theorem sampleTryT_eq (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) :
    sampleTryT L W scaled dimN = (startT dimN).bind fun y₀ =>
      (hitAndRunWalkT L.facets L.normal W.offsets W.steps y₀).bind (finishT L W scaled) := rfl

/-! ### Leaving the cap alone -/

theorem free_roundCoordsT (one : Num ℤ) :
    ∀ (k : ℕ) (q : Fin k → Num ℝ), Free (roundCoordsT (d := d) one k q)
  | 0, _ => trivial
  | k + 1, _ => Free.bind free_unitT fun _ => Free.bind (free_compute _) fun _ =>
      Free.bind (free_roundCoordsT one k _) fun _ => free_pure _

theorem free_roundPointT (p : NumPoint d) : Free (roundPointT p) :=
  free_roundCoordsT _ d p

theorem free_startT (dimN : Num ℕ) : Free (startT (d := d) dimN) :=
  Free.bind free_gaussianT fun _ => Free.bind free_unitT fun _ => free_compute _

theorem free_hitAndRunWalkT (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (steps : Num ℕ) (x : NumPoint d) : Free (hitAndRunWalkT r a β' steps x) :=
  Free.bind (Tree.free_loopRounds (free_walkBodyT r a β') _ x) fun _ => free_pure _

theorem free_finishT (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (y : NumPoint d) : Free (finishT L W scaled y) :=
  Free.bind (free_compute _) fun p => Free.bind (free_roundPointT p) fun _ =>
    Free.bind (free_compute _) fun _ => free_pure _

/-! ### Measurability -/

theorem mf_memberEnd (L : Loaded d) (scaled : Fin L.facets → Num ℝ) :
    MeasFam fun z : Fin d → Num ℤ => (compute (latticeMember L scaled z)).bind
      fun ok => (Tree.pure (if ok then some z else none) : Tree d _) :=
  MeasFam.compute (mp_latticeMember L scaled measurable_id)
    (MeasFam.pure (measurable_bif measurable_snd (measurable_some.comp measurable_fst)
      measurable_const))

theorem mf_finishT (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) : MeasFam fun y : NumPoint d => finishT L W scaled y := by
  unfold finishT chartProg
  refine MeasFam.compute (mp_chart W measurable_id) ?_
  exact MeasFam.bind' (mf_roundPoint measurable_snd) ((mf_memberEnd L scaled).comp measurable_snd)

theorem mf_restT (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) :
    MeasFam fun y₀ : NumPoint d =>
      (hitAndRunWalkT L.facets L.normal W.offsets W.steps y₀).bind (finishT L W scaled) :=
  MeasFam.bind' (mf_hitAndRunWalk _ _ _ _ measurable_id) ((mf_finishT L W scaled).comp measurable_snd)

/-! ### Laws -/

theorem pure_bindT {α β : Type} (a : α) (f : α → Tree d β) : (Tree.pure a).bind f = f a := rfl

/-- An integer point, sealed. -/
def sealZ {k : ℕ} (w : Fin k → ℤ) : Fin k → Num ℤ := fun i => (sealDraw (w i)).val

@[simp] theorem getZ_sealZ {k : ℕ} (w : Fin k → ℤ) : getZ (sealZ w) = w := by
  funext i; simp [getZ, sealZ]

@[simp] theorem sealZ_getZ {k : ℕ} (z : Fin k → Num ℤ) : sealZ (getZ z) = z := by
  funext i; exact Num.ext (by simp [getZ, sealZ])

theorem measurable_sealZ {k : ℕ} : Measurable (sealZ (k := k)) :=
  measurable_pi_iff.mpr fun i => measurable_sealDraw.comp (measurable_pi_apply i)

/-- Whether an integer point is accepted: the sealed membership test. -/
def accepts (L : Loaded d) (scaled : Fin L.facets → Num ℝ) (w : Fin d → ℤ) : Bool :=
  (latticeMember L scaled (sealZ w)).val

/-- The result of an attempt with integer point `w`. -/
def verdict (L : Loaded d) (scaled : Fin L.facets → Num ℝ) (w : Fin d → ℤ) :
    Option (Option (Fin d → ℤ)) :=
  some (if accepts L scaled w then some w else none)

/-- The result of an attempt, as integers. -/
def attemptView : Option (Option (Fin d → Num ℤ)) → Option (Option (Fin d → ℤ)) :=
  Option.map (Option.map getZ)

theorem measurable_attemptView : Measurable (attemptView (d := d)) :=
  measurable_optionMap (measurable_optionMap measurable_getZ)

/-- The sealed rounding's law, held. -/
theorem vlaw_roundPointT' (p : NumPoint d) (b : ℕ) :
    vlaw (roundPointT p) b = (roundPointLaw (toPt p)).map fun w => some (sealZ w) := by
  have h := congrArg (Measure.map (Option.map sealZ)) (vlaw_roundPointT p b)
  rw [Measure.map_map (measurable_optionMap measurable_sealZ) (measurable_optionMap measurable_getZ),
    Measure.map_map (measurable_optionMap measurable_sealZ) measurable_some] at h
  have hid : Option.map sealZ ∘ Option.map (getZ (k := d)) = id := by
    funext o; cases o <;> simp
  rw [hid, Measure.map_id] at h
  rw [h]
  rfl

/-- **After the walk**: the rounding law at the chart's point, with the membership verdict. -/
theorem vlaw_finishT (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (y : NumPoint d) (b : ℕ) :
    (vlaw (finishT L W scaled y) b).map attemptView =
      (roundPointLaw (toPt (chartProg W y).val)).map (verdict L scaled) := by
  have hm : Measurable fun t => outcome (exec (roundPointT (d := d) (chartProg W y).val) b t) :=
    (mf_roundPoint (Q := Unit) (p := fun _ => (chartProg W y).val) measurable_const).outcome () b
  have hK : ∀ z : Fin d → Num ℤ, vlaw ((compute (latticeMember L scaled z)).bind
      fun ok => (Tree.pure (if ok then some z else none) : Tree d _)) b =
      Measure.dirac (some (if (latticeMember L scaled z).val then some z else none)) := by
    intro z
    show vlaw (Tree.step _ _) b = _
    rw [vlaw_step, pure_bindT, vlaw_pure]
  show (vlaw (Tree.step (chartProg W y) _) b).map attemptView = _
  rw [vlaw_step, pure_bindT, vlaw_bind (mf_memberEnd L scaled) (free_roundPointT _) b hm,
    vlaw_roundPointT', Measure.bind_map (f := fun w => some (sealZ w))
      (measurable_some.comp measurable_sealZ).aemeasurable (measurable_optionKernel ((mf_memberEnd L scaled).measurable_vlaw b)).aemeasurable]
  simp only [Function.comp_def, Option.elim, hK]
  rw [Measure.bind_dirac_eq_map _ (measurable_of_countable _),
    Measure.map_map measurable_attemptView (measurable_of_countable _)]
  congr 1
  funext w
  simp only [Function.comp_apply, attemptView, verdict, accepts, Option.map_some]
  split_ifs with h <;> simp [h]


/-- The walk's result law, held. -/
theorem vlaw_hitAndRunWalkT' [NeZero d] (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (hK : Bornology.IsBounded (bodyOf r a β')) (steps : Num ℕ) (x : NumPoint d)
    (hx : toPt x ∈ bodyOf r a β') (b : ℕ) :
    vlaw (hitAndRunWalkT r a β' steps x) b =
      (iterate (ttc.HitAndRunLaw.lazyKernel (presOf r a β')) (Measure.dirac (toPt x))
        steps.get).map fun z => some (ofPt z) := by
  have h := congrArg (Measure.map (Option.map ofPt)) (vlaw_hitAndRunWalkT r a β' hK steps x hx b)
  rw [Measure.map_map (measurable_optionMap measurable_ofPt) (measurable_optionMap measurable_toPt),
    Measure.map_map (measurable_optionMap measurable_ofPt) measurable_some] at h
  have hid : Option.map ofPt ∘ Option.map (toPt (d := d)) = id := by
    funext o; cases o <;> simp
  rw [hid, Measure.map_id] at h
  rw [h]
  rfl

/-- The start point's law, held. -/
theorem vlaw_startT' (dimN : Num ℕ) (hdim : dimN.get = d) (b : ℕ) :
    vlaw (startT dimN) b = (ballStartLaw d).map fun z => some (ofPt z) := by
  have h := congrArg (Measure.map (Option.map ofPt)) (vlaw_startT dimN hdim b)
  rw [Measure.map_map (measurable_optionMap measurable_ofPt) (measurable_optionMap measurable_toPt),
    Measure.map_map (measurable_optionMap measurable_ofPt) measurable_some] at h
  have hid : Option.map ofPt ∘ Option.map (toPt (d := d)) = id := by
    funext o; cases o <;> simp
  rw [hid, Measure.map_id] at h
  rw [h]
  rfl

/-- The law of what follows a walk ending at `z`. -/
def finishLaw (L : Loaded d) (W : WalkConstants d L.facets) (scaled : Fin L.facets → Num ℝ)
    (b : ℕ) (z : EuclideanSpace ℝ (Fin d)) : Measure (Option (Option (Fin d → ℤ))) :=
  (vlaw (finishT L W scaled (ofPt z)) b).map attemptView

theorem measurable_finishLaw (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (b : ℕ) : Measurable (finishLaw L W scaled b) :=
  (Measure.measurable_map _ measurable_attemptView).comp
    (((mf_finishT L W scaled).measurable_vlaw b).comp measurable_ofPt)

theorem finishLaw_eq (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (b : ℕ) (z : EuclideanSpace ℝ (Fin d)) :
    finishLaw L W scaled b z =
      (roundPointLaw (toPt (chartProg W (ofPt z)).val)).map (verdict L scaled) :=
  vlaw_finishT L W scaled (ofPt z) b

/-- The walk's body: the polytope with the walk's facets and offsets. -/
abbrev walkBody (L : Loaded d) (W : WalkConstants d L.facets) : Set (EuclideanSpace ℝ (Fin d)) :=
  bodyOf L.facets L.normal W.offsets

/-- The walk's kernel: arlib's lazy Hit-and-Run on the walk's body. -/
abbrev walkKernel (L : Loaded d) (W : WalkConstants d L.facets) :=
  ttc.HitAndRunLaw.lazyKernel (presOf L.facets L.normal W.offsets)

/-- **A walk from a point of the body, then the rest of an attempt.** -/
theorem vlaw_restT [NeZero d] (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (hK : Bornology.IsBounded (walkBody L W)) (y₀ : NumPoint d)
    (hy : toPt y₀ ∈ walkBody L W) (b : ℕ) :
    (vlaw ((hitAndRunWalkT L.facets L.normal W.offsets W.steps y₀).bind (finishT L W scaled)) b).map
        attemptView =
      (iterate (walkKernel L W) (Measure.dirac (toPt y₀)) W.steps.get).bind
        (finishLaw L W scaled b) := by
  have hm : Measurable fun t =>
      outcome (exec (hitAndRunWalkT L.facets L.normal W.offsets W.steps y₀) b t) :=
    (mf_hitAndRunWalk (Q := Unit) _ _ _ _ (x := fun _ => y₀) measurable_const).outcome () b
  have hker := (mf_finishT L W scaled).measurable_vlaw b
  rw [vlaw_bind (mf_finishT L W scaled) (free_hitAndRunWalkT _ _ _ _ _) b hm,
    vlaw_hitAndRunWalkT' _ _ _ hK _ _ hy, Measure.bind_map (f := fun z => some (ofPt z))
      (measurable_some.comp measurable_ofPt).aemeasurable (measurable_optionKernel hker).aemeasurable]
  simp only [Option.elim]
  rw [Measure.map_bind (show Measurable fun a => vlaw (finishT L W scaled (ofPt a)) b from
    hker.comp measurable_ofPt).aemeasurable measurable_attemptView.aemeasurable]
  rfl

/-- **One attempt has the old model's proposal law**: start uniformly in the unit ball, run
the walk for its `T` steps, map by the chart, round, and test membership.  The unit ball must
lie in the walk's body (the chart puts the inscribed ball there). -/
theorem vlaw_sampleTryT [NeZero d] (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) (hdim : dimN.get = d)
    (hK : Bornology.IsBounded (walkBody L W))
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ walkBody L W) (b : ℕ) :
    (vlaw (sampleTryT L W scaled dimN) b).map attemptView =
      (iterate (walkKernel L W) (ballStartLaw d) W.steps.get).bind (finishLaw L W scaled b) := by
  have hm : Measurable fun t => outcome (exec (startT (d := d) dimN) b t) := by
    have : MeasFam fun _ : Unit => startT (d := d) dimN := by
      unfold startT
      refine MeasFam.gaussianT ?_
      refine MeasFam.unitT ?_
      exact MeasFam.computeEnd (mp_ballStart measurable_const measurable_fst.snd measurable_snd)
    exact this.outcome () b
  have hker := (mf_restT L W scaled).measurable_vlaw b
  have hF := measurable_finishLaw L W scaled b
  -- the start point lies in the body
  have hae : ∀ᵐ y ∂ballStartLaw d, y ∈ walkBody L W := by
    rw [BallStart.ballStartLaw_eq, ae_iff]
    refine measure_mono_null (fun y hy => ?_) (?_ : ArlibCommunity.Foundations.Convex.uniformOn
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) (Metric.ball 0 1)ᶜ = 0)
    · exact fun hb => hy (hball hb)
    · simp [ArlibCommunity.Foundations.Convex.uniformOn,
        ArlibCommunity.Foundations.Convex.condOn, Measure.restrict_apply measurableSet_ball.compl]
  have hcongr : (fun y => (vlaw ((hitAndRunWalkT L.facets L.normal W.offsets W.steps (ofPt y)).bind
      (finishT L W scaled)) b).map attemptView) =ᵐ[ballStartLaw d]
      fun y => (iterate (walkKernel L W) (Measure.dirac y) W.steps.get).bind
        (finishLaw L W scaled b) :=
    hae.mono fun y hy => by
      have := vlaw_restT L W scaled hK (ofPt y) (by rwa [toPt_ofPt]) b
      rwa [toPt_ofPt] at this
  rw [sampleTryT_eq, vlaw_bind (mf_restT L W scaled) (free_startT dimN) b hm, vlaw_startT' dimN hdim,
    Measure.bind_map (f := fun z => some (ofPt z)) (measurable_some.comp measurable_ofPt).aemeasurable
      (measurable_optionKernel hker).aemeasurable]
  simp only [Option.elim]
  rw [Measure.map_bind (show Measurable fun a => vlaw ((hitAndRunWalkT L.facets L.normal W.offsets
      W.steps (ofPt a)).bind (finishT L W scaled)) b from hker.comp measurable_ofPt).aemeasurable
      measurable_attemptView.aemeasurable,
    Measure.bind_congr_right hcongr,
    iterate_eq_bind, Measure.bind_bind (measurable_iterate_dirac _ _).aemeasurable hF.aemeasurable]

end ttc.Tape

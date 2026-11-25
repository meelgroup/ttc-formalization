/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.ChargedExec

/-!
# The sealed CV18 runs like the charged CV18

On every tape, the sealed program's CV18 (`cv18T`) and the charged CV18 program the accuracy
theorem is about (`ttc.ChargedCV18.cv18Program`) compute the same thing, when the charged
program's membership queries are answered by the sealed program's membership routine.

The two are written procedure by procedure in the same way, so the proof goes procedure by
procedure: `Sim R p P` says that the tree `p` and the charged program `P`, run on the same
tape with the same membership calls left, give results related by `R` and leave the same
calls and the same tape.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Tape.Tree
open ttc.ChargedCV18 (ChargedProgram)

variable {d : ℕ} {α β γ δ : Type}

/-! ## Simulation -/

section Sim

variable (O : EuclideanSpace ℝ (Fin d) → Bool)

/-- **`p` runs like `P`**: on every tape and with every number of membership calls left, the
results are related by `R`, and the calls left and the tapes left are the same. -/
def Sim (R : α → β → Prop) (p : Tree d α) (P : ChargedProgram d β) : Prop :=
  ∀ (b : ℕ) (t : Tape d), Option.Rel R (exec p b t).1 (cexec O P b t).1 ∧
    ((exec p b t).2.2.1 : ℕ∞) = (cexec O P b t).2.1 ∧ (exec p b t).2.2.2 = (cexec O P b t).2.2

variable {O}

theorem Sim.bind {R : α → β → Prop} {S : γ → δ → Prop} {p : Tree d α} {P : ChargedProgram d β}
    {f : α → Tree d γ} {F : β → ChargedProgram d δ} (hp : Sim O R p P)
    (hf : ∀ a a', R a a' → Sim O S (f a) (F a')) : Sim O S (p.bind f) (P.bind F) := by
  intro b t
  rw [exec_bind, cexec_bind]
  obtain ⟨h1, h2, h3⟩ := hp b t
  rcases e : exec p b t with ⟨o, m, b', t'⟩
  rcases E : cexec O P b t with ⟨o', B', T'⟩
  rw [e, E] at h1 h2 h3
  simp only at h1 h2 h3
  subst h2 h3
  cases h1 with
  | none => exact ⟨Option.Rel.none, rfl, rfl⟩
  | some h => exact hf _ _ h b' t'

theorem sim_pure {R : α → β → Prop} {a : α} {a' : β} (h : R a a') :
    Sim O R (Tree.pure a) (ChargedProgram.pure a') :=
  fun _ _ => ⟨Option.Rel.some h, rfl, rfl⟩

theorem sim_pure_eq (a : α) : Sim O Eq (Tree.pure a) (ChargedProgram.pure a) :=
  sim_pure rfl

theorem sim_compute {R : α → β → Prop} (c : Prog α) (c' : ttc.ChargedCV18.Counted β)
    (h : R c.val c'.value) : Sim O R (compute c) (ttc.ChargedCV18.compute c') :=
  fun _ _ => ⟨Option.Rel.some h, rfl, rfl⟩

theorem sim_compute_eq (c : Prog α) (c' : ttc.ChargedCV18.Counted α) (h : c.val = c'.value) :
    Sim O Eq (compute c) (ttc.ChargedCV18.compute c') :=
  sim_compute c c' h

theorem sim_ite {R : α → β → Prop} (c : Prop) [Decidable c] {p q : Tree d α}
    {P Q : ChargedProgram d β} (hp : Sim O R p P) (hq : Sim O R q Q) :
    Sim O R (if c then p else q) (if c then P else Q) := by
  split_ifs
  · exact hp
  · exact hq

theorem Sim.mono {R R' : α → β → Prop} {p : Tree d α} {P : ChargedProgram d β}
    (h : Sim O R p P) (hR : ∀ a a', R a a' → R' a a') : Sim O R' p P := by
  intro b t
  obtain ⟨h1, h2, h3⟩ := h b t
  refine ⟨?_, h2, h3⟩
  generalize (exec p b t).1 = x at h1 ⊢
  generalize (cexec O P b t).1 = y at h1 ⊢
  cases h1 with
  | none => exact Option.Rel.none
  | some h => exact Option.Rel.some (hR _ _ h)

/-- A Gaussian vector from the tape. -/
theorem sim_gaussianT :
    Sim O Eq (gaussianT (n := d))
      (ttc.ChargedCV18.drawPoint (ttc.ChargedCV18.standardGaussian d)) := by
  intro b t
  refine ⟨Option.Rel.some ?_, rfl, rfl⟩
  funext i
  apply Num.ext
  simp [gaussianT, exec, cexec, ttc.ChargedCV18.drawPoint, ttc.ChargedCV18.compute,
    get_sealVector, ttc.ChargedCV18.Counted.forEach_value]

/-- A uniform number from the tape. -/
theorem sim_unitT :
    Sim O Eq (unitT (n := d)) (ttc.ChargedCV18.drawReal ArlibCommunity.Algorithms.CV18.uniformUnit) := by
  intro b t
  refine ⟨Option.Rel.some ?_, rfl, rfl⟩
  apply Num.ext
  simp [unitT, exec, cexec, ttc.ChargedCV18.drawReal, ttc.ChargedCV18.compute]

/-- The rounds of a loop. -/
theorem sim_loopRounds {β' : Type} {body : β → Tree d (β ⊕ β')}
    {body' : β → ChargedProgram d (β ⊕ β')} (h : ∀ s, Sim O Eq (body s) (body' s)) :
    ∀ (k : ℕ) (s : β), Sim O Eq (loopRounds body k s) (ChargedProgram.loopRounds body' k s)
  | 0, s => sim_pure_eq _
  | k + 1, s => by
      refine Sim.bind (h s) fun r r' hr => ?_
      subst hr
      rcases r with s' | c
      · exact sim_loopRounds h k s'
      · exact sim_pure_eq _

/-- A loop of `count` rounds. -/
theorem sim_loopTree {β' : Type} (count : Num ℕ) {body : β → Tree d (β ⊕ β')}
    {body' : β → ChargedProgram d (β ⊕ β')} (h : ∀ s, Sim O Eq (body s) (body' s)) (init : β) :
    Sim O Eq (loopTree count body init) (ttc.ChargedCV18.loopUntil count body' init) :=
  fun b t => sim_loopRounds h count.get init b t

end Sim


section Loops

/-- A loop with a break computes the same in any currency, round by round. -/
theorem val_foldlWhile_congr {κ₁ κₛ₁ κ₂ κₛ₂ δ ι : Type}
    (f : δ → ι → Charged κ₁ κₛ₁ (Option δ)) (g : δ → ι → Charged κ₂ κₛ₂ (Option δ))
    (h : ∀ b a, (f b a).val = (g b a).val) :
    ∀ (l : List ι) (b : δ), (Charged.foldlWhile f l b).val = (Charged.foldlWhile g l b).val
  | [], b => rfl
  | a :: l, b => by
      have ih := val_foldlWhile_congr f g h l
      have hf : (Charged.foldlWhile f (a :: l) b).val =
          match (f b a).val with
          | none => b
          | some b' => (Charged.foldlWhile f l b').val := by
        rcases e : (f b a).val with _ | b'
        · simp only [Charged.foldlWhile]
          simp only [Charged.val] at e ⊢
          rw [e]
        · simp only [Charged.foldlWhile]
          simp only [Charged.val] at e ⊢
          rw [e]
      have hg : (Charged.foldlWhile g (a :: l) b).val =
          match (g b a).val with
          | none => b
          | some b' => (Charged.foldlWhile g l b').val := by
        rcases e : (g b a).val with _ | b'
        · simp only [Charged.foldlWhile]
          simp only [Charged.val] at e ⊢
          rw [e]
        · simp only [Charged.foldlWhile]
          simp only [Charged.val] at e ⊢
          rw [e]
      rw [hf, hg, h b a]
      rcases (g b a).val with _ | b'
      · rfl
      · exact ih b'

theorem val_iterateWhile_congr {κ₁ κₛ₁ κ₂ κₛ₂ δ : Type} [Fintype κ₁] [Fintype κ₂]
    [DecidableEq κ₁] [DecidableEq κ₂] [Arlib.Computation.NumOps κ₁] [Arlib.Computation.NumOps κ₂]
    (f : ℕ → δ → Charged κ₁ κₛ₁ (Option δ)) (g : ℕ → δ → Charged κ₂ κₛ₂ (Option δ))
    (h : ∀ i b, (f i b).val = (g i b).val) (n : Num ℕ) (b : δ) :
    (Num.iterateWhile f n b).val = (Num.iterateWhile g n b).val := by
  unfold Num.iterateWhile Charged.repeatWhile
  exact val_foldlWhile_congr _ _ (fun b r => h r b) _ _

end Loops

/-! ## The same arithmetic in both currencies -/

section Values

open ttc.Program

theorem get_Apow (x : Num ℝ) : ∀ k : ℕ, (A.pow x k).val.get = x.get ^ k
  | 0 => by simp [A.pow, A.lit]
  | k + 1 => by
      simp only [A.pow, Charged.val_bind, A.mul, Num.get_mul, get_Apow x k]
      ring

/-- Normalise both programs' values to formulas. -/
macro "cv_simp" : tactic => `(tactic| simp [Num.ext_iff, funext_iff, A.add, A.sub, A.mul, A.div,
  A.max, A.min, A.le, A.lit, A.cast, A.sqrt, A.log, A.exp, A.root, A.ceil, A.smul, A.addVec,
  A.normSq, A.norm, A.ballStart, A.gaussianLogWeight, A.mulLit, A.divLit, A.litDiv, A.litMax,
  A.protectedLog, A.cell, A.push, get_Apow, val_Alt, val_forEach, get_dot, dotProduct,
  ttc.Model.Operations.cell, ttc.Model.Operations.push,
  ttc.ChargedCV18.Counted.smul, ttc.ChargedCV18.Counted.addVec, ttc.ChargedCV18.Counted.normSq,
  ttc.ChargedCV18.Counted.norm, ttc.ChargedCV18.Counted.ballStart,
  ttc.ChargedCV18.Counted.gaussianLogWeight, ttc.ChargedCV18.Counted.mulLit,
  ttc.ChargedCV18.Counted.divLit, ttc.ChargedCV18.Counted.litDiv, ttc.ChargedCV18.Counted.litMax,
  ttc.ChargedCV18.Counted.protectedLog, ttc.ChargedCV18.Counted.dot_value,
  ttc.ChargedCV18.Counted.forEach_value, ttc.ChargedCV18.Counted.lt_value,
  ttc.ChargedCV18.NumPoint.view_apply, ttc.ChargedCV18.Counted.bind_value,
  ttc.ChargedCV18.Counted.pure_value, ttc.ChargedCV18.Counted.pure_value',
  ttc.ChargedCV18.Counted.le_value, ttc.ChargedCV18.Counted.sqrt_value])

/-- The sealed program's constants of a call, as the charged program's. -/
def RunConstants.toC (G : ttc.Program.RunConstants) : ttc.ChargedCV18.RunConstants :=
  ⟨G.dimension, G.dimensionCount, G.terminal, G.rootTerminal, G.rootInitial, G.gaussianIntegral,
   G.scale, G.scaleInv, G.schedule, G.sampleCount, G.fixedRateSampleCount, G.maxRetries,
   G.accuracyLog, G.blockError, G.warm, G.queryBudget, G.repetitions⟩

/-- The sealed program's constants of a phase, as the charged program's. -/
def PhaseConstants.toC (P : ttc.Program.PhaseConstants) : ttc.ChargedCV18.PhaseConstants :=
  ⟨P.radius, P.proposal, P.steps, P.cap, P.samples⟩

variable {n : ℕ}

theorem val_ballProposalProg (dimN : Num ℕ) (x : NumPoint n) (r : Num ℝ) (g : NumPoint n)
    (u : Num ℝ) : (ballProposalProg dimN x r g u).val =
      (ttc.ChargedCV18.ballProposalProg dimN x r g u).value := by
  simp only [ballProposalProg, ttc.ChargedCV18.ballProposalProg]; cv_simp

theorem val_properTestProg (a b : Num ℝ) (y : NumPoint n) :
    (properTestProg a b y).val = (ttc.ChargedCV18.properTestProg a b y).value := by
  simp only [properTestProg, ttc.ChargedCV18.properTestProg]; cv_simp

theorem val_lazyTestProg (s : Num ℝ) (x y : NumPoint n) (c : Num ℝ) :
    (lazyTestProg s x y c).val = (ttc.ChargedCV18.lazyTestProg s x y c).value := by
  simp only [lazyTestProg, ttc.ChargedCV18.lazyTestProg]; cv_simp

theorem val_scaleAcceptTestProg (s c : Num ℝ) (y : NumPoint n) (u : Num ℝ) :
    (scaleAcceptTestProg s c y u).val = (ttc.ChargedCV18.scaleAcceptTestProg s c y u).value := by
  simp only [scaleAcceptTestProg, ttc.ChargedCV18.scaleAcceptTestProg]; cv_simp

theorem val_gaussianRatioWeightProg (s t : Num ℝ) (x : NumPoint n) :
    (gaussianRatioWeightProg s t x).val = (ttc.ChargedCV18.gaussianRatioWeightProg s t x).value := by
  simp only [gaussianRatioWeightProg, ttc.ChargedCV18.gaussianRatioWeightProg]; cv_simp

theorem val_uniformRatioWeightProg (s : Num ℝ) (x : NumPoint n) :
    (uniformRatioWeightProg s x).val = (ttc.ChargedCV18.uniformRatioWeightProg s x).value := by
  simp only [uniformRatioWeightProg, ttc.ChargedCV18.uniformRatioWeightProg]; cv_simp

theorem val_gaussianStartProg (r : Num ℝ) (g : NumPoint n) :
    (gaussianStartProg r g).val = (ttc.ChargedCV18.gaussianStartProg r g).value := by
  simp only [gaussianStartProg, ttc.ChargedCV18.gaussianStartProg]; cv_simp

theorem val_smul (a : Num ℝ) (x : NumPoint n) :
    (A.smul a x).val = (ttc.ChargedCV18.Counted.smul a x).value := by
  cv_simp

/-- The walk-length requirement, as a formula. -/
def walkReqF (a b c e f : ℝ) : ℝ :=
  4 * ((Real.log e + 2 * Real.log (1 / f)) / (b * Real.log 2 / (640 * c * Real.sqrt a)) ^ 2) + 1

theorem get_walkRequirementProg (a b c e f : Num ℝ) :
    (walkRequirementProg a b c e f).val.get = walkReqF a.get b.get c.get e.get f.get := by
  simp only [walkRequirementProg, walkReqF]
  cv_simp

theorem get_walkRequirementProgC (a b c e f : Num ℝ) :
    (ttc.ChargedCV18.walkRequirementProg a b c e f).value.get =
      walkReqF a.get b.get c.get e.get f.get := by
  simp only [ttc.ChargedCV18.walkRequirementProg, walkReqF]
  cv_simp

theorem val_phaseConstantsProg (G : ttc.Program.RunConstants) (s : Num ℝ) :
    PhaseConstants.toC (phaseConstantsProg G s).val =
      (ttc.ChargedCV18.phaseConstantsProg (RunConstants.toC G) s).value := by
  simp only [phaseConstantsProg, ttc.ChargedCV18.phaseConstantsProg, Charged.val_bind,
    ttc.ChargedCV18.Counted.bind_value]
  simp only [PhaseConstants.toC, RunConstants.toC]
  cv_simp
  simp only [get_walkRequirementProg, get_walkRequirementProgC]
  and_intros <;> first | rfl | (split_ifs <;> rfl)

theorem val_nextVarianceProg (a b s : Num ℝ) :
    (nextVarianceProg a b s).val = (ttc.ChargedCV18.nextVarianceProg a b s).value := by
  simp only [nextVarianceProg, ttc.ChargedCV18.nextVarianceProg]
  by_cases hs : s.get ≤ 1 <;> cv_simp <;> simp [hs] <;> cv_simp
theorem val_scheduleRound (a b : Num ℝ) (one : Num ℕ) (st : List (Num ℝ) × Num ℝ × Num ℕ) :
    (scheduleRound a b one st).val = (ttc.ChargedCV18.scheduleRound a b one st).value := by
  simp only [scheduleRound, ttc.ChargedCV18.scheduleRound]
  by_cases hs : b.get ≤ st.2.1.get <;> cv_simp <;> simp [hs, val_nextVarianceProg] <;> cv_simp
theorem val_scheduleProg (a b : Num ℝ) (fuel : Num ℕ) (s : Num ℝ) :
    (scheduleProg a b fuel s).val = (ttc.ChargedCV18.scheduleProg a b fuel s).value := by
  simp only [scheduleProg, ttc.ChargedCV18.scheduleProg, Charged.val_bind,
    ttc.ChargedCV18.Counted.bind_value]
  rw [show (A.iterateWhile (scheduleRound a b (A.lit (1:ℕ)).val) fuel
      ([], s, (A.lit (1:ℕ)).val)).val = (ttc.ChargedCV18.Counted.iterateWhile
      (ttc.ChargedCV18.scheduleRound a b (A.lit (1:ℕ)).val) fuel ([], s, (A.lit (1:ℕ)).val)).value
      from val_iterateWhile_congr _ _ (fun _ st => val_scheduleRound a b _ st) _ _]
  rfl
open ArlibCommunity.Algorithms.CV18 in
theorem holds_runConstantsProg (q : VolumeParams) (eps roundness p : Num ℝ) (he : eps.get = q.eps)
    (hr : roundness.get = q.roundness) (hp : p.get = q.p) :
    (RunConstants.toC (runConstantsProg q.n eps roundness p).val).Holds q := by
  constructor
  have hpos : 0 < 2 * Real.pi * initialVariance q := by
    have := initialVariance_pos q
    positivity
  have hZ : Real.exp (Real.log (2 * Real.pi * initialVariance q) * ((q.n : ℝ) / 2)) =
      initialGaussianIntegral q := by
    rw [initialGaussianIntegral, Real.rpow_eq_pow, Real.rpow_def_of_pos hpos]
  simp only [initialVariance] at hZ hpos
  have hsched := fun {d T s : Num ℝ} {F : Num ℕ} (hd : d.get = q.n)
      (hT : T.get = terminalVariance q) (hs : s.get = q.eps / (64 * (q.n : ℝ)))
      (hF : F.get = slowPhaseSteps q + fastPhaseSteps q) =>
    val_scheduleProg d T F s ▸ ttc.ChargedCV18.scheduleProg_spec q hd hT hs
      (by rw [hF]; exact terminalPhaseSteps_le_total q)
  simp only [terminalVariance, terminalScale, slowPhaseSteps, fastPhaseSteps, protectedLog] at hsched
  unfold ttc.ChargedCV18.RunConstants.view
  simp only [runConstantsProg, RunConstants.toC, Charged.val_bind, val_Apure, val_cpure,
    A.lit, A.cast, A.div, A.mul, A.max, A.sqrt, A.log, A.exp, A.sub, A.ceil, A.add,
    A.mulLit, A.divLit, A.litDiv, A.litMax, A.protectedLog,
    Num.get_lit, Num.get_cast, Num.get_div, Num.get_mul, Num.get_max, Num.get_sqrt, Num.get_log,
    Num.get_exp, Num.get_sub, Num.get_ceil, Num.get_add, get_Apow, he, hr, hp]
  rw [(hsched (by simp [A.lit, A.cast]) (by simp [A.lit, A.cast, A.litMax, A.max, A.mul, A.mulLit,
      A.protectedLog, A.litDiv, A.div, A.log, get_Apow, he, hr]) (by simp [A.lit, A.cast, A.div,
      A.mulLit, A.mul, he]) (by simp [A.add, A.ceil, A.mul, A.mulLit, A.add, A.lit, A.cast,
      A.protectedLog, A.div, A.max, A.log, A.litMax, A.litDiv, get_Apow, he, hr])).1,
    (hsched (by simp [A.lit, A.cast]) (by simp [A.lit, A.cast, A.litMax, A.max, A.mul, A.mulLit,
      A.protectedLog, A.litDiv, A.div, A.log, get_Apow, he, hr]) (by simp [A.lit, A.cast, A.div,
      A.mulLit, A.mul, he]) (by simp [A.add, A.ceil, A.mul, A.mulLit, A.add, A.lit, A.cast,
      A.protectedLog, A.div, A.max, A.log, A.litMax, A.litDiv, get_Apow, he, hr])).2.1]
  unfold ttc.ChargedCV18.runConstants
  simp only [ttc.ChargedCV18.RunValues.mk.injEq, true_and]
  repeat' apply And.intro
  all_goals first
    | rfl
    | exact hZ
    | simp [scaleFactor, one_div, protectedLog]

theorem RunConstants.eq_of_view {G₁ G₂ : ttc.ChargedCV18.RunConstants} (h : G₁.view = G₂.view) :
    G₁ = G₂ := by
  cases G₁; cases G₂
  simp only [ttc.ChargedCV18.RunConstants.view, ttc.ChargedCV18.RunValues.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  simp only [ttc.ChargedCV18.RunConstants.mk.injEq]
  refine ⟨Num.ext h1, Num.ext h2, Num.ext h3, Num.ext h4, Num.ext h5, Num.ext h6, Num.ext h7,
    Num.ext h8, ?_, Num.ext h10, Num.ext h11, Num.ext h12, Num.ext h13, Num.ext h14, Num.ext h15,
    Num.ext h16, Num.ext h17⟩
  exact (List.map_injective_iff.mpr Num.get_injective) h9

/-- **The constants of a call are the same in both programs.** -/
theorem val_runConstantsProg (q : ArlibCommunity.Algorithms.CV18.VolumeParams)
    (eps roundness p : Num ℝ) (he : eps.get = q.eps) (hr : roundness.get = q.roundness)
    (hp : p.get = q.p) :
    RunConstants.toC (runConstantsProg q.n eps roundness p).val =
      (ttc.ChargedCV18.runConstantsProg q).value :=
  RunConstants.eq_of_view ((holds_runConstantsProg q eps roundness p he hr hp).view_eq.trans
    (ttc.ChargedCV18.runConstantsProg_value q).view_eq.symm)

/-! ### The median -/

section Median

theorem val_Alt_gen {α : Type} [LinearOrder α] (x y : Num α) :
    (A.lt x y).val = decide (x.get < y.get) := by
  simp only [A.lt, Charged.val_bind, Num.val_le, val_Apure]
  by_cases h : x.get < y.get
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

theorem val_mapM {α β : Type} (f : α → Prog β) :
    ∀ l : List α, (l.mapM f).val = l.map fun x => (f x).val
  | [] => rfl
  | x :: l => by
      rw [List.mapM_cons]
      simp only [Charged.val_bind, val_mapM f l, List.map_cons]
      rfl

theorem get_sumList : ∀ l : List (Num ℕ), (A.sumList l).val.get = (l.map Num.get).sum
  | [] => by simp [A.sumList, A.lit]
  | [a] => by simp [A.sumList]
  | a :: b :: rest => by
      simp only [A.sumList, Charged.val_bind, A.add, Num.get_add, get_sumList (b :: rest),
        List.map_cons, List.sum_cons]

theorem val_firstPassing : ∀ l : List (Num ℝ × Bool),
    (A.firstPassing l).val = ((l.find? (·.2)).map (·.1)).getD (A.lit (0 : ℝ)).val
  | [] => rfl
  | e :: rest => by
      rcases e with ⟨x, _ | _⟩
      · simp only [A.firstPassing, Bool.false_eq_true, ite_false, List.find?_cons_of_neg,
          not_false_eq_true]
        exact val_firstPassing rest
      · simp [A.firstPassing]

/-- How many entries of `v` stand in relation `r` to `x`. -/
def countRel (r : ℝ → ℝ → Prop) [DecidableRel r] (v : List (Num ℝ)) (x : Num ℝ) : ℕ :=
  (v.map fun y => if r y.get x.get then 1 else 0).sum

/-- Whether `x` has rank `⌊m/2⌋` in `v`. -/
def rankTest (m : Num ℕ) (v : List (Num ℝ)) (x : Num ℝ) : Bool :=
  decide (countRel (· < ·) v x ≤ m.get / 2) && decide (m.get / 2 < countRel (· ≤ ·) v x)

theorem val_median (m : Num ℕ) (v : List (Num ℝ)) :
    (A.median m v).val = ((v.find? (rankTest m v)).getD (A.lit (0 : ℝ)).val) := by
  have hc : (v.mapM A.cell).val = v := by
    rw [val_mapM]; simp [A.cell, ttc.Model.Operations.cell]
  simp only [A.median, Charged.val_bind, hc, val_mapM, val_firstPassing, List.find?_map,
    Option.map_map, Function.comp_def, val_Apure, Option.map_id']
  congr 2
  funext x
  have hs : ∀ (R : ℝ → ℝ → Prop) [DecidableRel R],
      (A.sumList ((v.map fun y => decide (R y.get x.get)).map fun f =>
        if f = true then (Num.lit (κ := Op) (κₛ := Cell) (1 : ℕ)).val
        else (Num.lit (κ := Op) (κₛ := Cell) (0 : ℕ)).val)).val.get = countRel R v x := by
    intro R _
    rw [get_sumList, countRel, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun y _ => ?_
    simp only [Function.comp_apply]
    split_ifs <;> simp_all
  simp only [val_Alt, A.le, A.div, A.lit, Num.val_le, Charged.val_bind, val_Apure, Num.get_div,
    Num.get_lit]
  simp only [hs, rankTest, val_Alt_gen, Num.get_div, Num.get_lit]

open ttc.ChargedCV18 in
theorem value_medianC (m : Num ℕ) (v : List (Num ℝ)) :
    (ttc.ChargedCV18.Counted.median m v).value = (v.find? (rankTest m v)).getD (A.lit (0 : ℝ)).val := by
  simp only [ttc.ChargedCV18.Counted.median, ttc.ChargedCV18.Counted.bind_value, ttc.ChargedCV18.Counted.forEach_value, ttc.ChargedCV18.Counted.cell_value]
  have hpred : (fun i : Fin v.length => (ttc.ChargedCV18.Counted.pure
      ((ttc.ChargedCV18.Counted.le (ttc.ChargedCV18.Counted.sum v.length fun j =>
          if (ttc.ChargedCV18.Counted.lt (v.get j) (v.get i)).value = true then (ttc.ChargedCV18.Counted.lit (1 : ℕ)).value
          else (ttc.ChargedCV18.Counted.lit (0 : ℕ)).value).value (ttc.ChargedCV18.Counted.div m (ttc.ChargedCV18.Counted.lit 2).value).value).value &&
        (ttc.ChargedCV18.Counted.lt (ttc.ChargedCV18.Counted.div m (ttc.ChargedCV18.Counted.lit 2).value).value
          (ttc.ChargedCV18.Counted.sum v.length fun j =>
            if (ttc.ChargedCV18.Counted.le (v.get j) (v.get i)).value = true then (ttc.ChargedCV18.Counted.lit (1 : ℕ)).value
            else (ttc.ChargedCV18.Counted.lit (0 : ℕ)).value).value).value)).value) =
      rankTest m v ∘ v.get := by
    funext i
    simp only [ttc.ChargedCV18.Counted.pure_value, ttc.ChargedCV18.Counted.le_value, ttc.ChargedCV18.Counted.lt_value, Function.comp_apply]
    simp only [rankTest]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have hcnt : ∀ (R : ℝ → ℝ → Prop) (inst : DecidableRel R),
        (ttc.ChargedCV18.Counted.sum v.length fun j => @ite _ (R (v.get j).get (v.get i).get) (inst _ _)
          (ttc.ChargedCV18.Counted.lit (1 : ℕ)).value (ttc.ChargedCV18.Counted.lit (0 : ℕ)).value).value.get =
          countRel R v (v.get i) := by
      intro R inst
      rw [ttc.ChargedCV18.Counted.sum_value, countRel, ← Fin.sum_univ_fun_getElem]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [List.get_eq_getElem]
      split_ifs <;> simp_all
    rw [hcnt (· < ·) _, hcnt (· ≤ ·) _, ttc.ChargedCV18.Counted.div_value, ttc.ChargedCV18.Counted.lit_value]
  rw [hpred]
  have hfind : v.find? (rankTest m v) =
      ((List.finRange v.length).find? (rankTest m v ∘ v.get)).map v.get := by
    conv_lhs => arg 2; rw [← List.map_get_finRange v]
    rw [List.find?_map]
  rw [hfind]
  cases h : (List.finRange v.length).find? (rankTest m v ∘ v.get) with
  | none => rfl
  | some i => rfl

/-- **The median is the same in both programs.** -/
theorem val_median_eq (m : Num ℕ) (v : List (Num ℝ)) :
    (A.median m v).val = (ttc.ChargedCV18.Counted.median m v).value := by
  rw [val_median, value_medianC]

end Median

end Values


/-! ## CV18's procedures, side by side -/

section Procedures

open ttc.Program
open ArlibCommunity.Algorithms.CV18 (VolumeParams)

/-- Membership queries answered by the sealed program's membership routine. -/
def memberOracle {d : ℕ} (member : NumPoint d → Prog Bool) (y : EuclideanSpace ℝ (Fin d)) : Bool :=
  (member (ofPt y)).val

variable (q : VolumeParams) (G : ttc.Program.RunConstants) (member : NumPoint q.n → Prog Bool)

local notation "O" => memberOracle member
local notation "G'" => RunConstants.toC G

theorem sim_isMember (x : NumPoint q.n) :
    Sim O Eq (isMemberT q.n member x) (ttc.ChargedCV18.isMember x) := by
  intro b t
  cases b with
  | zero => exact ⟨Option.Rel.none, rfl, rfl⟩
  | succ b =>
      have h1 : ((b + 1 : ℕ) : ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero b
      simp only [isMemberT, spendT, Tree.bind, exec, ttc.ChargedCV18.isMember, cexec, h1, ite_false,
        enat_succ_sub_one, ttc.ChargedCV18.compute, compute, ite_true]
      refine ⟨Option.Rel.some ?_, ?_, ?_⟩
      · show (member x).val = memberOracle member (WithLp.toLp 2 fun i => (x i).get)
        simp only [memberOracle]
        rw [show (WithLp.toLp 2 fun i => (x i).get : EuclideanSpace ℝ (Fin q.n)) = toPt x from rfl,
          ofPt_toPt]
      all_goals first | trivial | rfl

theorem sim_ballWalkStep (P : ttc.Program.PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint q.n) :
    Sim O Eq (ballWalkStepT q.n G member P sigma2 x)
      (ttc.ChargedCV18.ballWalkStep q G' (PhaseConstants.toC P) sigma2 x) := by
  refine Sim.bind sim_gaussianT fun g _ hg => ?_
  subst hg
  refine Sim.bind sim_unitT fun u _ hu => ?_
  subst hu
  refine Sim.bind (sim_compute_eq _ _ (val_ballProposalProg _ _ _ _ _)) fun y _ hy => ?_
  subst hy
  refine Sim.bind (sim_isMember q member y) fun inside _ hi => ?_
  subst hi
  refine Sim.bind sim_unitT fun coin _ hc => ?_
  subst hc
  refine Sim.bind (sim_compute_eq _ _ (val_properTestProg _ _ _)) fun proper _ hp => ?_
  subst hp
  refine Sim.bind (sim_compute_eq _ _ (val_lazyTestProg _ _ _ _)) fun move _ hm => ?_
  subst hm
  exact sim_ite _ (sim_pure_eq _) (sim_pure_eq _)

theorem sim_properWalkRound (P : ttc.Program.PhaseConstants) (sigma2 : Num ℝ) (left : Num ℕ)
    (x : NumPoint q.n) :
    Sim O Eq (properWalkRoundT q.n G member P sigma2 left x)
      (ttc.ChargedCV18.properWalkRound q G' (PhaseConstants.toC P) sigma2 left x) := by
  refine Sim.bind (sim_compute_eq _ _ (by cv_simp)) fun done _ h => ?_
  subst h
  refine sim_ite _ ?_ ?_
  · refine Sim.bind (sim_compute_eq _ _ (val_smul _ _)) fun y _ h => ?_
    subst h
    exact Sim.bind (sim_isMember q member y) fun _ _ h => sim_pure_eq _
  · refine Sim.bind (sim_ballWalkStep q G member P sigma2 x) fun r _ h => ?_
    subst h
    rcases r with ⟨proper, y⟩
    exact sim_ite _ (Sim.bind (sim_compute_eq _ _ (by cv_simp)) fun _ _ h => h ▸ sim_pure_eq _)
      (sim_pure_eq _)

theorem sim_properWalk (P : ttc.Program.PhaseConstants) (sigma2 : Num ℝ) (cap : Num ℕ)
    (x : NumPoint q.n) :
    Sim O Eq (properWalkT q.n G member P sigma2 cap x)
      (ttc.ChargedCV18.properWalk q G' (PhaseConstants.toC P) sigma2 cap x) := by
  refine Sim.bind (sim_loopTree cap (fun s => sim_properWalkRound q G member P sigma2 s.1 s.2) _)
    fun r _ h => ?_
  subst h
  rcases r with _ | y <;> exact sim_pure_eq _

theorem sim_rejectionAttempt (P : ttc.Program.PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint q.n) :
    Sim O Eq (rejectionAttemptT q.n G member P sigma2 x)
      (ttc.ChargedCV18.rejectionAttempt q G' (PhaseConstants.toC P) sigma2 x) := by
  refine Sim.bind (sim_compute_eq _ _ (val_smul _ _)) fun y _ h => ?_
  subst h
  refine Sim.bind (sim_isMember q member y) fun inside _ h => ?_
  subst h
  refine Sim.bind sim_unitT fun coin _ h => ?_
  subst h
  refine Sim.bind (sim_compute_eq _ _ (val_properTestProg _ _ _)) fun proper _ h => ?_
  subst h
  refine Sim.bind (sim_compute_eq _ _ (val_scaleAcceptTestProg _ _ _ _)) fun accept _ h => ?_
  subst h
  exact sim_ite _ (sim_pure_eq _) (sim_pure_eq _)

theorem sim_sampleAttempt (P : ttc.Program.PhaseConstants) (sigma2 : Num ℝ) (walkCap : Num ℕ)
    (x : NumPoint q.n) :
    Sim O Eq (sampleAttemptT q.n G member P sigma2 walkCap x)
      (ttc.ChargedCV18.sampleAttempt q G' (PhaseConstants.toC P) sigma2 walkCap x) := by
  refine Sim.bind (sim_properWalk q G member P sigma2 walkCap x) fun r _ h => ?_
  subst h
  rcases r with _ | y
  · exact sim_pure_eq _
  · refine Sim.bind (sim_rejectionAttempt q G member P sigma2 y) fun a _ h => ?_
    subst h
    rcases a with ⟨accepted, z⟩
    exact sim_ite _ (sim_pure_eq _) (sim_pure_eq _)

theorem sim_sampleFinish (weight : NumPoint q.n → Prog (Num ℝ))
    (weight' : NumPoint q.n → ttc.ChargedCV18.Counted (Num ℝ))
    (hw : ∀ z, (weight z).val = (weight' z).value) (total : Num ℝ)
    (a : NumPoint q.n ⊕ Option (NumPoint q.n × NumPoint q.n)) :
    Sim O Eq (sampleFinishT q.n weight total a) (ttc.ChargedCV18.sampleFinish q weight' total a) := by
  rcases a with _ | _ | ⟨z, y⟩
  · exact sim_pure_eq _
  · exact sim_pure_eq _
  · refine Sim.bind (sim_compute_eq _ _ (hw z)) fun w _ h => ?_
    subst h
    exact Sim.bind (sim_compute_eq _ _ (by cv_simp)) fun _ _ h => h ▸ sim_pure_eq _

theorem sim_sampleRound (P : ttc.Program.PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint q.n → Prog (Num ℝ))
    (weight' : NumPoint q.n → ttc.ChargedCV18.Counted (Num ℝ))
    (hw : ∀ z, (weight z).val = (weight' z).value) (walkCap : Num ℕ) (state : Num ℝ × NumPoint q.n) :
    Sim O Eq (sampleRoundT q.n G member P sigma2 weight walkCap state)
      (ttc.ChargedCV18.sampleRound q G' (PhaseConstants.toC P) sigma2 weight' walkCap state) :=
  Sim.bind (sim_loopTree _ (fun x => sim_sampleAttempt q G member P sigma2 walkCap x) _)
    fun a _ h => h ▸ sim_sampleFinish q member weight weight' hw state.1 a

theorem sim_collectSamples (P : ttc.Program.PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint q.n → Prog (Num ℝ))
    (weight' : NumPoint q.n → ttc.ChargedCV18.Counted (Num ℝ))
    (hw : ∀ z, (weight z).val = (weight' z).value) (samples : Num ℕ) (start : NumPoint q.n) :
    Sim O Eq (collectSamplesT q.n G member P sigma2 weight samples start)
      (ttc.ChargedCV18.collectSamples q G' (PhaseConstants.toC P) sigma2 weight' samples start) := by
  refine Sim.bind (sim_compute_eq _ _ (by cv_simp; rfl)) fun c _ h => ?_
  subst h
  rcases c with ⟨zero, walkCap⟩
  refine Sim.bind (sim_loopTree samples
    (fun s => sim_sampleRound q G member P sigma2 weight weight' hw walkCap s) _) fun r _ h => ?_
  subst h
  rcases r with _ | _ <;> exact sim_pure_eq _

theorem sim_coolingPhase (sigma2 tau2 : Num ℝ) (x : NumPoint q.n) :
    Sim O Eq (coolingPhaseT q.n G member sigma2 tau2 x)
      (ttc.ChargedCV18.coolingPhase q G' sigma2 tau2 x) := by
  refine Sim.bind (sim_compute (R := fun P P' => PhaseConstants.toC P = P') _ _
    (val_phaseConstantsProg G sigma2)) fun P _ h => ?_
  subst h
  refine Sim.bind (sim_compute_eq _ _ (val_smul _ _)) fun start _ h => ?_
  subst h
  refine Sim.bind (sim_collectSamples q G member P sigma2 _ _
    (fun z => val_gaussianRatioWeightProg _ _ z) _ start) fun r _ h => ?_
  subst h
  rcases r with _ | ⟨total, y⟩
  · exact sim_pure_eq _
  · refine Sim.bind (sim_compute_eq _ _ (by cv_simp; rfl)) fun W _ h => ?_
    subst h
    exact Sim.bind (sim_compute_eq _ _ (val_smul _ _)) fun _ _ h => h ▸ sim_pure_eq _

theorem sim_uniformPhase (sigma2 : Num ℝ) (x : NumPoint q.n) :
    Sim O Eq (uniformPhaseT q.n G member sigma2 x) (ttc.ChargedCV18.uniformPhase q G' sigma2 x) := by
  refine Sim.bind (sim_compute (R := fun P P' => PhaseConstants.toC P = P') _ _
    (val_phaseConstantsProg G sigma2)) fun P _ h => ?_
  subst h
  refine Sim.bind (sim_compute_eq _ _ (val_smul _ _)) fun start _ h => ?_
  subst h
  refine Sim.bind (sim_collectSamples q G member P sigma2 _ _
    (fun z => val_uniformRatioWeightProg _ z) _ start) fun r _ h => ?_
  subst h
  rcases r with _ | ⟨total, y⟩
  · exact sim_pure_eq _
  · exact Sim.bind (sim_compute_eq _ _ (by cv_simp; rfl)) fun _ _ h => h ▸ sim_pure_eq _

theorem sim_initialSample :
    Sim O Eq (initialSampleT q.n G member) (ttc.ChargedCV18.initialSample q G') := by
  refine Sim.bind sim_gaussianT fun g _ h => ?_
  subst h
  refine Sim.bind (sim_compute_eq _ _ (val_gaussianStartProg _ _)) fun x _ h => ?_
  subst h
  refine Sim.bind (sim_isMember q member x) fun inside _ h => ?_
  subst h
  exact Sim.bind (sim_compute_eq _ _ (by cv_simp; rfl)) fun _ _ h => h ▸ sim_pure_eq _

theorem sim_coolingPhases :
    ∀ (l : List (Num ℝ)) (x : NumPoint q.n),
      Sim O Eq (coolingPhasesT q.n G member l x) (ttc.ChargedCV18.coolingPhases q G' l x)
  | sigma2 :: tau2 :: rest, x => by
      refine Sim.bind (sim_compute_eq _ _ (by cv_simp)) fun s _ h => ?_
      subst h
      refine Sim.bind (sim_compute_eq _ _ (by cv_simp)) fun t _ h => ?_
      subst h
      refine Sim.bind (sim_coolingPhase q G member s t x) fun r _ h => ?_
      subst h
      rcases r with _ | ⟨W, y⟩
      · exact sim_pure_eq _
      · refine Sim.bind (sim_coolingPhases (tau2 :: rest) y) fun r' _ h => ?_
        subst h
        rcases r' with _ | ⟨product, z⟩
        · exact sim_pure_eq _
        · exact Sim.bind (sim_compute_eq _ _ (by cv_simp)) fun _ _ h => h ▸ sim_pure_eq _
  | [], x => Sim.bind (sim_compute_eq _ _ (by cv_simp)) fun _ _ h => h ▸ sim_pure_eq _
  | [_], x => Sim.bind (sim_compute_eq _ _ (by cv_simp)) fun _ _ h => h ▸ sim_pure_eq _

theorem sim_figureOneRun :
    Sim O Eq (figureOneRunT q.n G member) (ttc.ChargedCV18.figureOneRun q G') := by
  refine Sim.bind (sim_initialSample q G member) fun r₀ _ h => ?_
  subst h
  rcases r₀ with _ | x₀
  · exact sim_compute_eq _ _ (by cv_simp)
  · refine Sim.bind (sim_coolingPhases q G member _ x₀) fun r₁ _ h => ?_
    subst h
    rcases r₁ with _ | ⟨product, x⟩
    · exact sim_compute_eq _ _ (by cv_simp)
    · refine Sim.bind (sim_uniformPhase q G member _ x) fun r₂ _ h => ?_
      subst h
      rcases r₂ with _ | U
      · exact sim_compute_eq _ _ (by cv_simp)
      · exact sim_compute_eq _ _ (by simp only [RunConstants.toC]; cv_simp)

end Procedures


/-! ## The top level: no outer cap -/

section Top

variable {O : EuclideanSpace ℝ (Fin d) → Bool}

theorem cexec_top_budget (P : ChargedProgram d α) (t : Tape d) : (cexec O P ⊤ t).2.1 = ⊤ := by
  induction P generalizing t with
  | pure a => rfl
  | query x k ih =>
      simp only [cexec, ENat.top_ne_zero, ite_false, enat_top_sub_one]
      exact ih _ t
  | randomNat law k ih => exact ih _ t
  | randomPoint law h k ih => exact ih _ _
  | randomReal law h k ih => exact ih _ _
  | tick c k ih => exact ih t

variable (O) in
/-- **`p` runs like `P` with no cap on `P`**: from every number of calls left for `p`, the
results are related by `R`, and the tapes left are the same. -/
def SimTop (R : α → β → Prop) (p : Tree d α) (P : ChargedProgram d β) : Prop :=
  ∀ (b : ℕ) (t : Tape d), Option.Rel R (exec p b t).1 (cexec O P ⊤ t).1 ∧
    (exec p b t).2.2.2 = (cexec O P ⊤ t).2.2

theorem SimTop.bind {R : α → β → Prop} {S : γ → δ → Prop} {p : Tree d α}
    {P : ChargedProgram d β} {f : α → Tree d γ} {F : β → ChargedProgram d δ}
    (hp : SimTop O R p P) (hf : ∀ a a', R a a' → SimTop O S (f a) (F a')) :
    SimTop O S (p.bind f) (P.bind F) := by
  intro b t
  rw [exec_bind, cexec_bind]
  obtain ⟨h1, h3⟩ := hp b t
  have h2 := cexec_top_budget (O := O) P t
  rcases e : exec p b t with ⟨o, m, b', t'⟩
  rcases E : cexec O P ⊤ t with ⟨o', B', T'⟩
  rw [e, E] at h1 h3
  rw [E] at h2
  simp only at h1 h2 h3
  subst h2 h3
  cases h1 with
  | none => exact ⟨Option.Rel.none, rfl⟩
  | some h => exact hf _ _ h b' t'

theorem simTop_pure {R : α → β → Prop} {a : α} {a' : β} (h : R a a') :
    SimTop O R (Tree.pure a) (ChargedProgram.pure a') :=
  fun _ _ => ⟨Option.Rel.some h, rfl⟩

theorem simTop_compute {R : α → β → Prop} (c : Prog α) (c' : ttc.ChargedCV18.Counted β)
    (h : R c.val c'.value) : SimTop O R (compute c) (ttc.ChargedCV18.compute c') :=
  fun _ _ => ⟨Option.Rel.some h, rfl⟩

theorem simTop_loopRounds {β' : Type} {body : β → Tree d (β ⊕ β')}
    {body' : β → ChargedProgram d (β ⊕ β')} (h : ∀ s, SimTop O Eq (body s) (body' s)) :
    ∀ (k : ℕ) (s : β), SimTop O Eq (loopRounds body k s) (ChargedProgram.loopRounds body' k s)
  | 0, s => simTop_pure rfl
  | k + 1, s => by
      refine SimTop.bind (h s) fun r r' hr => ?_
      subst hr
      rcases r with s' | c
      · exact simTop_loopRounds h k s'
      · exact simTop_pure rfl

theorem simTop_loopTree {β' : Type} (count : Num ℕ) {body : β → Tree d (β ⊕ β')}
    {body' : β → ChargedProgram d (β ⊕ β')} (h : ∀ s, SimTop O Eq (body s) (body' s)) (init : β) :
    SimTop O Eq (loopTree count body init) (ttc.ChargedCV18.loopUntil count body' init) :=
  fun b t => simTop_loopRounds h count.get init b t

theorem simTop_repeatIndependently (count : Num ℕ) {body : Tree d (Num ℝ)}
    {body' : ChargedProgram d (Num ℝ)} (h : SimTop O Eq body body') :
    SimTop O Eq (repeatIndependentlyT count body)
      (ttc.ChargedCV18.repeatIndependently count body') := by
  refine SimTop.bind (simTop_loopTree count (fun es => SimTop.bind h fun x _ hx => ?_) [])
    fun r _ hr => ?_
  · subst hx
    exact SimTop.bind (simTop_compute _ _ (rfl : (ttc.Program.A.push es x).val = _))
      fun _ _ h => h ▸ simTop_pure rfl
  · subst hr
    rcases r with _ | e
    · exact simTop_pure rfl
    · exact e.elim

end Top


/-! ## CV18 -/

section CV18

open ttc.Program
open ArlibCommunity.Algorithms.CV18 (VolumeParams)

variable (q : VolumeParams) (member : NumPoint q.n → Prog Bool)

local notation "O" => memberOracle member

/-- **The capped run**: the cap set by `queryCap` is the charged program's query cap. -/
theorem simTop_cappedRun (G : ttc.Program.RunConstants) :
    SimTop O Eq (cappedRunT q.n G member) (ttc.ChargedCV18.cappedRun q (RunConstants.toC G)) := by
  intro b t
  obtain ⟨h1, h2, h3⟩ := sim_figureOneRun q G member G.queryBudget.get t
  have hours : exec (cappedRunT q.n G member) b t =
      let r := exec (figureOneRunT q.n G member) G.queryBudget.get t
      match r with
      | (some a, m, b', t') => (some a, 1 + m, b', t')
      | (none, m, b', t') =>
          let r' := exec (compute (A.lit (0 : ℝ))) b' t'
          (r'.1, 1 + (m + r'.2.1), r'.2.2) := by
    show exec (Tree.setBudget G.queryBudget ((Tree.pure ()).bind fun _ =>
      (figureOneRunT q.n G member).orElse (compute (A.lit (0 : ℝ))))) b t = _
    simp only [exec, Tree.bind, Tree.exec_orElse]
    rcases exec (figureOneRunT q.n G member) G.queryBudget.get t with ⟨_ | a, m, b', t'⟩ <;> rfl
  have htheirs : cexec O (ttc.ChargedCV18.cappedRun q (RunConstants.toC G)) ⊤ t =
      match (cexec O (ttc.ChargedCV18.figureOneRun q (RunConstants.toC G)) G.queryBudget.get t).1 with
      | some e => (some e, ⊤, (cexec O (ttc.ChargedCV18.figureOneRun q (RunConstants.toC G))
          G.queryBudget.get t).2.2)
      | none => (some (ttc.ChargedCV18.Counted.lit (0 : ℝ)).value, ⊤,
          (cexec O (ttc.ChargedCV18.figureOneRun q (RunConstants.toC G)) G.queryBudget.get t).2.2) := by
    show cexec O ((ChargedProgram.tick _ ((ttc.ChargedCV18.figureOneRun q (RunConstants.toC G)).withQueryCap
      G.queryBudget.get)).bind _) ⊤ t = _
    rw [cexec_bind]
    simp only [cexec]
    rw [cexec_withQueryCap]
    rcases (cexec O (ttc.ChargedCV18.figureOneRun q (RunConstants.toC G)) G.queryBudget.get t).1
      with _ | e <;> rfl
  rw [hours, htheirs]
  rcases e : exec (figureOneRunT q.n G member) G.queryBudget.get t with ⟨o, m, b', t'⟩
  rw [e] at h1 h2 h3
  simp only at h1 h3
  rw [← h3]
  generalize (cexec O (ttc.ChargedCV18.figureOneRun q (RunConstants.toC G)) G.queryBudget.get t).1
    = y at h1 ⊢
  cases h1 with
  | none => exact ⟨Option.Rel.some (Num.ext rfl), rfl⟩
  | some h => exact ⟨Option.Rel.some h, rfl⟩

/-- **CV18 runs like the charged CV18 program**: on every tape, the sealed program's
estimate is the charged program's, when the charged program's queries are answered by the
sealed program's membership routine. -/
theorem simTop_cv18T (eps roundness p : Num ℝ) (he : eps.get = q.eps)
    (hr : roundness.get = q.roundness) (hp : p.get = q.p) :
    SimTop O (fun (m : Num ℝ) (r : ℝ) => m.get = r) (cv18T q.n member eps roundness p)
      (ttc.ChargedCV18.cv18Program q) := by
  refine SimTop.bind (simTop_compute (R := fun G G' => RunConstants.toC G = G') _ _
    (val_runConstantsProg q eps roundness p he hr hp)) fun G _ h => ?_
  subst h
  refine SimTop.bind (simTop_repeatIndependently _ (simTop_cappedRun q member G)) fun est _ h => ?_
  subst h
  show SimTop O _ ((compute (A.median G.repetitions est)).bind Tree.pure) _
  exact SimTop.bind (simTop_compute _ _ (val_median_eq _ _)) fun m _ h => h ▸ simTop_pure rfl

end CV18

end ttc.Tape

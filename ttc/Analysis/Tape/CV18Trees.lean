/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.TTCTrees

/-!
# CV18 as trees

Each procedure of the program's CV18 (`Model/Program.lean`) written as a tree,
following its text, and the statement that the two agree (`agree_*`).  A membership call
spends one call of the query cap and stops the run when it is exhausted; `cappedRun`
recovers from that stop (`<|>`), which as a tree is `Tree.orElse`.

`cv18T_agrees` is the hypothesis `CV18Agrees` of `Analysis/Tape/TTCTrees.lean`, so
`agree_estimator` holds for the whole program.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {n : ℕ} {α β : Type}

/-! ## Recovering from a stop -/

theorem runFrom_orElse (X Y : M n α) (o : Oracle n) :
    runFrom (X <|> Y) o =
      runFrom X o >>= fun r =>
        match r.1 with
        | some a => Pure.pure (some a, r.2)
        | none => runFrom Y r.2 := by
  show (OptionT.orElse X fun _ => Y).run.run o = _
  simp only [OptionT.orElse, OptionT.mk, OptionT.run, StateT.run_bind, runFrom]
  congr 1
  funext r
  rcases r with ⟨_ | a, o'⟩ <;> rfl

theorem Agree.orElse {X X' Y Y' : M n α} (hX : Agree X X') (hY : Agree Y Y') :
    Agree (X <|> Y) (X' <|> Y') := by
  intro o
  rw [runFrom_orElse, runFrom_orElse]
  refine ⟨?_, ?_⟩
  · rw [Charged.val_bind, Charged.val_bind, (hX o).1]
    rcases (runFrom X' o).val with ⟨_ | a, o'⟩
    · exact (hY o').1
    · rfl
  · rw [Charged.cost_bind, Charged.cost_bind, (hX o).1, (hX o).2]
    rcases (runFrom X' o).val with ⟨_ | a, o'⟩
    · simp only [(hY o').2]
    · rfl

/-- A computation that never stops the run. -/
def Total (X : M n α) : Prop := ∀ o, ∃ a o', (runFrom X o).val = (some a, o')

theorem total_run (c : Prog α) : Total (run c : M n α) :=
  fun o => ⟨c.val, o, (runFrom_run c o).1⟩

theorem total_withOracle (f : Oracle n → Prog (α × Oracle n)) : Total (withOracle f) :=
  fun o => ⟨_, _, (runFrom_withOracle f o).1⟩

/-- A total first step commutes with recovery. -/
theorem agree_bind_orElse {X : M n α} (hX : Total X) (F : α → M n β) (Y : M n β) :
    Agree ((X >>= F) <|> Y) (X >>= fun a => F a <|> Y) := by
  intro o
  obtain ⟨a, o', h⟩ := hX o
  have ev : (runFrom (X >>= F) o).val = (runFrom (F a) o').val := by
    rw [val_runFrom_bind, h]
  have ec : (runFrom (X >>= F) o).cost = (runFrom X o).cost + (runFrom (F a) o').cost := by
    rw [cost_runFrom_bind, h]
  have rv : (runFrom (X >>= fun a => F a <|> Y) o).val = (runFrom (F a <|> Y) o').val := by
    rw [val_runFrom_bind, h]
  have rc : (runFrom (X >>= fun a => F a <|> Y) o).cost =
      (runFrom X o).cost + (runFrom (F a <|> Y) o').cost := by
    rw [cost_runFrom_bind, h]
  refine ⟨?_, ?_⟩
  · rw [rv, runFrom_orElse, runFrom_orElse, Charged.val_bind, Charged.val_bind, ev]
  · rw [rc, runFrom_orElse, runFrom_orElse, Charged.cost_bind, Charged.cost_bind, ev, ec,
      add_assoc]

theorem Agree.orElse_bind {X : M n α} (hX : Total X) {F : α → M n β} {G : α → M n β}
    (Y : M n β) (h : ∀ a, Agree (F a <|> Y) (G a)) : Agree ((X >>= F) <|> Y) (X >>= G) :=
  (agree_bind_orElse hX F Y).trans (Agree.bind_right X h)

/-- **Recovery as a tree**: `p.orElse q` stands for `interp p <|> interp q`. -/
theorem agree_interp_orElse (p q : Tree n α) :
    Agree (interp p <|> interp q) (interp (p.orElse q)) := by
  induction p with
  | pure a => intro o; exact ⟨rfl, rfl⟩
  | fail =>
      intro o
      show _ = (runFrom (interp q) o).val ∧ _ = (runFrom (interp q) o).cost
      rw [runFrom_orElse, Charged.val_bind, Charged.cost_bind, interp_fail,
        (runFrom_failure o).1, (runFrom_failure o).2, zero_add]
      exact ⟨rfl, rfl⟩
  | step c k ih => exact Agree.orElse_bind (total_run c) _ ih
  | coin k ih => exact Agree.orElse_bind (total_withOracle _) _ ih
  | unit k ih => exact Agree.orElse_bind (total_withOracle _) _ fun x => ih x.get
  | gaussian k ih => exact Agree.orElse_bind (total_withOracle _) _ fun g => ih _
  | poisson r k ih => exact Agree.orElse_bind (total_withOracle _) _ fun x => ih x.get
  | binom N k ih => exact Agree.orElse_bind (total_withOracle _) _ fun x => ih x.get
  | setBudget c k ih => exact Agree.orElse_bind (total_withOracle _) _ fun _ => ih
  | spend k ih => exact Agree.orElse_bind (total_withOracle _) _ ih

theorem agree_orElse {X Y : M n α} {p q : Tree n α} (hX : Agree X (interp p))
    (hY : Agree Y (interp q)) : Agree (X <|> Y) (interp (p.orElse q)) :=
  (Agree.orElse hX hY).trans (agree_interp_orElse p q)

theorem agree_iteP (c : Prop) [Decidable c] {X Y : M n α} {p q : Tree n α}
    (hX : Agree X (interp p)) (hY : Agree Y (interp q)) :
    Agree (if c then X else Y) (interp (if c then p else q)) := by
  split_ifs
  · exact hX
  · exact hY

theorem agree_queryCap (c : Num ℕ) : Agree (queryCap c : M n Unit) (interp (queryCapT c)) :=
  Agree.of_eq (interp_queryCapT c).symm

theorem agree_spend : Agree (withOracle spendQuery : M n Bool) (interp spendT) :=
  Agree.of_eq interp_spendT.symm

/-! ## CV18's procedures -/

section Procedures

variable (d : ℕ) (G : RunConstants) (member : NumPoint d → Prog Bool)

/-- A membership call, as a tree. -/
def isMemberT (x : NumPoint d) : Tree d Bool :=
  spendT.bind fun ok => if ok then compute (member x) else .fail

theorem agree_isMember (x : NumPoint d) :
    Agree (isMember member x) (interp (isMemberT d member x)) :=
  Agree.bindT agree_spend fun ok => agree_ite ok (agree_run _) agree_fail

def ballWalkStepT (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint d) :
    Tree d (Bool × NumPoint d) :=
  gaussianT.bind fun g => unitT.bind fun u =>
  (compute (ballProposalProg G.dimensionCount x P.proposal g u)).bind fun y =>
  (isMemberT d member y).bind fun inside => unitT.bind fun coin =>
  (compute (properTestProg G.rootTerminal P.radius y)).bind fun proper =>
  (compute (lazyTestProg sigma2 x y coin)).bind fun move =>
  if inside = true ∧ proper = true then .pure (true, if move = true then y else x)
  else .pure (false, x)

theorem agree_ballWalkStep (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint d) :
    Agree (ballWalkStep d G member P sigma2 x) (interp (ballWalkStepT d G member P sigma2 x)) :=
  Agree.bindT agree_gaussian fun g => Agree.bindT agree_unit fun u =>
  Agree.bindT (agree_run _) fun y => Agree.bindT (agree_isMember d member y) fun inside =>
  Agree.bindT agree_unit fun coin => Agree.bindT (agree_run _) fun proper =>
  Agree.bindT (agree_run _) fun move => agree_iteP _ (agree_pure _) (agree_pure _)

def properWalkRoundT (P : PhaseConstants) (sigma2 : Num ℝ) (left : Num ℕ) (x : NumPoint d) :
    Tree d ((Num ℕ × NumPoint d) ⊕ NumPoint d) :=
  (compute (do
    let zero ← A.lit (0 : ℕ)
    A.le left zero)).bind fun done =>
  if done then
    (compute (A.smul G.scaleInv x)).bind fun y =>
    (isMemberT d member y).bind fun _ => .pure (.inr x)
  else
    (ballWalkStepT d G member P sigma2 x).bind fun r =>
      if r.1 then
        (compute (do
          let one ← A.lit (1 : ℕ)
          A.sub left one)).bind fun left' => .pure (.inl (left', r.2))
      else .pure (.inl (left, r.2))

theorem agree_properWalkRound (P : PhaseConstants) (sigma2 : Num ℝ) (left : Num ℕ)
    (x : NumPoint d) :
    Agree (properWalkRound d G member P sigma2 left x)
      (interp (properWalkRoundT d G member P sigma2 left x)) := by
  refine Agree.bindT (agree_run _) fun done => agree_ite done ?_ ?_
  · exact Agree.bindT (agree_run _) fun y => Agree.bindT (agree_isMember d member y) fun _ =>
      agree_pure _
  · refine Agree.bindT (agree_ballWalkStep d G member P sigma2 x) fun r => ?_
    obtain ⟨proper, y⟩ := r
    exact agree_ite proper (Agree.bindT (agree_run _) fun _ => agree_pure _) (agree_pure _)

def properWalkT (P : PhaseConstants) (sigma2 : Num ℝ) (cap : Num ℕ) (x : NumPoint d) :
    Tree d (Option (NumPoint d)) :=
  (loopTree cap (fun s => properWalkRoundT d G member P sigma2 s.1 s.2) (P.steps, x)).bind
    fun r => .pure (r.elim (fun _ => none) some)

theorem agree_properWalk (P : PhaseConstants) (sigma2 : Num ℝ) (cap : Num ℕ) (x : NumPoint d) :
    Agree (properWalk d G member P sigma2 cap x) (interp (properWalkT d G member P sigma2 cap x)) :=
  Agree.bindT
    (agree_loop (bodyM := fun s => properWalkRound d G member P sigma2 s.1 s.2)
      (body := fun s => properWalkRoundT d G member P sigma2 s.1 s.2) cap
      (fun s => agree_properWalkRound d G member P sigma2 s.1 s.2) (P.steps, x))
    fun r => agree_pure_of_eq (by rcases r with _ | _ <;> rfl)

def rejectionAttemptT (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint d) :
    Tree d (Bool × NumPoint d) :=
  (compute (A.smul G.scaleInv x)).bind fun y =>
  (isMemberT d member y).bind fun inside => unitT.bind fun coin =>
  (compute (properTestProg G.rootTerminal P.radius y)).bind fun proper =>
  (compute (scaleAcceptTestProg sigma2 G.scale y coin)).bind fun accept =>
  if inside = true ∧ proper = true ∧ accept = true then .pure (true, y) else .pure (false, y)

theorem agree_rejectionAttempt (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint d) :
    Agree (rejectionAttempt d G member P sigma2 x)
      (interp (rejectionAttemptT d G member P sigma2 x)) :=
  Agree.bindT (agree_run _) fun y => Agree.bindT (agree_isMember d member y) fun inside =>
  Agree.bindT agree_unit fun coin => Agree.bindT (agree_run _) fun proper =>
  Agree.bindT (agree_run _) fun accept => agree_iteP _ (agree_pure _) (agree_pure _)

def sampleAttemptT (P : PhaseConstants) (sigma2 : Num ℝ) (walkCap : Num ℕ) (x : NumPoint d) :
    Tree d (NumPoint d ⊕ Option (NumPoint d × NumPoint d)) :=
  (properWalkT d G member P sigma2 walkCap x).bind fun r =>
  r.elim (.pure (.inr none)) fun y =>
    (rejectionAttemptT d G member P sigma2 y).bind fun a =>
      if a.1 then .pure (.inr (some (a.2, y))) else .pure (.inl y)

theorem agree_sampleAttempt (P : PhaseConstants) (sigma2 : Num ℝ) (walkCap : Num ℕ)
    (x : NumPoint d) :
    Agree (Program.sampleAttempt d G member P sigma2 walkCap x)
      (interp (sampleAttemptT d G member P sigma2 walkCap x)) := by
  refine Agree.bindT (agree_properWalk d G member P sigma2 walkCap x) fun r => ?_
  rcases r with _ | y
  · exact agree_pure _
  · refine Agree.bindT (agree_rejectionAttempt d G member P sigma2 y) fun a => ?_
    obtain ⟨accepted, z⟩ := a
    exact agree_ite accepted (agree_pure _) (agree_pure _)

def sampleFinishT (weight : NumPoint d → Prog (Num ℝ)) (total : Num ℝ)
    (a : NumPoint d ⊕ Option (NumPoint d × NumPoint d)) :
    Tree d ((Num ℝ × NumPoint d) ⊕ Unit) :=
  a.elim (fun _ => .pure (.inr ())) fun o => o.elim (.pure (.inr ())) fun zy =>
    (compute (weight zy.1)).bind fun w =>
    (compute (A.add total w)).bind fun total' => .pure (.inl (total', zy.2))

theorem agree_sampleFinish (weight : NumPoint d → Prog (Num ℝ)) (total : Num ℝ)
    (a : NumPoint d ⊕ Option (NumPoint d × NumPoint d)) :
    Agree (sampleFinish d weight total a) (interp (sampleFinishT d weight total a)) := by
  rcases a with _ | _ | ⟨z, y⟩
  · exact agree_pure _
  · exact agree_pure _
  · exact Agree.bindT (agree_run _) fun w => Agree.bindT (agree_run _) fun _ => agree_pure _

def sampleRoundT (P : PhaseConstants) (sigma2 : Num ℝ) (weight : NumPoint d → Prog (Num ℝ))
    (walkCap : Num ℕ) (state : Num ℝ × NumPoint d) : Tree d ((Num ℝ × NumPoint d) ⊕ Unit) :=
  (loopTree G.maxRetries (sampleAttemptT d G member P sigma2 walkCap) state.2).bind
    fun attempt => sampleFinishT d weight state.1 attempt

theorem agree_sampleRound (P : PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint d → Prog (Num ℝ)) (walkCap : Num ℕ) (state : Num ℝ × NumPoint d) :
    Agree (sampleRound d G member P sigma2 weight walkCap state)
      (interp (sampleRoundT d G member P sigma2 weight walkCap state)) :=
  Agree.bindT (agree_loop _ (fun x => agree_sampleAttempt d G member P sigma2 walkCap x) _)
    fun attempt => agree_sampleFinish d weight state.1 attempt

def collectSamplesT (P : PhaseConstants) (sigma2 : Num ℝ) (weight : NumPoint d → Prog (Num ℝ))
    (samples : Num ℕ) (start : NumPoint d) : Tree d (Option (Num ℝ × NumPoint d)) :=
  (compute (do
    let zero ← A.lit (0 : ℝ)
    let one ← A.lit (1 : ℕ)
    let walkCap ← A.add P.cap one
    A.pure (zero, walkCap))).bind fun c =>
    (loopTree samples (sampleRoundT d G member P sigma2 weight c.2) (c.1, start)).bind
      fun r => .pure (r.elim some fun _ => none)

theorem agree_collectSamples (P : PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint d → Prog (Num ℝ)) (samples : Num ℕ) (start : NumPoint d) :
    Agree (collectSamples d G member P sigma2 weight samples start)
      (interp (collectSamplesT d G member P sigma2 weight samples start)) := by
  refine Agree.bindT (agree_run _) fun c => ?_
  obtain ⟨zero, walkCap⟩ := c
  exact Agree.bindT (agree_loop _ (fun s => agree_sampleRound d G member P sigma2 weight
    walkCap s) _) fun r => agree_pure_of_eq (by rcases r with _ | _ <;> rfl)

def coolingPhaseT (sigma2 tau2 : Num ℝ) (x : NumPoint d) : Tree d (Option (Num ℝ × NumPoint d)) :=
  (compute (phaseConstantsProg G sigma2)).bind fun P =>
  (compute (A.smul G.scale x)).bind fun start =>
  (collectSamplesT d G member P sigma2 (gaussianRatioWeightProg sigma2 tau2) P.samples
      start).bind fun r =>
  r.elim (.pure none) fun ty =>
    (compute (do
      let k ← A.cast P.samples
      A.div ty.1 k)).bind fun W =>
    (compute (A.smul G.scaleInv ty.2)).bind fun z => .pure (some (W, z))

theorem agree_coolingPhase (sigma2 tau2 : Num ℝ) (x : NumPoint d) :
    Agree (coolingPhase d G member sigma2 tau2 x) (interp (coolingPhaseT d G member sigma2 tau2 x)) := by
  refine Agree.bindT (agree_run _) fun P => Agree.bindT (agree_run _) fun start => ?_
  refine Agree.bindT (agree_collectSamples d G member P sigma2 _ _ start) fun r => ?_
  rcases r with _ | ⟨total, y⟩
  · exact agree_pure _
  · exact Agree.bindT (agree_run _) fun W => Agree.bindT (agree_run _) fun z => agree_pure _

def uniformPhaseT (sigma2 : Num ℝ) (x : NumPoint d) : Tree d (Option (Num ℝ)) :=
  (compute (phaseConstantsProg G sigma2)).bind fun P =>
  (compute (A.smul G.scale x)).bind fun start =>
  (collectSamplesT d G member P sigma2 (uniformRatioWeightProg sigma2) G.sampleCount
      start).bind fun r =>
  r.elim (.pure none) fun ty =>
    (compute (do
      let k ← A.cast G.sampleCount
      A.div ty.1 k)).bind fun U => .pure (some U)

theorem agree_uniformPhase (sigma2 : Num ℝ) (x : NumPoint d) :
    Agree (uniformPhase d G member sigma2 x) (interp (uniformPhaseT d G member sigma2 x)) := by
  refine Agree.bindT (agree_run _) fun P => Agree.bindT (agree_run _) fun start => ?_
  refine Agree.bindT (agree_collectSamples d G member P sigma2 _ _ start) fun r => ?_
  rcases r with _ | ⟨total, y⟩
  · exact agree_pure _
  · exact Agree.bindT (agree_run _) fun U => agree_pure _

def initialSampleT : Tree d (Option (NumPoint d)) :=
  gaussianT.bind fun g =>
  (compute (gaussianStartProg G.rootInitial g)).bind fun x =>
  (isMemberT d member x).bind fun inside =>
  (compute (do
    let nx ← A.norm x
    A.le nx G.rootTerminal)).bind fun near =>
  .pure (if inside = true ∧ near = true then some x else none)

theorem agree_initialSample :
    Agree (initialSample d G member) (interp (initialSampleT d G member)) :=
  Agree.bindT agree_gaussian fun g => Agree.bindT (agree_run _) fun x =>
  Agree.bindT (agree_isMember d member x) fun inside => Agree.bindT (agree_run _) fun near =>
  agree_pure _

def coolingPhasesT : List (Num ℝ) → NumPoint d → Tree d (Option (Num ℝ × NumPoint d))
  | sigma2 :: tau2 :: rest, x =>
      (compute (A.cell sigma2)).bind fun s =>
      (compute (A.cell tau2)).bind fun t =>
      (coolingPhaseT d G member s t x).bind fun r =>
      r.elim (.pure none) fun Wy =>
        (coolingPhasesT (tau2 :: rest) Wy.2).bind fun r' =>
        r'.elim (.pure none) fun pz =>
          (compute (A.mul Wy.1 pz.1)).bind fun P => .pure (some (P, pz.2))
  | [], x => (compute (A.lit (1 : ℝ))).bind fun one => .pure (some (one, x))
  | [_], x => (compute (A.lit (1 : ℝ))).bind fun one => .pure (some (one, x))

theorem agree_coolingPhases :
    ∀ (l : List (Num ℝ)) (x : NumPoint d),
      Agree (coolingPhases d G member l x) (interp (coolingPhasesT d G member l x))
  | sigma2 :: tau2 :: rest, x => by
      refine Agree.bindT (agree_run _) fun s => Agree.bindT (agree_run _) fun t => ?_
      refine Agree.bindT (agree_coolingPhase d G member s t x) fun r => ?_
      rcases r with _ | ⟨W, y⟩
      · exact agree_pure _
      · refine Agree.bindT (agree_coolingPhases (tau2 :: rest) y) fun r' => ?_
        rcases r' with _ | ⟨product, z⟩
        · exact agree_pure _
        · exact Agree.bindT (agree_run _) fun P => agree_pure _
  | [], x => Agree.bindT (agree_run _) fun one => agree_pure _
  | [_], x => Agree.bindT (agree_run _) fun one => agree_pure _

def figureOneRunT : Tree d (Num ℝ) :=
  (initialSampleT d G member).bind fun r₀ =>
  r₀.elim (compute (A.lit 0)) fun x₀ =>
    (coolingPhasesT d G member G.schedule x₀).bind fun r₁ =>
    r₁.elim (compute (A.lit 0)) fun px =>
      (uniformPhaseT d G member G.terminal px.2).bind fun r₂ =>
      r₂.elim (compute (A.lit 0)) fun U =>
        compute (do
          let a ← A.mul G.gaussianIntegral px.1
          A.mul a U)

theorem agree_figureOneRun :
    Agree (figureOneRun d G member) (interp (figureOneRunT d G member)) := by
  refine Agree.bindT (agree_initialSample d G member) fun r₀ => ?_
  rcases r₀ with _ | x₀
  · exact agree_run _
  · refine Agree.bindT (agree_coolingPhases d G member _ x₀) fun r₁ => ?_
    rcases r₁ with _ | ⟨product, x⟩
    · exact agree_run _
    · refine Agree.bindT (agree_uniformPhase d G member _ x) fun r₂ => ?_
      rcases r₂ with _ | U
      · exact agree_run _
      · exact agree_run _

def cappedRunT : Tree d (Num ℝ) :=
  (queryCapT G.queryBudget).bind fun _ =>
    (figureOneRunT d G member).orElse (compute (A.lit 0))

theorem agree_cappedRun : Agree (cappedRun d G member) (interp (cappedRunT d G member)) :=
  Agree.bindT (agree_queryCap _) fun _ =>
    agree_orElse (agree_figureOneRun d G member) (agree_run _)

end Procedures

def repeatIndependentlyT {d : ℕ} (count : Num ℕ) (body : Tree d (Num ℝ)) :
    Tree d (List (Num ℝ)) :=
  (loopTree (γ := Empty) count (fun estimates =>
      body.bind fun x =>
      (compute (A.push estimates x)).bind fun estimates' => .pure (.inl estimates')) []).bind
    fun r => .pure (r.elim id Empty.elim)

theorem agree_repeatIndependently {d : ℕ} (count : Num ℕ) {bodyM : M d (Num ℝ)}
    {body : Tree d (Num ℝ)} (h : Agree bodyM (interp body)) :
    Agree (repeatIndependently count bodyM) (interp (repeatIndependentlyT count body)) :=
  Agree.bindT (agree_loop count (fun estimates => Agree.bindT h fun x =>
    Agree.bindT (agree_run _) fun _ => agree_pure _) _) fun r =>
    agree_pure_of_eq (by rcases r with _ | e <;> rfl)

/-- **CV18, as a tree.** -/
def cv18T (d : ℕ) : CV18Tree d := fun member eps roundness p =>
  (compute (runConstantsProg d eps roundness p)).bind fun G =>
  (repeatIndependentlyT G.repetitions (cappedRunT d G member)).bind fun estimates =>
  compute (A.median G.repetitions estimates)

/-- **CV18's tree stands for the program's CV18.** -/
theorem cv18T_agrees (d : ℕ) : CV18Agrees (cv18T d) := fun member eps roundness p =>
  Agree.bindT (agree_run _) fun G =>
  Agree.bindT (agree_repeatIndependently _ (agree_cappedRun d G member)) fun estimates =>
  agree_run _

/-- **The whole program agrees with its tree.** -/
theorem agree_estimatorT {d : ℕ} (fuel : ℕ) (cs : List (ComponentInput d)) (eps delta : ℝ) :
    Agree (estimator fuel cs eps delta) (interp (estimatorT (cv18T d) fuel cs eps delta)) :=
  agree_estimator (cv18T_agrees d) fuel cs eps delta

end ttc.Tape

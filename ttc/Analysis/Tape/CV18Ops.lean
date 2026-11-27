/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.RuntimeBudget
import ttc.Analysis.Tape.ChargedTapeCost
import ttc.Analysis.Tape.MedianOps
import ttc.Analysis.Tape.OpsExp
import ttc.Analysis.Tape.StepCap

/-!
# Cost simulation for CV18 on a tape

The two CV18 implementations share a tape and a membership routine. The
simulation used for accuracy matches their results, budget and tape. The
stronger relation here also bounds the sealed program's tally by that of the
charged reference trace. The reference keeps an extra query marker, so an
inequality is enough and does not erase any sealed charges.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open ttc.RuntimeBudget

open Arlib.Computation (Num Charged CostVec)
open ttc.Model.Operations
open ttc.Tape.Tree
open ArlibCommunity.Algorithms.CV18 (AmbientSpace VolumeParams)
open ttc.ChargedCV18 (ChargedProgram)

variable {d : ℕ} {α β γ δ : Type}
variable (member : NumPoint d → Prog Bool)

/-- For the scalar tally comparison, record the full facet-test tally in the
reference currency. The label does not affect the total. -/
def countedMember (x : AmbientSpace d) : ttc.ChargedCV18.Counted Bool :=
  let c := member (ofPt x)
  Charged.opMany ttc.ChargedCV18.Op.cell (opsTotal c.cost) c.val

@[simp] theorem countedMember_value (x : AmbientSpace d) :
    (countedMember member x).value = memberOracle member x := rfl

@[simp] theorem countedMember_cost (x : AmbientSpace d) :
    (countedMember member x).cost = opsTotal (member (ofPt x)).cost := by
  change ttc.ChargedCV18.opsTotal (CostVec.many _ _) = _
  exact ttc.ChargedCV18.opsTotal_many _ _

/-- A simulation that also accounts for the operations spent, for a finite
shared initial budget. -/
structure SimOps (R : α → β → Prop) (p : Tree d α) (P : ChargedProgram d β) : Prop where
  values : Sim (memberOracle member) R p P
  cost_le : ∀ b : ℕ, ∀ t : Tape d,
    (exec p b t).2.1 ≤ cexecOps (countedMember member) P b t

variable {member}

theorem SimOps.bind {R : α → β → Prop} {S : γ → δ → Prop} {p : Tree d α}
    {P : ChargedProgram d β} {f : α → Tree d γ} {F : β → ChargedProgram d δ}
    (hp : SimOps member R p P) (hf : ∀ a a', R a a' → SimOps member S (f a) (F a')) :
    SimOps member S (p.bind f) (P.bind F) := by
  refine ⟨hp.values.bind (fun a a' ha => (hf a a' ha).values), ?_⟩
  intro b t
  rw [exec_bind, cexecOps_bind]
  have hO : (fun x => (countedMember member x).value) = memberOracle member := rfl
  rw [hO]
  have hc := hp.cost_le b t
  obtain ⟨hr, hb, ht⟩ := hp.values b t
  rcases e : exec p b t with ⟨o, m, b', t'⟩
  rcases E : cexec (memberOracle member) P b t with ⟨o', B', T'⟩
  rw [e] at hc
  rw [e, E] at hr hb ht
  simp only at hr hb ht hc
  subst B' T'
  cases hr with
  | none => simpa using hc
  | some h => exact Nat.add_le_add hc ((hf _ _ h).cost_le b' t')

theorem simOps_pure {R : α → β → Prop} {a : α} {a' : β} (h : R a a') :
    SimOps member R (Tree.pure a) (ChargedProgram.pure a') :=
  ⟨sim_pure h, fun _ _ => le_rfl⟩

theorem simOps_compute {R : α → β → Prop} {c : Prog α} {c' : ttc.ChargedCV18.Counted β}
    (h : R c.val c'.value) (hc : opsTotal c.cost ≤ c'.cost) :
    SimOps member R (compute c) (ttc.ChargedCV18.compute c') := by
  refine ⟨sim_compute c c' h, fun b t => ?_⟩
  simpa only [compute, exec, ttc.ChargedCV18.compute, cexecOps, add_zero,
    ttc.ChargedCV18.Counted.cost] using hc

theorem simOps_compute_eq {c : Prog α} {c' : ttc.ChargedCV18.Counted α}
    (h : c.val = c'.value) (hc : opsTotal c.cost ≤ c'.cost) :
    SimOps member Eq (compute c) (ttc.ChargedCV18.compute c') :=
  simOps_compute h hc

theorem simOps_ite {R : α → β → Prop} (p : Prop) [Decidable p]
    {x y : Tree d α} {X Y : ChargedProgram d β}
    (hx : SimOps member R x X) (hy : SimOps member R y Y) :
    SimOps member R (if p then x else y) (if p then X else Y) := by
  split_ifs
  · exact hx
  · exact hy

theorem simOps_gaussian :
    SimOps member Eq (gaussianT (n := d))
      (ttc.ChargedCV18.drawPoint (ttc.ChargedCV18.standardGaussian d)) := by
  refine ⟨sim_gaussianT, fun b t => ?_⟩
  change d + 0 ≤
    (ttc.ChargedCV18.Counted.forEach fun i => ttc.ChargedCV18.Counted.pick ((t 0).2.1 i)).cost + 0
  simp

theorem simOps_unit :
    SimOps member Eq (unitT (n := d))
      (ttc.ChargedCV18.drawReal ArlibCommunity.Algorithms.CV18.uniformUnit) := by
  refine ⟨sim_unitT, fun b t => ?_⟩
  change 1 + 0 ≤ (ttc.ChargedCV18.Counted.pick (t 0).2.2).cost + 0
  simp

/-- A successful membership test pays for the facet computation. An exhausted
cap runs neither test. -/
theorem simOps_isMember (q : VolumeParams) (member : NumPoint q.n → Prog Bool)
    (x : NumPoint q.n) :
    SimOps member Eq (isMemberT q.n member x) (ttc.ChargedCV18.isMember x) := by
  refine ⟨sim_isMember q member x, fun b t => ?_⟩
  cases b with
  | zero => exact le_rfl
  | succ b =>
      have h1 : ((b + 1 : ℕ) : ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero b
      have hx : ofPt (ttc.ChargedCV18.NumPoint.view x) = x := ofPt_toPt x
      simp only [isMemberT, spendT, Tree.bind, exec, compute, ite_true,
        ttc.ChargedCV18.isMember, cexecOps, h1, ite_false, countedMember_cost, hx, add_zero]
      exact Nat.le_add_right _ _

theorem simOps_loopRounds {body : β → Tree d (β ⊕ γ)}
    {body' : β → ChargedProgram d (β ⊕ γ)} (h : ∀ s, SimOps member Eq (body s) (body' s)) :
    ∀ (k : ℕ) (s : β), SimOps member Eq (loopRounds body k s) (ChargedProgram.loopRounds body' k s)
  | 0, s => simOps_pure rfl
  | k + 1, s => by
      refine (h s).bind fun r r' hr => ?_
      subst hr
      rcases r with s' | a
      · exact simOps_loopRounds h k s'
      · exact simOps_pure rfl

theorem simOps_loopTree (count : Num ℕ) {body : β → Tree d (β ⊕ γ)}
    {body' : β → ChargedProgram d (β ⊕ γ)} (h : ∀ s, SimOps member Eq (body s) (body' s))
    (init : β) : SimOps member Eq (loopTree count body init)
      (ttc.ChargedCV18.loopUntil count body' init) := by
  refine ⟨sim_loopTree count (fun s => (h s).values) init, fun b t => ?_⟩
  rw [loopTree, exec, ttc.ChargedCV18.loopUntil, cexecOps, ttc.ChargedCV18.opsTotal_one]
  exact Nat.add_le_add_left ((simOps_loopRounds h count.get init).cost_le b t) 1

section Procedures

open ttc.Program

/-- Normalize scalar charges on either side of a cost simulation. -/
local macro "cv_cost" : tactic => `(tactic|
  simp [Arlib.Computation.Charged.cost_bind, opsTotal_add, opsTotal_bind,
    opsTotal_smul, opsTotal_pure, opsTotal_one, A.cast, A.ceil, A.log, A.max,
    A.mulLit, A.divLit, A.litDiv, A.litMax, A.pow,
    ttc.ChargedCV18.Counted.bind_cost, ttc.ChargedCV18.Counted.smul_cost,
    ttc.ChargedCV18.Counted.mulLit,
    ttc.ChargedCV18.Counted.divLit, ttc.ChargedCV18.Counted.litDiv,
    ttc.ChargedCV18.Counted.litMax, ttc.ChargedCV18.Counted.pow])

private theorem cost_phaseConstants (G : ttc.Program.RunConstants) (s : Num ℝ) :
    opsTotal (phaseConstantsProg G s).cost =
      (ttc.ChargedCV18.phaseConstantsProg (RunConstants.toC G) s).cost := by
  simp only [phaseConstantsProg, ttc.ChargedCV18.phaseConstantsProg, RunConstants.toC,
    walkRequirementProg, ttc.ChargedCV18.walkRequirementProg]
  cv_cost

variable (q : VolumeParams) (G : ttc.Program.RunConstants) (member : NumPoint q.n → Prog Bool)

local notation "G'" => RunConstants.toC G

private theorem cvDimPos (q : VolumeParams) : 0 < q.n := by
  have h := q.dim_ok
  omega

/-- The ball-walk move pays for all its draws, proposal arithmetic, facet
test, and Metropolis comparisons. -/
theorem simOps_ballWalkStep (P : ttc.Program.PhaseConstants) (s : Num ℝ) (x : NumPoint q.n) :
    SimOps member Eq (ballWalkStepT q.n G member P s x)
      (ttc.ChargedCV18.ballWalkStep q G' (PhaseConstants.toC P) s x) := by
  have hd := cvDimPos q
  refine SimOps.bind simOps_gaussian fun g _ h => ?_
  subst h
  refine SimOps.bind simOps_unit fun u _ h => ?_
  subst h
  refine SimOps.bind (simOps_compute_eq (val_ballProposalProg _ _ _ _ _) (by
    rw [opsTotal_ballProposalProg hd, ttc.ChargedCV18.ballProposalProg_cost hd])) fun y _ h => ?_
  subst h
  refine SimOps.bind (simOps_isMember q member y) fun inside _ h => ?_
  subst h
  refine SimOps.bind simOps_unit fun coin _ h => ?_
  subst h
  refine SimOps.bind (simOps_compute_eq (val_properTestProg _ _ _) (by
    rw [opsTotal_properTestProg hd, ttc.ChargedCV18.properTestProg_cost hd])) fun proper _ h => ?_
  subst h
  refine SimOps.bind (simOps_compute_eq (val_lazyTestProg _ _ _ _) (by
    rw [opsTotal_lazyTestProg hd, ttc.ChargedCV18.lazyTestProg_cost hd])) fun move _ h => ?_
  subst h
  exact simOps_ite _ (simOps_pure rfl) (simOps_pure rfl)

theorem simOps_properWalkRound (P : ttc.Program.PhaseConstants) (s : Num ℝ)
    (left : Num ℕ) (x : NumPoint q.n) :
    SimOps member Eq (properWalkRoundT q.n G member P s left x)
      (ttc.ChargedCV18.properWalkRound q G' (PhaseConstants.toC P) s left x) := by
  refine SimOps.bind (simOps_compute_eq (by cv_simp) (by
    simp [opsTotal_add, ttc.ChargedCV18.Counted.bind_cost])) fun done _ h => ?_
  subst h
  refine simOps_ite _ ?_ ?_
  · refine SimOps.bind (simOps_compute_eq (val_smul _ _) (by
      rw [opsTotal_smul, ttc.ChargedCV18.Counted.smul_cost])) fun y _ h => ?_
    subst h
    exact SimOps.bind (simOps_isMember q member y) fun _ _ _ => simOps_pure rfl
  · refine SimOps.bind (simOps_ballWalkStep q G member P s x) fun r _ h => ?_
    subst h
    rcases r with ⟨proper, y⟩
    exact simOps_ite _ (SimOps.bind (simOps_compute_eq (by cv_simp) (by
      simp [opsTotal_add, ttc.ChargedCV18.Counted.bind_cost])) fun _ _ h => h ▸ simOps_pure rfl)
      (simOps_pure rfl)

theorem simOps_properWalk (P : ttc.Program.PhaseConstants) (s : Num ℝ)
    (cap : Num ℕ) (x : NumPoint q.n) :
    SimOps member Eq (properWalkT q.n G member P s cap x)
      (ttc.ChargedCV18.properWalk q G' (PhaseConstants.toC P) s cap x) := by
  refine SimOps.bind (simOps_loopTree cap (fun a => simOps_properWalkRound q G member P s a.1 a.2) _)
    fun r _ h => ?_
  subst h
  rcases r with _ | y <;> exact simOps_pure rfl

theorem simOps_rejectionAttempt (P : ttc.Program.PhaseConstants) (s : Num ℝ) (x : NumPoint q.n) :
    SimOps member Eq (rejectionAttemptT q.n G member P s x)
      (ttc.ChargedCV18.rejectionAttempt q G' (PhaseConstants.toC P) s x) := by
  have hd := cvDimPos q
  refine SimOps.bind (simOps_compute_eq (val_smul _ _) (by
    rw [opsTotal_smul, ttc.ChargedCV18.Counted.smul_cost])) fun y _ h => ?_
  subst h
  refine SimOps.bind (simOps_isMember q member y) fun inside _ h => ?_
  subst h
  refine SimOps.bind simOps_unit fun coin _ h => ?_
  subst h
  refine SimOps.bind (simOps_compute_eq (val_properTestProg _ _ _) (by
    rw [opsTotal_properTestProg hd, ttc.ChargedCV18.properTestProg_cost hd])) fun proper _ h => ?_
  subst h
  refine SimOps.bind (simOps_compute_eq (val_scaleAcceptTestProg _ _ _ _) (by
    rw [opsTotal_scaleAcceptTestProg hd, ttc.ChargedCV18.scaleAcceptTestProg_cost hd]))
    fun accept _ h => ?_
  subst h
  exact simOps_ite _ (simOps_pure rfl) (simOps_pure rfl)

theorem simOps_sampleAttempt (P : ttc.Program.PhaseConstants) (s : Num ℝ)
    (cap : Num ℕ) (x : NumPoint q.n) :
    SimOps member Eq (sampleAttemptT q.n G member P s cap x)
      (ttc.ChargedCV18.sampleAttempt q G' (PhaseConstants.toC P) s cap x) := by
  refine SimOps.bind (simOps_properWalk q G member P s cap x) fun r _ h => ?_
  subst h
  rcases r with _ | y
  · exact simOps_pure rfl
  · refine SimOps.bind (simOps_rejectionAttempt q G member P s y) fun a _ h => ?_
    subst h
    rcases a with ⟨accepted, z⟩
    exact simOps_ite _ (simOps_pure rfl) (simOps_pure rfl)

theorem simOps_sampleFinish (weight : NumPoint q.n → Prog (Num ℝ))
    (weight' : NumPoint q.n → ttc.ChargedCV18.Counted (Num ℝ))
    (hv : ∀ z, (weight z).val = (weight' z).value)
    (hc : ∀ z, opsTotal (weight z).cost ≤ (weight' z).cost)
    (total : Num ℝ) (a : NumPoint q.n ⊕ Option (NumPoint q.n × NumPoint q.n)) :
    SimOps member Eq (sampleFinishT q.n weight total a)
      (ttc.ChargedCV18.sampleFinish q weight' total a) := by
  rcases a with _ | _ | ⟨z, y⟩
  · exact simOps_pure rfl
  · exact simOps_pure rfl
  · refine SimOps.bind (simOps_compute_eq (hv z) (hc z)) fun w _ h => ?_
    subst h
    exact SimOps.bind (simOps_compute_eq (by cv_simp) (by cv_cost))
      fun _ _ h => h ▸ simOps_pure rfl

theorem simOps_sampleRound (P : ttc.Program.PhaseConstants) (s : Num ℝ)
    (weight : NumPoint q.n → Prog (Num ℝ))
    (weight' : NumPoint q.n → ttc.ChargedCV18.Counted (Num ℝ))
    (hv : ∀ z, (weight z).val = (weight' z).value)
    (hc : ∀ z, opsTotal (weight z).cost ≤ (weight' z).cost)
    (cap : Num ℕ) (st : Num ℝ × NumPoint q.n) :
    SimOps member Eq (sampleRoundT q.n G member P s weight cap st)
      (ttc.ChargedCV18.sampleRound q G' (PhaseConstants.toC P) s weight' cap st) :=
  SimOps.bind (simOps_loopTree _ (fun x => simOps_sampleAttempt q G member P s cap x) _)
    fun a _ h => h ▸ simOps_sampleFinish q member weight weight' hv hc st.1 a

theorem simOps_collectSamples (P : ttc.Program.PhaseConstants) (s : Num ℝ)
    (weight : NumPoint q.n → Prog (Num ℝ))
    (weight' : NumPoint q.n → ttc.ChargedCV18.Counted (Num ℝ))
    (hv : ∀ z, (weight z).val = (weight' z).value)
    (hc : ∀ z, opsTotal (weight z).cost ≤ (weight' z).cost)
    (samples : Num ℕ) (start : NumPoint q.n) :
    SimOps member Eq (collectSamplesT q.n G member P s weight samples start)
      (ttc.ChargedCV18.collectSamples q G' (PhaseConstants.toC P) s weight' samples start) := by
  refine SimOps.bind (simOps_compute_eq (by cv_simp; rfl) (by cv_cost)) fun c _ h => ?_
  subst h
  rcases c with ⟨zero, cap⟩
  refine SimOps.bind (simOps_loopTree samples
    (fun st => simOps_sampleRound q G member P s weight weight' hv hc cap st) _) fun r _ h => ?_
  subst h
  rcases r with _ | _ <;> exact simOps_pure rfl

theorem simOps_coolingPhase (s t : Num ℝ) (x : NumPoint q.n) :
    SimOps member Eq (coolingPhaseT q.n G member s t x)
      (ttc.ChargedCV18.coolingPhase q G' s t x) := by
  have hd := cvDimPos q
  refine SimOps.bind (simOps_compute (R := fun P P' => PhaseConstants.toC P = P')
    (val_phaseConstantsProg G s) (cost_phaseConstants G s).le) fun P _ h => ?_
  subst h
  refine SimOps.bind (simOps_compute_eq (val_smul _ _) (by cv_cost)) fun start _ h => ?_
  subst h
  refine SimOps.bind (simOps_collectSamples q G member P s _ _
    (fun z => val_gaussianRatioWeightProg _ _ z) (fun z => ?_) _ start) fun r _ h => ?_
  · rw [opsTotal_gaussianRatioWeightProg hd, ttc.ChargedCV18.gaussianRatioWeightProg_cost hd]
  · subst h
    rcases r with _ | ⟨total, y⟩
    · exact simOps_pure rfl
    · refine SimOps.bind (simOps_compute_eq (by cv_simp; rfl) (by cv_cost)) fun W _ h => ?_
      subst h
      exact SimOps.bind (simOps_compute_eq (val_smul _ _) (by cv_cost))
        fun _ _ h => h ▸ simOps_pure rfl

theorem simOps_uniformPhase (s : Num ℝ) (x : NumPoint q.n) :
    SimOps member Eq (uniformPhaseT q.n G member s x) (ttc.ChargedCV18.uniformPhase q G' s x) := by
  have hd := cvDimPos q
  refine SimOps.bind (simOps_compute (R := fun P P' => PhaseConstants.toC P = P')
    (val_phaseConstantsProg G s) (cost_phaseConstants G s).le) fun P _ h => ?_
  subst h
  refine SimOps.bind (simOps_compute_eq (val_smul _ _) (by cv_cost)) fun start _ h => ?_
  subst h
  refine SimOps.bind (simOps_collectSamples q G member P s _ _
    (fun z => val_uniformRatioWeightProg _ z) (fun z => ?_) _ start) fun r _ h => ?_
  · rw [opsTotal_uniformRatioWeightProg hd, ttc.ChargedCV18.uniformRatioWeightProg_cost hd]
  · subst h
    rcases r with _ | ⟨total, y⟩
    · exact simOps_pure rfl
    · exact SimOps.bind (simOps_compute_eq (by cv_simp; rfl) (by cv_cost)) fun _ _ h =>
        h ▸ simOps_pure rfl

theorem simOps_initialSample :
    SimOps member Eq (initialSampleT q.n G member) (ttc.ChargedCV18.initialSample q G') := by
  have hd := cvDimPos q
  refine SimOps.bind simOps_gaussian fun g _ h => ?_
  subst h
  refine SimOps.bind (simOps_compute_eq (val_gaussianStartProg _ _) (by
    rw [gaussianStartProg, opsTotal_smul, ttc.ChargedCV18.gaussianStartProg_cost])) fun x _ h => ?_
  subst h
  refine SimOps.bind (simOps_isMember q member x) fun inside _ h => ?_
  subst h
  exact SimOps.bind (simOps_compute_eq (by cv_simp; rfl) (by
    simp [opsTotal_add, opsTotal_norm hd, ttc.ChargedCV18.Counted.bind_cost,
      ttc.ChargedCV18.Counted.norm_cost hd])) fun _ _ h => h ▸ simOps_pure rfl

theorem simOps_coolingPhases :
    ∀ (l : List (Num ℝ)) (x : NumPoint q.n), SimOps member Eq (coolingPhasesT q.n G member l x)
      (ttc.ChargedCV18.coolingPhases q G' l x)
  | s :: t :: rest, x => by
      refine SimOps.bind (simOps_compute_eq (by cv_simp) (by cv_cost)) fun s' _ h => ?_
      subst h
      refine SimOps.bind (simOps_compute_eq (by cv_simp) (by cv_cost)) fun t' _ h => ?_
      subst h
      refine SimOps.bind (simOps_coolingPhase q G member s' t' x) fun r _ h => ?_
      subst h
      rcases r with _ | ⟨W, y⟩
      · exact simOps_pure rfl
      · refine SimOps.bind (simOps_coolingPhases (t :: rest) y) fun r' _ h => ?_
        subst h
        rcases r' with _ | ⟨product, z⟩
        · exact simOps_pure rfl
        · exact SimOps.bind (simOps_compute_eq (by cv_simp) (by cv_cost))
            fun _ _ h => h ▸ simOps_pure rfl
  | [], x => SimOps.bind (simOps_compute_eq (by cv_simp) (by cv_cost))
      fun _ _ h => h ▸ simOps_pure rfl
  | [_], x => SimOps.bind (simOps_compute_eq (by cv_simp) (by cv_cost))
      fun _ _ h => h ▸ simOps_pure rfl

/-- One CV18 run before its cap is installed, with every operation tracked. -/
theorem simOps_figureOneRun :
    SimOps member Eq (figureOneRunT q.n G member) (ttc.ChargedCV18.figureOneRun q G') := by
  refine SimOps.bind (simOps_initialSample q G member) fun r₀ _ h => ?_
  subst h
  rcases r₀ with _ | x₀
  · exact simOps_compute_eq (by cv_simp) (by cv_cost)
  · refine SimOps.bind (simOps_coolingPhases q G member _ x₀) fun r₁ _ h => ?_
    subst h
    rcases r₁ with _ | ⟨product, x⟩
    · exact simOps_compute_eq (by cv_simp) (by cv_cost)
    · refine SimOps.bind (simOps_uniformPhase q G member _ x) fun r₂ _ h => ?_
      subst h
      rcases r₂ with _ | U
      · exact simOps_compute_eq (by cv_simp) (by cv_cost)
      · exact simOps_compute_eq (by simp only [RunConstants.toC]; cv_simp) (by cv_cost)

theorem exec_cappedRunT_ops_le (M : ℕ) (hM : ∀ x, opsTotal (member x).cost ≤ M)
    (b : ℕ) (t : Tape q.n) :
    (exec (cappedRunT q.n G member) b t).2.1 ≤ cappedRunOps G q.n M := by
  have h := ((simOps_figureOneRun q G member).cost_le G.queryBudget.get t).trans
    (cexecOps_le_of_credit (countedMember member) (fun x => by
      rw [countedMember_cost]
      exact hM _) (ttc.ChargedCV18.figureOneRun_opCredit q G') G.queryBudget.get t)
  change _ ≤ ttc.ChargedCV18.runReserve q.n G.schedule.length +
    (ttc.ChargedCV18.opsPerQuery q.n + M) * G.queryBudget.get at h
  simp only [ttc.ChargedCV18.runReserve, ttc.ChargedCV18.opsPerPhase,
    ttc.ChargedCV18.opsPerQuery] at h
  simp only [cappedRunT, queryCapT, Tree.bind, exec, exec_orElse, cappedRunOps]
  rcases he : exec (figureOneRunT q.n G member) G.queryBudget.get t with ⟨r, j, b', t'⟩
  rw [he] at h
  simp only at h
  rcases r with _ | x
  · simp only [compute, exec, opsTotal_lit, add_zero]
    omega
  · simp only
    omega

end Procedures

section Repetitions

open ttc.Program

private theorem post_repeatIndependentlyT_size (count : Num ℕ) (p : Tree d (Num ℝ)) :
    Post (repeatIndependentlyT count p) fun r => r.length ≤ count.get := by
  unfold repeatIndependentlyT
  show Post ((loopRounds _ count.get []).bind _) _
  refine Post.bind ((post_loopRounds_size List.length (fun xs => ?_) count.get []).mono ?_)
  · refine Post.bind (post_of_forall (fun x => ?_) _)
    refine post_compute_bind ?_
    change (A.push xs x).val.length ≤ xs.length + 1
    simp [A.push, ttc.Model.Operations.push, Charged.val_op]
  · rintro (xs | e) hr
    · change xs.length ≤ count.get
      simpa only [Sum.elim_inl, List.length_nil, Nat.zero_add] using hr
    · exact e.elim

private theorem exec_repeatIndependentlyT_ops_le (count : Num ℕ) (p : Tree d (Num ℝ)) (C : ℕ)
    (hC : ∀ b t, (exec p b t).2.1 ≤ C) (b : ℕ) (t : Tape d) :
    (exec (repeatIndependentlyT count p) b t).2.1 ≤ 1 + count.get * (C + 1) := by
  unfold repeatIndependentlyT
  show (exec (Tree.step _ fun _ => (loopRounds _ count.get []).bind _) b t).2.1 ≤ _
  simp only [exec, opsTotal_op]
  apply Nat.add_le_add_left
  refine (exec_ops_bind_le (post_of_forall (Q := fun _ => True) (fun _ => trivial) _)
    (count.get * (C + 1)) 0 b t ?_ (fun _ _ _ _ => Nat.le_refl _)).trans_eq (Nat.add_zero _)
  refine exec_ops_loopRounds_le (fun xs b' t' => ?_) _ _ _ _
  refine exec_ops_bind_le (post_of_forall (Q := fun _ => True) (fun _ => trivial) _)
    C 1 b' t' (hC b' t') fun x _ b'' t'' => ?_
  simp only [compute, exec, Tree.bind, opsTotal_push, add_zero, le_refl]

/-- Every execution of sealed CV18 on a certified input stays within its
arithmetic budget, including its charged membership tests. -/
theorem exec_cv18T_ops_le (q : VolumeParams) (member : NumPoint q.n → Prog Bool) (M : ℕ)
    (hM : ∀ x, opsTotal (member x).cost ≤ M) (eps roundness p : Num ℝ)
    (b : ℕ) (t : Tape q.n) :
    (exec (cv18T q.n member eps roundness p) b t).2.1 ≤ cv18TapeOpsBudget q.n M eps roundness p := by
  let c := runConstantsProg q.n eps roundness p
  let G := c.val
  let r := G.repetitions.get
  let P := cappedRunT q.n G member
  change opsTotal c.cost +
    (exec ((repeatIndependentlyT G.repetitions P).bind fun a =>
      compute (A.median G.repetitions a)) b t).2.1 ≤
      opsTotal c.cost + (1 + r * (cappedRunOps G q.n M + 1)) + (r * (4 * r + 5) + 5)
  rw [Nat.add_assoc]
  apply Nat.add_le_add_left
  refine exec_ops_bind_le (post_repeatIndependentlyT_size _ _) _ _ b t
    (exec_repeatIndependentlyT_ops_le G.repetitions P (cappedRunOps G q.n M)
      (exec_cappedRunT_ops_le q G member M hM) b t) fun a ha b' t' => ?_
  simp only [compute, exec, add_zero]
  refine (opsTotal_median_le _ _).trans (Nat.add_le_add_right ?_ _)
  exact Nat.mul_le_mul ha (Nat.add_le_add_right (Nat.mul_le_mul_left 4 ha) 5)

/-- The CV18 call used by a TTC component, with facet tests priced at their
proved cost rather than at a supplied membership allowance. -/
theorem Eops_cv18T_allFacets_le (q : VolumeParams) (r : ℕ) (a : Fin r → NumPoint q.n)
    (off : Fin r → Num ℝ) (eps roundness p : Num ℝ) (b : ℕ) :
    Eops (cv18T q.n (ttc.Program.allFacets r a off) eps roundness p) b ≤
      cv18TapeOpsBudget q.n (2 * q.n * r) eps roundness p := by
  have hm := (mf_cv18T (Q := Unit) (memberMP_allFacets r a off) eps roundness p).outcome () b
  refine Eops_le_of_exec_ops_le _ _ _ hm (exec_cv18T_ops_le q _ _ ?_ _ _ _ b)
  intro x
  exact (opsTotal_allFacets (cvDimPos q) r a off x).le

end Repetitions

end ttc.Tape

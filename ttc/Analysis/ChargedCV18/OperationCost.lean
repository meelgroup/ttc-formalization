/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.ChargedCV18.Bridge

/-!
# The arithmetic cost of `cv18Program`

`opCost` counts the operations `cv18Program` records with `compute`.  This file bounds it
(`cv18Program_opCost_le`):

```
opCost (cv18Program q) ≤ 11·T + 176 + m · (numPhases·(2n + 83) + 7n + 88 + (12n + 31)·B) + 4m²
```

with `T = terminalPhaseSteps q`, `m = confidenceRepetitions q` and `B = queryBudget q`.
So each run spends at most `12n + 31` operations per membership query it is allowed,
plus `2n + 83` per phase and `7n + 88` once.  The constants of the call cost at most
`10T + 169`, entering the repetition loop `1`, and the median of the `m` runs at most
`4m² + 5`.

## The credit argument

A run is stopped at its `B + 1`-st query, so its cost must be charged to the queries it
makes.  `OpCredit a p s Q` says: started with `s` credits, where each query adds `a`
credits and each operation spends one, `p` never runs out of credit, and it ends in a
state `(r, s')` with `Q r s'`.  Then the capped program spends at most `s + a·B`
operations (`opCost_withQueryCap_le`).  A loop over a held count runs on credit when each
round keeps an invariant (`opCredit_loopRounds`).

With `a = 12n + 31` every query pays for the arithmetic around it: a ball-walk step spends
`12n + 23` (the random point `n`, the uniform `1`, the proposal `5n + 2`, the query `1`, the
coin `1`, the properness test `2n + 2`, the lazy test `4n + 16`) and the walk's own counting
`4`, and the
two queries that end a walk and test its point pay for the rejection test, the weight and
the start of the next walk.  What remains is paid from the starting credit: `2n + 83` per
phase and `7n + 84` once.
-/

namespace ttc.ChargedCV18

open ArlibCommunity.Algorithms.CV18

namespace ChargedProgram

variable {n : ℕ} {α β : Type}

/-- **Running on credit.**  Started with `s` credits, each query adding `a` and each
operation spending one, `p` never runs out, and it ends in a state satisfying `Q`. -/
def OpCredit (a : ℕ) : ChargedProgram n α → ℕ → (α → ℕ → Prop) → Prop
  | .pure r, s, Q => Q r s
  | .query _ next, s, Q => ∀ b, OpCredit a (next b) (s + a) Q
  | .randomNat _ next, s, Q => ∀ v, OpCredit a (next v) s Q
  | .randomPoint _ _ next, s, Q => ∀ v, OpCredit a (next v) s Q
  | .randomReal _ _ next, s, Q => ∀ v, OpCredit a (next v) s Q
  | .tick k next, s, Q => opsTotal k ≤ s ∧ OpCredit a next (s - opsTotal k) Q

variable {a : ℕ}

theorem opCredit_bind (p : ChargedProgram n α) (f : α → ChargedProgram n β)
    (s : ℕ) (Q : β → ℕ → Prop) :
    OpCredit a (p.bind f) s Q ↔ OpCredit a p s fun r s' => OpCredit a (f r) s' Q := by
  induction p generalizing s with
  | pure r => exact Iff.rfl
  | query x next ih => exact forall_congr' fun b => ih b _
  | randomNat law next ih => exact forall_congr' fun v => ih v _
  | randomPoint law h next ih => exact forall_congr' fun v => ih v _
  | randomReal law h next ih => exact forall_congr' fun v => ih v _
  | tick k next ih => exact and_congr Iff.rfl (ih _)

theorem OpCredit.mono {p : ChargedProgram n α} {s : ℕ} {Q Q' : α → ℕ → Prop}
    (hQ : ∀ r s', Q r s' → Q' r s') (h : OpCredit a p s Q) : OpCredit a p s Q' := by
  induction p generalizing s with
  | pure r => exact hQ r s h
  | query x next ih => exact fun b => ih b (h b)
  | randomNat law next ih => exact fun v => ih v (h v)
  | randomPoint law hl next ih => exact fun v => ih v (h v)
  | randomReal law hl next ih => exact fun v => ih v (h v)
  | tick k next ih => exact ⟨h.1, ih h.2⟩

@[simp] theorem opCredit_pure (r : α) (s : ℕ) (Q : α → ℕ → Prop) :
    OpCredit a (Pure.pure r : ChargedProgram n α) s Q ↔ Q r s := Iff.rfl

@[simp] theorem opCredit_pure' (r : α) (s : ℕ) (Q : α → ℕ → Prop) :
    OpCredit a (ChargedProgram.pure (n := n) r) s Q ↔ Q r s := Iff.rfl

@[simp] theorem opCredit_compute (c : Counted α) (s : ℕ) (Q : α → ℕ → Prop) :
    OpCredit a (compute (n := n) c) s Q ↔ c.cost ≤ s ∧ Q c.value (s - c.cost) := Iff.rfl

@[simp] theorem opCredit_isMember (x : NumPoint n) (s : ℕ) (Q : Bool → ℕ → Prop) :
    OpCredit a (isMember x) s Q ↔ ∀ b, 1 ≤ s + a ∧ Q b (s + a - 1) := by
  change (∀ b, (Counted.isMember b).cost ≤ s + a ∧ Q (Counted.isMember b).value (s + a - (Counted.isMember b).cost)) ↔ _
  simp only [Counted.isMember_cost, Counted.isMember_value]

@[simp] theorem opCredit_drawPoint (law : MeasureTheory.Measure (AmbientSpace n))
    [MeasureTheory.IsProbabilityMeasure law] (s : ℕ) (Q : NumPoint n → ℕ → Prop) :
    OpCredit a (drawPoint law) s Q ↔ ∀ g : AmbientSpace n, n ≤ s ∧
      Q (Counted.forEach fun i => Counted.pick (g i)).value (s - n) := by
  have hc : ∀ g : AmbientSpace n, (Counted.forEach fun i => Counted.pick (g i)).cost = n := by
    intro g; simp
  change (∀ g : AmbientSpace n, _ ∧ _) ↔ _
  simp only [Counted.cost] at hc
  simp only [hc]
  exact Iff.rfl

@[simp] theorem opCredit_drawReal (law : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (s : ℕ) (Q : Arlib.Computation.Num ℝ → ℕ → Prop) :
    OpCredit a (drawReal (n := n) law) s Q ↔ ∀ v : ℝ, 1 ≤ s ∧ Q (Counted.pick v).value (s - 1) := by
  have hc : ∀ v : ℝ, opsTotal (Counted.pick v).tally = 1 := fun v => Counted.pick_cost v
  change (∀ v : ℝ, _ ∧ _) ↔ _
  simp only [hc]
  exact Iff.rfl

@[simp] theorem opCredit_tick (k : Arlib.Computation.CostVec Op) (p : ChargedProgram n α)
    (s : ℕ) (Q : α → ℕ → Prop) :
    OpCredit a (.tick k p) s Q ↔ opsTotal k ≤ s ∧ OpCredit a p (s - opsTotal k) Q := Iff.rfl

@[simp] theorem opCredit_loopUntil {β γ : Type} (count : Arlib.Computation.Num ℕ)
    (body : β → ChargedProgram n (β ⊕ γ)) (init : β) (s : ℕ) (Q : β ⊕ γ → ℕ → Prop) :
    OpCredit a (loopUntil count body init) s Q ↔
      1 ≤ s ∧ OpCredit a (loopRounds body count.get init) (s - 1) Q := by
  simp [loopUntil]

/-- **A loop runs on credit** if each round keeps an invariant `Inv` of the state and the
credit, and the invariant gives the loop's postcondition when the rounds run out. -/
theorem opCredit_loopRounds {β γ : Type} (body : β → ChargedProgram n (β ⊕ γ))
    (Inv : β → ℕ → Prop) (Q : β ⊕ γ → ℕ → Prop) (hout : ∀ b s, Inv b s → Q (.inl b) s)
    (hbody : ∀ b s, Inv b s → OpCredit a (body b) s fun r s' => match r with
      | .inl b' => Inv b' s'
      | .inr c => Q (.inr c) s') :
    ∀ (k : ℕ) (b : β) (s : ℕ), Inv b s → OpCredit a (loopRounds body k b) s Q := by
  intro k
  induction k with
  | zero => intro b s h; exact hout b s h
  | succ k ih =>
    intro b s h
    simp only [loopRounds, opCredit_bind]
    refine (hbody b s h).mono fun r s' hr => ?_
    rcases r with b' | c
    · exact ih b' s' hr
    · exact hr

@[simp] theorem opCredit_ite (c : Prop) [Decidable c] (p p' : ChargedProgram n α)
    (s : ℕ) (Q : α → ℕ → Prop) :
    OpCredit a (if c then p else p') s Q ↔ if c then OpCredit a p s Q else OpCredit a p' s Q := by
  split <;> rfl

/-- **The capped program is paid for by its queries.**  A program that runs on `s`
credits with `a` per query spends at most `s + a·B` operations when stopped at its
`B + 1`-st query. -/
theorem opCost_withQueryCap_le {p : ChargedProgram n α} {s : ℕ} {Q : α → ℕ → Prop}
    (h : OpCredit a p s Q) (B : ℕ) :
    (p.withQueryCap B).opCost ≤ ((s + a * B : ℕ) : ℕ∞) := by
  induction p generalizing s B with
  | pure r => simp [withQueryCap, opCost]
  | query x next ih =>
      cases B with
      | zero => simp [withQueryCap, opCost]
      | succ B =>
          simp only [withQueryCap, opCost]
          refine iSup_le fun b => (ih b (h b) B).trans ?_
          exact Nat.cast_le.mpr (le_of_eq (by ring))
  | randomNat law next ih => exact iSup_le fun v => ih v (h v) B
  | randomPoint law hl next ih => exact iSup_le fun v => ih v (h v) B
  | randomReal law hl next ih => exact iSup_le fun v => ih v (h v) B
  | tick k next ih =>
      simp only [withQueryCap, opCost]
      calc (opsTotal k : ℕ∞) + (next.withQueryCap B).opCost
            ≤ opsTotal k + ((s - opsTotal k + a * B : ℕ) : ℕ∞) :=
            add_le_add le_rfl (ih h.2 B)
        _ = ((s + a * B : ℕ) : ℕ∞) := by
            have h1 := h.1
            generalize opsTotal k = t at h1 ⊢
            rw [← Nat.cast_add]
            congr 1
            omega

/-! ### `opCost` of sequential composition -/

theorem opCost_bind_le (p : ChargedProgram n α) {f : α → ChargedProgram n β}
    {M : ℕ∞} (hf : ∀ r, (f r).opCost ≤ M) : (p.bind f).opCost ≤ p.opCost + M := by
  induction p with
  | pure r => simpa [bind, opCost] using hf r
  | query x next ih =>
      simp only [bind, opCost]
      exact iSup_le fun b => (ih b).trans
        (add_le_add (le_iSup (fun b => (next b).opCost) b) le_rfl)
  | randomNat law next ih =>
      simp only [bind, opCost]
      exact iSup_le fun v => (ih v).trans
        (add_le_add (le_iSup (fun v => (next v).opCost) v) le_rfl)
  | randomPoint law h next ih =>
      simp only [bind, opCost]
      exact iSup_le fun v => (ih v).trans
        (add_le_add (le_iSup (fun v => (next v).opCost) v) le_rfl)
  | randomReal law h next ih =>
      simp only [bind, opCost]
      exact iSup_le fun v => (ih v).trans
        (add_le_add (le_iSup (fun v => (next v).opCost) v) le_rfl)
  | tick k next ih =>
      simp only [bind, opCost]
      rw [add_assoc]
      exact add_le_add le_rfl ih

theorem opCost_compute_bind (c : Counted α) (f : α → ChargedProgram n β) :
    ((compute c).bind f).opCost = c.cost + (f c.value).opCost := rfl

theorem opCost_compute (c : Counted α) : (compute (n := n) c).opCost = c.cost := by
  simp only [compute, opCost, add_zero]
  rfl

theorem opCost_pure (r : α) : (Pure.pure r : ChargedProgram n α).opCost = 0 := rfl

/-- **Every result of `p` satisfies `P`**, on every execution. -/
def Results (P : α → Prop) : ChargedProgram n α → Prop
  | .pure r => P r
  | .query _ next => ∀ b, Results P (next b)
  | .randomNat _ next => ∀ v, Results P (next v)
  | .randomPoint _ _ next => ∀ v, Results P (next v)
  | .randomReal _ _ next => ∀ v, Results P (next v)
  | .tick _ next => Results P next

theorem results_bind {P : β → Prop} (p : ChargedProgram n α)
    (f : α → ChargedProgram n β) :
    Results P (p.bind f) ↔ Results (fun r => Results P (f r)) p := by
  induction p with
  | pure r => exact Iff.rfl
  | query x next ih => exact forall_congr' fun b => ih b
  | randomNat law next ih => exact forall_congr' fun v => ih v
  | randomPoint law h next ih => exact forall_congr' fun v => ih v
  | randomReal law h next ih => exact forall_congr' fun v => ih v
  | tick k next ih => exact ih

theorem results_of_forall {P : α → Prop} (hP : ∀ r, P r) :
    ∀ p : ChargedProgram n α, Results P p
  | .pure r => hP r
  | .query _ next => fun b => results_of_forall hP (next b)
  | .randomNat _ next => fun v => results_of_forall hP (next v)
  | .randomPoint _ _ next => fun v => results_of_forall hP (next v)
  | .randomReal _ _ next => fun v => results_of_forall hP (next v)
  | .tick _ next => results_of_forall hP next

/-- `opCost_bind_le`, needing the bound only on the results `p` can return. -/
theorem opCost_bind_le_of_results (p : ChargedProgram n α) {P : α → Prop}
    (hp : Results P p) {f : α → ChargedProgram n β} {M : ℕ∞}
    (hf : ∀ r, P r → (f r).opCost ≤ M) : (p.bind f).opCost ≤ p.opCost + M := by
  induction p with
  | pure r => simpa [bind, opCost] using hf r hp
  | query x next ih =>
      simp only [bind, opCost]
      exact iSup_le fun b => (ih b (hp b)).trans
        (add_le_add (le_iSup (fun b => (next b).opCost) b) le_rfl)
  | randomNat law next ih =>
      simp only [bind, opCost]
      exact iSup_le fun v => (ih v (hp v)).trans
        (add_le_add (le_iSup (fun v => (next v).opCost) v) le_rfl)
  | randomPoint law h next ih =>
      simp only [bind, opCost]
      exact iSup_le fun v => (ih v (hp v)).trans
        (add_le_add (le_iSup (fun v => (next v).opCost) v) le_rfl)
  | randomReal law h next ih =>
      simp only [bind, opCost]
      exact iSup_le fun v => (ih v (hp v)).trans
        (add_le_add (le_iSup (fun v => (next v).opCost) v) le_rfl)
  | tick k next ih =>
      simp only [bind, opCost]
      rw [add_assoc]
      exact add_le_add le_rfl (ih hp)

/-! ### Answering the queries with a charged routine -/

/-- **`answerWith` keeps the output law**: answering each query with `member` is running
the program against the oracle `x ↦ (member x).value`.  The oracle passed to the result
is never consulted, since it has no queries left. -/
theorem runEstimate_answerWith [MeasurableSpace α] (member : AmbientSpace n → Counted Bool)
    (oracle : AmbientSpace n → Bool) (p : ChargedProgram n α) :
    (p.answerWith member).runEstimate oracle = p.runEstimate fun x => (member x).value := by
  induction p with
  | pure r => rfl
  | query x next ih => exact ih _
  | randomNat law next ih => simp only [answerWith, runEstimate, ih]
  | randomPoint law h next ih => simp only [answerWith, runEstimate, ih]
  | randomReal law h next ih => simp only [answerWith, runEstimate, ih]
  | tick k next ih => exact ih

/-- **`answerWith` leaves no queries.** -/
theorem queryCost_answerWith (member : AmbientSpace n → Counted Bool)
    (p : ChargedProgram n α) : (p.answerWith member).queryCost = 0 := by
  induction p with
  | pure r => rfl
  | query x next ih => exact ih _
  | randomNat law next ih => simp [answerWith, queryCost, ih]
  | randomPoint law h next ih => simp [answerWith, queryCost, ih]
  | randomReal law h next ih => simp [answerWith, queryCost, ih]
  | tick k next ih => exact ih

/-- **`answerWith` costs at most `M` operations per query**: if every membership test
`member x` spends at most `M` operations, then answering the queries of `p` with it
costs at most `p.opCost + M · p.queryCost`. -/
theorem opCost_answerWith_le (member : AmbientSpace n → Counted Bool) {M : ℕ}
    (hM : ∀ x, (member x).cost ≤ M) (p : ChargedProgram n α) :
    (p.answerWith member).opCost ≤ p.opCost + (M : ℕ∞) * p.queryCost := by
  induction p with
  | pure r => simp [answerWith, opCost]
  | query x next ih =>
      simp only [answerWith, opCost, queryCost]
      set b := (member x).value
      have h1 : (opsTotal (member x).tally : ℕ∞) ≤ M := Nat.cast_le.mpr (hM x)
      calc (opsTotal (member x).tally : ℕ∞) + (answerWith member (next b)).opCost
          ≤ M + ((next b).opCost + M * (next b).queryCost) := add_le_add h1 (ih b)
        _ ≤ M + ((⨆ b, (next b).opCost) + M * ⨆ b, (next b).queryCost) :=
            add_le_add le_rfl (add_le_add (le_iSup (fun b => (next b).opCost) b)
              (mul_le_mul_right (le_iSup (fun b => (next b).queryCost) b) _))
        _ = (⨆ b, (next b).opCost) + M * (1 + ⨆ b, (next b).queryCost) := by
            rw [mul_add, mul_one]; ring
  | randomNat law next ih =>
      simp only [answerWith, opCost, queryCost]
      exact iSup_le fun v => (ih v).trans (add_le_add (le_iSup (fun v => (next v).opCost) v)
        (mul_le_mul_right (le_iSup (fun v => (next v).queryCost) v) _))
  | randomPoint law h next ih =>
      simp only [answerWith, opCost, queryCost]
      exact iSup_le fun v => (ih v).trans (add_le_add (le_iSup (fun v => (next v).opCost) v)
        (mul_le_mul_right (le_iSup (fun v => (next v).queryCost) v) _))
  | randomReal law h next ih =>
      simp only [answerWith, opCost, queryCost]
      exact iSup_le fun v => (ih v).trans (add_le_add (le_iSup (fun v => (next v).opCost) v)
        (mul_le_mul_right (le_iSup (fun v => (next v).queryCost) v) _))
  | tick k next ih =>
      simp only [answerWith, opCost, queryCost]
      rw [add_assoc]
      exact add_le_add le_rfl ih

end ChargedProgram

open ChargedProgram

open Arlib.Computation (Num)

/-! ## The credit of each subroutine -/

/-- The operations each membership query pays for. -/
def opsPerQuery (n : ℕ) : ℕ := 12 * n + 31

/-- The operations each phase spends outside its walks and rejection attempts. -/
def opsPerPhase (n : ℕ) : ℕ := 2 * n + 83

variable (q : VolumeParams) (G : RunConstants)

private theorem dim_pos : 0 < q.n := lt_of_lt_of_le (by norm_num) q.dim_ok

theorem ballWalkStep_opCredit (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint q.n)
    {s : ℕ} (hs : 6 * q.n + 3 ≤ s) :
    OpCredit (opsPerQuery q.n) (ballWalkStep q G P sigma2 x) s fun _ s' => s + 8 ≤ s' := by
  have hn := dim_pos q
  simp only [ballWalkStep, bind_eq, opCredit_bind, opCredit_drawPoint, opCredit_drawReal,
    opCredit_compute, opCredit_isMember, opCredit_ite, opCredit_pure, ballProposalProg_cost hn,
    properTestProg_cost hn, lazyTestProg_cost hn, ite_self, opsPerQuery]
  repeat' (first | intro _ | apply And.intro)
  all_goals omega

/-- A round of the proper-step walk: with `6n + 5` credits it keeps its credit, and a
round that stops has been paid a query. -/
theorem properWalkRound_opCredit (P : PhaseConstants) (sigma2 : Num ℝ) (left : Num ℕ)
    (x : NumPoint q.n) {s : ℕ} (hs : 6 * q.n + 5 ≤ s) :
    OpCredit (opsPerQuery q.n) (properWalkRound q G P sigma2 left x) s fun r s' =>
      match r with
      | .inl _ => s ≤ s'
      | .inr _ => s + opsPerQuery q.n ≤ s' + q.n + 3 := by
  simp only [properWalkRound, bind_eq, opCredit_bind, opCredit_compute, Counted.bind_cost,
    Counted.lit_cost, Counted.le_cost]
  refine ⟨by omega, ?_⟩
  split
  · simp only [opCredit_bind, opCredit_compute, opCredit_isMember, opCredit_pure,
      Counted.smul_cost]
    repeat' (first | intro _ | apply And.intro)
    all_goals omega
  · rw [opCredit_bind]
    refine (ballWalkStep_opCredit q G P sigma2 x (by omega)).mono fun r s' h => ?_
    obtain ⟨proper, y⟩ := r
    cases proper
    · simp only [Bool.false_eq_true, ↓reduceIte, opCredit_pure]; omega
    · simp only [↓reduceIte, opCredit_bind, opCredit_compute, opCredit_pure, Counted.bind_cost,
        Counted.lit_cost, Counted.sub_cost]
      exact ⟨by omega, by omega⟩

theorem properWalk_opCredit (P : PhaseConstants) (sigma2 : Num ℝ) (cap : Num ℕ)
    (x : NumPoint q.n) {s : ℕ} (hs : 6 * q.n + 6 ≤ s) :
    OpCredit (opsPerQuery q.n) (properWalk q G P sigma2 cap x) s fun r s' =>
      match r with
      | none => s ≤ s' + 1
      | some _ => s + opsPerQuery q.n ≤ s' + q.n + 4 := by
  simp only [properWalk, bind_eq, opCredit_bind, opCredit_loopUntil]
  refine ⟨by omega, ?_⟩
  refine opCredit_loopRounds _ (fun _ s' => 6 * q.n + 5 ≤ s' ∧ s - 1 ≤ s')
    (fun r s' => match r with
      | .inl _ => s - 1 ≤ s'
      | .inr _ => s - 1 + opsPerQuery q.n ≤ s' + q.n + 3)
    (fun _ _ h => h.2) (fun b s1 h => ?_) _ _ _ ⟨by omega, le_rfl⟩ |>.mono fun r s' h => ?_
  · refine (properWalkRound_opCredit q G P sigma2 b.1 b.2 h.1).mono fun r s' h' => ?_
    rcases r with b' | c
    · exact ⟨by omega, by omega⟩
    · change s - 1 + opsPerQuery q.n ≤ s' + q.n + 3
      change s1 + opsPerQuery q.n ≤ s' + q.n + 3 at h'
      omega
  · rcases r with b' | c
    · change s - 1 ≤ s' at h
      simp only [opCredit_pure]; omega
    · change s - 1 + opsPerQuery q.n ≤ s' + q.n + 3 at h
      simp only [opCredit_pure]; omega

theorem rejectionAttempt_opCredit (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint q.n)
    {s : ℕ} (hs : q.n ≤ s) :
    OpCredit (opsPerQuery q.n) (rejectionAttempt q G P sigma2 x) s fun _ s' =>
      s + opsPerQuery q.n ≤ s' + (7 * q.n + 20) := by
  have hn := dim_pos q
  simp only [rejectionAttempt, bind_eq, opCredit_bind, opCredit_drawReal, opCredit_compute,
    opCredit_isMember, opCredit_ite, opCredit_pure, Counted.smul_cost, properTestProg_cost hn,
    scaleAcceptTestProg_cost hn, ite_self, opsPerQuery]
  repeat' (first | intro _ | apply And.intro)
  all_goals omega

theorem sampleAttempt_opCredit (P : PhaseConstants) (sigma2 : Num ℝ) (walkCap : Num ℕ)
    (x : NumPoint q.n) {s : ℕ} (hs : 6 * q.n + 6 ≤ s) :
    OpCredit (opsPerQuery q.n) (sampleAttempt q G P sigma2 walkCap x) s fun r s' =>
      match r with
      | .inr none => s ≤ s' + 1
      | _ => s + 2 * opsPerQuery q.n ≤ s' + (8 * q.n + 24) := by
  simp only [sampleAttempt, bind_eq, opCredit_bind]
  refine (properWalk_opCredit q G P sigma2 walkCap x hs).mono fun r s1 h1 => ?_
  rcases r with _ | y
  · exact h1
  · simp only [opCredit_bind]
    change s + opsPerQuery q.n ≤ s1 + q.n + 4 at h1
    refine (rejectionAttempt_opCredit q G P sigma2 y (by unfold opsPerQuery at h1; omega)).mono
      fun r s2 h2 => ?_
    obtain ⟨accepted, z⟩ := r
    cases accepted <;> simp only [Bool.false_eq_true, ↓reduceIte, opCredit_pure] <;> omega

theorem sampleRound_opCredit (P : PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint q.n → Counted (Num ℝ)) (hw : ∀ z, (weight z).cost ≤ 4 * q.n + 11)
    (walkCap : Num ℕ) (state : Num ℝ × NumPoint q.n) {s : ℕ} (hs : 6 * q.n + 7 ≤ s) :
    OpCredit (opsPerQuery q.n) (sampleRound q G P sigma2 weight walkCap state) s fun r s' =>
      match r with
      | .inl _ => s ≤ s'
      | .inr _ => s ≤ s' + 2 := by
  simp only [sampleRound, bind_eq, opCredit_bind, opCredit_loopUntil]
  refine ⟨by omega, ?_⟩
  refine opCredit_loopRounds _ (fun _ s' => 6 * q.n + 6 ≤ s' ∧ s - 1 ≤ s')
    (fun r s' => match r with
      | .inr none => s - 1 ≤ s' + 1
      | .inr (some _) => s - 1 + 2 * opsPerQuery q.n ≤ s' + (8 * q.n + 24)
      | .inl _ => s - 1 ≤ s')
    (fun _ _ h => h.2) (fun b s1 h => ?_) _ _ _ ⟨by omega, le_rfl⟩ |>.mono fun r s' h => ?_
  · refine (sampleAttempt_opCredit q G P sigma2 walkCap b h.1).mono fun r s' h' => ?_
    unfold opsPerQuery at h' ⊢
    rcases r with b' | _ | c
    · change s1 + 2 * (12 * q.n + 31) ≤ s' + (8 * q.n + 24) at h'
      exact ⟨by omega, by omega⟩
    · change s - 1 ≤ s' + 1
      change s1 ≤ s' + 1 at h'
      omega
    · change s - 1 + 2 * (12 * q.n + 31) ≤ s' + (8 * q.n + 24)
      change s1 + 2 * (12 * q.n + 31) ≤ s' + (8 * q.n + 24) at h'
      omega
  · rcases r with b' | _ | ⟨z, y⟩
    · change s - 1 ≤ s' at h
      simp only [sampleFinish, opCredit_pure]; omega
    · change s - 1 ≤ s' + 1 at h
      simp only [sampleFinish, opCredit_pure]; omega
    · change s - 1 + 2 * opsPerQuery q.n ≤ s' + (8 * q.n + 24) at h
      have hw' := hw z
      unfold opsPerQuery at h
      simp only [sampleFinish, bind_eq, opCredit_bind, opCredit_compute, opCredit_pure,
        Counted.add_cost]
      exact ⟨by omega, by omega, by omega⟩

theorem collectSamples_opCredit (P : PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint q.n → Counted (Num ℝ)) (hw : ∀ z, (weight z).cost ≤ 4 * q.n + 11)
    (samples : Num ℕ) (x : NumPoint q.n) {s : ℕ} (hs : 6 * q.n + 11 ≤ s) :
    OpCredit (opsPerQuery q.n) (collectSamples q G P sigma2 weight samples x) s fun _ s' =>
      s ≤ s' + 6 := by
  simp only [collectSamples, bind_eq, opCredit_bind, opCredit_compute, Counted.bind_cost,
    Counted.lit_cost, Counted.add_cost, Counted.pure_cost, Counted.bind_value,
    Counted.pure_value, opCredit_loopUntil]
  refine ⟨by omega, by omega, ?_⟩
  refine opCredit_loopRounds _ (fun _ s' => 6 * q.n + 7 ≤ s' ∧ s - 4 ≤ s')
    (fun r s' => match r with
      | .inl _ => s - 4 ≤ s'
      | .inr _ => s - 4 ≤ s' + 2)
    (fun _ _ h => h.2) (fun b s1 h => ?_) _ _ _ ⟨by omega, by omega⟩ |>.mono fun r s' h => ?_
  · refine (sampleRound_opCredit q G P sigma2 weight hw _ b h.1).mono fun r s' h' => ?_
    rcases r with b' | c
    · exact ⟨by change s1 ≤ s' at h'; omega, by change s1 ≤ s' at h'; omega⟩
    · change s - 4 ≤ s' + 2
      change s1 ≤ s' + 2 at h'
      omega
  · rcases r with b' | c
    · change s - 4 ≤ s' at h
      simp only [opCredit_pure]; omega
    · change s - 4 ≤ s' + 2 at h
      simp only [opCredit_pure]; omega

theorem coolingPhase_opCredit (sigma2 tau2 : Num ℝ) (x : NumPoint q.n) {s : ℕ}
    (hs : 7 * q.n + 83 ≤ s) :
    OpCredit (opsPerQuery q.n) (coolingPhase q G sigma2 tau2 x) s fun _ s' =>
      s ≤ s' + (2 * q.n + 80) := by
  have hn := dim_pos q
  simp only [coolingPhase, bind_eq, opCredit_bind, opCredit_compute, phaseConstantsProg_cost,
    Counted.smul_cost]
  refine ⟨by omega, by omega, ?_⟩
  refine (collectSamples_opCredit q G _ sigma2 _
    (fun z => (gaussianRatioWeightProg_cost hn sigma2 tau2 z).le) _ _
    (by omega)).mono fun r s1 h1 => ?_
  rcases r with _ | ⟨total, y⟩
  · simp only [opCredit_pure]; omega
  · simp only [opCredit_bind, opCredit_compute, opCredit_pure, Counted.bind_cost,
      Counted.cast_cost, Counted.div_cost, Counted.smul_cost]
    omega

theorem uniformPhase_opCredit (sigma2 : Num ℝ) (x : NumPoint q.n) {s : ℕ}
    (hs : 7 * q.n + 83 ≤ s) :
    OpCredit (opsPerQuery q.n) (uniformPhase q G sigma2 x) s fun _ s' =>
      s ≤ s' + (q.n + 80) := by
  have hn := dim_pos q
  simp only [uniformPhase, bind_eq, opCredit_bind, opCredit_compute, phaseConstantsProg_cost,
    Counted.smul_cost]
  refine ⟨by omega, by omega, ?_⟩
  refine (collectSamples_opCredit q G _ sigma2 _
    (fun z => (uniformRatioWeightProg_cost hn sigma2 z).le.trans (by omega)) _ _
    (by omega)).mono fun r s1 h1 => ?_
  rcases r with _ | ⟨total, y⟩
  · simp only [opCredit_pure]; omega
  · simp only [opCredit_bind, opCredit_compute, opCredit_pure, Counted.bind_cost,
      Counted.cast_cost, Counted.div_cost]
    omega

theorem initialSample_opCredit {s : ℕ} (hs : 2 * q.n ≤ s) :
    OpCredit (opsPerQuery q.n) (initialSample q G) s fun _ s' => s ≤ s' := by
  have hn := dim_pos q
  simp only [initialSample, bind_eq, opCredit_bind, opCredit_drawPoint, opCredit_compute,
    opCredit_isMember, opCredit_pure, gaussianStartProg_cost, Counted.bind_cost,
    Counted.norm_cost hn, Counted.le_cost, opsPerQuery]
  repeat' (first | intro _ | apply And.intro)
  all_goals omega

theorem coolingPhases_opCredit :
    ∀ (variances : List (Num ℝ)) (x : NumPoint q.n) {s : ℕ},
      variances.length * opsPerPhase q.n + (7 * q.n + 84) ≤ s →
      OpCredit (opsPerQuery q.n) (coolingPhases q G variances x) s fun _ s' =>
        s ≤ s' + variances.length * opsPerPhase q.n + 1
  | [], x, s, hs => by
      simp only [coolingPhases, bind_eq, opCredit_bind, opCredit_compute, opCredit_pure,
        Counted.lit_cost, List.length_nil, zero_mul, zero_add] at hs ⊢
      exact ⟨by omega, by omega⟩
  | [_], x, s, hs => by
      simp only [coolingPhases, bind_eq, opCredit_bind, opCredit_compute, opCredit_pure,
        Counted.lit_cost, List.length_singleton, one_mul] at hs ⊢
      exact ⟨by omega, by omega⟩
  | sigma2 :: tau2 :: rest, x, s, hs => by
      have hD : 2 * q.n + 83 = opsPerPhase q.n := rfl
      simp only [coolingPhases, bind_eq, opCredit_bind, opCredit_compute, Counted.cell_cost,
        Counted.cell_value]
      simp only [List.length_cons, Nat.succ_mul] at hs ⊢
      refine ⟨by omega, by omega, ?_⟩
      refine OpCredit.mono (h := coolingPhase_opCredit q G sigma2 tau2 x (by omega))
        fun r s1 h1 => ?_
      rcases r with _ | ⟨W, y⟩
      · simp only [opCredit_pure]; omega
      · simp only [opCredit_bind]
        have hpre : (rest.length + 1) * opsPerPhase q.n + (7 * q.n + 84) ≤ s1 := by
          rw [Nat.succ_mul]; omega
        have ih := coolingPhases_opCredit (tau2 :: rest) y hpre
        simp only [List.length_cons, Nat.succ_mul] at ih
        refine OpCredit.mono (h := ih) fun r s2 h2 => ?_
        rcases r with _ | ⟨product, z⟩
        · simp only [opCredit_pure]; omega
        · simp only [opCredit_bind, opCredit_compute, opCredit_pure, Counted.mul_cost]
          omega

/-- The starting credit of one run: `opsPerPhase n` for each entry of the schedule, and
`7n + 84` for the last phase and the final products. -/
def runReserve (n phases : ℕ) : ℕ := phases * opsPerPhase n + (7 * n + 84)

theorem figureOneRun_opCredit :
    OpCredit (opsPerQuery q.n) (figureOneRun q G) (runReserve q.n G.schedule.length)
      fun _ _ => True := by
  simp only [figureOneRun, bind_eq, opCredit_bind]
  refine (initialSample_opCredit q G (by unfold runReserve; omega)).mono fun r s1 h1 => ?_
  rcases r with _ | x₀
  · simp only [opCredit_compute, Counted.lit_cost]
    unfold runReserve at h1
    exact ⟨by omega, trivial⟩
  · simp only [opCredit_bind]
    refine (coolingPhases_opCredit q G G.schedule x₀ (by unfold runReserve at h1; omega)).mono
      fun r s2 h2 => ?_
    rcases r with _ | ⟨product, x⟩
    · simp only [opCredit_compute, Counted.lit_cost]
      unfold runReserve at h1
      exact ⟨by omega, trivial⟩
    · simp only [opCredit_bind]
      refine (uniformPhase_opCredit q G G.terminal x (by unfold runReserve at h1; omega)).mono
        fun r s3 h3 => ?_
      unfold runReserve at h1
      rcases r with _ | U
      · simp only [opCredit_compute, Counted.lit_cost]
        exact ⟨by omega, trivial⟩
      · simp only [opCredit_compute, Counted.bind_cost, Counted.mul_cost]
        exact ⟨by omega, trivial⟩

/-! ## The bound -/

/-- **One capped run** spends at most `runReserve + (12n + 31)·B + 2` operations. -/
theorem cappedRun_opCost_le :
    (cappedRun q G).opCost ≤
      ((runReserve q.n G.schedule.length + opsPerQuery q.n * G.queryBudget.get + 2 : ℕ) : ℕ∞) := by
  unfold cappedRun ChargedProgram.withHeldQueryCap
  simp only [bind_eq]
  have hcap := opCost_withQueryCap_le (figureOneRun_opCredit q G) G.queryBudget.get
  have htail : ∀ r : Option (Num ℝ), ((match r with
      | some estimate => Pure.pure estimate
      | none => compute (Counted.lit 0)) : ChargedProgram q.n (Num ℝ)).opCost ≤ 1 := by
    intro r
    rcases r with _ | e
    · simp [opCost_compute]
    · simp [opCost]
  refine (opCost_bind_le _ htail).trans ?_
  simp only [opCost, opsTotal_one]
  refine (add_le_add (add_le_add le_rfl hcap) le_rfl).trans (le_of_eq ?_)
  push_cast
  ring

theorem results_mono {n : ℕ} {α : Type} {P P' : α → Prop} (hP : ∀ r, P r → P' r) :
    ∀ {p : ChargedProgram n α}, Results P p → Results P' p
  | .pure r, h => hP r h
  | .query _ _, h => fun b => results_mono hP (h b)
  | .randomNat _ _, h => fun v => results_mono hP (h v)
  | .randomPoint _ _ _, h => fun v => results_mono hP (h v)
  | .randomReal _ _ _, h => fun v => results_mono hP (h v)
  | .tick _ next, h => results_mono hP (p := next) h

theorem repeatRounds_opCost_le {n : ℕ} (run : ChargedProgram n (Num ℝ)) {M : ℕ∞}
    (h : run.opCost ≤ M) : ∀ (k : ℕ) (done : List (Num ℝ)),
      (loopRounds (γ := Empty) (fun estimates => run.bind fun x =>
        (compute (Counted.push estimates x)).bind fun e => .pure (.inl e)) k done).opCost ≤
        k * (M + 1)
  | 0, _ => by simp [loopRounds, opCost]
  | k + 1, done => by
      simp only [loopRounds, bind_assoc', pure_bind', compute, tick_bind']
      refine (opCost_bind_le _ (M := 1 + k * (M + 1)) fun x => ?_).trans ?_
      · simp only [opCost]
        rw [show opsTotal (Counted.push done x).tally = 1 from Counted.push_cost _ _]
        push_cast
        exact add_le_add le_rfl (repeatRounds_opCost_le run h k _)
      · calc run.opCost + (1 + k * (M + 1)) ≤ M + (1 + k * (M + 1)) := add_le_add h le_rfl
          _ = ((k + 1 : ℕ) : ℕ∞) * (M + 1) := by push_cast; ring

theorem repeatRounds_results {n : ℕ} (run : ChargedProgram n (Num ℝ)) :
    ∀ (k : ℕ) (done : List (Num ℝ)),
      Results (fun r : List (Num ℝ) ⊕ Empty => ∃ l, r = .inl l ∧ l.length = done.length + k)
        (loopRounds (fun estimates => run.bind fun x =>
          (compute (Counted.push estimates x)).bind fun e => .pure (.inl e)) k done)
  | 0, done => ⟨done, rfl, by simp⟩
  | k + 1, done => by
      simp only [loopRounds, bind_assoc', pure_bind', compute, tick_bind']
      rw [results_bind]
      refine results_of_forall (fun x => ?_) run
      exact results_mono (fun r ⟨l, hr, hl⟩ => ⟨l, hr, by simp at hl; omega⟩)
        (repeatRounds_results run k ((Counted.push done x).value))

theorem confidenceRepetitions_pos : 0 < confidenceRepetitions q := by
  unfold confidenceRepetitions
  exact Nat.ceil_pos.mpr (mul_pos (by norm_num) (lt_max_of_lt_left one_pos))

theorem coolingSchedule_length : (coolingSchedule q).length = numPhases q := by
  simp [coolingSchedule, numPhases]

/-- **The arithmetic cost of the CV18 volume algorithm.**  With `T = terminalPhaseSteps q`,
`m = confidenceRepetitions q` and `B = queryBudget q`, every execution of `cv18Program q`
performs at most
`11T + 176 + m · (numPhases·(2n + 83) + 7n + 88 + (12n + 31)·B) + 4m²`
arithmetic operations: the constants of the call, `m` capped runs, and the median. -/
theorem cv18Program_opCost_le :
    (cv18Program q).opCost ≤
      ((11 * terminalPhaseSteps q + 176 +
        confidenceRepetitions q * (numPhases q * opsPerPhase q.n + (7 * q.n + 88) +
          opsPerQuery q.n * queryBudget q) +
        4 * confidenceRepetitions q ^ 2 : ℕ) : ℕ∞) := by
  have hm := confidenceRepetitions_pos q
  have hG := runConstantsProg_value q
  simp only [cv18Program, bind_eq, opCost_compute_bind]
  set G := (runConstantsProg q).value
  have hlen : G.schedule.length = numPhases q := by
    rw [← List.length_map (f := Arlib.Computation.Num.get), hG.schedule, coolingSchedule_length]
  have hres : Results (fun l : List (Num ℝ) => l.length = confidenceRepetitions q)
      (repeatIndependently G.repetitions (cappedRun q G)) := by
    unfold repeatIndependently loopUntil
    simp only [bind_eq, pure_eq]
    rw [results_bind]
    exact results_mono (fun r ⟨l, hr, hl⟩ => by
        subst hr
        show l.length = _
        simpa [hG.repetitions] using hl)
      (repeatRounds_results (cappedRun q G) G.repetitions.get [])
  have hmed : ∀ l : List (Num ℝ), l.length = confidenceRepetitions q →
      ((compute (Counted.median G.repetitions l)).bind fun m =>
        (report m : ChargedProgram q.n ℝ)).opCost ≤
        ((4 * confidenceRepetitions q ^ 2 + confidenceRepetitions q + 5 : ℕ) : ℕ∞) := by
    intro l hl
    rw [opCost_compute_bind]
    simp only [report, opCost, add_zero, Nat.cast_le]
    have := Counted.median_cost_le G.repetitions l (by omega)
    rwa [hl] at this
  have hrep : (repeatIndependently G.repetitions (cappedRun q G)).opCost ≤
      ((1 + confidenceRepetitions q * (runReserve q.n (numPhases q) +
        opsPerQuery q.n * queryBudget q + 3) : ℕ) : ℕ∞) := by
    unfold repeatIndependently loopUntil
    simp only [bind_eq, pure_eq]
    refine (opCost_bind_le _ (M := 0) fun _ => le_rfl).trans ?_
    simp only [opCost, opsTotal_one, add_zero]
    have h := repeatRounds_opCost_le (cappedRun q G) (cappedRun_opCost_le q G) G.repetitions.get []
    rw [hG.repetitions, hlen, hG.queryBudget] at h
    refine (add_le_add le_rfl h).trans (le_of_eq ?_)
    push_cast
    ring
  refine (add_le_add (Nat.cast_le.mpr (runConstantsProg_cost_le q))
    ((opCost_bind_le_of_results _ hres hmed).trans (add_le_add hrep le_rfl))).trans
    (le_of_eq ?_)
  simp only [runReserve]
  push_cast
  ring

end ttc.ChargedCV18

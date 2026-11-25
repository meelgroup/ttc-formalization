/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.ChargedCV18.Erasure
import ttc.Analysis.ChargedCV18.ConstantsArithmetic
import ttc.Analysis.ChargedCV18.DrawRefinement
import ttc.Analysis.ChargedCV18.PointDrawLaws

/-!
# The pseudocode is the analysed program

`cv18Program` (arlib-community `CV18/Analysis/OracleProgram.lean`) holds its numbers sealed and is written in `do`
notation.  The proof of Theorem 1.1 was developed against the same algorithm written with
the program constructors, on plain numbers (`Analysis/ScheduledProgram.lean`).  This file
proves that the first, with its operation counts erased, refines the second
(`cv18Program_refines`), subroutine by subroutine, and that the syntax-level query
certificate `QueryBound` bounds the cost model `queryCost`.

A subroutine of `cv18Program` returns held numbers where the analysed one returns numbers,
so the subroutines are related through a view `v` of their results (`Simulates`): any two
continuations that agree on what a held result stands for give refining programs.
-/

open Arlib.Computation (Num)

namespace ttc.ChargedCV18

open ArlibCommunity.Algorithms.CV18

variable (q : VolumeParams)

section Bridge
variable {n : ℕ} {α β γ : Type}

@[simp] theorem bind_eq (p : ChargedProgram n α)
    (f : α → ChargedProgram n β) : p >>= f = p.bind f := rfl

@[simp] theorem pure_eq (a : α) : (pure a : ChargedProgram n α) = .pure a := rfl

@[simp] theorem pure_bind' (a : α) (f : α → ChargedProgram n β) :
    (ChargedProgram.pure a).bind f = f a := rfl

theorem bind_assoc' (p : ChargedProgram n α)
    (f : α → ChargedProgram n β) (g : β → ChargedProgram n γ) :
    (p.bind f).bind g = p.bind fun x => (f x).bind g := by
  induction p with
  | pure a => rfl
  | query x next ih => simp only [ChargedProgram.bind, ih]
  | randomNat law next ih => simp only [ChargedProgram.bind, ih]
  | randomPoint law h next ih => simp only [ChargedProgram.bind, ih]
  | randomReal law h next ih => simp only [ChargedProgram.bind, ih]
  | tick ops next ih => simp only [ChargedProgram.bind, ih]

theorem bind_pure_right (p : ChargedProgram n α) : p.bind .pure = p := by
  induction p with
  | pure a => rfl
  | query x next ih => simp only [ChargedProgram.bind, ih]
  | randomNat law next ih => simp only [ChargedProgram.bind, ih]
  | randomPoint law h next ih => simp only [ChargedProgram.bind, ih]
  | randomReal law h next ih => simp only [ChargedProgram.bind, ih]
  | tick ops next ih => simp only [ChargedProgram.bind, ih]

end Bridge

/-! arlib-community's versions of the same facts, for the analysed side. -/

section Analysed
variable {n : ℕ} {α β γ : Type}

theorem mbind_eq (p : MembershipOracleProgram n α)
    (f : α → MembershipOracleProgram n β) : p >>= f = p.bind f := rfl

theorem mpure_eq (a : α) : (pure a : MembershipOracleProgram n α) = .pure a := rfl

theorem mpure_bind' (a : α) (f : α → MembershipOracleProgram n β) :
    (MembershipOracleProgram.pure a).bind f = f a := rfl

theorem mbind_assoc' (p : MembershipOracleProgram n α)
    (f : α → MembershipOracleProgram n β) (g : β → MembershipOracleProgram n γ) :
    (p.bind f).bind g = p.bind fun x => (f x).bind g :=
  ArlibCommunity.Algorithms.CV18.bind_assoc' p f g

theorem mbind_pure_right (p : MembershipOracleProgram n α) : p.bind .pure = p := by
  induction p with
  | pure a => rfl
  | query x next ih => simp only [MembershipOracleProgram.bind, ih]
  | randomNat law next ih => simp only [MembershipOracleProgram.bind, ih]
  | randomPoint law h next ih => simp only [MembershipOracleProgram.bind, ih]
  | randomReal law h next ih => simp only [MembershipOracleProgram.bind, ih]

theorem withQueryCap_bind_pure {α β : Type} (f : α → β) :
    ∀ (b : ℕ) (p : MembershipOracleProgram n α),
      (p.bind fun a => .pure (f a)).withQueryCap b =
        (p.withQueryCap b).bind fun r => .pure (r.map f)
  | b, .pure a => rfl
  | 0, .query _ _ => rfl
  | b + 1, .query x next => by
      simp only [MembershipOracleProgram.bind, MembershipOracleProgram.withQueryCap]
      congr 1; funext a; exact withQueryCap_bind_pure f b (next a)
  | b, .randomNat law next => by
      simp only [MembershipOracleProgram.bind, MembershipOracleProgram.withQueryCap]
      congr 1; funext a; exact withQueryCap_bind_pure f b (next a)
  | b, .randomPoint law h next => by
      simp only [MembershipOracleProgram.bind, MembershipOracleProgram.withQueryCap]
      congr 1; funext a; exact withQueryCap_bind_pure f b (next a)
  | b, .randomReal law h next => by
      simp only [MembershipOracleProgram.bind, MembershipOracleProgram.withQueryCap]
      congr 1; funext a; exact withQueryCap_bind_pure f b (next a)

end Analysed

@[simp] theorem tick_bind' {n : ℕ} {α β : Type} (k : Arlib.Computation.CostVec Op)
    (p : ChargedProgram n α) (f : α → ChargedProgram n β) :
    (ChargedProgram.tick k p).bind f = .tick k (p.bind f) := rfl

open ChargedProgram GaussianSampling

/-! ## Sealing, for the specification

Every held number is determined by the number it stands for (`Num.ext`), so a held point
is the sealing of its view.  Sealing is specification vocabulary: no program uses it. -/

/-- The held point standing for `p`. -/
noncomputable def NumPoint.seal {n : ℕ} (p : AmbientSpace n) : NumPoint n :=
  fun i => (Counted.lit (p i)).value

@[simp] theorem NumPoint.view_seal {n : ℕ} (p : AmbientSpace n) : (NumPoint.seal p).view = p :=
  rfl

theorem NumPoint.seal_view {n : ℕ} (x : NumPoint n) : NumPoint.seal x.view = x := by
  funext i
  exact Num.ext rfl

theorem NumPoint.eq_seal {n : ℕ} {x : NumPoint n} {p : AmbientSpace n} (h : x.view = p) :
    x = NumPoint.seal p := by
  rw [← h, NumPoint.seal_view]

@[simp] theorem drawPoint_view {n : ℕ} (g : AmbientSpace n) :
    NumPoint.view (Counted.forEach fun i => Counted.pick (g i)).value = g := by
  ext i
  simp [NumPoint.view_apply]

/-! ## Simulation through a view -/

namespace ChargedProgram

variable {n : ℕ} {α β δ ε : Type}

/-- **`S` simulates `A` through the view `v`**: with its operation counts erased, `S`
followed by any continuation refines `A` followed by any continuation that agrees on what
`S`'s result stands for. -/
def Simulates (v : β → α) (A : MembershipOracleProgram n α) (S : ChargedProgram n β) :
    Prop :=
  ∀ (γ : Type) (F : α → MembershipOracleProgram n γ) (F' : β → MembershipOracleProgram n γ),
    (∀ s, Refines (F (v s)) (F' s)) → Refines (A.bind F) (S.erase.bind F')

theorem Simulates.pure' {v : β → α} {a : α} {s : β} (h : v s = a) :
    Simulates v (.pure a : MembershipOracleProgram n α) (.pure s) := by
  intro γ F F' hF
  subst h
  exact hF s

theorem Simulates.bind {v : β → α} {w : ε → δ} {A : MembershipOracleProgram n α}
    {S : ChargedProgram n β} {B : α → MembershipOracleProgram n δ}
    {T : β → ChargedProgram n ε} (hA : Simulates v A S)
    (hB : ∀ s, Simulates w (B (v s)) (T s)) : Simulates w (A.bind B) (S.bind T) := by
  intro γ F F' hF
  rw [mbind_assoc', erase_bind, mbind_assoc']
  exact hA _ _ _ fun s => hB s γ F F' hF

theorem Simulates.tick {v : β → α} {A : MembershipOracleProgram n α}
    {S : ChargedProgram n β} (k : Arlib.Computation.CostVec Op) (h : Simulates v A S) :
    Simulates v A (.tick k S) := h

@[simp] theorem simulates_tick_iff {v : β → α} {A : MembershipOracleProgram n α}
    {S : ChargedProgram n β} (k : Arlib.Computation.CostVec Op) :
    Simulates v A (.tick k S) ↔ Simulates v A S := Iff.rfl

theorem Simulates.compute {v : β → α} {a : α} {c : Counted β} (h : v c.value = a) :
    Simulates v (.pure a : MembershipOracleProgram n α) (ChargedCV18.compute c) := by
  intro γ F F' hF
  subst h
  exact hF c.value

/-- A simulation through the identity is a refinement. -/
theorem Simulates.refines {A : MembershipOracleProgram n α} {S : ChargedProgram n α} (h : Simulates id A S) :
    Refines A S.erase := by
  have := h _ .pure .pure fun s => Refines.refl _
  rwa [mbind_pure_right, mbind_pure_right] at this

theorem erase_loopUntil {β γ : Type} (count : Num ℕ)
    (body : β → ChargedProgram n (β ⊕ γ)) (init : β) :
    (loopUntil count body init).erase = (loopRounds body count.get init).erase := rfl

/-- A simulation through `v` is a refinement once `S`'s results are read through `v`. -/
theorem Simulates.refines_map {v : β → α} {A : MembershipOracleProgram n α}
    {S : ChargedProgram n β} (h : Simulates v A S) :
    Refines A (S.erase.bind fun s => .pure (v s)) := by
  have := h _ .pure (fun s => .pure (v s)) fun s => Refines.refl _
  rwa [mbind_pure_right] at this

/-- **And back**, when the view is a bijection, with inverse `σ`. -/
theorem Simulates.of_refines_map {v : β → α} (σ : α → β) (hσ : ∀ s, σ (v s) = s)
    (hv : ∀ a, v (σ a) = a) {A : MembershipOracleProgram n α} {S : ChargedProgram n β}
    (h : Refines A (S.erase.bind fun s => .pure (v s))) : Simulates v A S := by
  intro γ F F' hF
  have hS : S.erase.bind F' = (S.erase.bind fun s => .pure (v s)).bind fun a => F' (σ a) := by
    rw [mbind_assoc']
    simp only [mpure_bind', hσ]
  rw [hS]
  refine Refines.bind h fun a => ?_
  have := hF (σ a)
  rwa [hv] at this

end ChargedProgram

/-! ## The subroutines -/

variable {q} {G : RunConstants} {P : PhaseConstants}

/-- The ball-walk proposal map `(g, u) ↦ x + r · (u^{1/n} / ‖g‖) · g`. -/
theorem measurable_proposalMap (x : AmbientSpace q.n) (r : ℝ) :
    Measurable fun ω : AmbientSpace q.n × ℝ => x + r • ballStartMap q.n ω := by
  unfold ballStartMap
  fun_prop

theorem ballWalkStep_simulates (hG : G.Holds q) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (hP : P.view = phaseConstants q sigma2) {s : Num ℝ} (hs : s.get = sigma2) (x : NumPoint q.n) :
    Simulates (fun r : Bool × NumPoint q.n => (r.1, r.2.view))
      (scheduledAccuracyMetropolisMarkedBallStep q sigma2 x.view) (ballWalkStep q G P s x) := by
  have : NeZero q.n := ⟨by have := q.dim_ok; omega⟩
  have hrad : P.radius.get = phaseRadius q sigma2 := congrArg PhaseValues.radius hP
  have hprop : P.proposal.get = proposalRadius q sigma2 := congrArg PhaseValues.proposal hP
  intro γ F F' hF
  let K' : AmbientSpace q.n → MembershipOracleProgram q.n γ := fun y =>
    .query y fun inside => .randomReal uniformUnit inferInstance fun coin =>
      if inside = true ∧ ‖y‖ ≤ Real.sqrt (terminalVariance q) ∧ ‖y‖ ≤ phaseRadius q sigma2 then
        F' (true, if coin ≤ lazyAcceptance sigma2 x.view y then NumPoint.seal y else x)
      else F' (false, x)
  have hnew : (ballWalkStep q G P s x).erase.bind F' =
      .randomPoint (standardGaussian q.n) inferInstance fun g =>
        .randomReal uniformUnit inferInstance fun u =>
          K' (x.view + proposalRadius q sigma2 • ballStartMap q.n (g, u)) := by
    simp only [ballWalkStep, drawPoint, drawReal, isMember, compute, bind_eq, pure_eq,
      ChargedProgram.bind, erase, MembershipOracleProgram.bind]
    congr 1; funext g; congr 1; funext u
    have hy := NumPoint.eq_seal (ballProposalProg_value G.dimensionCount x P.proposal
      (Counted.forEach fun i => Counted.pick (g i)).value (Counted.pick u).value)
    rw [hy]
    simp only [K', NumPoint.view_seal, drawPoint_view, Counted.pick_value, Counted.isMember_value, hprop,
      hG.dimensionCount, properTestProg_value, lazyTestProg_value, hG.rootTerminal, hrad, hs,
      decide_eq_true_eq, ballStartMap]
    congr 1; funext inside; congr 1; funext coin
    split_ifs <;> rfl
  rw [hnew]
  exact Refines.split (uniformBall q.n x.view (proposalRadius q sigma2)) inferInstance
    (standardGaussian q.n) inferInstance uniformUnit inferInstance
    (fun ω => x.view + proposalRadius q sigma2 • ballStartMap q.n ω)
    (measurable_proposalMap x.view _) (uniformBall_eq_map x.view (proposalRadius_pos q hsigma2))
    (k := fun y => (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 x.view y).bind F)
    fun y => by
      simp only [scheduledAccuracyMetropolisMarkedProposalProgram, MembershipOracleProgram.bind,
        K']
      refine Refines.query _ fun inside => Refines.randomReal _ _ fun coin => ?_
      split_ifs with h1 h2
      · simpa using hF (true, NumPoint.seal y)
      · simpa using hF (true, x)
      · simpa using hF (false, x)

theorem rejectionAttempt_simulates (hG : G.Holds q) {sigma2 : ℝ}
    (hP : P.view = phaseConstants q sigma2) {s : Num ℝ} (hs : s.get = sigma2) (x : NumPoint q.n) :
    Simulates (fun r : Bool × NumPoint q.n => (r.1, r.2.view))
      (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 x.view)
      (rejectionAttempt q G P s x) := by
  have hrad : P.radius.get = phaseRadius q sigma2 := congrArg PhaseValues.radius hP
  intro γ F F' hF
  have hy := Counted.smul_value G.scaleInv x
  rw [hG.scaleInv] at hy
  simp only [rejectionAttempt, scheduledBalancedAccuracyGaussianRejectionAttempt, drawReal,
    isMember, compute, bind_eq, pure_eq, ChargedProgram.bind, erase, hy, MembershipOracleProgram.bind]
  refine Refines.query _ fun inside => Refines.randomReal _ _ fun coin => ?_
  simp only [properTestProg_value, scaleAcceptTestProg_value, Counted.pick_value, Counted.isMember_value, hy,
    hG.rootTerminal, hrad, hs, hG.scale, decide_eq_true_eq]
  split_ifs with h1 h2 h2
  · simpa [hy] using hF (true, (Counted.smul G.scaleInv x).value)
  · exfalso; tauto
  · exfalso; tauto
  · simpa [hy] using hF (false, (Counted.smul G.scaleInv x).value)

/-- What a round of the proper-step walk stands for: `none` while it runs out of proposals,
`some (0, y)` once it stops at `y`. -/
noncomputable def properWalkView {n : ℕ} :
    (Num ℕ × NumPoint n) ⊕ NumPoint n → Option (ℝ × AmbientSpace n)
  | .inl _ => none
  | .inr y => some (0, y.view)

theorem properWalkRounds_simulates (hG : G.Holds q) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (hP : P.view = phaseConstants q sigma2) {s : Num ℝ} (hs : s.get = sigma2) (stride : ℕ) :
    ∀ (cap : ℕ) (left : Num ℕ) (x : NumPoint q.n),
      Simulates properWalkView
        (cappedScheduledAccuracyProperBlockAux q sigma2 stride cap left.get x.view)
        (loopRounds (fun st => properWalkRound q G P s st.1 st.2) cap (left, x)) := by
  intro cap
  induction cap with
  | zero =>
    intro left x
    simp only [cappedScheduledAccuracyProperBlockAux, loopRounds]
    exact Simulates.pure' (v := properWalkView) rfl
  | succ cap ih =>
    intro left x
    rcases hl : left.get with _ | k
    · -- no proper steps left: the endpoint call, and stop
      intro γ F F' hF
      have hy := Counted.smul_value G.scaleInv x
      rw [hG.scaleInv] at hy
      simp only [cappedScheduledAccuracyProperBlockAux, scheduledAccuracyZeroObservation,
        loopRounds, properWalkRound, compute, isMember, bind_eq, pure_eq,
        ChargedProgram.bind, erase, Counted.bind_value, Counted.le_value,
        Counted.lit_value, Counted.isMember_value, hl, le_refl, decide_true, ↓reduceIte, hy, MembershipOracleProgram.bind]
      exact Refines.query _ fun _ => hF (.inr x)
    · -- take a ball-walk step, and count it if it was proper
      rw [cappedScheduledAccuracyProperBlockAux, loopRounds, properWalkRound]
      simp only [bind_eq, compute, tick_bind', pure_bind', Counted.bind_value, Counted.le_value,
        Counted.lit_value, hl, nonpos_iff_eq_zero, Nat.add_one_ne_zero, decide_false,
        Bool.false_eq_true, ↓reduceIte, bind_assoc']
      refine Simulates.tick _ (Simulates.bind (ballWalkStep_simulates hG hsigma2 hP hs x)
        fun r => ?_)
      obtain ⟨proper, y⟩ := r
      cases proper
      · simpa [hl] using ih left y
      · have hleft : (Counted.sub left (Counted.lit (1 : ℕ)).value).value.get = k := by
          simp [hl]
        have := ih (Counted.sub left (Counted.lit (1 : ℕ)).value).value y
        rw [hleft] at this
        cases k <;>
        · simp only [tick_bind', ↓reduceIte,
]
          exact Simulates.tick _ this

theorem properWalk_simulates (hG : G.Holds q) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (hP : P.view = phaseConstants q sigma2) {s : Num ℝ} (hs : s.get = sigma2) (cap : Num ℕ)
    (x : NumPoint q.n) :
    Simulates (fun r : Option (NumPoint q.n) => r.map fun y => ((0 : ℝ), y.view))
      (cappedScheduledAccuracyProperBlock q sigma2 cap.get (walkSteps q sigma2) x.view)
      (properWalk q G P s cap x) := by
  have hsteps : P.steps.get = walkSteps q sigma2 := congrArg PhaseValues.steps hP
  unfold properWalk cappedScheduledAccuracyProperBlock
  rw [← mbind_pure_right (cappedScheduledAccuracyProperBlockAux _ _ _ _ _ _)]
  simp only [bind_eq, pure_eq]
  refine Simulates.bind (v := properWalkView) ?_ fun r => ?_
  · have := properWalkRounds_simulates hG hsigma2 hP hs (walkSteps q sigma2) cap.get P.steps x
    rw [hsteps] at this
    exact Simulates.tick _ this
  · rcases r with _ | y <;> exact Simulates.pure' rfl

/-- What a round of sample collection stands for: `some (total, y)` while it runs,
`none` once the phase is abandoned. -/
noncomputable def collectView {n : ℕ} :
    (Num ℝ × NumPoint n) ⊕ Unit → Option (ℝ × AmbientSpace n)
  | .inl (t, y) => some (t.get, y.view)
  | .inr _ => none

/-- Reading a list cell, then continuing: one `cell`, then the continuation on the cell. -/
theorem compute_cell_bind {α β : Type} (a : α) (k : α → ChargedProgram q.n β) :
    (compute (Counted.cell a)).bind k = .tick (Counted.cell a).tally (k a) := rfl

/-- The rounds of sample collection simulate the analysed collector, which counts the
attempts left for the current sample and the samples left. -/
theorem collectRounds_simulates (hG : G.Holds q) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (hP : P.view = phaseConstants q sigma2) {s : Num ℝ} (hs : s.get = sigma2)
    {w : AmbientSpace q.n → ℝ} {weight : NumPoint q.n → Counted (Num ℝ)}
    (hw : ∀ z, (weight z).value.get = w z.view) {walkCap : Num ℕ}
    (hcap : walkCap.get = maxProposals q sigma2 + 1) :
    ∀ (m : ℕ) (total : Num ℝ) (x : NumPoint q.n),
      Simulates collectView
        (scheduledBalancedAccuracyRetryCollectAux q sigma2 w (maxProposals q sigma2)
          (walkSteps q sigma2) (maxRetries q) (maxRetries q) m total.get x.view)
        (loopRounds (sampleRound q G P s weight walkCap) m (total, x)) := by
  intro m
  induction m with
  | zero =>
    intro total x
    simp only [scheduledBalancedAccuracyRetryCollectAux, loopRounds]
    exact Simulates.pure' (v := collectView) rfl
  | succ m ihm =>
    -- the attempts at one sample, followed by any continuation that goes on like the
    -- analysed collector with `m` samples left
    have inner : ∀ (k : ℕ) (total : Num ℝ) (x : NumPoint q.n)
        {C : (Num ℝ × NumPoint q.n) ⊕ Unit →
          ChargedProgram q.n ((Num ℝ × NumPoint q.n) ⊕ Unit)},
        (∀ (t : Num ℝ) (y : NumPoint q.n), Simulates collectView
          (scheduledBalancedAccuracyRetryCollectAux q sigma2 w (maxProposals q sigma2)
            (walkSteps q sigma2) (maxRetries q) (maxRetries q) m t.get y.view) (C (.inl (t, y)))) →
        Simulates collectView (.pure none) (C (.inr ())) →
        Simulates collectView
          (scheduledBalancedAccuracyRetryCollectAux q sigma2 w (maxProposals q sigma2)
            (walkSteps q sigma2) (maxRetries q) k (m + 1) total.get x.view)
          ((loopRounds (sampleAttempt q G P s walkCap) k x).bind fun a =>
            (sampleFinish q weight total a).bind C) := by
      intro k
      induction k with
      | zero =>
        intro total x C _ hnone
        simpa [scheduledBalancedAccuracyRetryCollectAux, loopRounds, sampleFinish] using hnone
      | succ k ihk =>
        intro total x C hsome hnone
        rw [scheduledBalancedAccuracyRetryCollectAux, cappedScheduledAccuracyProperBlock,
          loopRounds, sampleAttempt]
        simp only [bind_eq, pure_eq, bind_assoc']
        have hwalk := properWalk_simulates hG hsigma2 hP hs walkCap x
        rw [hcap] at hwalk
        refine Simulates.bind hwalk fun r => ?_
        rcases r with _ | y
        · simpa [sampleFinish] using hnone
        · simp only [Option.map_some, bind_assoc']
          refine Simulates.bind (rejectionAttempt_simulates hG hP hs y) fun a => ?_
          obtain ⟨accepted, z⟩ := a
          cases accepted
          · simpa using ihk total y hsome hnone
          · have ht : (Counted.add total (weight z).value).value.get = total.get + w z.view := by
              simp [hw]
            have := hsome (Counted.add total (weight z).value).value y
            rw [ht] at this
            simpa [sampleFinish, compute] using this
    intro total x
    rw [loopRounds, sampleRound]
    simp only [bind_eq, bind_assoc', loopUntil, tick_bind']
    have hR : G.maxRetries.get = maxRetries q := hG.maxRetries
    refine Simulates.tick _ ?_
    rw [hR]
    refine inner (maxRetries q) total x (fun t y => ?_) ?_
    · simpa using ihm t y
    · exact Simulates.pure' rfl

theorem collectSamples_simulates (hG : G.Holds q) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (hP : P.view = phaseConstants q sigma2) {s : Num ℝ} (hs : s.get = sigma2)
    {w : AmbientSpace q.n → ℝ} {weight : NumPoint q.n → Counted (Num ℝ)}
    (hw : ∀ z, (weight z).value.get = w z.view) (samples : Num ℕ) (x : NumPoint q.n) :
    Simulates (fun r : Option (Num ℝ × NumPoint q.n) => r.map fun p => (p.1.get, p.2.view))
      (scheduledBalancedAccuracyRetryCollectAux q sigma2 w (maxProposals q sigma2)
        (walkSteps q sigma2) (maxRetries q) (maxRetries q) samples.get 0 x.view)
      (collectSamples q G P s weight samples x) := by
  have hcap : P.cap.get = maxProposals q sigma2 := congrArg PhaseValues.cap hP
  unfold collectSamples
  simp only [bind_eq, pure_eq, compute, tick_bind', pure_bind', Counted.bind_value,
    Counted.pure_value, loopUntil]
  refine Simulates.tick _ ?_
  rw [← mbind_pure_right (scheduledBalancedAccuracyRetryCollectAux _ _ _ _ _ _ _ _ _ _)]
  refine Simulates.tick _ (Simulates.bind (v := collectView) ?_ fun r => ?_)
  · have := collectRounds_simulates hG hsigma2 hP hs hw
      (walkCap := (Counted.add P.cap (Counted.lit (1 : ℕ)).value).value) (by simp [hcap])
      samples.get (Counted.lit (0 : ℝ)).value x
    simpa using this
  · rcases r with ⟨t, y⟩ | _ <;> exact Simulates.pure' rfl

theorem coolingPhase_simulates (hG : G.Holds q) {sigma2 tau2 : ℝ} (hsigma2 : 0 < sigma2)
    {s t : Num ℝ} (hs : s.get = sigma2) (ht : t.get = tau2) (x : NumPoint q.n) :
    Simulates (fun r : Option (Num ℝ × NumPoint q.n) => r.map fun p => (p.1.get, p.2.view))
      (scheduledBalancedCoolingRatioEstimate figureOneFinalScheduledBalancedParameters
        q sigma2 tau2 x.view) (coolingPhase q G s t x) := by
  set P := (phaseConstantsProg G s).value with hPdef
  have hP : P.view = phaseConstants q sigma2 := by
    rw [hPdef, phaseConstantsProg_value q hG, hs]
  have hsamples : P.samples.get = phaseSampleCount q sigma2 := congrArg PhaseValues.samples hP
  have hstart : (Counted.smul G.scale x).value.view = scaleFactor q • x.view := by
    rw [Counted.smul_value, hG.scale]
  have hw : ∀ z : NumPoint q.n, (gaussianRatioWeightProg s t z).value.get = gaussianRatioWeight sigma2 tau2 z.view :=
    fun z => by rw [gaussianRatioWeightProg_value, hs, ht]
  have hcol := collectSamples_simulates hG hsigma2 hP hs hw P.samples
    (Counted.smul G.scale x).value
  rw [hsamples, hstart] at hcol
  unfold coolingPhase scheduledBalancedCoolingRatioEstimate scheduledBalancedAccuracyRetryCollect
  simp only [figureOneFinalScheduledBalancedParameters, bind_eq, pure_eq, compute, tick_bind',
    pure_bind', simulates_tick_iff, ← hPdef, mbind_assoc', mpure_bind']
  refine Simulates.bind hcol fun r => ?_
  rcases r with _ | ⟨total, y⟩
  · exact Simulates.pure' rfl
  · refine Simulates.pure' ?_
    simp [balancedAccuracyRetryOutput, balancedCoolingAverage, Counted.smul_value, hG.scaleInv,
      hsamples]

theorem uniformPhase_simulates (hG : G.Holds q) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {s : Num ℝ} (hs : s.get = sigma2) (x : NumPoint q.n) :
    Simulates (fun r : Option (Num ℝ) => r.map Num.get)
      (scheduledBalancedCoolingUniformRatioEstimate figureOneFinalScheduledBalancedParameters
        q sigma2 x.view) (uniformPhase q G s x) := by
  set P := (phaseConstantsProg G s).value with hPdef
  have hP : P.view = phaseConstants q sigma2 := by
    rw [hPdef, phaseConstantsProg_value q hG, hs]
  have hstart : (Counted.smul G.scale x).value.view = scaleFactor q • x.view := by
    rw [Counted.smul_value, hG.scale]
  have hw : ∀ z : NumPoint q.n, (uniformRatioWeightProg s z).value.get = uniformRatioWeight sigma2 z.view :=
    fun z => by rw [uniformRatioWeightProg_value, hs]
  have hcol := collectSamples_simulates hG hsigma2 hP hs hw G.sampleCount
    (Counted.smul G.scale x).value
  rw [hG.sampleCount, hstart] at hcol
  unfold uniformPhase scheduledBalancedCoolingUniformRatioEstimate
    scheduledBalancedCoolingUniformEstimateWithState scheduledBalancedAccuracyRetryCollect
  simp only [figureOneFinalScheduledBalancedParameters, bind_eq, pure_eq, compute, tick_bind',
    pure_bind', simulates_tick_iff, ← hPdef, mbind_assoc', mpure_bind']
  refine Simulates.bind hcol fun r => ?_
  rcases r with _ | ⟨total, y⟩
  · exact Simulates.pure' rfl
  · refine Simulates.pure' ?_
    simp [balancedAccuracyRetryOutput, balancedCoolingAverage, balancedCoolingForgetState,
      hG.sampleCount]

theorem initialSample_simulates (hG : G.Holds q) :
    Simulates (fun r : Option (NumPoint q.n) => r.map NumPoint.view)
      (figureOneAbortInitialSample q) (initialSample q G) := by
  intro γ F F' hF
  let K' : AmbientSpace q.n → MembershipOracleProgram q.n γ := fun y =>
    .query y fun inside =>
      F' (if inside = true ∧ ‖y‖ ≤ Real.sqrt (terminalVariance q) then some (NumPoint.seal y)
        else none)
  have hnew : (initialSample q G).erase.bind F' =
      .randomPoint (standardGaussian q.n) inferInstance fun g =>
        K' (Real.sqrt (initialVariance q) • g) := by
    simp only [initialSample, drawPoint, isMember, compute, bind_eq, pure_eq,
      ChargedProgram.bind, erase, MembershipOracleProgram.bind]
    congr 1; funext g
    have hx := NumPoint.eq_seal (gaussianStartProg_value G.rootInitial
      (Counted.forEach fun i => Counted.pick (g i)).value)
    rw [hx]
    simp only [K', NumPoint.view_seal, drawPoint_view, Counted.isMember_value, hG.rootInitial, Counted.bind_value,
      Counted.le_value, Counted.norm_value, hG.rootTerminal, decide_eq_true_eq]
  rw [hnew]
  exact Refines.push (initialGaussianLaw q) inferInstance (standardGaussian q.n) inferInstance
    (Real.sqrt (initialVariance q) • ·) (by fun_prop) (initialGaussianLaw_eq_map q)
    (k := fun y => (MembershipOracleProgram.query y fun inside => .pure
      (if inside = true ∧ ‖y‖ ≤ Real.sqrt (terminalVariance q) then some y else none)).bind F)
    fun y => by
      simp only [MembershipOracleProgram.bind, K']
      refine Refines.query _ fun inside => ?_
      split_ifs
      · simpa using hF (some (NumPoint.seal y))
      · simpa using hF none

theorem coolingPhases_simulates (hG : G.Holds q) :
    ∀ (variances : List (Num ℝ)), (∀ v ∈ variances, 0 < v.get) → ∀ (x : NumPoint q.n),
      Simulates (fun r : Option (Num ℝ × NumPoint q.n) => r.map fun p => (p.1.get, p.2.view))
        (coolingProduct (scheduledBalancedAbortCoolingPrimitives
          figureOneFinalScheduledBalancedParameters) q (variances.map Num.get) x.view)
        (coolingPhases q G variances x) := by
  intro variances
  induction variances with
  | nil =>
    intro _ x
    simp only [List.map_nil, coolingProduct, coolingPhases, compute, bind_eq, pure_eq,
      tick_bind', pure_bind', simulates_tick_iff]
    exact Simulates.pure' (by simp)
  | cons sigma2 rest ih =>
    intro hpos x
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil, coolingProduct, coolingPhases, compute, bind_eq,
        pure_eq, tick_bind', pure_bind', simulates_tick_iff]
      exact Simulates.pure' (by simp)
    | cons tau2 rest =>
      simp only [List.map_cons]
      rw [coolingProduct, coolingPhases]
      simp only [bind_eq, scheduledBalancedAbortCoolingPrimitives, compute_cell_bind,
        simulates_tick_iff]
      refine Simulates.bind (coolingPhase_simulates hG (hpos sigma2 (by simp)) rfl rfl x)
        fun r => ?_
      rcases r with _ | ⟨W, y⟩
      · exact Simulates.pure' rfl
      · refine Simulates.bind (ih (fun v hv => hpos v (List.mem_cons_of_mem _ hv)) y)
          fun t => ?_
        rcases t with _ | ⟨product, z⟩
        · exact Simulates.pure' rfl
        · simp only [compute, pure_eq, tick_bind', pure_bind', simulates_tick_iff]
          exact Simulates.pure' (by simp)

theorem figureOneRun_simulates (hG : G.Holds q) :
    Simulates Num.get (figureOneFinalScheduledAbortBaseProgram q) (figureOneRun q G) := by
  have hpos : ∀ v ∈ G.schedule, 0 < v.get := by
    intro v hv
    have : v.get ∈ coolingSchedule q := hG.schedule ▸ List.mem_map_of_mem hv
    simp only [coolingSchedule, List.mem_ofFn] at this
    obtain ⟨i, hi⟩ := this
    rw [← hi]
    exact scheduleValue_pos q i
  unfold figureOneRun figureOneFinalScheduledAbortBaseProgram baseVolumeCoolingOn
  simp only [bind_eq, scheduledBalancedAbortCoolingPrimitives]
  refine Simulates.bind (initialSample_simulates hG) fun r => ?_
  rcases r with _ | x₀
  · exact Simulates.compute rfl
  · have hc := coolingPhases_simulates hG G.schedule hpos x₀
    rw [hG.schedule] at hc
    refine Simulates.bind hc fun t => ?_
    rcases t with _ | ⟨product, x⟩
    · exact Simulates.compute rfl
    · refine Simulates.bind (uniformPhase_simulates hG (terminalVariance_pos' q) hG.terminal x)
        fun u => ?_
      rcases u with _ | U
      · exact Simulates.compute rfl
      · exact Simulates.compute (by simp [hG.gaussianIntegral])

/-- The held real standing for `a`. -/
noncomputable def sealReal (a : ℝ) : Num ℝ := (Counted.lit a).value

theorem cappedRun_simulates (hG : G.Holds q) :
    Simulates Num.get (figureOneFinalScheduledCappedValueProgram q) (cappedRun q G) := by
  have hrun := (figureOneRun_simulates hG).refines_map
  have hcap := hrun.withQueryCap (queryBudget q)
  rw [withQueryCap_bind_pure] at hcap
  refine Simulates.of_refines_map sealReal (fun s => Num.ext rfl) (fun a => rfl) ?_
  unfold cappedRun figureOneFinalScheduledCappedValueProgram ChargedProgram.withHeldQueryCap
  simp only [bind_eq, erase_bind, erase_tick, erase_withQueryCap, hG.queryBudget, mbind_assoc']
  convert Refines.bind hcap (fun e => Refines.refl (MembershipOracleProgram.pure (e.getD 0)))
    using 1
  rw [mbind_assoc']
  congr 1
  funext r
  rcases r with _ | e <;> rfl

/-- The analysed repetition of `run` against the held one, with the estimates of the
first runs already held. -/
theorem repeatRounds_refines {A : MembershipOracleProgram q.n ℝ}
    {S : ChargedProgram q.n (Num ℝ)} (hrun : Simulates Num.get A S) :
    ∀ (k : ℕ) (done : List (Num ℝ)) {γ : Type} (F : (Fin k → ℝ) → MembershipOracleProgram q.n γ)
      (F' : List (Num ℝ) ⊕ Empty → MembershipOracleProgram q.n γ),
      (∀ (v : Fin k → ℝ) (l : List (Num ℝ)), l.map Num.get = done.map Num.get ++ List.ofFn v →
        Refines (F v) (F' (.inl l))) →
      Refines ((repeatOracleProgram A k).bind F)
        ((loopRounds (fun estimates => S.bind fun x =>
            (ChargedProgram.tick (Counted.push estimates x).tally
              (.pure (Counted.push estimates x).value)).bind fun e => .pure (.inl e)) k
          done).erase.bind F') := by
  intro k
  induction k with
  | zero =>
    intro done γ F F' hF
    exact hF Fin.elim0 done (by simp)
  | succ k ih =>
    intro done γ F F' hF
    simp only [repeatOracleProgram, loopRounds, bind_assoc', erase_bind, pure_bind', tick_bind',
      erase_tick, Counted.push_value, mbind_assoc', mpure_bind']
    refine hrun _ _ _ fun x => ?_
    refine ih (done ++ [x]) _ _ fun v l hl => ?_
    exact hF (Fin.cons x.get v) l (by simp [hl, List.ofFn_succ])

/-- With its operation counts erased, `cv18Program` refines the program the accuracy proof
was developed against: the two differ in how the random points are drawn, each point
having the same law, and in that `cv18Program` holds its numbers sealed. -/
theorem cv18Program_refines (q : VolumeParams) :
    Refines (amplifyOracleProgram figureOneFinalScheduledCappedValueProgram q)
      (cv18Program q).erase := by
  have hG := runConstantsProg_value q
  set G := (runConstantsProg q).value
  simp only [cv18Program, amplifyOracleProgram, repeatIndependently, report, loopUntil,
    bind_eq, pure_eq, erase_bind, pure_bind', bind_assoc',
    compute, erase, mpure_bind']
  rw [hG.repetitions]
  refine repeatRounds_refines (cappedRun_simulates hG) _ [] _ _ fun v l hl => ?_
  simp only [List.map_nil, List.nil_append] at hl
  have hlen : l.length = confidenceRepetitions q := by
    simpa using congrArg List.length hl
  refine Refines.of_eq (congrArg MembershipOracleProgram.pure ?_)
  dsimp only
  rw [Counted.median_value _ _ (hG.repetitions.trans hlen.symm)]
  clear hG
  revert v
  rw [← hlen]
  intro v hl
  congr 1
  funext i
  have h2 := congrArg (fun L : List ℝ => L[i.1]?) hl
  simpa using h2.symm

#print axioms cv18Program_refines

end ttc.ChargedCV18

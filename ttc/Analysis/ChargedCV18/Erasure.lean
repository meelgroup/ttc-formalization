/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.ChargedCV18.Program

/-!
# Erasing the operation counts

The charged `cv18Program` runs its arithmetic through `compute`, which records an
operation count (`tick`) next to each value.  `erase` deletes the ticks, and what remains
is a program of arlib-community's language `MembershipOracleProgram`.  Erasing changes
neither the output law (`runEstimate_erase`) nor the membership-query count
(`queryCost_erase`).

`CountedArithmetic.lean` proves that each counted program computes the formula it stands
for; with both, `Bridge.lean` identifies the erased program with the program
arlib-community's accuracy proof was developed against.
-/

open MeasureTheory

namespace ttc.ChargedCV18

open ArlibCommunity.Algorithms.CV18

/-! ## Erasure -/

/-- Delete every `tick` of a charged program, keeping all other steps: a program of
arlib-community's `MembershipOracleProgram`. -/
def ChargedProgram.erase {n : ℕ} {α : Type} :
    ChargedProgram n α → MembershipOracleProgram n α
  | .pure r => .pure r
  | .query x next => .query x fun answer => (next answer).erase
  | .randomNat law next => .randomNat law fun seed => (next seed).erase
  | .randomPoint law h next => .randomPoint law h fun point => (next point).erase
  | .randomReal law h next => .randomReal law h fun value => (next value).erase
  | .tick _ next => next.erase

namespace ChargedProgram

variable {n : ℕ} {α β : Type}

@[simp] theorem erase_pure (r : α) : (ChargedProgram.pure (n := n) r).erase = .pure r :=
  rfl

@[simp] theorem erase_tick (k : Arlib.Computation.CostVec Op) (p : ChargedProgram n α) :
    (ChargedProgram.tick k p).erase = p.erase := rfl

@[simp] theorem erase_query (x : AmbientSpace n) (next : Bool → ChargedProgram n α) :
    (ChargedProgram.query x next).erase = .query x fun a => (next a).erase := rfl

@[simp] theorem erase_randomNat (law : PMF ℕ) (next : ℕ → ChargedProgram n α) :
    (ChargedProgram.randomNat law next).erase =
      .randomNat law fun s => (next s).erase := rfl

@[simp] theorem erase_randomPoint (law : Measure (AmbientSpace n)) (h : IsProbabilityMeasure law)
    (next : AmbientSpace n → ChargedProgram n α) :
    (ChargedProgram.randomPoint law h next).erase =
      .randomPoint law h fun p => (next p).erase := rfl

@[simp] theorem erase_randomReal (law : Measure ℝ) (h : IsProbabilityMeasure law)
    (next : ℝ → ChargedProgram n α) :
    (ChargedProgram.randomReal law h next).erase =
      .randomReal law h fun v => (next v).erase := rfl

/-- Erasure commutes with sequential composition. -/
theorem erase_bind (p : ChargedProgram n α) (f : α → ChargedProgram n β) :
    (p.bind f).erase = p.erase.bind fun a => (f a).erase := by
  induction p with
  | pure a => rfl
  | query x next ih => simp only [bind, erase, MembershipOracleProgram.bind, ih]
  | randomNat law next ih => simp only [bind, erase, MembershipOracleProgram.bind, ih]
  | randomPoint law h next ih => simp only [bind, erase, MembershipOracleProgram.bind, ih]
  | randomReal law h next ih => simp only [bind, erase, MembershipOracleProgram.bind, ih]
  | tick k next ih => simp only [bind, erase, ih]

@[simp] theorem erase_bind' (p : ChargedProgram n α)
    (f : α → ChargedProgram n β) :
    (p >>= f).erase = p.erase >>= fun a => (f a).erase :=
  erase_bind p f

@[simp] theorem erase_pure' (r : α) :
    (Pure.pure r : ChargedProgram n α).erase = .pure r := rfl

@[simp] theorem erase_compute (c : Counted α) :
    (compute (n := n) c).erase = .pure c.value := rfl

/-- **Erasure keeps the output law.** -/
theorem runEstimate_erase [MeasurableSpace α] (oracle : AmbientSpace n → Bool)
    (p : ChargedProgram n α) : p.erase.runEstimate oracle = p.runEstimate oracle := by
  induction p with
  | pure a => rfl
  | query x next ih =>
      simp only [erase, runEstimate, MembershipOracleProgram.runEstimate, ih]
  | randomNat law next ih =>
      simp only [erase, runEstimate, MembershipOracleProgram.runEstimate, ih]
  | randomPoint law h next ih =>
      simp only [erase, runEstimate, MembershipOracleProgram.runEstimate, ih]
  | randomReal law h next ih =>
      simp only [erase, runEstimate, MembershipOracleProgram.runEstimate, ih]
  | tick k next ih => simp only [erase, runEstimate, ih]

/-- **Erasure keeps the membership-query count.** -/
theorem queryCost_erase (p : ChargedProgram n α) : p.erase.queryCost = p.queryCost := by
  induction p with
  | pure a => rfl
  | query x next ih => simp only [erase, queryCost, MembershipOracleProgram.queryCost, ih]
  | randomNat law next ih =>
      simp only [erase, queryCost, MembershipOracleProgram.queryCost, ih]
  | randomPoint law h next ih =>
      simp only [erase, queryCost, MembershipOracleProgram.queryCost, ih]
  | randomReal law h next ih =>
      simp only [erase, queryCost, MembershipOracleProgram.queryCost, ih]
  | tick k next ih => simp only [erase, queryCost, ih]

/-- Erasure commutes with the global query cap. -/
theorem erase_withQueryCap (budget : ℕ) (p : ChargedProgram n α) :
    (p.withQueryCap budget).erase = p.erase.withQueryCap budget := by
  induction p generalizing budget with
  | pure a => rfl
  | query x next ih =>
      cases budget with
      | zero => rfl
      | succ budget =>
          simp only [withQueryCap, erase, MembershipOracleProgram.withQueryCap, ih]
  | randomNat law next ih =>
      simp only [withQueryCap, erase, MembershipOracleProgram.withQueryCap, ih]
  | randomPoint law h next ih =>
      simp only [withQueryCap, erase, MembershipOracleProgram.withQueryCap, ih]
  | randomReal law h next ih =>
      simp only [withQueryCap, erase, MembershipOracleProgram.withQueryCap, ih]
  | tick k next ih => simp only [withQueryCap, erase, ih]

end ChargedProgram

end ttc.ChargedCV18

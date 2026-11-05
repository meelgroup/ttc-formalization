import Kr25Ssmxt.Analysis.ManuscriptOriginValidUpdate
import Kr25Ssmxt.Analysis.ManuscriptFixedLevelProductFold

/-! A deterministic finite fold of component source tapes. At every fixed
absolute level, its point counts obey the manuscript's delete-and-append
recurrence. -/

namespace Kr25Ssmxt

open Classical

structure ManuscriptOriginSourceStep (n : Nat) where
  component : PolytopeData n
  firstLabel : Nat
  basePending : Nat
  preRounds : Nat
  preCoins : Nat × Nat → Bool
  futureCoins : Nat × Nat → Bool
  tape : Nat → LatticePoint n

structure ManuscriptOriginSourceState (n : Nat) where
  processed : Nat
  valid : Finset (Nat × Nat)
  marks : Nat × Nat → LatticePoint n
  coins : Nat → Nat × Nat → Bool

noncomputable def ManuscriptOriginSourceState.step {n : Nat}
    (g : ManuscriptOriginSourceState n)
    (d : ManuscriptOriginSourceStep n) :
    ManuscriptOriginSourceState n where
  processed := g.processed + 1
  valid := manuscriptValidUpdate g.valid g.marks d.component g.processed
    d.firstLabel d.basePending
  marks := manuscriptMarksAppend g.marks g.processed d.tape
  coins := manuscriptCoinsAppend g.coins g.processed d.preCoins
    d.futureCoins d.preRounds

noncomputable def ManuscriptOriginSourceState.pointCounts {n : Nat}
    (g : ManuscriptOriginSourceState n)
    (level : Nat) (S : Finset (LatticePoint n)) : S → Nat :=
  manuscriptOriginSourcePointCounts g.valid g.marks g.coins level S

theorem ManuscriptOriginSourceState.step_pointCounts {n : Nat}
    (g : ManuscriptOriginSourceState n)
    (d : ManuscriptOriginSourceStep n)
    (level : Nat) (S : Finset (LatticePoint n))
    (hbound : ManuscriptValidBound g.valid g.processed) :
    (g.step d).pointCounts level S =
      fun x : S =>
        (if x.1.toPoint ∈ d.component.carrier then 0 else
          g.pointCounts level S x) +
        manuscriptPoissonTapePointCounts S d.firstLabel level
          (d.basePending,
            spliceCoins d.preCoins d.futureCoins d.preRounds, d.tape) x := by
  exact manuscriptOriginSourcePointCounts_update g.valid g.marks g.coins
    g.processed d.firstLabel d.basePending d.preRounds level
    d.preCoins d.futureCoins d.tape d.component S hbound

theorem ManuscriptOriginSourceState.step_validBound {n : Nat}
    (g : ManuscriptOriginSourceState n)
    (d : ManuscriptOriginSourceStep n)
    (hbound : ManuscriptValidBound g.valid g.processed) :
    ManuscriptValidBound (g.step d).valid (g.step d).processed := by
  exact manuscriptValidBound_append
    (g.valid.filter fun tag => (g.marks tag).toPoint ∉ d.component.carrier)
    g.processed d.firstLabel d.basePending
    (manuscriptValidBound_filter g.valid g.processed _ hbound)

noncomputable def manuscriptOriginSourceFold {n : Nat} :
    List (ManuscriptOriginSourceStep n) → ManuscriptOriginSourceState n →
      ManuscriptOriginSourceState n
  | [], g => g
  | d :: rest, g => manuscriptOriginSourceFold rest (g.step d)

noncomputable def manuscriptOriginCountFold {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat) :
    List (ManuscriptOriginSourceStep n) → (S → Nat) → (S → Nat)
  | [], initial => initial
  | d :: rest, initial =>
      manuscriptOriginCountFold S level rest (fun x =>
        (if x.1.toPoint ∈ d.component.carrier then 0 else initial x) +
          manuscriptPoissonTapePointCounts S d.firstLabel level
            (d.basePending,
              spliceCoins d.preCoins d.futureCoins d.preRounds, d.tape) x)

theorem manuscriptOriginSourceFold_pointCounts {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat)
    (steps : List (ManuscriptOriginSourceStep n))
    (g : ManuscriptOriginSourceState n)
    (hbound : ManuscriptValidBound g.valid g.processed) :
    (manuscriptOriginSourceFold steps g).pointCounts level S =
      manuscriptOriginCountFold S level steps (g.pointCounts level S) := by
  induction steps generalizing g with
  | nil => rfl
  | cons d rest ih =>
      change (manuscriptOriginSourceFold rest (g.step d)).pointCounts level S =
        manuscriptOriginCountFold S level rest
          (fun x : S =>
            (if x.1.toPoint ∈ d.component.carrier then 0 else
              g.pointCounts level S x) +
              manuscriptPoissonTapePointCounts S d.firstLabel level
                (d.basePending,
                  spliceCoins d.preCoins d.futureCoins d.preRounds, d.tape) x)
      rw [ih (g.step d) (g.step_validBound d hbound)]
      rw [g.step_pointCounts d level S hbound]

noncomputable def ManuscriptOriginSourceStep.fixedStep {n : Nat}
    (S : Finset (LatticePoint n)) (d : ManuscriptOriginSourceStep n) :
    FixedLevelStep S :=
  { deleted := componentDeletedCodes S d.component
    incoming := fun _ => 0 }

noncomputable def manuscriptOriginFixedSteps {n : Nat}
    (S : Finset (LatticePoint n)) :
    List (ManuscriptOriginSourceStep n) → List (FixedLevelStep S)
  | [] => []
  | d :: rest => d.fixedStep S :: manuscriptOriginFixedSteps S rest

noncomputable def ManuscriptOriginSourceStep.pointIncoming {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat)
    (d : ManuscriptOriginSourceStep n) : S → Nat :=
  manuscriptPoissonTapePointCounts S d.firstLabel level
    (d.basePending,
      spliceCoins d.preCoins d.futureCoins d.preRounds, d.tape)

noncomputable def manuscriptOriginIncomingFixed {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat) :
    (steps : List (ManuscriptOriginSourceStep n)) →
      Fin (manuscriptOriginFixedSteps S steps).length → S → Nat
  | [], i => Fin.elim0 i
  | d :: rest, i => Fin.cons (α := fun _ => S → Nat)
      (d.pointIncoming S level)
      (manuscriptOriginIncomingFixed S level rest) i

theorem manuscriptOriginCountFold_eq_fixedLevelFold {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat)
    (steps : List (ManuscriptOriginSourceStep n))
    (initial : S → Nat) :
    manuscriptOriginCountFold S level steps initial =
      fixedLevelFold (manuscriptOriginFixedSteps S steps)
        initial (manuscriptOriginIncomingFixed S level steps) := by
  induction steps generalizing initial with
  | nil => rfl
  | cons d rest ih =>
      have htail : Fin.tail
          (manuscriptOriginIncomingFixed S level (d :: rest)) =
          manuscriptOriginIncomingFixed S level rest := by
        change Fin.tail (Fin.cons (α := fun _ => S → Nat)
          (d.pointIncoming S level)
          (manuscriptOriginIncomingFixed S level rest)) = _
        exact Fin.tail_cons (α := fun _ => S → Nat)
          (d.pointIncoming S level)
          (manuscriptOriginIncomingFixed S level rest)
      change manuscriptOriginCountFold S level rest
          (fun x : S =>
            (if x.1.toPoint ∈ d.component.carrier then 0 else initial x) +
              d.pointIncoming S level x) =
        fixedLevelFold (manuscriptOriginFixedSteps S rest)
          (fun x : S =>
            (if x ∈ (d.fixedStep S).deleted then 0 else initial x) +
              d.pointIncoming S level x)
          (Fin.tail (manuscriptOriginIncomingFixed S level (d :: rest)))
      rw [htail]
      have hupdate : (fun x : S =>
          (if x ∈ (d.fixedStep S).deleted then 0 else initial x) +
            d.pointIncoming S level x) =
          (fun x : S =>
            (if x.1.toPoint ∈ d.component.carrier then 0 else initial x) +
              d.pointIncoming S level x) := by
        funext x
        simp [ManuscriptOriginSourceStep.fixedStep,
          componentDeletedCodes]
      rw [hupdate]
      exact ih _

noncomputable def ManuscriptOriginSourceState.initial {n : Nat} :
    ManuscriptOriginSourceState n where
  processed := 0
  valid := ∅
  marks := fun _ => 0
  coins := fun _ _ => false

theorem ManuscriptOriginSourceState.initial_validBound {n : Nat} :
    ManuscriptValidBound (ManuscriptOriginSourceState.initial (n := n)).valid
      (ManuscriptOriginSourceState.initial (n := n)).processed := by
  exact manuscriptValidBound_initial

theorem ManuscriptOriginSourceState.initial_pointCounts {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat) :
    (ManuscriptOriginSourceState.initial (n := n)).pointCounts level S =
      fun _ => 0 := by
  funext x
  change ((∅ : Finset (Nat × Nat)).filter fun tag =>
    survives ((fun _ _ => false) tag.1) level tag.2 ∧
      (0 : LatticePoint n) = x.1).card = 0
  simp

/-- A source-driven fold started with no copies has exactly the fixed-level
delete-and-append point counts. -/
theorem manuscriptOriginSourceFold_initial_fixedLevelCounts {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat)
    (steps : List (ManuscriptOriginSourceStep n)) :
    (manuscriptOriginSourceFold steps
      (ManuscriptOriginSourceState.initial (n := n))).pointCounts level S =
    fixedLevelFold (manuscriptOriginFixedSteps S steps) (fun _ => 0)
      (manuscriptOriginIncomingFixed S level steps) := by
  rw [manuscriptOriginSourceFold_pointCounts S level steps
    ManuscriptOriginSourceState.initial
    ManuscriptOriginSourceState.initial_validBound]
  rw [ManuscriptOriginSourceState.initial_pointCounts]
  exact manuscriptOriginCountFold_eq_fixedLevelFold S level steps (fun _ => 0)

end Kr25Ssmxt

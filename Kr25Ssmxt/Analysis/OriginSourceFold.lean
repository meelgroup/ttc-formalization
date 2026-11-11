import Kr25Ssmxt.Analysis.OriginValidUpdate
import Kr25Ssmxt.Analysis.FixedLevelProductFold

/-! A deterministic finite fold of component source tapes. At every fixed
absolute level, its point counts obey the paper's delete-and-append
recurrence. -/

namespace Kr25Ssmxt

open Classical

structure OriginSourceStep (n : Nat) where
  component : PolytopeData n
  firstLabel : Nat
  basePending : Nat
  preRounds : Nat
  preCoins : Nat × Nat → Bool
  futureCoins : Nat × Nat → Bool
  tape : Nat → LatticePoint n

structure OriginSourceState (n : Nat) where
  processed : Nat
  valid : Finset (Nat × Nat)
  marks : Nat × Nat → LatticePoint n
  coins : Nat → Nat × Nat → Bool

noncomputable def OriginSourceState.step {n : Nat}
    (g : OriginSourceState n)
    (d : OriginSourceStep n) :
    OriginSourceState n where
  processed := g.processed + 1
  valid := validUpdate g.valid g.marks d.component g.processed
    d.firstLabel d.basePending
  marks := marksAppend g.marks g.processed d.tape
  coins := coinsAppend g.coins g.processed d.preCoins
    d.futureCoins d.preRounds

noncomputable def OriginSourceState.pointCounts {n : Nat}
    (g : OriginSourceState n)
    (level : Nat) (S : Finset (LatticePoint n)) : S → Nat :=
  originSourcePointCounts g.valid g.marks g.coins level S

theorem OriginSourceState.step_pointCounts {n : Nat}
    (g : OriginSourceState n)
    (d : OriginSourceStep n)
    (level : Nat) (S : Finset (LatticePoint n))
    (hbound : ValidBound g.valid g.processed) :
    (g.step d).pointCounts level S =
      fun x : S =>
        (if x.1.toPoint ∈ d.component.carrier then 0 else
          g.pointCounts level S x) +
        poissonTapePointCounts S d.firstLabel level
          (d.basePending,
            spliceCoins d.preCoins d.futureCoins d.preRounds, d.tape) x := by
  exact originSourcePointCounts_update g.valid g.marks g.coins
    g.processed d.firstLabel d.basePending d.preRounds level
    d.preCoins d.futureCoins d.tape d.component S hbound

theorem OriginSourceState.step_validBound {n : Nat}
    (g : OriginSourceState n)
    (d : OriginSourceStep n)
    (hbound : ValidBound g.valid g.processed) :
    ValidBound (g.step d).valid (g.step d).processed := by
  exact validBound_append
    (g.valid.filter fun tag => (g.marks tag).toPoint ∉ d.component.carrier)
    g.processed d.firstLabel d.basePending
    (validBound_filter g.valid g.processed _ hbound)

noncomputable def originSourceFold {n : Nat} :
    List (OriginSourceStep n) → OriginSourceState n →
      OriginSourceState n
  | [], g => g
  | d :: rest, g => originSourceFold rest (g.step d)

noncomputable def originCountFold {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat) :
    List (OriginSourceStep n) → (S → Nat) → (S → Nat)
  | [], initial => initial
  | d :: rest, initial =>
      originCountFold S level rest (fun x =>
        (if x.1.toPoint ∈ d.component.carrier then 0 else initial x) +
          poissonTapePointCounts S d.firstLabel level
            (d.basePending,
              spliceCoins d.preCoins d.futureCoins d.preRounds, d.tape) x)

theorem originSourceFold_pointCounts {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat)
    (steps : List (OriginSourceStep n))
    (g : OriginSourceState n)
    (hbound : ValidBound g.valid g.processed) :
    (originSourceFold steps g).pointCounts level S =
      originCountFold S level steps (g.pointCounts level S) := by
  induction steps generalizing g with
  | nil => rfl
  | cons d rest ih =>
      change (originSourceFold rest (g.step d)).pointCounts level S =
        originCountFold S level rest
          (fun x : S =>
            (if x.1.toPoint ∈ d.component.carrier then 0 else
              g.pointCounts level S x) +
              poissonTapePointCounts S d.firstLabel level
                (d.basePending,
                  spliceCoins d.preCoins d.futureCoins d.preRounds, d.tape) x)
      rw [ih (g.step d) (g.step_validBound d hbound)]
      rw [g.step_pointCounts d level S hbound]

noncomputable def OriginSourceStep.fixedStep {n : Nat}
    (S : Finset (LatticePoint n)) (d : OriginSourceStep n) :
    FixedLevelStep S :=
  { deleted := componentDeletedCodes S d.component
    incoming := fun _ => 0 }

noncomputable def originFixedSteps {n : Nat}
    (S : Finset (LatticePoint n)) :
    List (OriginSourceStep n) → List (FixedLevelStep S)
  | [] => []
  | d :: rest => d.fixedStep S :: originFixedSteps S rest

noncomputable def OriginSourceStep.pointIncoming {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat)
    (d : OriginSourceStep n) : S → Nat :=
  poissonTapePointCounts S d.firstLabel level
    (d.basePending,
      spliceCoins d.preCoins d.futureCoins d.preRounds, d.tape)

noncomputable def originIncomingFixed {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat) :
    (steps : List (OriginSourceStep n)) →
      Fin (originFixedSteps S steps).length → S → Nat
  | [], i => Fin.elim0 i
  | d :: rest, i => Fin.cons (α := fun _ => S → Nat)
      (d.pointIncoming S level)
      (originIncomingFixed S level rest) i

theorem originCountFold_eq_fixedLevelFold {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat)
    (steps : List (OriginSourceStep n))
    (initial : S → Nat) :
    originCountFold S level steps initial =
      fixedLevelFold (originFixedSteps S steps)
        initial (originIncomingFixed S level steps) := by
  induction steps generalizing initial with
  | nil => rfl
  | cons d rest ih =>
      have htail : Fin.tail
          (originIncomingFixed S level (d :: rest)) =
          originIncomingFixed S level rest := by
        change Fin.tail (Fin.cons (α := fun _ => S → Nat)
          (d.pointIncoming S level)
          (originIncomingFixed S level rest)) = _
        exact Fin.tail_cons (α := fun _ => S → Nat)
          (d.pointIncoming S level)
          (originIncomingFixed S level rest)
      change originCountFold S level rest
          (fun x : S =>
            (if x.1.toPoint ∈ d.component.carrier then 0 else initial x) +
              d.pointIncoming S level x) =
        fixedLevelFold (originFixedSteps S rest)
          (fun x : S =>
            (if x ∈ (d.fixedStep S).deleted then 0 else initial x) +
              d.pointIncoming S level x)
          (Fin.tail (originIncomingFixed S level (d :: rest)))
      rw [htail]
      have hupdate : (fun x : S =>
          (if x ∈ (d.fixedStep S).deleted then 0 else initial x) +
            d.pointIncoming S level x) =
          (fun x : S =>
            (if x.1.toPoint ∈ d.component.carrier then 0 else initial x) +
              d.pointIncoming S level x) := by
        funext x
        simp [OriginSourceStep.fixedStep,
          componentDeletedCodes]
      rw [hupdate]
      exact ih _

noncomputable def OriginSourceState.initial {n : Nat} :
    OriginSourceState n where
  processed := 0
  valid := ∅
  marks := fun _ => 0
  coins := fun _ _ => false

theorem OriginSourceState.initial_validBound {n : Nat} :
    ValidBound (OriginSourceState.initial (n := n)).valid
      (OriginSourceState.initial (n := n)).processed := by
  exact validBound_initial

theorem OriginSourceState.initial_pointCounts {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat) :
    (OriginSourceState.initial (n := n)).pointCounts level S =
      fun _ => 0 := by
  funext x
  change ((∅ : Finset (Nat × Nat)).filter fun tag =>
    survives ((fun _ _ => false) tag.1) level tag.2 ∧
      (0 : LatticePoint n) = x.1).card = 0
  simp

/-- A source-driven fold started with no copies has exactly the fixed-level
delete-and-append point counts. -/
theorem originSourceFold_initial_fixedLevelCounts {n : Nat}
    (S : Finset (LatticePoint n)) (level : Nat)
    (steps : List (OriginSourceStep n)) :
    (originSourceFold steps
      (OriginSourceState.initial (n := n))).pointCounts level S =
    fixedLevelFold (originFixedSteps S steps) (fun _ => 0)
      (originIncomingFixed S level steps) := by
  rw [originSourceFold_pointCounts S level steps
    OriginSourceState.initial
    OriginSourceState.initial_validBound]
  rw [OriginSourceState.initial_pointCounts]
  exact originCountFold_eq_fixedLevelFold S level steps (fun _ => 0)

end Kr25Ssmxt

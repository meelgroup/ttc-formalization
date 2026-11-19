import ttc.Analysis.OriginConfiguration

/-! An arbitrary finite source-driven component trace agrees pathwise with
the fixed-level delete-and-append fold at its final absolute level. -/

namespace ttc

open Classical

structure OriginInput (n : Nat) where
  component : PolytopeData n
  intensity : NNReal
  threshold : Real
  basePending : Nat
  preCoins : Nat × Nat → Bool
  futureCoins : Nat × Nat → Bool
  tape : Nat → LatticePoint n

noncomputable def OriginInput.sourceStep {n : Nat}
    (d : OriginInput n) (c : OriginConfiguration n) :
    OriginSourceStep n where
  component := d.component
  firstLabel := c.state.nextLabel
  basePending := d.basePending
  preRounds := c.level + ttcReference.firstLoopExit
    (c.state.removeComponent d.component) d.intensity d.threshold
  preCoins := d.preCoins
  futureCoins := d.futureCoins
  tape := d.tape

noncomputable def OriginConfiguration.advanceInput {n : Nat}
    (c : OriginConfiguration n) (d : OriginInput n) :
    OriginConfiguration n :=
  c.advance d.component d.intensity d.threshold d.basePending
    d.preCoins d.futureCoins d.tape

theorem OriginConfiguration.advanceInput_source {n : Nat}
    (c : OriginConfiguration n) (d : OriginInput n) :
    (c.advanceInput d).source = c.source.step (d.sourceStep c) := by
  exact c.advance_source d.component d.intensity d.threshold
    d.basePending d.preCoins d.futureCoins d.tape

noncomputable def originAdvanceFold {n : Nat} :
    List (OriginInput n) → OriginConfiguration n →
      OriginConfiguration n
  | [], c => c
  | d :: rest, c => originAdvanceFold rest (c.advanceInput d)

noncomputable def originAdvanceSteps {n : Nat} :
    List (OriginInput n) → OriginConfiguration n →
      List (OriginSourceStep n)
  | [], _ => []
  | d :: rest, c =>
      d.sourceStep c :: originAdvanceSteps rest (c.advanceInput d)

theorem originAdvanceFold_source {n : Nat}
    (inputs : List (OriginInput n))
    (c : OriginConfiguration n) :
    (originAdvanceFold inputs c).source =
      originSourceFold (originAdvanceSteps inputs c)
        c.source := by
  induction inputs generalizing c with
  | nil => rfl
  | cons d rest ih =>
      change (originAdvanceFold rest (c.advanceInput d)).source =
        originSourceFold
          (originAdvanceSteps rest (c.advanceInput d))
          (c.source.step (d.sourceStep c))
      rw [ih]
      rw [c.advanceInput_source d]

/-- Every finite input trace, including adaptively selected rounds and label
offsets, has the same final point counts as its source fold evaluated at the
trace's final level. -/
theorem originAdvanceFold_pointCounts {n : Nat}
    (inputs : List (OriginInput n))
    (c : OriginConfiguration n)
    (S : Finset (LatticePoint n)) :
    let final := originAdvanceFold inputs c
    final.state.pointCounts S =
      fixedLevelFold (originFixedSteps S
        (originAdvanceSteps inputs c))
        (c.source.pointCounts final.level S)
        (originIncomingFixed S final.level
          (originAdvanceSteps inputs c)) := by
  dsimp only
  let final := originAdvanceFold inputs c
  rw [final.pointCounts_eq_source S,
    originAdvanceFold_source inputs c]
  rw [originSourceFold_pointCounts S final.level
    (originAdvanceSteps inputs c) c.source c.bound]
  exact originCountFold_eq_fixedLevelFold S final.level
    (originAdvanceSteps inputs c)
    (c.source.pointCounts final.level S)

theorem originAdvanceFold_initial_pointCounts {n : Nat}
    (inputs : List (OriginInput n))
    (S : Finset (LatticePoint n)) :
    let initial := OriginConfiguration.initial n
    let final := originAdvanceFold inputs initial
    final.state.pointCounts S =
      fixedLevelFold (originFixedSteps S
        (originAdvanceSteps inputs initial)) (fun _ => 0)
        (originIncomingFixed S final.level
          (originAdvanceSteps inputs initial)) := by
  dsimp only
  rw [originAdvanceFold_pointCounts]
  have hzero : (OriginConfiguration.initial n).source.pointCounts
      (originAdvanceFold inputs
        (OriginConfiguration.initial n)).level S =
      fun _ => 0 := by
    change (OriginSourceState.initial (n := n)).pointCounts
      (originAdvanceFold inputs
        (OriginConfiguration.initial n)).level S = fun _ => 0
    exact OriginSourceState.initial_pointCounts S _
  rw [hzero]

end ttc

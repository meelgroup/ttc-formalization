import Kr25Ssmxt.Analysis.ManuscriptOriginConfiguration

/-! An arbitrary finite source-driven component trace agrees pathwise with
the fixed-level delete-and-append fold at its final absolute level. -/

namespace Kr25Ssmxt

open Classical

structure ManuscriptOriginInput (n : Nat) where
  component : PolytopeData n
  intensity : NNReal
  threshold : Real
  basePending : Nat
  preCoins : Nat × Nat → Bool
  futureCoins : Nat × Nat → Bool
  tape : Nat → LatticePoint n

noncomputable def ManuscriptOriginInput.sourceStep {n : Nat}
    (d : ManuscriptOriginInput n) (c : ManuscriptOriginConfiguration n) :
    ManuscriptOriginSourceStep n where
  component := d.component
  firstLabel := c.state.nextLabel
  basePending := d.basePending
  preRounds := c.level + manuscriptRateExit
    (c.state.removeComponent d.component) d.intensity d.threshold
  preCoins := d.preCoins
  futureCoins := d.futureCoins
  tape := d.tape

noncomputable def ManuscriptOriginConfiguration.advanceInput {n : Nat}
    (c : ManuscriptOriginConfiguration n) (d : ManuscriptOriginInput n) :
    ManuscriptOriginConfiguration n :=
  c.advance d.component d.intensity d.threshold d.basePending
    d.preCoins d.futureCoins d.tape

theorem ManuscriptOriginConfiguration.advanceInput_source {n : Nat}
    (c : ManuscriptOriginConfiguration n) (d : ManuscriptOriginInput n) :
    (c.advanceInput d).source = c.source.step (d.sourceStep c) := by
  exact c.advance_source d.component d.intensity d.threshold
    d.basePending d.preCoins d.futureCoins d.tape

noncomputable def manuscriptOriginAdvanceFold {n : Nat} :
    List (ManuscriptOriginInput n) → ManuscriptOriginConfiguration n →
      ManuscriptOriginConfiguration n
  | [], c => c
  | d :: rest, c => manuscriptOriginAdvanceFold rest (c.advanceInput d)

noncomputable def manuscriptOriginAdvanceSteps {n : Nat} :
    List (ManuscriptOriginInput n) → ManuscriptOriginConfiguration n →
      List (ManuscriptOriginSourceStep n)
  | [], _ => []
  | d :: rest, c =>
      d.sourceStep c :: manuscriptOriginAdvanceSteps rest (c.advanceInput d)

theorem manuscriptOriginAdvanceFold_source {n : Nat}
    (inputs : List (ManuscriptOriginInput n))
    (c : ManuscriptOriginConfiguration n) :
    (manuscriptOriginAdvanceFold inputs c).source =
      manuscriptOriginSourceFold (manuscriptOriginAdvanceSteps inputs c)
        c.source := by
  induction inputs generalizing c with
  | nil => rfl
  | cons d rest ih =>
      change (manuscriptOriginAdvanceFold rest (c.advanceInput d)).source =
        manuscriptOriginSourceFold
          (manuscriptOriginAdvanceSteps rest (c.advanceInput d))
          (c.source.step (d.sourceStep c))
      rw [ih]
      rw [c.advanceInput_source d]

/-- Every finite input trace, including adaptively selected rounds and label
offsets, has the same final point counts as its source fold evaluated at the
trace's final level. -/
theorem manuscriptOriginAdvanceFold_pointCounts {n : Nat}
    (inputs : List (ManuscriptOriginInput n))
    (c : ManuscriptOriginConfiguration n)
    (S : Finset (LatticePoint n)) :
    let final := manuscriptOriginAdvanceFold inputs c
    final.state.pointCounts S =
      fixedLevelFold (manuscriptOriginFixedSteps S
        (manuscriptOriginAdvanceSteps inputs c))
        (c.source.pointCounts final.level S)
        (manuscriptOriginIncomingFixed S final.level
          (manuscriptOriginAdvanceSteps inputs c)) := by
  dsimp only
  let final := manuscriptOriginAdvanceFold inputs c
  rw [final.pointCounts_eq_source S,
    manuscriptOriginAdvanceFold_source inputs c]
  rw [manuscriptOriginSourceFold_pointCounts S final.level
    (manuscriptOriginAdvanceSteps inputs c) c.source c.bound]
  exact manuscriptOriginCountFold_eq_fixedLevelFold S final.level
    (manuscriptOriginAdvanceSteps inputs c)
    (c.source.pointCounts final.level S)

theorem manuscriptOriginAdvanceFold_initial_pointCounts {n : Nat}
    (inputs : List (ManuscriptOriginInput n))
    (S : Finset (LatticePoint n)) :
    let initial := ManuscriptOriginConfiguration.initial n
    let final := manuscriptOriginAdvanceFold inputs initial
    final.state.pointCounts S =
      fixedLevelFold (manuscriptOriginFixedSteps S
        (manuscriptOriginAdvanceSteps inputs initial)) (fun _ => 0)
        (manuscriptOriginIncomingFixed S final.level
          (manuscriptOriginAdvanceSteps inputs initial)) := by
  dsimp only
  rw [manuscriptOriginAdvanceFold_pointCounts]
  have hzero : (ManuscriptOriginConfiguration.initial n).source.pointCounts
      (manuscriptOriginAdvanceFold inputs
        (ManuscriptOriginConfiguration.initial n)).level S =
      fun _ => 0 := by
    change (ManuscriptOriginSourceState.initial (n := n)).pointCounts
      (manuscriptOriginAdvanceFold inputs
        (ManuscriptOriginConfiguration.initial n)).level S = fun _ => 0
    exact ManuscriptOriginSourceState.initial_pointCounts S _
  rw [hzero]

end Kr25Ssmxt

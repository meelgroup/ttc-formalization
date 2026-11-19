import ttc.Analysis.PoissonVectorTotal

/-! Deterministic point-intensity envelope for a fixed-level union prefix.
At each component, overlap is deleted and replaced by the new component's
Poisson rate; points outside the component keep their previous rate. -/

namespace ttc

def FixedLevelStep.RateEnvelope {ι : Type*} [DecidableEq ι]
    (step : FixedLevelStep ι) (lower upper : NNReal) : Prop :=
  (∀ x ∈ step.deleted,
    lower ≤ step.incoming x ∧ step.incoming x ≤ upper) ∧
  (∀ x ∉ step.deleted, step.incoming x = 0)

def fixedLevelCoverage {ι : Type*} [DecidableEq ι] :
    List (FixedLevelStep ι) → Finset ι → Finset ι
  | [], covered => covered
  | step :: rest, covered =>
      fixedLevelCoverage rest (covered ∪ step.deleted)

/-- The pointwise rate envelope is preserved by every fixed-level prefix.
In particular, the final rate vanishes off the union of processed components. -/
theorem fixedLevelRates_envelope {ι : Type*} [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) (r : ι → NNReal)
    (covered : Finset ι) (lower upper : NNReal)
    (hstart :
      (∀ x ∈ covered, lower ≤ r x ∧ r x ≤ upper) ∧
      (∀ x ∉ covered, r x = 0))
    (hsteps : ∀ step ∈ steps, step.RateEnvelope lower upper) :
    (∀ x ∈ fixedLevelCoverage steps covered,
      lower ≤ fixedLevelRates steps r x ∧
        fixedLevelRates steps r x ≤ upper) ∧
    (∀ x ∉ fixedLevelCoverage steps covered,
      fixedLevelRates steps r x = 0) := by
  induction steps generalizing r covered with
  | nil => simpa [fixedLevelRates, fixedLevelCoverage] using hstart
  | cons step rest ih =>
      have hstep : step.RateEnvelope lower upper := hsteps step (by simp)
      let nextRate : ι → NNReal := fun x =>
        (if x ∈ step.deleted then 0 else r x) + step.incoming x
      have hnext :
          (∀ x ∈ covered ∪ step.deleted,
            lower ≤ nextRate x ∧ nextRate x ≤ upper) ∧
          (∀ x ∉ covered ∪ step.deleted, nextRate x = 0) := by
        constructor
        · intro x hx
          by_cases hd : x ∈ step.deleted
          · simpa [nextRate, hd] using hstep.1 x hd
          · have hc : x ∈ covered := by
              rcases Finset.mem_union.mp hx with hc | hd'
              · exact hc
              · exact False.elim (hd hd')
            simpa [nextRate, hd, hstep.2 x hd] using hstart.1 x hc
        · intro x hx
          have hc : x ∉ covered := fun h => hx (Finset.mem_union.mpr (Or.inl h))
          have hd : x ∉ step.deleted :=
            fun h => hx (Finset.mem_union.mpr (Or.inr h))
          simp [nextRate, hd, hstart.2 x hc, hstep.2 x hd]
      have hrest : ∀ item ∈ rest, item.RateEnvelope lower upper := by
        intro item hi
        exact hsteps item (by simp [hi])
      simpa only [fixedLevelRates, fixedLevelCoverage] using
        ih nextRate (covered ∪ step.deleted) hnext hrest

theorem fixedLevelRates_zero_envelope {ι : Type*} [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) (lower upper : NNReal)
    (hsteps : ∀ step ∈ steps, step.RateEnvelope lower upper) :
    (∀ x ∈ fixedLevelCoverage steps ∅,
      lower ≤ fixedLevelRates steps (fun _ => 0) x ∧
        fixedLevelRates steps (fun _ => 0) x ≤ upper) ∧
    (∀ x ∉ fixedLevelCoverage steps ∅,
      fixedLevelRates steps (fun _ => 0) x = 0) := by
  apply fixedLevelRates_envelope steps (fun _ => 0) ∅ lower upper
  · constructor
    · intro x hx
      simp at hx
    · intro x hx
      rfl
  · exact hsteps

theorem fixedLevelRates_total_mean_bounds
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) (lower upper : NNReal)
    (hsteps : ∀ step ∈ steps, step.RateEnvelope lower upper) :
    ((fixedLevelCoverage steps ∅).card : Nat) • lower ≤
        ∑ x, fixedLevelRates steps (fun _ => 0) x ∧
      (∑ x, fixedLevelRates steps (fun _ => 0) x) ≤
        ((fixedLevelCoverage steps ∅).card : Nat) • upper := by
  let covered := fixedLevelCoverage steps ∅
  let rates := fixedLevelRates steps (fun _ => 0)
  have henv := fixedLevelRates_zero_envelope steps lower upper hsteps
  have hsum : (∑ x ∈ covered, rates x) = ∑ x, rates x := by
    apply Finset.sum_subset (Finset.subset_univ covered)
    intro x _ hx
    exact henv.2 x hx
  have hlow : (∑ _x ∈ covered, lower) ≤ ∑ x ∈ covered, rates x :=
    Finset.sum_le_sum (fun x hx => (henv.1 x hx).1)
  have hupp : (∑ x ∈ covered, rates x) ≤ ∑ _x ∈ covered, upper :=
    Finset.sum_le_sum (fun x hx => (henv.1 x hx).2)
  simp only [Finset.sum_const] at hlow hupp
  exact ⟨hlow.trans_eq hsum, hsum.symm.le.trans hupp⟩

end ttc

import Kr25Ssmxt.Analysis.PreludeProof
import Kr25Ssmxt.Model.Program

/-!
# From retained-count concentration to estimator concentration

The stochastic invariant naturally controls the retained cardinality at the final sampling
rate.  This module isolates the cancellation of that positive rate and the passage through
the estimator map.
-/

noncomputable section

open MeasureTheory

namespace Kr25Ssmxt

/-- Concentration of the retained cardinality around `rate * target` implies concentration
of the published estimate `cardinality / rate` around `target`, provided the rate is
almost surely nonzero.

INTERNAL: final estimate assembly in
`process_components_lattice_count_accuracy`.
-/
lemma process_components_lattice_count_accuracy_estimate_of_count
    {n : Nat}
    (mu : Measure (TTCState n))
    (epsilon delta target : Real)
    (hfinite : IsFiniteMeasure mu)
    (hmeasurable : AEMeasurable TTCState.estimate mu)
    (hrate : ∀ᵐ state ∂mu, state.rate ≠ 0)
    (hcount : mu.real
      {state | (state.samples.card : Real) ∈
        Arlib.relErr epsilon ((state.rate : Real) * target)} ≥ 1 - delta) :
    (mu.map TTCState.estimate).real
        {estimate | (estimate : Real) ∈ Arlib.relErr epsilon target} ≥
      1 - delta := by
  let A : Set (TTCState n) :=
    {state | (state.samples.card : Real) ∈
      Arlib.relErr epsilon ((state.rate : Real) * target)}
  let B : Set NNReal :=
    {estimate | (estimate : Real) ∈ Arlib.relErr epsilon target}
  have hB : MeasurableSet B := by
    dsimp [B, Arlib.relErr]
    measurability
  have hevents : ∀ᵐ state ∂mu, state ∈ A ↔ TTCState.estimate state ∈ B := by
    filter_upwards [hrate] with state hrate_ne
    have hrate_pos : 0 < (state.rate : Real) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hrate_ne)
    change
      (state.samples.card : Real) ∈
          Arlib.relErr epsilon ((state.rate : Real) * target) ↔
        (((state.samples.card : NNReal) / state.rate : NNReal) : Real) ∈
          Arlib.relErr epsilon target
    simp only [NNReal.coe_div, NNReal.coe_natCast, Arlib.mem_relErr]
    constructor
    · rintro ⟨hlower, hupper⟩
      constructor
      · rw [le_div_iff₀ hrate_pos]
        calc
          (1 - epsilon) * target * (state.rate : Real) =
              (1 - epsilon) * ((state.rate : Real) * target) := by ring
          _ ≤ (state.samples.card : Real) := hlower
      · rw [div_le_iff₀ hrate_pos]
        calc
          (state.samples.card : Real) ≤
              (1 + epsilon) * ((state.rate : Real) * target) := hupper
          _ = (1 + epsilon) * target * (state.rate : Real) := by ring
    · rintro ⟨hlower, hupper⟩
      constructor
      · have hlower' := (le_div_iff₀ hrate_pos).mp hlower
        calc
          (1 - epsilon) * ((state.rate : Real) * target) =
              (1 - epsilon) * target * (state.rate : Real) := by ring
          _ ≤ (state.samples.card : Real) := hlower'
      · have hupper' := (div_le_iff₀ hrate_pos).mp hupper
        calc
          (state.samples.card : Real) ≤
              (1 + epsilon) * target * (state.rate : Real) := hupper'
          _ = (1 + epsilon) * ((state.rate : Real) * target) := by ring
  have hmeasure : mu A = mu (TTCState.estimate ⁻¹' B) :=
    measure_eq_of_mem_ae_iff hevents
  rw [MeasureTheory.map_measureReal_apply_of_aemeasurable hmeasurable hB]
  change mu.real (TTCState.estimate ⁻¹' B) ≥ 1 - delta
  rw [← hmeasure]
  exact hcount

end Kr25Ssmxt

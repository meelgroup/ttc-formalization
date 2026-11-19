import ttc.Analysis.ReferenceProgram

/-!
# A one-step probability union bound for measure bind

This module records the measure-theoretic composition estimate used when a good event for
one randomized step leads to a uniformly good continuation.
-/

noncomputable section

open MeasureTheory

namespace ttc

/-- A probability kernel loses at most the sum of the first-step and continuation failure
budgets when composed by `Measure.bind`.

INTERNAL: one-step union-bound bookkeeping for stochastic list folds.
-/
lemma probability_bind_good_event_lower_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (K : α → Measure β) (G : Set α) (A : Set β) (r s : Real)
    (hμ : IsProbabilityMeasure μ)
    (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hK : Measurable K) (hG : MeasurableSet G) (hA : MeasurableSet A)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hμG : μ.real G ≥ 1 - s)
    (hKA : ∀ x ∈ G, (K x).real A ≥ 1 - r) :
    (μ.bind K).real A ≥ 1 - (r + s) := by
  letI : IsProbabilityMeasure μ := hμ
  have hKcompl : ∀ x ∈ G, K x Aᶜ ≤ ENNReal.ofReal r := by
    intro x hx
    letI : IsProbabilityMeasure (K x) := hKprob x
    rw [← ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal hr, ← Measure.real_def,
      probReal_compl_eq_one_sub hA]
    linarith [hKA x hx]
  have hμcompl_real : μ.real Gᶜ ≤ s := by
    rw [probReal_compl_eq_one_sub hG]
    linarith
  have hμcompl : μ Gᶜ ≤ ENNReal.ofReal s := by
    rw [← ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top]
    simpa [Measure.real_def, ENNReal.toReal_ofReal hs] using hμcompl_real
  have hbind_compl : μ.bind K Aᶜ ≤ ENNReal.ofReal (r + s) := by
    rw [Measure.bind_apply hA.compl hK.aemeasurable]
    rw [← lintegral_add_compl (fun x => K x Aᶜ) hG]
    calc
      (∫⁻ x in G, K x Aᶜ ∂μ) + ∫⁻ x in Gᶜ, K x Aᶜ ∂μ ≤
          (∫⁻ _x in G, ENNReal.ofReal r ∂μ) + ∫⁻ _x in Gᶜ, 1 ∂μ := by
            apply add_le_add
            · exact setLIntegral_mono' hG hKcompl
            · apply setLIntegral_mono' hG.compl
              intro x _hx
              letI : IsProbabilityMeasure (K x) := hKprob x
              exact prob_le_one
      _ = ENNReal.ofReal r * μ G + μ Gᶜ := by
            simp only [setLIntegral_const, one_mul]
      _ ≤ ENNReal.ofReal r * 1 + ENNReal.ofReal s := by
            exact add_le_add
              (mul_le_mul le_rfl prob_le_one (zero_le _) (zero_le _)) hμcompl
      _ = ENNReal.ofReal (r + s) := by
            rw [mul_one, ENNReal.ofReal_add hr hs]
  letI : IsProbabilityMeasure (μ.bind K) :=
    MeasureTheory.isProbabilityMeasure_bind hK.aemeasurable
      (Filter.Eventually.of_forall hKprob)
  have hbind_compl_real : (μ.bind K).real Aᶜ ≤ r + s := by
    rw [Measure.real_def]
    calc
      (μ.bind K Aᶜ).toReal ≤ (ENNReal.ofReal (r + s)).toReal :=
        ENNReal.toReal_mono (by finiteness) hbind_compl
      _ = r + s := ENNReal.toReal_ofReal (add_nonneg hr hs)
  rw [probReal_compl_eq_one_sub hA] at hbind_compl_real
  linarith

end ttc

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · split the bind integral over the first-step good event and its
  complement
-/

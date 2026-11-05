import Kr25Ssmxt.Analysis.ManuscriptGlobalCoinSource

/-! The manuscript's stored-copy thinning reads fair coins only on labels
already allocated by the current state. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

def allocatedCoinRestriction (nextLabel : Nat)
    (coins : Nat × Nat → Bool) : Nat × Fin nextLabel → Bool :=
  fun index => coins (index.1, index.2.val)

def allocatedCoinExtension (nextLabel : Nat)
    (coins : Nat × Fin nextLabel → Bool) : Nat × Nat → Bool :=
  fun index => if h : index.2 < nextLabel then
    coins (index.1, ⟨index.2, h⟩) else false

theorem measurable_allocatedCoinRestriction (nextLabel : Nat) :
    Measurable (allocatedCoinRestriction nextLabel) :=
  measurable_pi_lambda _ (fun index =>
    measurable_pi_apply (index.1, index.2.val))

theorem measurable_allocatedCoinExtension (nextLabel : Nat) :
    Measurable (allocatedCoinExtension nextLabel) := by
  apply measurable_pi_lambda
  intro index
  by_cases h : index.2 < nextLabel
  · simpa only [allocatedCoinExtension, h, dite_true] using
      (measurable_pi_apply (index.1, (⟨index.2, h⟩ : Fin nextLabel)))
  · simpa only [allocatedCoinExtension, h, dite_false] using
      (measurable_const : Measurable
        (fun _ : Nat × Fin nextLabel → Bool => false))

theorem fairCoinStreamLaw_allocatedCoinRestriction (nextLabel : Nat) :
    fairCoinStreamLaw.map (allocatedCoinRestriction nextLabel) =
      Measure.infinitePi
        (fun _ : Nat × Fin nextLabel => fairCoinLaw) := by
  exact fairCoinStreamLaw_reindex_labels
    (fun label : Fin nextLabel => label.val)
    (fun _ _ h => Fin.ext h)

theorem allocatedCoinExtension_restriction_at
    (nextLabel : Nat) (coins : Nat × Nat → Bool)
    (round label : Nat) (hlabel : label < nextLabel) :
    allocatedCoinExtension nextLabel
      (allocatedCoinRestriction nextLabel coins) (round, label) =
      coins (round, label) := by
  simp [allocatedCoinExtension, allocatedCoinRestriction, hlabel]

theorem samplesAfter_congr_allocated {n : Nat}
    (s : TTCState n) (rounds : Nat) (h : s.LabelsFresh)
    (coins other : Nat × Nat → Bool)
    (hagrees : ∀ round label, label < s.nextLabel →
      coins (round, label) = other (round, label)) :
    samplesAfter coins rounds s.samples =
      samplesAfter other rounds s.samples := by
  ext copy
  by_cases hcopy : copy ∈ s.samples
  · simp only [samplesAfter, Finset.mem_filter, hcopy, true_and]
    unfold survives
    constructor <;> intro hsurv round hround
    · rw [← hagrees round copy.1 (h.1 copy hcopy)]
      exact hsurv round hround
    · rw [hagrees round copy.1 (h.1 copy hcopy)]
      exact hsurv round hround
  · simp [samplesAfter, hcopy]

theorem manuscriptRateThinningResult_congr_allocated {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (h : s.LabelsFresh) (coins other : Nat × Nat → Bool)
    (hagrees : ∀ round label, label < s.nextLabel →
      coins (round, label) = other (round, label)) :
    manuscriptRateThinningResult s intensity threshold coins =
      manuscriptRateThinningResult s intensity threshold other := by
  simp only [manuscriptRateThinningResult,
    samplesAfter_congr_allocated s _ h coins other hagrees]

theorem firstExitRoundSplit_congr_old_allocated {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (h : s.LabelsFresh) (coins other fresh : Nat × Nat → Bool)
    (hagrees : ∀ round label, label < s.nextLabel →
      coins (round, label) = other (round, label)) :
    firstExitRoundSplit s pending threshold coins fresh =
      firstExitRoundSplit s pending threshold other fresh := by
  simp only [firstExitRoundSplit,
    samplesAfter_congr_allocated s _ h coins other hagrees]

theorem thinningResultSplit_congr_old_allocated {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (h : s.LabelsFresh) (coins other fresh : Nat × Nat → Bool)
    (hagrees : ∀ round label, label < s.nextLabel →
      coins (round, label) = other (round, label)) :
    thinningResultSplit s pending threshold coins fresh =
      thinningResultSplit s pending threshold other fresh := by
  simp only [thinningResultSplit,
    firstExitRoundSplit_congr_old_allocated s pending threshold h coins
      other fresh hagrees,
    samplesAfter_congr_allocated s _ h coins other hagrees]

theorem thinningResultSplitFinite_congr_old_allocated {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (h : s.LabelsFresh) (coins other : Nat × Nat → Bool)
    (fresh : Nat × Fin pending → Bool)
    (hagrees : ∀ round label, label < s.nextLabel →
      coins (round, label) = other (round, label)) :
    thinningResultSplitFinite s pending threshold coins fresh =
      thinningResultSplitFinite s pending threshold other fresh := by
  exact thinningResultSplit_congr_old_allocated s pending threshold h
    coins other _ hagrees

end Kr25Ssmxt

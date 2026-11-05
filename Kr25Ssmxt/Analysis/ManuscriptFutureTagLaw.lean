import Kr25Ssmxt.Analysis.ManuscriptOriginMeasurable
import Kr25Ssmxt.Analysis.ManuscriptCoinBlockLaw

/-! A global refreshed fair source gives independent survival decisions to
every finite set of distinct component/original-copy tags. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem globalFairSource_survivalVector_finite
    (tags : Finset (Nat × Nat)) (rounds : Nat) :
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
        (fun future => fun tag : tags =>
          labelSurvives rounds
            (fun r => future (tag.1.1, (r, tag.1.2)))) =
      Measure.pi (fun _ : tags =>
        ProbabilityTheory.bernoulliMeasure true false
          (survivalProbability rounds)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let bitLaw : Measure ((tags × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let streamLaw : Measure (Nat → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let index : tags × Nat → Nat × (Nat × Nat) :=
    fun pair => (pair.1.1.1, (pair.2, pair.1.1.2))
  have hinj : Function.Injective index := by
    intro a b hab
    change (a.1.1.1, (a.2, a.1.1.2)) =
      (b.1.1.1, (b.2, b.1.1.2)) at hab
    simp only [Prod.mk.injEq] at hab
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact hab.1
      · exact hab.2.2
    · exact hab.2.1
  have hbits : sourceLaw.map
      (fun future => fun pair : tags × Nat => future (index pair)) =
      bitLaw := by
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    exact @Measure.map_infinitePi_infinitePi_of_inj
      (Nat × (Nat × Nat)) (tags × Nat) (fun _ => Bool)
      (fun _ => inferInstance) (fun _ => fairCoinLaw)
      (fun _ => fairCoinLaw_isProbabilityMeasure) index hinj
  have hcurry : bitLaw.map (MeasurableEquiv.curry tags Nat Bool) =
      Measure.infinitePi (fun _ : tags => streamLaw) := by
    letI : ∀ _ : tags, ∀ _ : Nat, IsProbabilityMeasure fairCoinLaw :=
      fun _ _ => fairCoinLaw_isProbabilityMeasure
    exact Measure.infinitePi_map_curry
      (hμ := fun _ _ => fairCoinLaw_isProbabilityMeasure)
      (fun _ : tags => fun _ : Nat => fairCoinLaw)
  let survive : (tags → Nat → Bool) → tags → Bool :=
    fun streams tag => labelSurvives rounds (streams tag)
  have hsurvive : Measurable survive :=
    measurable_pi_lambda _ (fun tag =>
      (measurable_labelSurvives rounds).comp (measurable_pi_apply tag))
  have hprob : ∀ _ : tags, IsProbabilityMeasure streamLaw := by
    intro tag
    dsimp [streamLaw]
    letI : ∀ _ : Nat, IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  have hmap :
      (Measure.infinitePi (fun _ : tags => streamLaw)).map survive =
      Measure.pi (fun _ : tags =>
        streamLaw.map (labelSurvives rounds)) := by
    have hdecisionProb : ∀ _ : tags, IsProbabilityMeasure
        (streamLaw.map (labelSurvives rounds)) := by
      intro tag
      rw [labelStreamLaw_survivalProbability]
      infer_instance
    calc
      _ = Measure.infinitePi
          (fun _ : tags => streamLaw.map (labelSurvives rounds)) := by
            exact Measure.infinitePi_map_pi
              (hμ := hprob)
              (fun _ : tags => streamLaw)
              (fun _ : tags => measurable_labelSurvives rounds)
      _ = _ := Measure.infinitePi_eq_pi
        (hμ := hdecisionProb)
        (fun _ : tags => streamLaw.map (labelSurvives rounds))
  calc
    sourceLaw.map (fun future => fun tag : tags =>
        labelSurvives rounds
          (fun r => future (tag.1.1, (r, tag.1.2)))) =
      (sourceLaw.map (fun future => fun pair : tags × Nat =>
        future (index pair))).map
          (survive ∘ MeasurableEquiv.curry tags Nat Bool) := by
            rw [Measure.map_map
              (hsurvive.comp (MeasurableEquiv.curry tags Nat Bool).measurable)
              (measurable_pi_lambda _ (fun pair =>
                measurable_pi_apply (index pair)))]
            rfl
    _ = (bitLaw.map (MeasurableEquiv.curry tags Nat Bool)).map survive := by
      rw [hbits, Measure.map_map hsurvive
        (MeasurableEquiv.curry tags Nat Bool).measurable]
    _ = (Measure.infinitePi (fun _ : tags => streamLaw)).map survive := by
      rw [hcurry]
    _ = Measure.pi (fun _ : tags => streamLaw.map
        (labelSurvives rounds)) := hmap
    _ = _ := by
      congr 1
      funext tag
      exact labelStreamLaw_survivalProbability rounds

noncomputable def manuscriptFutureTagPointCounts
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (S : Finset (LatticePoint n))
    (bits : c.source.valid → Bool) : S → Nat := by
  classical
  exact fun x : S =>
    (c.source.valid.filter fun tag =>
      Kr25Ssmxt.survives (c.source.coins tag.1) c.level tag.2 ∧
      (if h : tag ∈ c.source.valid then bits ⟨tag, h⟩ else false) = true ∧
      c.source.marks tag = x.1).card

/-- Conditional on an incoming configuration, refreshed old counts at any
future level are obtained by independent Bernoulli decisions on its finite
set of valid source tags. -/
theorem ManuscriptOriginConfiguration.refreshLaw_future_pointCounts_bernoulli
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (observedLevel : Nat) (hle : c.level ≤ observedLevel)
    (S : Finset (LatticePoint n)) :
    c.refreshLaw.map
      (fun next => next.source.pointCounts observedLevel S) =
    (Measure.pi (fun _ : c.source.valid =>
      ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability (observedLevel - c.level)))).map
      (manuscriptFutureTagPointCounts c S) := by
  classical
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let decision : (Nat × (Nat × Nat) → Bool) → c.source.valid → Bool :=
    fun future tag => labelSurvives (observedLevel - c.level)
      (fun r => future (tag.1.1, (r, tag.1.2)))
  have hdecision : Measurable decision := by
    exact measurable_pi_lambda _ (fun tag =>
      (measurable_labelSurvives (observedLevel - c.level)).comp
        (measurable_pi_lambda _ (fun r =>
          measurable_pi_apply (tag.1.1, (r, tag.1.2)))))
  have hcount : Measurable (manuscriptFutureTagPointCounts c S) :=
    Measurable.of_discrete
  have hpath (future : Nat × (Nat × Nat) → Bool) :
      manuscriptRefreshedFuturePointCounts c future observedLevel S =
      manuscriptFutureTagPointCounts c S (decision future) := by
    funext x
    change (c.source.valid.filter fun tag : Nat × Nat =>
        Kr25Ssmxt.survives (c.source.coins tag.1) c.level tag.2 ∧
        Kr25Ssmxt.survives (fun pair => future (tag.1, pair))
          (observedLevel - c.level) tag.2 ∧
        c.source.marks tag = x.1).card =
      (c.source.valid.filter fun tag : Nat × Nat =>
        Kr25Ssmxt.survives (c.source.coins tag.1) c.level tag.2 ∧
        (if h : tag ∈ c.source.valid then decision future ⟨tag, h⟩
          else false) = true ∧ c.source.marks tag = x.1).card
    apply congrArg Finset.card
    ext tag
    simp only [Finset.mem_filter]
    by_cases htag : tag ∈ c.source.valid
    · simp only [htag, dite_true, true_and]
      simp [decision, labelSurvives, Kr25Ssmxt.survives]
    · simp [htag]
  rw [c.refreshLaw_map_future_pointCounts observedLevel hle S]
  have hfunctions :
      (fun future =>
        manuscriptRefreshedFuturePointCounts c future observedLevel S) =
      (manuscriptFutureTagPointCounts c S) ∘ decision := funext hpath
  rw [hfunctions, ← Measure.map_map hcount hdecision]
  rw [globalFairSource_survivalVector_finite c.source.valid
    (observedLevel - c.level)]

end Kr25Ssmxt

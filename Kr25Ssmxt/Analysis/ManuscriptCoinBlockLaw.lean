import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.FairThinningExpectation
import Kr25Ssmxt.Analysis.ManuscriptLabelFreshness

/-! Reindex the manuscript's fair coin stream by copy label. Distinct labels
then receive independent infinite streams of round coins. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem fairCoinStreamLaw_swap :
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
      fun p : Nat × Nat => coins (p.2, p.1)) = fairCoinStreamLaw := by
  letI : ∀ _ : Nat × Nat, IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  unfold fairCoinStreamLaw
  have hswap := Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : Nat × Nat => fairCoinLaw)
    (hμ := fun _ => fairCoinLaw_isProbabilityMeasure)
    (Equiv.prodComm Nat Nat)
  convert hswap using 1
  congr 1

theorem fairCoinStreamLaw_byLabel :
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
      fun label round => coins (round, label)) =
    Measure.infinitePi (fun _ : Nat =>
      Measure.infinitePi (fun _ : Nat => fairCoinLaw)) := by
  letI : ∀ _ : Nat × Nat, IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : ∀ _ : Nat, ∀ _ : Nat, IsProbabilityMeasure fairCoinLaw :=
    fun _ _ => fairCoinLaw_isProbabilityMeasure
  calc
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
        fun label round => coins (round, label)) =
      (fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
        fun p : Nat × Nat => coins (p.2, p.1))).map
          (MeasurableEquiv.curry Nat Nat Bool) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
    _ = fairCoinStreamLaw.map (MeasurableEquiv.curry Nat Nat Bool) := by
      rw [fairCoinStreamLaw_swap]
    _ = _ := by
      unfold fairCoinStreamLaw
      exact Measure.infinitePi_map_curry
        (hμ := fun _ _ => fairCoinLaw_isProbabilityMeasure)
        (fun _ : Nat => fun _ : Nat => fairCoinLaw)

def labelSurvives (rounds : Nat) (stream : Nat → Bool) : Bool :=
  if ∀ r < rounds, stream r = true then true else false

noncomputable def survivalProbability (rounds : Nat) : unitInterval :=
  ⟨(((1 / 2 : NNReal) ^ rounds) : Real), ⟨by positivity,
    by exact_mod_cast (pow_le_one₀
      (by norm_num : (0 : NNReal) ≤ 1 / 2)
      (by norm_num : (1 / 2 : NNReal) ≤ 1))⟩⟩

theorem measurable_labelSurvives (rounds : Nat) :
    Measurable (labelSurvives rounds) := by
  classical
  have hset : MeasurableSet {stream : Nat → Bool |
      ∀ r < rounds, stream r = true} := by
    have h : MeasurableSet
        (⋂ r ∈ Finset.range rounds, {stream : Nat → Bool | stream r = true}) := by
      apply MeasurableSet.biInter (Finset.countable_toSet _)
      intro r hr
      measurability
    convert h using 1
    ext stream
    simp [Finset.mem_range]
  unfold labelSurvives
  exact measurable_const.ite hset measurable_const

theorem labelStreamLaw_survivalProbability (rounds : Nat) :
    (Measure.infinitePi (fun _ : Nat => fairCoinLaw)).map
      (labelSurvives rounds) =
      ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability rounds) := by
  letI : ∀ _ : Nat, IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  have htrue : (Measure.infinitePi (fun _ : Nat => fairCoinLaw))
      {stream | labelSurvives rounds stream = true} =
      (1 / 2 : ENNReal) ^ rounds := by
    have hset : {stream : Nat → Bool | labelSurvives rounds stream = true} =
        Set.pi (Finset.range rounds : Set Nat) (fun _ => {true}) := by
      ext stream
      simp [labelSurvives, Set.mem_pi, Finset.mem_range]
    rw [hset, Measure.infinitePi_pi
      (μ := fun _ : Nat => fairCoinLaw)
      (hμ := fun _ => fairCoinLaw_isProbabilityMeasure)
      (s := Finset.range rounds) (t := fun _ => {true})
      (by intros; measurability)]
    simp [fairCoinLaw_true]
  have hbernoulli :
      ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability rounds) {true} =
      (1 / 2 : ENNReal) ^ rounds := by
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem
      (survivalProbability rounds) (by measurability) (by simp) (by simp)]
    change (((1 / 2 : NNReal) ^ rounds : NNReal) : ENNReal) =
      (1 / 2 : ENNReal) ^ rounds
    norm_num [ENNReal.coe_pow]
  have hleft : IsProbabilityMeasure
      ((Measure.infinitePi (fun _ : Nat => fairCoinLaw)).map
        (labelSurvives rounds)) :=
    Measure.isProbabilityMeasure_map (measurable_labelSurvives rounds).aemeasurable
  have hright : IsProbabilityMeasure
      (ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability rounds)) := inferInstance
  letI := hleft
  letI := hright
  have htrueEq :
      ((Measure.infinitePi (fun _ : Nat => fairCoinLaw)).map
        (labelSurvives rounds)) {true} =
      ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability rounds) {true} := by
    rw [Measure.map_apply (measurable_labelSurvives rounds) (by measurability)]
    exact htrue.trans hbernoulli.symm
  apply Measure.ext_of_singleton
  intro b
  cases b
  · have hcompl : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by ext x; cases x <;> simp
    rw [hcompl, prob_compl_eq_one_sub (by measurability),
      prob_compl_eq_one_sub (by measurability)]
    rw [htrueEq]
  · exact htrueEq

/-- Survival decisions for distinct labels are independent because their
round streams are separate coordinates of the product measure. -/
theorem fairCoinStreamLaw_survivalVector (rounds : Nat) :
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
      fun label => labelSurvives rounds (fun r => coins (r, label))) =
    Measure.infinitePi (fun _ : Nat =>
      (Measure.infinitePi (fun _ : Nat => fairCoinLaw)).map
        (labelSurvives rounds)) := by
  have hblock := fairCoinStreamLaw_byLabel
  let streamLaw : Measure (Nat → Bool) :=
    Measure.infinitePi (fun _ : Nat => fairCoinLaw)
  letI : ∀ _ : Nat, IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  haveI : ∀ _ : Nat, IsProbabilityMeasure streamLaw := by
    intro label
    dsimp only [streamLaw]
    exact inferInstance
  calc
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
        fun label => labelSurvives rounds (fun r => coins (r, label))) =
      (fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
        fun label round => coins (round, label))).map
          (fun streams label => labelSurvives rounds (streams label)) := by
        have hdecision : Measurable (fun streams : Nat → Nat → Bool =>
            fun label => labelSurvives rounds (streams label)) :=
          Measurable.of_eval (fun label =>
            (measurable_labelSurvives rounds).comp (measurable_pi_apply label))
        rw [Measure.map_map hdecision (by fun_prop)]
        rfl
    _ = (Measure.infinitePi (fun _ : Nat => streamLaw)).map
          (fun streams label => labelSurvives rounds (streams label)) := by
      rw [hblock]
    _ = _ := by
      exact Measure.infinitePi_map_pi
        (μ := fun _ : Nat => streamLaw)
        (hμ := fun _ => inferInstance)
        (fun _ : Nat => measurable_labelSurvives rounds)

theorem fairCoinStreamLaw_survivalVector_finite
    (rounds : Nat) (labels : Finset Nat) :
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
      fun label : labels => labelSurvives rounds
        (fun r => coins (r, label.1))) =
    Measure.pi (fun _ : labels =>
      ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability rounds)) := by
  let vector : (Nat × Nat → Bool) → Nat → Bool :=
    fun coins label => labelSurvives rounds (fun r => coins (r, label))
  have hmap : Measurable vector := by
    unfold vector
    exact Measurable.of_eval (fun label =>
      (measurable_labelSurvives rounds).comp
        (Measurable.of_eval (fun r => measurable_pi_apply (r, label))))
  change fairCoinStreamLaw.map (labels.restrict ∘ vector) = _
  rw [← Measure.map_map (Finset.measurable_restrict labels) hmap,
    fairCoinStreamLaw_survivalVector]
  have hprob : ∀ _ : Nat, IsProbabilityMeasure
      ((Measure.infinitePi (fun _ : Nat => fairCoinLaw)).map
        (labelSurvives rounds)) := by
    intro label
    rw [labelStreamLaw_survivalProbability]
    infer_instance
  rw [Measure.infinitePi_map_restrict (hμ := hprob)]
  congr 1
  funext label
  exact labelStreamLaw_survivalProbability rounds

/-- At a fixed round, the actual stored-plus-pending population is the count
of independent survival decisions on its distinct copy labels. -/
theorem TTCState.fixed_round_population_law {n : Nat} (s : TTCState n)
    (pending rounds : Nat) (h : s.LabelsFresh) :
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
      (samplesAfter coins rounds s.samples).card +
        pendingAfter coins rounds s.nextLabel pending) =
    (Measure.pi (fun _ : {label : Nat // label ∈
        (s.samples.image Prod.fst) ∪
          ((Finset.range pending).image (fun i => s.nextLabel + i))} =>
      ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability rounds))).map
      (fun decisions => (Finset.univ.filter (fun label => decisions label = true)).card) := by
  classical
  let labels : Finset Nat := (s.samples.image Prod.fst) ∪
    ((Finset.range pending).image (fun i => s.nextLabel + i))
  let decisions : (Nat × Nat → Bool) → (labels → Bool) :=
    fun coins label => labelSurvives rounds (fun r => coins (r, label.1))
  have hdecisions : Measurable decisions := by
    unfold decisions
    exact Measurable.of_eval (fun label =>
      (measurable_labelSurvives rounds).comp
        (Measurable.of_eval (fun r => measurable_pi_apply (r, label.1))))
  have hcount : Measurable (fun bits : labels → Bool =>
      (Finset.univ.filter (fun label => bits label = true)).card) := by
    fun_prop
  have hpoint (coins : Nat × Nat → Bool) :
      (samplesAfter coins rounds s.samples).card +
        pendingAfter coins rounds s.nextLabel pending =
      (Finset.univ.filter (fun label : labels => decisions coins label = true)).card := by
    rw [s.thinningPopulation_eq_filter_labels pending rounds coins h]
    change (labels.filter (fun label => survives coins rounds label)).card = _
    have hfilter : (Finset.univ.filter (fun label : labels =>
        decisions coins label = true)) =
        labels.attach.filter (fun label => survives coins rounds label.1) := by
      ext label
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_attach, true_and]
      simp [decisions, labelSurvives, survives]
    rw [hfilter]
    have hattach := congrArg Finset.card
      (Finset.filter_attach (p := fun label => survives coins rounds label) labels)
    simpa only [Finset.card_map, Finset.card_attach] using hattach.symm
  calc
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
        (samplesAfter coins rounds s.samples).card +
          pendingAfter coins rounds s.nextLabel pending) =
      fairCoinStreamLaw.map (fun coins =>
        (Finset.univ.filter (fun label : labels => decisions coins label = true)).card) := by
      congr 1
      funext coins
      exact hpoint coins
    _ = (fairCoinStreamLaw.map decisions).map
        (fun bits => (Finset.univ.filter (fun label => bits label = true)).card) := by
      rw [Measure.map_map hcount hdecisions]
      rfl
    _ = _ := by
      rw [fairCoinStreamLaw_survivalVector_finite rounds labels]

end Kr25Ssmxt

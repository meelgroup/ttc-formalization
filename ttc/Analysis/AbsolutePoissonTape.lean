import ttc.Analysis.MathlibCompat
import ttc.Analysis.TapeCoupling

/-! One component's level-zero Poisson copies, absolute-level survival coins,
and permanent point marks form a source that can be evaluated at every dyadic
level. -/

namespace ttc

open Classical MeasureTheory

abbrev PoissonTape (n : Nat) :=
  Nat × (Nat × Nat → Bool) × (Nat → LatticePoint n)

noncomputable def poissonTapePointCounts
    {n : Nat} (S : Finset (LatticePoint n))
    (firstLabel level : Nat) (source : PoissonTape n) : S → Nat :=
  fun x => ((Finset.range source.1).filter (fun i =>
    survives source.2.1 level (firstLabel + i) ∧
      source.2.2 (firstLabel + i) = x.1)).card

theorem poissonTapePointCounts_eq_selected
    {n : Nat} (S : Finset (LatticePoint n))
    (firstLabel level pending : Nat)
    (coins : Nat × Nat → Bool) (tape : Nat → LatticePoint n) :
    poissonTapePointCounts S firstLabel level
      (pending, coins, tape) =
    fun x : S => Arlib.Probability.colourCount
      (fun (i : Fin (pendingAfter coins level firstLabel pending)) =>
        tape (firstLabel +
          (pendingSurvivorIndices coins level firstLabel pending).orderEmbOfFin
            (pendingSurvivorIndices_card coins level firstLabel pending) i)) x.1 := by
  funext x
  exact (colourCount_pendingSurvivors_eq_filter tape coins level firstLabel
    pending x.1).symm

theorem measurable_poissonTapePointCounts
    {n : Nat} (S : Finset (LatticePoint n))
    (firstLabel level : Nat) :
    Measurable (poissonTapePointCounts S firstLabel level) := by
  apply Measurable.of_eval
  intro x
  apply measurable_from_prod_countable_right
  intro pending
  let predicate : ((Nat × Nat → Bool) × (Nat → LatticePoint n)) → Nat → Prop :=
    fun z i => survives z.1 level (firstLabel + i) ∧
      z.2 (firstLabel + i) = x.1
  have hpred (i : Nat) : MeasurableSet {z | predicate z i} := by
    have hsurv : MeasurableSet
        {z : (Nat × Nat → Bool) × (Nat → LatticePoint n) |
          survives z.1 level (firstLabel + i)} :=
      (measurableSet_survives level (firstLabel + i)).preimage measurable_fst
    have hmark : MeasurableSet
        {z : (Nat × Nat → Bool) × (Nat → LatticePoint n) |
          z.2 (firstLabel + i) = x.1} := by
      change MeasurableSet
        (((fun z : (Nat × Nat → Bool) × (Nat → LatticePoint n) =>
          z.2 (firstLabel + i)) ⁻¹' {x.1}))
      exact (measurableSet_singleton x.1).preimage
        ((measurable_pi_apply (firstLabel + i)).comp measurable_snd)
    exact hsurv.inter hmark
  have hfilter : Measurable (fun z :
      (Nat × Nat → Bool) × (Nat → LatticePoint n) =>
      (Finset.range pending).filter (predicate z)) := by
    rw [measurable_finset_iff]
    intro i
    apply measurable_to_prop
    by_cases hi : i ∈ Finset.range pending
    · simpa [hi, predicate] using hpred i
    · simp [hi]
  have hcard : Measurable (fun T : Finset Nat => T.card) :=
    measurable_of_countable _
  simpa only [poissonTapePointCounts, Function.comp_def] using
    hcard.comp hfilter

noncomputable def poissonTapeLaw
    {n : Nat} (mean : NNReal) (pointLaw : Measure (LatticePoint n)) :
    Measure (PoissonTape n) :=
  (ProbabilityTheory.poissonMeasure mean).bind fun pending =>
    fairCoinStreamLaw.bind fun coins =>
      (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
        (pending, coins, tape)

theorem poissonTapeLaw_isProbabilityMeasure
    {n : Nat} (mean : NNReal)
    (pointLaw : Measure (LatticePoint n)) [IsProbabilityMeasure pointLaw] :
    IsProbabilityMeasure (poissonTapeLaw mean pointLaw) := by
  let tapeLaw : Measure (Nat → LatticePoint n) :=
    Measure.infinitePi (fun _ : Nat => pointLaw)
  letI : IsProbabilityMeasure tapeLaw := inferInstance
  let K₂ (pending : Nat) (coins : Nat × Nat → Bool) :
      Measure (PoissonTape n) :=
    tapeLaw.map fun tape => (pending, coins, tape)
  have hK₂ (pending : Nat) : Measurable (K₂ pending) := by
    apply measurable_parametric_probability_map
      (fun _ : Nat × Nat → Bool => tapeLaw) measurable_const
      (fun _ => inferInstance)
      (fun z : (Nat × Nat → Bool) × (Nat → LatticePoint n) =>
        (pending, z.1, z.2))
      (by fun_prop)
  have hK₂prob (pending : Nat) (coins : Nat × Nat → Bool) :
      IsProbabilityMeasure (K₂ pending coins) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let K₁ : Nat → Measure (PoissonTape n) := fun pending =>
    fairCoinStreamLaw.bind (K₂ pending)
  have hK₁ : Measurable K₁ := Measurable.of_discrete
  have hK₁prob (pending : Nat) : IsProbabilityMeasure (K₁ pending) := by
    letI : IsProbabilityMeasure fairCoinStreamLaw :=
      fairCoinStreamLaw_isProbabilityMeasure
    exact isProbabilityMeasure_bind (hK₂ pending).aemeasurable
      (Filter.Eventually.of_forall (hK₂prob pending))
  change IsProbabilityMeasure
    ((ProbabilityTheory.poissonMeasure mean).bind K₁)
  letI : IsProbabilityMeasure (ProbabilityTheory.poissonMeasure mean) := inferInstance
  exact isProbabilityMeasure_bind hK₁.aemeasurable
    (Filter.Eventually.of_forall hK₁prob)

theorem poissonTapeLaw_fixedLevel_pointCounts
    {n : Nat} (mean : NNReal)
    (pointLaw : Measure (LatticePoint n)) [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n))
    (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (firstLabel level : Nat) :
    (poissonTapeLaw mean pointLaw).map
      (poissonTapePointCounts S firstLabel level) =
    Measure.pi (fun x : S =>
      ProbabilityTheory.poissonMeasure (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) * mean : NNReal) : Real)))) := by
  let tapeLaw : Measure (Nat → LatticePoint n) :=
    Measure.infinitePi (fun _ : Nat => pointLaw)
  letI : IsProbabilityMeasure tapeLaw := inferInstance
  let output := poissonTapePointCounts S firstLabel level
  have hout : Measurable output :=
    measurable_poissonTapePointCounts S firstLabel level
  let K₂ (pending : Nat) (coins : Nat × Nat → Bool) :
      Measure (PoissonTape n) :=
    tapeLaw.map fun tape => (pending, coins, tape)
  have hK₂ (pending : Nat) : Measurable (K₂ pending) := by
    apply measurable_parametric_probability_map
      (fun _ : Nat × Nat → Bool => tapeLaw) measurable_const
      (fun _ => inferInstance)
      (fun z : (Nat × Nat → Bool) × (Nat → LatticePoint n) =>
        (pending, z.1, z.2))
      (by fun_prop)
  let K₁ : Nat → Measure (PoissonTape n) := fun pending =>
    fairCoinStreamLaw.bind (K₂ pending)
  have hK₁ : Measurable K₁ := Measurable.of_discrete
  change ((ProbabilityTheory.poissonMeasure mean).bind K₁).map output = _
  rw [map_bind_measure (ProbabilityTheory.poissonMeasure mean) K₁ output
    hK₁.aemeasurable hout]
  have hinner (pending : Nat) :
      (K₁ pending).map output =
        fairCoinStreamLaw.bind fun coins =>
          tapeLaw.map fun tape => output (pending, coins, tape) := by
    change (fairCoinStreamLaw.bind (K₂ pending)).map output = _
    rw [map_bind_measure fairCoinStreamLaw (K₂ pending) output
      (hK₂ pending).aemeasurable hout]
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro coins
    change (tapeLaw.map (fun tape => (pending, coins, tape))).map output = _
    rw [Measure.map_map hout (by fun_prop)]
    rfl
  simp_rw [hinner]
  dsimp only [output]
  simp_rw [poissonTapePointCounts_eq_selected]
  exact fixed_round_marked_poisson_tape_law pointLaw S hsupport
    mean firstLabel level

/-- Independent component source tapes retain their joint product Poisson
point-count law at each fixed dyadic level. The source product is the same
measure for every level. -/
theorem poissonTape_product_fixedLevel_pointCounts
    {n m : Nat} (mean : Fin m → NNReal)
    (pointLaw : Fin m → Measure (LatticePoint n))
    (hprob : ∀ i, IsProbabilityMeasure (pointLaw i))
    (S : Finset (LatticePoint n))
    (hsupport : ∀ i, (pointLaw i) (S : Set (LatticePoint n))ᶜ = 0)
    (firstLabel : Fin m → Nat) (level : Nat) :
    (Measure.pi (fun i : Fin m =>
      poissonTapeLaw (mean i) (pointLaw i))).map
        (fun sources i => poissonTapePointCounts S
          (firstLabel i) level (sources i)) =
      Measure.pi (fun i : Fin m =>
        Measure.pi (fun x : S =>
          ProbabilityTheory.poissonMeasure (Real.toNNReal
            ((pointLaw i).real {(x : LatticePoint n)} *
              ((unitInterval.toNNReal (survivalProbability level) *
                mean i : NNReal) : Real))))) := by
  letI : ∀ i : Fin m, IsProbabilityMeasure (pointLaw i) := hprob
  have hsource (i : Fin m) : IsProbabilityMeasure
      (poissonTapeLaw (mean i) (pointLaw i)) :=
    poissonTapeLaw_isProbabilityMeasure (mean i) (pointLaw i)
  letI : ∀ i : Fin m, IsProbabilityMeasure
      (poissonTapeLaw (mean i) (pointLaw i)) := hsource
  have hmap (i : Fin m) : IsProbabilityMeasure
      ((poissonTapeLaw (mean i) (pointLaw i)).map
        (poissonTapePointCounts S (firstLabel i) level)) :=
    Measure.isProbabilityMeasure_map
      (measurable_poissonTapePointCounts S (firstLabel i) level).aemeasurable
  letI : ∀ i : Fin m, SigmaFinite
      ((poissonTapeLaw (mean i) (pointLaw i)).map
        (poissonTapePointCounts S (firstLabel i) level)) :=
    fun i => by letI := hmap i; infer_instance
  rw [Measure.pi_map_pi (fun i =>
    (measurable_poissonTapePointCounts S
      (firstLabel i) level).aemeasurable)]
  congr 1
  funext i
  exact poissonTapeLaw_fixedLevel_pointCounts (mean i)
    (pointLaw i) S (hsupport i) (firstLabel i) level

end ttc

import Kr25Ssmxt.Analysis.ManuscriptPoissonVectorRestriction

/-! Deleting all copies at a finite set of lattice points is coordinatewise
zeroing of an independent Poisson vector. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem poissonMeasure_zero_eq_dirac :
    ProbabilityTheory.poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro k
  rw [ProbabilityTheory.poissonMeasure_singleton]
  by_cases hk : k = 0
  · subst k
    norm_num
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    simp [hk, zero_pow hk]

/-- Zeroing point counts in the incoming component preserves independence
and sets precisely those Poisson rates to zero. -/
theorem poisson_vector_zero_on
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (T : Finset ι) (r : ι → NNReal) :
    (Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (r i))).map
      (fun counts : ι → Nat =>
        fun i => if i ∈ T then 0 else counts i) =
    Measure.pi (fun i : ι =>
      ProbabilityTheory.poissonMeasure (if i ∈ T then 0 else r i)) := by
  classical
  calc
    (Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (r i))).map
        (fun counts : ι → Nat =>
          fun i => if i ∈ T then 0 else counts i) =
      Measure.pi (fun i : ι =>
        (ProbabilityTheory.poissonMeasure (r i)).map
          (fun count => if i ∈ T then 0 else count)) := by
            exact Measure.pi_map_pi
              (f := fun i : ι => fun count : Nat =>
                if i ∈ T then 0 else count)
              (fun i => (by fun_prop : Measurable
                (fun count : Nat => if i ∈ T then 0 else count)).aemeasurable)
    _ = _ := by
      congr 1
      funext i
      by_cases hi : i ∈ T
      · simp [hi, Measure.map_const, poissonMeasure_zero_eq_dirac]
      · simp [hi]

/-- Delete the incoming component from an old independent Poisson vector,
then add an independent new vector. The resulting point rates are the new
rates plus the old rates outside the deleted set. -/
theorem poisson_vector_delete_then_add
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (T : Finset ι) (r t : ι → NNReal) :
    ((Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (r i))).prod
      (Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (t i)))).map
        (fun pair : (ι → Nat) × (ι → Nat) =>
          fun i => (if i ∈ T then 0 else pair.1 i) + pair.2 i) =
      Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure
        ((if i ∈ T then 0 else r i) + t i)) := by
  classical
  let old : Measure (ι → Nat) :=
    Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (r i))
  let fresh : Measure (ι → Nat) :=
    Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (t i))
  let erase : (ι → Nat) → (ι → Nat) :=
    fun counts i => if i ∈ T then 0 else counts i
  let add : ((ι → Nat) × (ι → Nat)) → (ι → Nat) :=
    fun pair i => pair.1 i + pair.2 i
  have herase : Measurable erase := by unfold erase; fun_prop
  have hadd : Measurable add := by unfold add; fun_prop
  have hmap : Measurable (Prod.map erase (id : (ι → Nat) → (ι → Nat))) :=
    herase.prodMap measurable_id
  change (old.prod fresh).map
    (add ∘ Prod.map erase (id : (ι → Nat) → (ι → Nat))) = _
  calc
    (old.prod fresh).map
        (add ∘ Prod.map erase (id : (ι → Nat) → (ι → Nat))) =
      ((old.prod fresh).map
        (Prod.map erase (id : (ι → Nat) → (ι → Nat)))).map add := by
        rw [Measure.map_map hadd hmap]
    _ = ((old.map erase).prod fresh).map add := by
      have hprod := Measure.map_prod_map old fresh herase measurable_id
      simp only [Measure.map_id] at hprod
      rw [hprod]
    _ = ((Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure
          (if i ∈ T then 0 else r i))).prod fresh).map add := by
      rw [show old.map erase = Measure.pi (fun i : ι =>
        ProbabilityTheory.poissonMeasure (if i ∈ T then 0 else r i)) from
        poisson_vector_zero_on ι T r]
    _ = _ := by
      exact poisson_vector_pointwise_sum ι
        (fun i => if i ∈ T then 0 else r i) t

/-- One fixed-level component update: delete overlap from an old independent
Poisson point-count vector, thin the incoming Poisson pending count by the
program's labelled coins, draw iid points, and append their counts. -/
theorem manuscript_fixed_round_component_poisson_update
    {X : Type*} [Countable X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (S : Finset X) (hsupport : pointLaw (S : Set X)ᶜ = 0)
    (T : Finset S) (oldRate : S → NNReal)
    (mean : NNReal) (firstLabel rounds : Nat) :
    ((Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure (oldRate x))).prod
      ((ProbabilityTheory.poissonMeasure mean).bind fun pending =>
        (fairCoinStreamLaw.map (fun coins =>
          pendingAfter coins rounds firstLabel pending)).bind fun count =>
          (Measure.pi (fun _ : Fin count => pointLaw)).map
            (fun batch (x : S) => Arlib.Probability.colourCount batch x.1))).map
        (fun pair : (S → Nat) × (S → Nat) =>
          fun x => (if x ∈ T then 0 else pair.1 x) + pair.2 x) =
      Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
        ((if x ∈ T then 0 else oldRate x) +
          Real.toNNReal (pointLaw.real {(x : X)} *
            ((unitInterval.toNNReal (survivalProbability rounds) * mean : NNReal) : Real)))) := by
  classical
  rw [manuscript_fixed_round_marked_poisson_law pointLaw S hsupport
    mean firstLabel rounds]
  exact poisson_vector_delete_then_add S T oldRate
    (fun x => Real.toNNReal (pointLaw.real {(x : X)} *
      ((unitInterval.toNNReal (survivalProbability rounds) * mean : NNReal) : Real)))

end Kr25Ssmxt

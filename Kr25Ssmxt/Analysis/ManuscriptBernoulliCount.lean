import Kr25Ssmxt.Analysis.ManuscriptCoinBlockLaw
import Kr25Ssmxt.Analysis.ManuscriptMarkingMeasure
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-! A finite independent Bernoulli vector, viewed as its set of true
coordinates, has the set-Bernoulli law. This will identify fixed-round
survivor counts with a binomial law. -/

namespace Kr25Ssmxt

open MeasureTheory
open scoped ProbabilityTheory

theorem finite_bernoulli_vector_set_law
    (ι : Type*) [Fintype ι] [DecidableEq ι] (p : unitInterval) :
    (Measure.pi (fun _ : ι =>
      ProbabilityTheory.bernoulliMeasure true false p)).map
        (fun bits : ι → Bool => {i | bits i = true}) =
      ProbabilityTheory.setBernoulli Set.univ p := by
  classical
  let toSet : (ι → Bool) → Set ι := fun bits => {i | bits i = true}
  have htoSet : Measurable toSet := by
    unfold toSet
    exact measurable_setOfPred.comp (by fun_prop)
  change (Measure.pi (fun _ : ι =>
    ProbabilityTheory.bernoulliMeasure true false p)).map toSet = _
  apply Measure.ext_of_singleton
  intro A
  have hpre : toSet ⁻¹' {A} =
      {fun i : ι => decide (i ∈ A)} := by
    ext bits
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext i
      have hi := congrArg (fun S : Set ι => i ∈ S) h
      change (bits i = true) = (i ∈ A) at hi
      by_cases hA : i ∈ A <;> cases hb : bits i <;> simp_all
    · intro h
      ext i
      have hi := congrFun h i
      by_cases hA : i ∈ A <;> cases hb : bits i <;> simp_all [toSet]
  rw [Measure.map_apply htoSet (by measurability), hpre,
    Measure.pi_singleton,
    ProbabilityTheory.setBernoulli_singleton p (Set.subset_univ A)
      Set.finite_univ]
  have hsingle (i : ι) :
      ProbabilityTheory.bernoulliMeasure true false p
        {decide (i ∈ A)} =
      if i ∈ A then (unitInterval.toNNReal p : ENNReal)
      else (unitInterval.toNNReal (unitInterval.symm p) : ENNReal) := by
    by_cases hi : i ∈ A <;> simp [hi, ProbabilityTheory.bernoulliMeasure_def]
  simp_rw [hsingle]
  rw [Finset.prod_ite]
  have hA : (Finset.univ.filter (fun i : ι => i ∈ A)).card = A.ncard := by
    simp [Set.ncard_eq_toFinset_card']
  have hAc : (Finset.univ.filter (fun i : ι => i ∉ A)).card =
      (Set.univ \ A).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext i
    simp
  simp only [Finset.prod_const]
  rw [hA, hAc]

/-- The number of true coordinates in a finite independent Bernoulli vector
has the binomial law, for any finite index type. -/
theorem finite_bernoulli_count_law
    (ι : Type*) [Fintype ι] [DecidableEq ι] (p : unitInterval) :
    (Measure.pi (fun _ : ι =>
      ProbabilityTheory.bernoulliMeasure true false p)).map
        (fun bits : ι → Bool =>
          (Finset.univ.filter (fun i => bits i = true)).card) =
      ProbabilityTheory.binomial (Fintype.card ι) p := by
  classical
  let μ : Measure (ι → Bool) := Measure.pi (fun _ : ι =>
    ProbabilityTheory.bernoulliMeasure true false p)
  let toSet : (ι → Bool) → Set ι := fun bits => {i | bits i = true}
  have htoSet : Measurable toSet := by
    unfold toSet
    exact measurable_setOfPred.comp (by fun_prop)
  have hcount (bits : ι → Bool) :
      (Finset.univ.filter (fun i => bits i = true)).card =
        (toSet bits).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext i
    simp [toSet]
  change μ.map (fun bits : ι → Bool =>
    (Finset.univ.filter (fun i => bits i = true)).card) = _
  calc
    μ.map (fun bits : ι → Bool =>
        (Finset.univ.filter (fun i => bits i = true)).card) =
      μ.map (Set.ncard ∘ toSet) := by
        congr 1
        funext bits
        exact hcount bits
    _ = (μ.map toSet).map Set.ncard := by
      rw [Measure.map_map measurable_ncard htoSet]
    _ = (ProbabilityTheory.setBernoulli Set.univ p).map Set.ncard := by
      rw [finite_bernoulli_vector_set_law]
    _ = ProbabilityTheory.binomial (Fintype.card ι) p := by
      apply Measure.ext_of_singleton
      intro k
      rw [ProbabilityTheory.map_ncard_setBernoulli_singleton Set.finite_univ p k,
        ProbabilityTheory.binomial_singleton]
      simp [Set.ncard_univ, Nat.card_eq_fintype_card]

/-- Before the adaptive stopping test, a fixed-round population of actual
stored and pending copies is exactly binomial. -/
theorem TTCState.fixed_round_population_binomial_law {n : Nat}
    (s : TTCState n) (pending rounds : Nat) (h : s.LabelsFresh) :
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
      (samplesAfter coins rounds s.samples).card +
        pendingAfter coins rounds s.nextLabel pending) =
      ProbabilityTheory.binomial (s.samples.card + pending)
        (survivalProbability rounds) := by
  classical
  rw [s.fixed_round_population_law pending rounds h,
    finite_bernoulli_count_law]
  simp [s.populationLabels_card pending h]

/-- A Poisson pending batch thinned by the program's labelled fair coins has
the exact scaled Poisson law at every fixed round. -/
theorem manuscript_poisson_pendingAfter_law (mean : NNReal)
    (firstLabel rounds : Nat) :
    (ProbabilityTheory.poissonMeasure mean).bind (fun pending =>
      fairCoinStreamLaw.map (fun coins =>
        pendingAfter coins rounds firstLabel pending)) =
      ProbabilityTheory.poissonMeasure
        (unitInterval.toNNReal (survivalProbability rounds) * mean) := by
  let s : TTCState 0 :=
    { rate := 1, samples := ∅, nextLabel := firstLabel }
  have hs : s.LabelsFresh := by
    simp [s, TTCState.LabelsFresh]
  have hbin (pending : Nat) :
      fairCoinStreamLaw.map (fun coins =>
        pendingAfter coins rounds firstLabel pending) =
        ProbabilityTheory.binomial pending (survivalProbability rounds) := by
    have h := s.fixed_round_population_binomial_law pending rounds hs
    simpa [s, samplesAfter] using h
  calc
    (ProbabilityTheory.poissonMeasure mean).bind (fun pending =>
        fairCoinStreamLaw.map (fun coins =>
          pendingAfter coins rounds firstLabel pending)) =
      (ProbabilityTheory.poissonMeasure mean).bind (fun pending =>
        ProbabilityTheory.binomial pending (survivalProbability rounds)) := by
          congr 1
          funext pending
          exact hbin pending
    _ = _ := manuscript_poisson_binomial_thinning mean
      (survivalProbability rounds)

/-- At a fixed dyadic level, thinning the manuscript's pending Poisson count
and then drawing its iid point batch gives independent Poisson point counts. -/
theorem manuscript_fixed_round_marked_poisson_law
    {X : Type*} [Countable X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (S : Finset X) (hsupport : pointLaw (S : Set X)ᶜ = 0)
    (mean : NNReal) (firstLabel rounds : Nat) :
    ((ProbabilityTheory.poissonMeasure mean).bind fun pending =>
      (fairCoinStreamLaw.map (fun coins =>
        pendingAfter coins rounds firstLabel pending)).bind fun count =>
        (Measure.pi (fun _ : Fin count => pointLaw)).map
          (fun batch (x : S) => Arlib.Probability.colourCount batch x.1)) =
      Measure.pi (fun x : S =>
        ProbabilityTheory.poissonMeasure (Real.toNNReal
          (pointLaw.real {(x : X)} *
            ((unitInterval.toNNReal (survivalProbability rounds) * mean : NNReal) : Real)))) := by
  let K : Nat → Measure Nat := fun pending =>
    fairCoinStreamLaw.map (fun coins =>
      pendingAfter coins rounds firstLabel pending)
  let G : Nat → Measure (S → Nat) := fun count =>
    (Measure.pi (fun _ : Fin count => pointLaw)).map
      (fun batch (x : S) => Arlib.Probability.colourCount batch x.1)
  change (ProbabilityTheory.poissonMeasure mean).bind
    (fun pending => (K pending).bind G) = _
  calc
    (ProbabilityTheory.poissonMeasure mean).bind
        (fun pending => (K pending).bind G) =
      ((ProbabilityTheory.poissonMeasure mean).bind K).bind G := by
        exact (Measure.bind_bind Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable).symm
    _ = (ProbabilityTheory.poissonMeasure
        (unitInterval.toNNReal (survivalProbability rounds) * mean)).bind G := by
          rw [show (ProbabilityTheory.poissonMeasure mean).bind K =
            ProbabilityTheory.poissonMeasure
              (unitInterval.toNNReal (survivalProbability rounds) * mean) from
            manuscript_poisson_pendingAfter_law mean firstLabel rounds]
    _ = _ := manuscript_poisson_marked_count_law_finiteSupport pointLaw S
      hsupport (unitInterval.toNNReal (survivalProbability rounds) * mean)

end Kr25Ssmxt

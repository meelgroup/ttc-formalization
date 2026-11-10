import Kr25Ssmxt.Analysis.OracleContracts
import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ManuscriptPoissonMarking
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Binomial
import Kr25Ssmxt.Model.Run
import Kr25Ssmxt.Analysis.NormalizedHitAndRunGeometry

/-! Bridge between an actual finite IID batch law and Arlib's algebraic
`countMass` used by the Poisson marking theorem. -/

namespace Kr25Ssmxt

open MeasureTheory Arlib.Probability ProbabilityTheory
open scoped ENNReal ProbabilityTheory

theorem manuscript_iid_countMass
    {X : Type*} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (N : Nat) (counts : X → Nat) :
    (Measure.pi (fun _ : Fin N => pointLaw)).real
      {f | ∀ x : X, colourCount f x = counts x} =
      countMass Finset.univ (fun x => pointLaw.real {x}) N counts := by
  let event : Finset (Fin N → X) :=
    Finset.univ.filter (fun f => ∀ x : X, colourCount f x = counts x)
  have hevent : ({f | ∀ x : X, colourCount f x = counts x} : Set (Fin N → X)) =
      event := by
    ext f
    simp [event]
  rw [hevent, ← MeasureTheory.sum_measureReal_singleton (μ :=
    Measure.pi (fun _ : Fin N => pointLaw)) event]
  unfold countMass
  have hfull : (Fintype.piFinset fun _ : Fin N => (Finset.univ : Finset X)) =
      (Finset.univ : Finset (Fin N → X)) := by
    ext f
    simp
  rw [hfull]
  simp only [Finset.mem_univ, forall_true_left]
  change (∑ f ∈ event, (Measure.pi (fun _ : Fin N => pointLaw)).real {f}) =
    ∑ f ∈ event, ∏ i : Fin N, pointLaw.real {f i}
  apply Finset.sum_congr rfl
  intro f hf
  rw [Measure.real, Measure.pi_singleton]
  simp only [ENNReal.toReal_prod, Measure.real]

/-- A Poisson mixture of probability kernels has the expected real mass sum. -/
theorem manuscript_poisson_bind_real {Y : Type*} [MeasurableSpace Y]
    (mean : NNReal) (kernel : Nat → Measure Y)
    (hkernel : ∀ N, IsProbabilityMeasure (kernel N))
    (event : Set Y) (hevent : MeasurableSet event) :
    ((poissonMeasure mean).bind kernel).real event =
      ∑' N : Nat, Arlib.Probability.poissonPMF (mean : Real) N *
        (kernel N).real event := by
  have hmeas : AEMeasurable kernel (poissonMeasure mean) :=
    Measurable.of_discrete.aemeasurable
  have hfinite : ∀ᵐ N ∂poissonMeasure mean,
      kernel N event < ∞ :=
    Filter.Eventually.of_forall fun N =>
      lt_of_le_of_lt (measure_mono (Set.subset_univ event))
        (by simpa [isProbabilityMeasure_iff.mp (hkernel N)] :
          kernel N Set.univ < ∞)
  rw [Measure.real, Measure.bind_apply hevent hmeas]
  rw [← MeasureTheory.integral_toReal
    (Measurable.of_discrete.aemeasurable) hfinite]
  rw [ProbabilityTheory.integral_poissonMeasure]
  simp [Arlib.Probability.poissonPMF, Measure.real, smul_eq_mul]

/-- Poisson many independent marks give independent Poisson counts at every
point of a finite mark space. This is an identity of the actual measure law. -/
theorem manuscript_poisson_marked_counts
    {X : Type*} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (mean : NNReal) (counts : X → Nat) :
    ((poissonMeasure mean).bind fun N =>
      (Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch x => colourCount batch x)).real {counts} =
      ∏ x : X, poissonPMF (pointLaw.real {x} * (mean : Real)) (counts x) := by
  have hkernel : ∀ N : Nat, IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch x => colourCount batch x)) := by
    intro N
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  rw [manuscript_poisson_bind_real mean _ hkernel {counts}
    (MeasurableSet.of_discrete)]
  have hbatch : ∀ N : Nat,
      ((Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch x => colourCount batch x)).real {counts} =
      countMass Finset.univ (fun x => pointLaw.real {x}) N counts := by
    intro N
    rw [MeasureTheory.map_measureReal_apply Measurable.of_discrete
      (MeasurableSet.of_discrete)]
    have hset : ((fun batch : Fin N → X => fun x => colourCount batch x) ⁻¹' {counts}) =
        {f | ∀ x : X, colourCount f x = counts x} := by
      ext batch
      simp [funext_iff]
    rw [hset]
    exact manuscript_iid_countMass pointLaw N counts
  simp_rw [hbatch]
  have hq : ∑ x : X, pointLaw.real {x} = 1 := by
    rw [MeasureTheory.sum_measureReal_singleton (μ := pointLaw)
      (Finset.univ : Finset X)]
    simp
  exact manuscript_poisson_marking_exact Finset.univ
    (fun x => pointLaw.real {x}) (by simpa using hq) (mean : Real) counts

/-- The same finite colouring mass formula when the ambient mark type is
infinite but the actual point law is supported on a finite set. -/
theorem manuscript_iid_countMass_finiteSupport
    {X : Type*} [Countable X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (S : Finset X) (hsupport : pointLaw (S : Set X)ᶜ = 0)
    (N : Nat) (counts : X → Nat) :
    (Measure.pi (fun _ : Fin N => pointLaw)).real
      {f | ∀ x ∈ S, colourCount f x = counts x} =
      countMass S (fun x => pointLaw.real {x}) N counts := by
  let allowed : Set (Fin N → X) := Set.pi Set.univ (fun _ => (S : Set X))
  let event : Set (Fin N → X) :=
    {f | ∀ x ∈ S, colourCount f x = counts x}
  let valid : Finset (Fin N → X) :=
    (Fintype.piFinset fun _ : Fin N => S).filter
      (fun f => ∀ x ∈ S, colourCount f x = counts x)
  have hpoint : pointLaw (S : Set X) = 1 := by
    exact (prob_compl_eq_zero_iff (MeasurableSet.of_discrete)).mp hsupport
  have hallowed : (Measure.pi (fun _ : Fin N => pointLaw)) allowed = 1 := by
    change (Measure.pi (fun _ : Fin N => pointLaw))
      (Set.pi Set.univ (fun _ => (S : Set X))) = 1
    rw [Measure.pi_pi]
    simp [hpoint]
  have hae : ∀ᵐ f ∂Measure.pi (fun _ : Fin N => pointLaw), f ∈ allowed :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.pi Set.countable_univ
      (fun _ _ => MeasurableSet.of_discrete))).2 hallowed
  have hvalid : allowed ∩ event = (valid : Set (Fin N → X)) := by
    ext f
    simp [allowed, event, valid, Fintype.mem_piFinset]
  change (Measure.pi (fun _ : Fin N => pointLaw)).real event = _
  change ((Measure.pi (fun _ : Fin N => pointLaw)) event).toReal = _
  rw [← Measure.measure_inter_eq_of_ae hae, hvalid]
  change (Measure.pi (fun _ : Fin N => pointLaw)).real (valid : Set (Fin N → X)) = _
  rw [← MeasureTheory.sum_measureReal_singleton
    (μ := Measure.pi (fun _ : Fin N => pointLaw)) valid]
  unfold countMass
  change (∑ f ∈ valid, (Measure.pi (fun _ : Fin N => pointLaw)).real {f}) =
    ∑ f ∈ valid, ∏ i : Fin N, pointLaw.real {f i}
  apply Finset.sum_congr rfl
  intro f hf
  rw [Measure.real, Measure.pi_singleton]
  simp only [ENNReal.toReal_prod, Measure.real]

/-- Poisson marking for a finite support inside a countable ambient type. -/
theorem manuscript_poisson_marked_counts_finiteSupport
    {X : Type*} [Countable X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (S : Finset X) (hsupport : pointLaw (S : Set X)ᶜ = 0)
    (mean : NNReal) (counts : S → Nat) :
    ((poissonMeasure mean).bind fun N =>
      (Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch (x : S) => colourCount batch x.1)).real {counts} =
      ∏ x : S, poissonPMF (pointLaw.real {(x : X)} * (mean : Real))
        (counts x) := by
  let extended : X → Nat := fun x => if h : x ∈ S then counts ⟨x, h⟩ else 0
  have hkernel : ∀ N : Nat, IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch (x : S) => colourCount batch x.1)) := by
    intro N
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  rw [manuscript_poisson_bind_real mean _ hkernel {counts}
    (MeasurableSet.of_discrete)]
  have hbatch : ∀ N : Nat,
      ((Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch (x : S) => colourCount batch x.1)).real {counts} =
      countMass S (fun x => pointLaw.real {x}) N extended := by
    intro N
    rw [MeasureTheory.map_measureReal_apply Measurable.of_discrete
      (MeasurableSet.of_discrete)]
    have hset : ((fun batch : Fin N → X =>
        fun x : S => colourCount batch x.1) ⁻¹' {counts}) =
        {f | ∀ x ∈ S, colourCount f x = extended x} := by
      ext batch
      constructor
      · intro h x hx
        have h' := congrFun h ⟨x, hx⟩
        simpa [extended, hx] using h'
      · intro h
        funext x
        have h' := h x.1 x.2
        simpa [extended, x.2] using h'
    rw [hset]
    exact manuscript_iid_countMass_finiteSupport pointLaw S hsupport N extended
  simp_rw [hbatch]
  have hq : ∑ x ∈ S, pointLaw.real {x} = 1 := by
    rw [MeasureTheory.sum_measureReal_singleton]
    have hpoint : pointLaw (S : Set X) = 1 :=
      (prob_compl_eq_zero_iff (MeasurableSet.of_discrete)).mp hsupport
    simp [hpoint, Measure.real]
  rw [manuscript_poisson_marking_exact S (fun x => pointLaw.real {x})
    hq (mean : Real) extended]
  rw [Finset.prod_subtype (p := fun x => x ∈ S) S (by intro x; rfl)
    (fun x => poissonPMF (pointLaw.real {x} * (mean : Real)) (extended x))]
  apply Finset.prod_congr rfl
  intro x hx
  simp [extended, x.2]

/-- The count-vector law itself is a product of independent Poisson measures. -/
theorem manuscript_poisson_marked_count_law_finiteSupport
    {X : Type*} [Countable X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (S : Finset X) (hsupport : pointLaw (S : Set X)ᶜ = 0)
    (mean : NNReal) :
    ((poissonMeasure mean).bind fun N =>
      (Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch (x : S) => colourCount batch x.1)) =
      Measure.pi (fun x : S =>
        poissonMeasure (Real.toNNReal
          (pointLaw.real {(x : X)} * (mean : Real)))) := by
  let marks : Measure (S → Nat) :=
    (poissonMeasure mean).bind fun N =>
      (Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch (x : S) => colourCount batch x.1)
  let rates : S → NNReal := fun x =>
    Real.toNNReal (pointLaw.real {(x : X)} * (mean : Real))
  let independent : Measure (S → Nat) :=
    Measure.pi (fun x : S => poissonMeasure (rates x))
  have hmarks : IsProbabilityMeasure marks := by
    dsimp only [marks]
    apply isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
    exact Filter.Eventually.of_forall fun N =>
      Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  have hindependent : IsProbabilityMeasure independent := by
    dsimp only [independent]
    infer_instance
  have hsingle : ∀ counts : S → Nat,
      marks.real {counts} = independent.real {counts} := by
    intro counts
    rw [show marks.real {counts} =
        ∏ x : S, Arlib.Probability.poissonPMF
          (pointLaw.real {(x : X)} * (mean : Real))
          (counts x) from
      manuscript_poisson_marked_counts_finiteSupport pointLaw S hsupport mean counts]
    dsimp only [independent]
    rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro x hx
    rw [Measure.real, poissonMeasure_singleton]
    have hnonneg : 0 ≤ pointLaw.real {(x : X)} * (mean : Real) :=
      mul_nonneg measureReal_nonneg (by positivity)
    simp only [rates, Real.coe_toNNReal _ hnonneg,
      Arlib.Probability.poissonPMF]
    rw [ENNReal.toReal_ofReal (by positivity)]
    rfl
  change marks = independent
  apply Measure.ext_of_singleton
  intro counts
  exact (measureReal_eq_measureReal_iff
    (μ := marks) (ν := independent) (by finiteness) (by finiteness)).mp
      (hsingle counts)

/-- Each lattice point has its exact Poisson marginal after the iid batch. -/
theorem manuscript_poisson_marked_point_law_finiteSupport
    {X : Type*} [Countable X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (S : Finset X) (hsupport : pointLaw (S : Set X)ᶜ = 0)
    (mean : NNReal) (x : S) :
    (((poissonMeasure mean).bind fun N =>
      (Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch (y : S) => colourCount batch y.1)).map
          (Function.eval x)) =
      poissonMeasure (Real.toNNReal
        (pointLaw.real {(x : X)} * (mean : Real))) := by
  rw [manuscript_poisson_marked_count_law_finiteSupport pointLaw S hsupport mean]
  exact (measurePreserving_eval
    (fun y : S => poissonMeasure
      (Real.toNNReal (pointLaw.real {(y : X)} * (mean : Real)))) x).map_eq

/-- Exact measure-level Poisson thinning through Mathlib's binomial law. -/
theorem manuscript_poisson_binomial_thinning
    (mean : NNReal) (p : unitInterval) :
    (poissonMeasure mean).bind (fun N => ProbabilityTheory.binomial N p) =
      poissonMeasure (unitInterval.toNNReal p * mean) := by
  have hkernel : ∀ N : Nat, IsProbabilityMeasure
      (ProbabilityTheory.binomial N p) := fun _ => inferInstance
  have hbind : IsProbabilityMeasure
      ((poissonMeasure mean).bind (fun N => ProbabilityTheory.binomial N p)) := by
    apply isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
    exact Filter.Eventually.of_forall hkernel
  letI := hbind
  apply Measure.ext_of_singleton
  intro k
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  rw [manuscript_poisson_bind_real mean _ hkernel {k}
    (MeasurableSet.of_discrete)]
  simp_rw [ProbabilityTheory.binomial_real_singleton]
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  have hgeneral := Arlib.Probability.tsum_poissonPMF_mul_binomialPMF
    (mean : Real) (p : Real) k
  have hpcoe : ((unitInterval.toNNReal p * mean : NNReal) : Real) =
      (p : Real) * (mean : Real) := rfl
  rw [hpcoe]
  simpa [Arlib.Probability.poissonPMF, Arlib.Probability.binomialPMF] using hgeneral

/-- The manuscript batch adapter has the exact marked-Poisson law after
forgetting its always-true diagnostic tag. -/
theorem manuscript_iid_batch_poisson_count_law
    {n : Nat} (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n)) (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (mean : NNReal) :
    ((poissonMeasure mean).bind fun N =>
      (iidSampleBatchLaw (count := N) pointLaw).map
        (fun batch (x : S) => colourCount batch.2 x.1)) =
      Measure.pi (fun x : S =>
        poissonMeasure (Real.toNNReal
          (pointLaw.real {(x : LatticePoint n)} * (mean : Real)))) := by
  rw [← manuscript_poisson_marked_count_law_finiteSupport pointLaw S hsupport mean]
  congr 1
  funext N
  unfold iidSampleBatchLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The certified normalized Hit-and-Run batch, at any valid TTC call, gives
independent Poisson point counts after the program's Poisson draw. -/
theorem manuscript_normalized_batch_poisson_count_law
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n) (b : Nat)
    (hunit : 1 ≤ decimalScale b * P.inradius)
    (eta : Real) (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty)
    (mean : NNReal) :
    let pointLaw := normalizedHitAndRunPointLaw hn P b hunit eta heta0 heta1
      hfinite hnonempty
    let S := hfinite.toFinset
    ((poissonMeasure mean).bind fun N =>
      (iidSampleBatchLaw (count := N) pointLaw).map
        (fun batch (x : S) => colourCount batch.2 x.1)) =
      Measure.pi (fun x : S =>
        poissonMeasure (Real.toNNReal
          (pointLaw.real {(x : LatticePoint n)} * (mean : Real)))) := by
  dsimp only
  let pointLaw := normalizedHitAndRunPointLaw hn P b hunit eta heta0 heta1
    hfinite hnonempty
  have halmost : AlmostUniformPointwise pointLaw (codedLatticePoints P b) eta :=
    P.normalizedHitAndRun_latticePointLaw hn b hunit heta0 heta1 hfinite hnonempty
  letI : IsProbabilityMeasure pointLaw := halmost.1
  have hsupport : pointLaw (hfinite.toFinset : Set (LatticePoint n))ᶜ = 0 := by
    simpa using halmost.2.2.2.1
  exact manuscript_iid_batch_poisson_count_law pointLaw hfinite.toFinset
    hsupport mean

/-- Counting every mark in its finite support recovers the batch size. -/
theorem manuscript_sum_colourCount_eq_size
    {X : Type*} [DecidableEq X] (S : Finset X)
    {N : Nat} (batch : Fin N → X) (hbatch : ∀ i, batch i ∈ S) :
    (∑ x ∈ S, colourCount batch x) = N := by
  simp_rw [colourCount_eq_sum]
  rw [Finset.sum_comm]
  simp [hbatch]

theorem manuscript_iid_total_count_law
    {X : Type*} [Countable X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (S : Finset X) (hsupport : pointLaw (S : Set X)ᶜ = 0)
    (N : Nat) :
    (Measure.pi (fun _ : Fin N => pointLaw)).map
      (fun batch => ∑ x ∈ S, colourCount batch x) = Measure.dirac N := by
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin N => pointLaw)) :=
    inferInstance
  have hpoint : pointLaw (S : Set X) = 1 :=
    (prob_compl_eq_zero_iff (MeasurableSet.of_discrete)).mp hsupport
  have hallowed : (Measure.pi (fun _ : Fin N => pointLaw))
      (Set.pi Set.univ (fun _ => (S : Set X))) = 1 := by
    rw [Measure.pi_pi]
    simp [hpoint]
  have hae : ∀ᵐ batch ∂Measure.pi (fun _ : Fin N => pointLaw),
      ∀ i, batch i ∈ S := by
    have h := (mem_ae_iff_prob_eq_one
      (MeasurableSet.pi Set.countable_univ
        (fun _ _ => MeasurableSet.of_discrete))).2 hallowed
    change ∀ᵐ batch ∂Measure.pi (fun _ : Fin N => pointLaw),
      batch ∈ Set.pi Set.univ (fun _ => (S : Set X)) at h
    filter_upwards [h] with batch hb
    intro i
    exact hb i (by simp)
  rw [Measure.map_congr (hae.mono fun batch hbatch =>
    manuscript_sum_colourCount_eq_size S batch hbatch)]
  simp

/-- Summing the point counts of a marked Poisson batch recovers its original
Poisson draw, at the level of the full measure law. -/
theorem manuscript_poisson_marked_total_count_law
    {X : Type*} [Countable X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (S : Finset X) (hsupport : pointLaw (S : Set X)ᶜ = 0)
    (mean : NNReal) :
    (((poissonMeasure mean).bind fun N =>
      (Measure.pi (fun _ : Fin N => pointLaw)).map
        (fun batch (x : S) => colourCount batch x.1)).map
          (fun counts => ∑ x : S, counts x)) = poissonMeasure mean := by
  let kernel : Nat → Measure (S → Nat) := fun N =>
    (Measure.pi (fun _ : Fin N => pointLaw)).map
      (fun batch (x : S) => colourCount batch x.1)
  let total : (S → Nat) → Nat := fun counts => ∑ x : S, counts x
  have htotal : Measurable total := Measurable.of_discrete
  have hkernel : ∀ N, (kernel N).map total = Measure.dirac N := by
    intro N
    dsimp only [kernel]
    rw [Measure.map_map htotal Measurable.of_discrete]
    have hfun : (total ∘ fun batch : Fin N → X =>
        fun x : S => colourCount batch x.1) =
        (fun batch : Fin N → X => ∑ x ∈ S, colourCount batch x) := by
      funext batch
      exact (Finset.sum_subtype (p := fun x => x ∈ S) S
        (by intro x; rfl) (fun x => colourCount batch x)).symm
    rw [hfun]
    exact manuscript_iid_total_count_law pointLaw S hsupport N
  change ((poissonMeasure mean).bind kernel).map total = poissonMeasure mean
  calc
    ((poissonMeasure mean).bind kernel).map total =
        ((poissonMeasure mean).bind kernel).bind
          (fun counts => Measure.dirac (total counts)) := by
          exact (Measure.bind_dirac_eq_map _ htotal).symm
    _ = (poissonMeasure mean).bind fun N =>
          (kernel N).bind (fun counts => Measure.dirac (total counts)) := by
          apply Measure.bind_bind Measurable.of_discrete.aemeasurable
          exact Measurable.of_discrete.aemeasurable
    _ = (poissonMeasure mean).bind Measure.dirac := by
          congr 1
          funext N
          rw [Measure.bind_dirac_eq_map _ htotal, hkernel]
    _ = poissonMeasure mean := Measure.bind_dirac

#print axioms manuscript_poisson_marked_count_law_finiteSupport
#print axioms manuscript_poisson_binomial_thinning
#print axioms manuscript_poisson_marked_total_count_law

end Kr25Ssmxt

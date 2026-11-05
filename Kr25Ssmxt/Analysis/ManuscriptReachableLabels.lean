import Kr25Ssmxt.Analysis.ManuscriptLabelFreshness
import Kr25Ssmxt.Analysis.MeasurableAddBatch

/-! Almost-sure preservation of distinct copy labels through randomized
manuscript state transitions. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurableSet_labelsFresh {n : Nat} :
    MeasurableSet {s : TTCState n | s.LabelsFresh} := by
  let good : Set (Finset (SampleCopy n) × Nat) :=
    {x | (∀ c ∈ x.1, c.1 < x.2) ∧
      (∀ c ∈ x.1, ∀ d ∈ x.1, c.1 = d.1 → c = d)}
  have hgood : MeasurableSet good := good.to_countable.measurableSet
  have hpair : Measurable (fun s : TTCState n => (s.samples, s.nextLabel)) :=
    measurable_snd.comp
      (comap_measurable (fun s : TTCState n => (s.rate, s.samples, s.nextLabel)))
  convert hgood.preimage hpair using 1
  ext s
  rfl

theorem ae_bind_labelsFresh_of_forall {n : Nat} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → Measure (TTCState n))
    (hf : ∀ a, ∀ᵐ s ∂f a, s.LabelsFresh) :
    ∀ᵐ s ∂μ.bind f, s.LabelsFresh := by
  rw [ae_iff]
  apply le_antisymm
  · calc
      (μ.bind f) {s | ¬s.LabelsFresh} ≤
          ∫⁻ a, f a {s | ¬s.LabelsFresh} ∂μ :=
        Measure.bind_apply_le f measurableSet_labelsFresh.compl
      _ = 0 := by
        have hzero : ∀ a, f a {s | ¬s.LabelsFresh} = 0 := by
          intro a
          exact (ae_iff.mp (hf a))
        simp [hzero]
  · exact zero_le

theorem ae_bind_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → Measure β} {P : α → Prop} {Q : β → Prop}
    (hQ : MeasurableSet {b | Q b})
    (hP : ∀ᵐ a ∂μ, P a)
    (hf : ∀ a, P a → ∀ᵐ b ∂f a, Q b) :
    ∀ᵐ b ∂μ.bind f, Q b := by
  rw [ae_iff]
  apply le_antisymm
  · calc
      (μ.bind f) {b | ¬Q b} ≤ ∫⁻ a, f a {b | ¬Q b} ∂μ :=
        Measure.bind_apply_le f hQ.compl
      _ = 0 := by
        have hzero : (fun a => f a {b | ¬Q b}) =ᵐ[μ] (fun _ => 0) :=
          hP.mono fun a ha => ae_iff.mp (hf a ha)
        rw [lintegral_congr_ae hzero]
        simp
  · exact zero_le

theorem manuscriptRateThinUntil_labelsFresh {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) (h : s.LabelsFresh) :
    ∀ᵐ t ∂manuscriptRateThinUntil s intensity threshold, t.LabelsFresh := by
  unfold manuscriptRateThinUntil
  rw [ae_map_iff
    (measurable_manuscriptRateThinningResult s intensity threshold).aemeasurable
    measurableSet_labelsFresh]
  exact Filter.Eventually.of_forall fun coins =>
    manuscriptRateThinningResult_labelsFresh s intensity threshold coins h

theorem thinUntil_labelsFresh {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (h : s.LabelsFresh) :
    ∀ᵐ result ∂thinUntil s pending threshold, result.1.LabelsFresh := by
  have hset : MeasurableSet
      {result : TTCState n × Nat | result.1.LabelsFresh} :=
    measurableSet_labelsFresh.preimage measurable_fst
  unfold thinUntil
  rw [ae_map_iff (measurable_thinningResult s pending threshold).aemeasurable hset]
  exact Filter.Eventually.of_forall fun coins =>
    thinningResult_labelsFresh s pending threshold coins h

theorem manuscript_sample_append_labelsFresh {n k : Nat} (O : TTCOracles n k)
    (P : PolytopeData n) (s : TTCState n) (count b : Nat)
    (epsilonPrime deltaPrime : Real) (h : s.LabelsFresh) :
    ∀ᵐ result ∂(O.generateSamples P count b epsilonPrime deltaPrime).map
      (fun batch => s.addBatch batch.2), result.LabelsFresh := by
  have hmap : Measurable (fun batch : SampleBatch n count => s.addBatch batch.2) :=
    measurable_addBatch.comp (measurable_const.prodMk measurable_snd)
  rw [ae_map_iff hmap.aemeasurable measurableSet_labelsFresh]
  exact Filter.Eventually.of_forall fun batch => s.labelsFresh_addBatch batch.2 h

theorem manuscript_count_sample_tail_labelsFresh {n k : Nat}
    (O : TTCOracles n k) (P : PolytopeData n) (s : TTCState n)
    (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (pending : Nat) (h : s.LabelsFresh) :
    ∀ᵐ result ∂(thinUntil s pending threshold).bind
      (fun secondThinned =>
        (O.generateSamples P secondThinned.2 b epsilonPrime deltaPrime).map
          (fun batch => secondThinned.1.addBatch batch.2)),
      result.LabelsFresh := by
  apply ae_bind_of_ae
    (P := fun secondThinned : TTCState n × Nat => secondThinned.1.LabelsFresh)
    (Q := fun result : TTCState n => result.LabelsFresh)
    measurableSet_labelsFresh
    (thinUntil_labelsFresh s pending threshold h)
  intro secondThinned hsecond
  exact manuscript_sample_append_labelsFresh O P secondThinned.1
    secondThinned.2 b epsilonPrime deltaPrime hsecond

theorem manuscript_poisson_count_sample_tail_labelsFresh {n k : Nat}
    (O : TTCOracles n k) (P : PolytopeData n) (s : TTCState n)
    (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (intensity : NNReal) (h : s.LabelsFresh) :
    ∀ᵐ result ∂(ProbabilityTheory.poissonMeasure (intensity * s.rate)).bind
      (fun pending =>
        (thinUntil s pending threshold).bind (fun secondThinned =>
          (O.generateSamples P secondThinned.2 b epsilonPrime deltaPrime).map
            (fun batch => secondThinned.1.addBatch batch.2))),
      result.LabelsFresh := by
  apply ae_bind_labelsFresh_of_forall
  intro pending
  exact manuscript_count_sample_tail_labelsFresh O P s b epsilonPrime
    deltaPrime threshold pending h

theorem manuscript_rate_poisson_tail_labelsFresh {n k : Nat}
    (O : TTCOracles n k) (P : PolytopeData n) (s : TTCState n)
    (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (intensity : NNReal) (h : s.LabelsFresh) :
    ∀ᵐ result ∂(manuscriptRateThinUntil s intensity threshold).bind
      (fun firstThinned =>
        (ProbabilityTheory.poissonMeasure (intensity * firstThinned.rate)).bind
          (fun pending =>
            (thinUntil firstThinned pending threshold).bind (fun secondThinned =>
              (O.generateSamples P secondThinned.2 b epsilonPrime deltaPrime).map
                (fun batch => secondThinned.1.addBatch batch.2)))),
      result.LabelsFresh := by
  apply ae_bind_of_ae
    (P := fun firstThinned : TTCState n => firstThinned.LabelsFresh)
    (Q := fun result : TTCState n => result.LabelsFresh)
    measurableSet_labelsFresh
    (manuscriptRateThinUntil_labelsFresh s intensity threshold h)
  intro firstThinned hfresh
  exact manuscript_poisson_count_sample_tail_labelsFresh O P firstThinned b
    epsilonPrime deltaPrime threshold intensity hfresh

/-- Every component transition preserves label freshness almost surely, for
arbitrary oracle laws. -/
theorem manuscriptProcessComponent_labelsFresh {n k : Nat} (O : TTCOracles n k)
    (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (P : PolytopeData n) (s : TTCState n) (h : s.LabelsFresh) :
    ∀ᵐ result ∂manuscriptProcessComponent O b epsilonPrime deltaPrime
      threshold P s, result.LabelsFresh := by
  unfold manuscriptProcessComponent
  apply ae_bind_labelsFresh_of_forall
  intro volumeOutcome
  exact manuscript_rate_poisson_tail_labelsFresh O P (s.removeComponent P)
    b epsilonPrime deltaPrime threshold
    (manuscriptIntensity b n threshold volumeOutcome.2)
    (s.labelsFresh_removeComponent P h)

/-- The entire sequential component fold reaches only states with distinct
stored copy labels, almost surely. -/
theorem manuscriptProcessComponents_labelsFresh {n k : Nat}
    (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real)
    (Ps : List (PolytopeData n)) (s : TTCState n)
    (h : s.LabelsFresh) :
    ∀ᵐ result ∂manuscriptProcessComponents O b epsilonPrime deltaPrime
      threshold Ps s, result.LabelsFresh := by
  induction Ps generalizing s with
  | nil =>
      change ∀ᵐ result ∂Measure.dirac s, result.LabelsFresh
      exact (ae_dirac_iff measurableSet_labelsFresh).2 h
  | cons P rest ih =>
      change ∀ᵐ result ∂
        (manuscriptProcessComponent O b epsilonPrime deltaPrime threshold P s).bind
          (manuscriptProcessComponents O b epsilonPrime deltaPrime threshold rest),
        result.LabelsFresh
      apply ae_bind_of_ae
        (P := fun next : TTCState n => next.LabelsFresh)
        (Q := fun result : TTCState n => result.LabelsFresh)
        measurableSet_labelsFresh
        (manuscriptProcessComponent_labelsFresh O b epsilonPrime deltaPrime
          threshold P s h)
      intro next hnext
      exact ih next hnext

end Kr25Ssmxt

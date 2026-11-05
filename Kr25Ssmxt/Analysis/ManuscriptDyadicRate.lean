import Kr25Ssmxt.Analysis.ManuscriptReachableLabels

/-! The manuscript state rate always lies on the dyadic grid. The witness is
the absolute stopping level used in the finite-level error union. -/

namespace Kr25Ssmxt

open MeasureTheory

def TTCState.IsDyadicRate {n : Nat} (s : TTCState n) : Prop :=
  ∃ level : Nat, s.rate = 1 / (2 : NNReal) ^ level

theorem TTCState.initial_isDyadicRate (n : Nat) :
    (TTCState.initial n).IsDyadicRate := by
  exact ⟨0, by simp [TTCState.initial]⟩

theorem TTCState.isDyadicRate_removeComponent {n : Nat}
    (s : TTCState n) (P : PolytopeData n)
    (h : s.IsDyadicRate) :
    (s.removeComponent P).IsDyadicRate := h

theorem TTCState.isDyadicRate_addBatch {n count : Nat}
    (s : TTCState n) (points : Fin count → LatticePoint n)
    (h : s.IsDyadicRate) :
    (s.addBatch points).IsDyadicRate := h

theorem manuscriptRateThinningResult_isDyadicRate {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (coins : Nat × Nat → Bool) (h : s.IsDyadicRate) :
    (manuscriptRateThinningResult s intensity threshold coins).IsDyadicRate := by
  obtain ⟨level, hrate⟩ := h
  refine ⟨level + manuscriptRateExit s intensity threshold, ?_⟩
  simp only [manuscriptRateThinningResult, hrate, pow_add,
    div_eq_mul_inv, mul_inv_rev]
  ac_rfl

theorem thinningResult_isDyadicRate {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (coins : Nat × Nat → Bool) (h : s.IsDyadicRate) :
    (thinningResult s pending threshold coins).1.IsDyadicRate := by
  obtain ⟨level, hrate⟩ := h
  refine ⟨level + firstExitRound s pending threshold coins, ?_⟩
  simp only [thinningResult, hrate, pow_add,
    div_eq_mul_inv, mul_inv_rev]
  ac_rfl

theorem measurableSet_isDyadicRate {n : Nat} :
    MeasurableSet {s : TTCState n | s.IsDyadicRate} := by
  let good : Set NNReal := Set.range fun level : Nat =>
    1 / (2 : NNReal) ^ level
  have hgood : MeasurableSet good :=
    (Set.countable_range _).measurableSet
  have hrate : Measurable (fun s : TTCState n => s.rate) :=
    measurable_fst.comp
      (comap_measurable (fun s : TTCState n => (s.rate, s.samples, s.nextLabel)))
  convert hgood.preimage hrate using 1
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_range, good,
    TTCState.IsDyadicRate]
  exact exists_congr fun _ => eq_comm

theorem manuscriptRateThinUntil_isDyadicRate {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (h : s.IsDyadicRate) :
    ∀ᵐ t ∂manuscriptRateThinUntil s intensity threshold,
      t.IsDyadicRate := by
  unfold manuscriptRateThinUntil
  rw [ae_map_iff
    (measurable_manuscriptRateThinningResult s intensity threshold).aemeasurable
    measurableSet_isDyadicRate]
  exact Filter.Eventually.of_forall fun coins =>
    manuscriptRateThinningResult_isDyadicRate s intensity threshold coins h

theorem thinUntil_isDyadicRate {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (h : s.IsDyadicRate) :
    ∀ᵐ result ∂thinUntil s pending threshold,
      result.1.IsDyadicRate := by
  have hset : MeasurableSet
      {result : TTCState n × Nat | result.1.IsDyadicRate} :=
    measurableSet_isDyadicRate.preimage measurable_fst
  unfold thinUntil
  rw [ae_map_iff
    (measurable_thinningResult s pending threshold).aemeasurable hset]
  exact Filter.Eventually.of_forall fun coins =>
    thinningResult_isDyadicRate s pending threshold coins h

theorem manuscript_sample_append_isDyadicRate {n k : Nat}
    (O : TTCOracles n k) (P : PolytopeData n)
    (s : TTCState n) (count b : Nat)
    (epsilonPrime deltaPrime : Real) (h : s.IsDyadicRate) :
    ∀ᵐ result ∂(O.generateSamples P count b epsilonPrime deltaPrime).map
      (fun batch => s.addBatch batch.2), result.IsDyadicRate := by
  have hmap : Measurable (fun batch : SampleBatch n count => s.addBatch batch.2) :=
    measurable_addBatch.comp (measurable_const.prodMk measurable_snd)
  rw [ae_map_iff hmap.aemeasurable measurableSet_isDyadicRate]
  exact Filter.Eventually.of_forall fun batch => s.isDyadicRate_addBatch batch.2 h

end Kr25Ssmxt

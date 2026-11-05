import Kr25Ssmxt.Analysis.ManuscriptOriginSourceFold
import Kr25Ssmxt.Analysis.ManuscriptCoinSpliceLaw

/-! A component's two fresh coin streams have the same fixed-level incoming
point-count law as one absolute fair stream, at any deterministic splice round. -/

namespace Kr25Ssmxt

open MeasureTheory

set_option maxHeartbeats 800000 in
theorem manuscript_spliced_source_fixedLevel_pointCounts
    {n : Nat} (mean : NNReal)
    (pointLaw : Measure (LatticePoint n)) [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n))
    (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (firstLabel level preRounds : Nat) :
    ((ProbabilityTheory.poissonMeasure mean).bind fun pending =>
      (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun pair =>
        (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
          manuscriptPoissonTapePointCounts S firstLabel level
            (pending, spliceCoins pair.1 pair.2 preRounds, tape)) =
    Measure.pi (fun x : S =>
      ProbabilityTheory.poissonMeasure (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) * mean : NNReal) : Real)))) := by
  let tapeLaw : Measure (Nat → LatticePoint n) :=
    Measure.infinitePi (fun _ : Nat => pointLaw)
  letI : IsProbabilityMeasure tapeLaw := inferInstance
  let output := manuscriptPoissonTapePointCounts S firstLabel level
  have houtput : Measurable output :=
    measurable_manuscriptPoissonTapePointCounts S firstLabel level
  let K (pending : Nat) (coins : Nat × Nat → Bool) : Measure (S → Nat) :=
    tapeLaw.map fun tape => output (pending, coins, tape)
  have hK (pending : Nat) : Measurable (K pending) := by
    apply measurable_parametric_probability_map
      (fun _ : Nat × Nat → Bool => tapeLaw) measurable_const
      (fun _ => inferInstance)
      (fun z : (Nat × Nat → Bool) × (Nat → LatticePoint n) =>
        output (pending, z.1, z.2))
    exact houtput.comp (by fun_prop)
  have hinner (pending : Nat) :
      ((fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun pair =>
        K pending (spliceCoins pair.1 pair.2 preRounds)) =
      fairCoinStreamLaw.bind (K pending) := by
    let splice : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
        Nat × Nat → Bool := fun pair =>
      spliceCoins pair.1 pair.2 preRounds
    have hbind :
        ((fairCoinStreamLaw.prod fairCoinStreamLaw).map splice).bind
          (K pending) =
        (fairCoinStreamLaw.prod fairCoinStreamLaw).bind
          (K pending ∘ splice) :=
      bind_mapped_measure _ splice (measurable_spliceCoins_pair preRounds)
        (K pending) (hK pending)
    calc
      (fairCoinStreamLaw.prod fairCoinStreamLaw).bind
          (K pending ∘ splice) =
        ((fairCoinStreamLaw.prod fairCoinStreamLaw).map splice).bind
          (K pending) := hbind.symm
      _ = fairCoinStreamLaw.bind (K pending) := by
        rw [fairCoinStreamLaw_splice preRounds]
  change ((ProbabilityTheory.poissonMeasure mean).bind fun pending =>
    (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun pair =>
      K pending (spliceCoins pair.1 pair.2 preRounds)) = _
  rw [show ((ProbabilityTheory.poissonMeasure mean).bind fun pending =>
      (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun pair =>
        K pending (spliceCoins pair.1 pair.2 preRounds)) =
      (ProbabilityTheory.poissonMeasure mean).bind fun pending =>
        fairCoinStreamLaw.bind (K pending) from by
    congr 1
    funext pending
    exact hinner pending]
  let K₂ (pending : Nat) (coins : Nat × Nat → Bool) :
      Measure (ManuscriptPoissonTape n) :=
    tapeLaw.map fun tape => (pending, coins, tape)
  have hK₂ (pending : Nat) : Measurable (K₂ pending) := by
    apply measurable_parametric_probability_map
      (fun _ : Nat × Nat → Bool => tapeLaw) measurable_const
      (fun _ => inferInstance)
      (fun z : (Nat × Nat → Bool) × (Nat → LatticePoint n) =>
        (pending, z.1, z.2))
    fun_prop
  let K₁ (pending : Nat) : Measure (ManuscriptPoissonTape n) :=
    fairCoinStreamLaw.bind (K₂ pending)
  have hK₁ : Measurable K₁ := Measurable.of_discrete
  have hsource : (manuscriptPoissonTapeLaw mean pointLaw).map output =
      (ProbabilityTheory.poissonMeasure mean).bind fun pending =>
        fairCoinStreamLaw.bind (K pending) := by
    change ((ProbabilityTheory.poissonMeasure mean).bind K₁).map output = _
    rw [map_bind_measure (ProbabilityTheory.poissonMeasure mean) K₁ output
      hK₁.aemeasurable houtput]
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro pending
    change (fairCoinStreamLaw.bind (K₂ pending)).map output = _
    rw [map_bind_measure fairCoinStreamLaw (K₂ pending) output
      (hK₂ pending).aemeasurable houtput]
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro coins
    change (tapeLaw.map (fun tape => (pending, coins, tape))).map output =
      K pending coins
    rw [Measure.map_map houtput (by fun_prop)]
    rfl
  rw [← hsource]
  exact manuscriptPoissonTapeLaw_fixedLevel_pointCounts mean pointLaw S
    hsupport firstLabel level

end Kr25Ssmxt

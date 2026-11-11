import Kr25Ssmxt.Analysis.CoinSplice
import Kr25Ssmxt.Analysis.AbsoluteCoinStream
import Mathlib.Probability.Independence.InfinitePi

/-! Combining the fresh coin streams for the first and second paper
loops yields one fair coin stream at a deterministic splice round. -/

namespace Kr25Ssmxt

open MeasureTheory

def spliceCoinIndex (rounds : Nat) (pair : Nat × Nat) :
    Fin 2 × (Nat × Nat) :=
  if pair.1 < rounds then (0, pair)
  else (1, (pair.1 - rounds, pair.2))

theorem spliceCoinIndex_injective (rounds : Nat) :
    Function.Injective (spliceCoinIndex rounds) := by
  intro a b hab
  unfold spliceCoinIndex at hab
  by_cases ha : a.1 < rounds <;> by_cases hb : b.1 < rounds
  · simpa [ha, hb] using hab
  · simp [ha, hb] at hab
  · simp [ha, hb] at hab
  · have hround : a.1 - rounds = b.1 - rounds := by
      simpa [ha, hb, spliceCoinIndex] using
        congrArg (fun z : Fin 2 × (Nat × Nat) => z.2.1) hab
    have hlabel : a.2 = b.2 := by
      simpa [ha, hb, spliceCoinIndex] using
        congrArg (fun z : Fin 2 × (Nat × Nat) => z.2.2) hab
    exact Prod.ext (by omega) hlabel

theorem measurable_spliceCoins_pair (rounds : Nat) :
    Measurable (fun pair : (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      spliceCoins pair.1 pair.2 rounds) := by
  apply Measurable.of_eval
  intro index
  by_cases h : index.1 < rounds
  · simpa only [spliceCoins, h, ite_true, Function.comp_def] using
      (measurable_pi_apply index).comp measurable_fst
  · simpa only [spliceCoins, h, ite_false, Function.comp_def] using
      (measurable_pi_apply (index.1 - rounds, index.2)).comp measurable_snd

theorem fairCoinStreamLaw_splice (rounds : Nat) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair => spliceCoins pair.1 pair.2 rounds) =
    fairCoinStreamLaw := by
  let global : Measure (Fin 2 × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : ∀ _ : Fin 2 × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hpair : global.map (fun coins =>
      ((fun pair => coins (0, pair)), fun pair => coins (1, pair))) =
      fairCoinStreamLaw.prod fairCoinStreamLaw := by
    have hcurry := Measure.infinitePi_map_curry
      (μ := fun _ : Fin 2 => fun _ : Nat × Nat => fairCoinLaw)
      (hμ := fun _ _ => fairCoinLaw_isProbabilityMeasure)
    have hcurry' : global.map
        (MeasurableEquiv.curry (Fin 2) (Nat × Nat) Bool) =
        Measure.infinitePi (fun _ : Fin 2 => fairCoinStreamLaw) := by
      simpa [global, fairCoinStreamLaw] using hcurry
    have htwo :
        (Measure.infinitePi (fun _ : Fin 2 => fairCoinStreamLaw)).map
          MeasurableEquiv.finTwoArrow =
        fairCoinStreamLaw.prod fairCoinStreamLaw := by
      rw [Measure.infinitePi_eq_pi]
      exact (measurePreserving_finTwoArrow fairCoinStreamLaw).map_eq
    calc
      global.map (fun coins =>
          ((fun pair => coins (0, pair)), fun pair => coins (1, pair))) =
        (global.map (MeasurableEquiv.curry (Fin 2) (Nat × Nat) Bool)).map
          MeasurableEquiv.finTwoArrow := by
            rw [Measure.map_map
              (MeasurableEquiv.finTwoArrow.measurable)
              (MeasurableEquiv.curry (Fin 2) (Nat × Nat) Bool).measurable]
            congr 1
      _ = _ := by rw [hcurry', htwo]
  rw [← hpair]
  have hmeas : Measurable
      (fun coins : Fin 2 × (Nat × Nat) → Bool =>
        ((fun pair => coins (0, pair)), fun pair => coins (1, pair))) := by
    fun_prop
  rw [Measure.map_map (measurable_spliceCoins_pair rounds) hmeas]
  have hfun :
      ((fun pair : (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
        spliceCoins pair.1 pair.2 rounds) ∘
        (fun coins : Fin 2 × (Nat × Nat) → Bool =>
          ((fun pair => coins (0, pair)), fun pair => coins (1, pair)))) =
      (fun coins pair => coins (spliceCoinIndex rounds pair)) := by
    funext coins pair
    by_cases h : pair.1 < rounds <;>
      simp [spliceCoins, spliceCoinIndex, h]
  rw [hfun]
  change global.map (fun coins pair => coins (spliceCoinIndex rounds pair)) =
    fairCoinStreamLaw
  exact @Measure.map_infinitePi_infinitePi_of_inj
    (Fin 2 × (Nat × Nat)) (Nat × Nat) (fun _ => Bool)
    (fun _ => inferInstance) (fun _ => fairCoinLaw)
    (fun _ => fairCoinLaw_isProbabilityMeasure)
    (spliceCoinIndex rounds) (spliceCoinIndex_injective rounds)

theorem shiftCoins_spliceCoins
    (first second : Nat × Nat → Bool) (rounds : Nat) :
    shiftCoins rounds (spliceCoins first second rounds) = second := by
  funext pair
  simp [shiftCoins, spliceCoins]

theorem rateThinningResult_spliceCoins
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (first second : Nat × Nat → Bool) :
    ttcPseudocode.firstLoopResult s intensity threshold
      (spliceCoins first second (ttcPseudocode.firstLoopExit s intensity threshold)) =
    ttcPseudocode.firstLoopResult s intensity threshold first := by
  let rounds := ttcPseudocode.firstLoopExit s intensity threshold
  have hsurv (label : Nat) :
      survives (spliceCoins first second rounds) rounds label ↔
        survives first rounds label := by
    have h := survives_spliceCoins first second rounds 0 label
    simpa [survives] using h
  simp only [ttcPseudocode.firstLoopResult]
  congr 1
  ext copy
  simp only [samplesAfter, Finset.mem_filter]
  exact and_congr_right (fun _ => hsurv copy.1)

end Kr25Ssmxt

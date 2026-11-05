import Kr25Ssmxt.Analysis.ManuscriptIIDIndexedSelection
import Kr25Ssmxt.Analysis.ManuscriptVolumeTrace

/-! Move an IID sample draw across the pending-count thinning law: the same
output can be read from preassigned independent point marks on the surviving
pending labels. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

theorem iid_tape_pending_survivors_bind
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (pointLaw : Measure α) [IsProbabilityMeasure pointLaw]
    (rounds firstLabel pending : Nat)
    (g : (count : Nat) → (Fin count → α) → β)
    (hg : ∀ count, Measurable (g count)) :
    ((fairCoinStreamLaw.map (fun coins =>
      pendingAfter coins rounds firstLabel pending)).bind fun count =>
        (Measure.pi (fun _ : Fin count => pointLaw)).map (g count)) =
      fairCoinStreamLaw.bind fun coins =>
        (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
          g (pendingAfter coins rounds firstLabel pending)
            (fun (i : Fin (pendingAfter coins rounds firstLabel pending)) =>
              tape (firstLabel +
                (pendingSurvivorIndices coins rounds firstLabel pending).orderEmbOfFin
                  (pendingSurvivorIndices_card coins rounds firstLabel pending) i)) := by
  let K : Nat → Measure β := fun count =>
    (Measure.pi (fun _ : Fin count => pointLaw)).map (g count)
  have hK : Measurable K := Measurable.of_discrete
  rw [bind_mapped_measure fairCoinStreamLaw
    (fun coins => pendingAfter coins rounds firstLabel pending)
    (measurable_pendingAfter_fixed rounds firstLabel pending) K hK]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro coins
  dsimp only
  let count := pendingAfter coins rounds firstLabel pending
  let selected : (Nat → α) → (Fin count → α) := fun tape i =>
    tape (firstLabel +
      (pendingSurvivorIndices coins rounds firstLabel pending).orderEmbOfFin
        (pendingSurvivorIndices_card coins rounds firstLabel pending) i)
  have hselected : Measurable selected :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hlaw := iid_tape_pending_survivors pointLaw coins rounds firstLabel pending
  change K count =
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape => g count (selected tape))
  calc
    K count = ((Measure.infinitePi (fun _ : Nat => pointLaw)).map selected).map
        (g count) := by rw [hlaw]
    _ = (Measure.infinitePi (fun _ : Nat => pointLaw)).map
          (fun tape => g count (selected tape)) := by
            rw [Measure.map_map (hg count) hselected]
            rfl

/-- Pre-drawn Poisson copies, independent absolute-level fair coins, and
preassigned IID marks have independent Poisson point counts at every fixed
dyadic level. -/
theorem manuscript_fixed_round_marked_poisson_tape_law
    {X : Type*} [Countable X] [DecidableEq X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (pointLaw : Measure X) [IsProbabilityMeasure pointLaw]
    (S : Finset X) (hsupport : pointLaw (S : Set X)ᶜ = 0)
    (mean : NNReal) (firstLabel rounds : Nat) :
    (ProbabilityTheory.poissonMeasure mean).bind (fun pending =>
      fairCoinStreamLaw.bind fun coins =>
        (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
          fun x : S => Arlib.Probability.colourCount
            (fun (i : Fin (pendingAfter coins rounds firstLabel pending)) =>
              tape (firstLabel +
                (pendingSurvivorIndices coins rounds firstLabel pending).orderEmbOfFin
                  (pendingSurvivorIndices_card coins rounds firstLabel pending) i)) x.1) =
      Measure.pi (fun x : S =>
        ProbabilityTheory.poissonMeasure (Real.toNNReal
          (pointLaw.real {(x : X)} *
            ((unitInterval.toNNReal (survivalProbability rounds) * mean : NNReal) : Real)))) := by
  let g : (count : Nat) → (Fin count → X) → (S → Nat) :=
    fun _ batch x => Arlib.Probability.colourCount batch x.1
  have hg : ∀ count, Measurable (g count) := by
    intro count
    exact Measurable.of_discrete
  calc
    (ProbabilityTheory.poissonMeasure mean).bind (fun pending =>
        fairCoinStreamLaw.bind fun coins =>
          (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
            g (pendingAfter coins rounds firstLabel pending)
              (fun (i : Fin (pendingAfter coins rounds firstLabel pending)) =>
                tape (firstLabel +
                  (pendingSurvivorIndices coins rounds firstLabel pending).orderEmbOfFin
                    (pendingSurvivorIndices_card coins rounds firstLabel pending) i))) =
      (ProbabilityTheory.poissonMeasure mean).bind (fun pending =>
        (fairCoinStreamLaw.map (fun coins =>
          pendingAfter coins rounds firstLabel pending)).bind fun count =>
            (Measure.pi (fun _ : Fin count => pointLaw)).map (g count)) := by
              congr 1
              funext pending
              exact (iid_tape_pending_survivors_bind pointLaw rounds firstLabel
                pending g hg).symm
    _ = _ := manuscript_fixed_round_marked_poisson_law pointLaw S hsupport
      mean firstLabel rounds

/-- A point count read from the enumerated survivors equals the direct
finite count of pre-marked base copies that survive the same rounds. -/
theorem colourCount_pendingSurvivors_eq_filter
    {X : Type*} [DecidableEq X]
    (tape : Nat → X) (coins : Nat × Nat → Bool)
    (rounds firstLabel pending : Nat) (x : X) :
    Arlib.Probability.colourCount
      (fun (i : Fin (pendingAfter coins rounds firstLabel pending)) =>
        tape (firstLabel +
          (pendingSurvivorIndices coins rounds firstLabel pending).orderEmbOfFin
            (pendingSurvivorIndices_card coins rounds firstLabel pending) i)) x =
      ((Finset.range pending).filter (fun i =>
        survives coins rounds (firstLabel + i) ∧
          tape (firstLabel + i) = x)).card := by
  classical
  let T := pendingSurvivorIndices coins rounds firstLabel pending
  let e : Fin (pendingAfter coins rounds firstLabel pending) ↪o Nat :=
    T.orderEmbOfFin (pendingSurvivorIndices_card coins rounds firstLabel pending)
  have himage : (Finset.univ.image e) = T :=
    Finset.image_orderEmbOfFin_univ T _
  have hcard : ((Finset.univ.filter
      (fun i : Fin (pendingAfter coins rounds firstLabel pending) =>
        tape (firstLabel + e i) = x)).image e).card =
      (Finset.univ.filter
        (fun i : Fin (pendingAfter coins rounds firstLabel pending) =>
          tape (firstLabel + e i) = x)).card :=
    Finset.card_image_of_injective _ e.injective
  calc
    Arlib.Probability.colourCount
        (fun (i : Fin (pendingAfter coins rounds firstLabel pending)) =>
          tape (firstLabel + e i)) x =
      (Finset.univ.filter (fun i : Fin
        (pendingAfter coins rounds firstLabel pending) =>
          tape (firstLabel + e i) = x)).card := rfl
    _ = ((Finset.univ.filter (fun i : Fin
        (pendingAfter coins rounds firstLabel pending) =>
          tape (firstLabel + e i) = x)).image e).card := hcard.symm
    _ = (T.filter (fun i => tape (firstLabel + i) = x)).card := by
      rw [← himage]
      exact congrArg Finset.card
        (Finset.filter_image (s := Finset.univ) (f := e)
          (p := fun i => tape (firstLabel + i) = x)).symm
    _ = ((Finset.range pending).filter (fun i =>
        survives coins rounds (firstLabel + i) ∧
          tape (firstLabel + i) = x)).card := by
      congr 1
      ext i
      simp [T, pendingSurvivorIndices, and_assoc]

end Kr25Ssmxt

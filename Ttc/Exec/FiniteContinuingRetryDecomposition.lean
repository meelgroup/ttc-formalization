import Ttc.Exec.FiniteContinuingRetryKernel
import Ttc.Volume.ContinuingRejectionSignificant

/-! Output/tail decomposition for the finite continuing-retry state machine. -/

namespace Ttc.FiniteContinuingRetryDecomposition

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open scoped ENNReal Classical

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

def runningStates : Set (RetryState E F) := acceptedStatesᶜ

theorem measurableSet_runningStates :
    MeasurableSet (runningStates : Set (RetryState E F)) :=
  measurableSet_acceptedStates.compl

/-- At the retry cutoff, return the stored accepted output or the external fallback. -/
noncomputable def cutoffOutput (fallback : F) (s : RetryState E F) : F :=
  if accepted s = true then output s else fallback

theorem measurable_cutoffOutput (fallback : F) :
    Measurable (cutoffOutput (E := E) fallback) := by
  have hpiece : cutoffOutput (E := E) fallback =
      (acceptedStates : Set (RetryState E F)).piecewise output (fun _ => fallback) := by
    funext s
    by_cases hs : accepted s = true <;>
      simp [cutoffOutput, acceptedStates, hs]
  rw [hpiece]
  exact measurable_output.piecewise measurableSet_acceptedStates measurable_const

theorem cutoffOutput_preimage {T : Set F} (fallback : F) :
    cutoffOutput (E := E) fallback ⁻¹' T =
      acceptedOutputEvent (E := E) T ∪
        if fallback ∈ T then runningStates else ∅ := by
  ext s
  by_cases hs : accepted s = true <;>
    by_cases hf : fallback ∈ T <;>
      simp [cutoffOutput, acceptedOutputEvent, runningStates, acceptedStates, hs, hf]

/-- Exact law decomposition: accepted outputs plus the single unresolved survival tail
placed at the fallback. -/
theorem map_cutoffOutput_apply
    (mu : Measure (RetryState E F)) [IsProbabilityMeasure mu]
    (fallback : F) {T : Set F} (hT : MeasurableSet T) :
    Measure.map (cutoffOutput (E := E) fallback) mu T =
      mu (acceptedOutputEvent T) +
        mu runningStates * T.indicator (fun _ => (1 : ENNReal)) fallback := by
  rw [Measure.map_apply (measurable_cutoffOutput fallback) hT,
    cutoffOutput_preimage fallback]
  have hdisj : Disjoint (acceptedOutputEvent (E := E) T)
      (if fallback ∈ T then runningStates else ∅) := by
    split_ifs
    · exact Set.disjoint_left.2 fun s hsA hsR => hsR hsA.1
    · exact disjoint_empty _
  rw [measure_union hdisj (by
    split_ifs
    · exact measurableSet_runningStates
    · exact MeasurableSet.empty)]
  by_cases hf : fallback ∈ T
  · simp [hf, Set.indicator_of_mem]
  · simp [hf, Set.indicator_of_notMem]

/-- Accepted mass and unresolved survival mass partition the retry state law. -/
theorem accepted_add_survival_eq_one
    (mu : Measure (RetryState E F)) [IsProbabilityMeasure mu] :
    mu (acceptedOutputEvent (E := E) Set.univ) + mu runningStates = 1 := by
  have hunion : acceptedOutputEvent (E := E) (Set.univ : Set F) ∪
      (runningStates : Set (RetryState E F)) = Set.univ := by
    ext s
    by_cases hs : accepted s = true <;>
      simp [acceptedOutputEvent, runningStates, acceptedStates, hs]
  have hdisj : Disjoint (acceptedOutputEvent (E := E) (Set.univ : Set F))
      (runningStates : Set (RetryState E F)) :=
    Set.disjoint_left.2 fun s hsA hsR => hsR hsA.1
  rw [← measure_union hdisj measurableSet_runningStates,
    hunion, measure_univ]

/-- A tail bound transfers directly to cutoff-output TV once the accepted sublaw has been
identified with an accepted mixture.  This is the adapter used with
`tvLe_acceptedMixture`. -/
theorem map_cutoffOutput_eq_acceptedMixture_of_apply
    (mu : Measure (RetryState E F)) [IsProbabilityMeasure mu]
    (L : Nat) (w : Fin L → ENNReal) (q : Fin L → Measure F)
    (fallback : F)
    (haccepted : ∀ T, MeasurableSet T →
      mu (acceptedOutputEvent T) = ∑ i, w i * q i T) :
    Measure.map (cutoffOutput (E := E) fallback) mu =
      Ttc.ContinuingRejectionSignificant.acceptedMixture
        L w q (mu runningStates) fallback := by
  ext T hT
  rw [map_cutoffOutput_apply mu fallback hT, haccepted T hT]
  rw [Ttc.ContinuingRejectionSignificant.acceptedMixture,
    Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hT]
  have hsumEval : (∑ i, w i • q i) T = ∑ i, w i * q i T := by
    simpa only [Measure.smul_apply, smul_eq_mul] using
      (Measure.finsetSum_apply Finset.univ (fun i => w i • q i) T)
  rw [hsumEval]
  simp only [smul_eq_mul]
  by_cases hf : fallback ∈ T <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hf]

section AdaptiveEvent

variable {S : Type*} [MeasurableSpace S]

/-- Generic one-step accepted-mass recursion for an absorbing event family.  `D` is the
whole absorbing region and `B ⊆ D` is the selected accepted-output event. -/
theorem adaptiveMarginal_absorbingEvent_succ
    (P : Nat → Kernel S S) [∀ j, IsMarkovKernel (P j)]
    (mu0 : Measure S) [IsProbabilityMeasure mu0]
    {D B : Set S} (hD : MeasurableSet D) (hB : MeasurableSet B) (hBD : B ⊆ D)
    (g : Nat → S → ENNReal) (hg : ∀ j, Measurable (g j))
    (hstep : ∀ j s, P j s B =
      if s ∈ D then B.indicator (fun _ => (1 : ENNReal)) s else g j s)
    (j : Nat) :
    Arlib.adaptiveMarginal P mu0 (j + 1) B =
      Arlib.adaptiveMarginal P mu0 j B +
        ∫⁻ s in Dᶜ, g j s ∂(Arlib.adaptiveMarginal P mu0 j) := by
  rw [Arlib.adaptiveMarginal, Measure.bind_apply hB (P j).aemeasurable]
  simp_rw [hstep j]
  have hfun : (fun s : S =>
      if s ∈ D then B.indicator (fun _ => (1 : ENNReal)) s else g j s) =
      (fun s => B.indicator (fun _ => (1 : ENNReal)) s) +
        Dᶜ.indicator (g j) := by
    funext s
    by_cases hsD : s ∈ D
    · simp [hsD, Set.indicator_of_mem, Set.indicator_of_notMem]
    · have hsB : s ∉ B := fun h => hsD (hBD h)
      simp [hsD, hsB, Set.indicator_of_mem, Set.indicator_of_notMem]
  rw [hfun]
  change (∫⁻ s, B.indicator (fun _ => (1 : ENNReal)) s +
      Dᶜ.indicator (g j) s ∂(Arlib.adaptiveMarginal P mu0 j)) = _
  rw [lintegral_add_left]
  · have hfirst : (∫⁻ s, B.indicator (fun _ => (1 : ENNReal)) s
        ∂(Arlib.adaptiveMarginal P mu0 j)) =
        Arlib.adaptiveMarginal P mu0 j B := by
      exact lintegral_indicator_one hB
    rw [hfirst, lintegral_indicator hD.compl]
  · exact (measurable_const.indicator hB)

/-- Telescoping form of the preceding recursion. -/
theorem adaptiveMarginal_absorbingEvent_eq_sum
    (P : Nat → Kernel S S) [∀ j, IsMarkovKernel (P j)]
    (mu0 : Measure S) [IsProbabilityMeasure mu0]
    {D B : Set S} (hD : MeasurableSet D) (hB : MeasurableSet B) (hBD : B ⊆ D)
    (g : Nat → S → ENNReal) (hg : ∀ j, Measurable (g j))
    (hstep : ∀ j s, P j s B =
      if s ∈ D then B.indicator (fun _ => (1 : ENNReal)) s else g j s)
    (L : Nat) :
    Arlib.adaptiveMarginal P mu0 L B = mu0 B +
      ∑ j ∈ Finset.range L,
        ∫⁻ s in Dᶜ, g j s ∂(Arlib.adaptiveMarginal P mu0 j) := by
  induction L with
  | zero => simp [Arlib.adaptiveMarginal]
  | succ L ih =>
      rw [adaptiveMarginal_absorbingEvent_succ P mu0 hD hB hBD g hg hstep L,
        ih, Finset.sum_range_succ, add_assoc]

end AdaptiveEvent

#print axioms map_cutoffOutput_apply
#print axioms accepted_add_survival_eq_one
#print axioms map_cutoffOutput_eq_acceptedMixture_of_apply
#print axioms adaptiveMarginal_absorbingEvent_succ
#print axioms adaptiveMarginal_absorbingEvent_eq_sum

end Ttc.FiniteContinuingRetryDecomposition

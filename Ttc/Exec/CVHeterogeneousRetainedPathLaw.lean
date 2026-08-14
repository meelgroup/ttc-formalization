import Ttc.Exec.CVHeterogeneousHistoryReference
import Ttc.Exec.CVRetainedHistoryPathLaw

/-!
# Score-prefix law of heterogeneous retained histories

The retained implementation stores every estimator score but only the current warm
seed.  This file proves that its terminal score prefix has exactly the score-prefix law
of the ordinary uncosted score/seed chain.  Thus path-law accuracy transfers without a
new probabilistic premise.
-/

set_option autoImplicit false

namespace Ttc.CVHeterogeneousRetainedPathLaw

open MeasureTheory ProbabilityTheory Finset Preorder
open Arlib Arlib.Probability
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVRetainedHistoryReferenceInduction
open Ttc.CVRetainedHistoryPathLaw
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVIdealAveragePathTelescope
open Ttc.CVIndependentStreamMoments
open Ttc.CVIndependentStreamDependence
open scoped ENNReal Classical

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

def initialHeterogeneousHistoryState (x : Score × Seed) :
    HeterogeneousHistoryState Score Seed :=
  ((0, fun _ ↦ x.1), x.2)

theorem measurable_initialHeterogeneousHistoryState :
    Measurable (initialHeterogeneousHistoryState :
      Score × Seed → HeterogeneousHistoryState Score Seed) := by
  unfold initialHeterogeneousHistoryState
  fun_prop

noncomputable def initialHeterogeneousHistoryLaw (mu : Measure (Score × Seed)) :
    Measure (HeterogeneousHistoryState Score Seed) :=
  Measure.map initialHeterogeneousHistoryState mu

instance initialHeterogeneousHistoryLaw.instIsProbabilityMeasure
    (mu : Measure (Score × Seed)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (initialHeterogeneousHistoryLaw mu) :=
  Measure.isProbabilityMeasure_map
    measurable_initialHeterogeneousHistoryState.aemeasurable

def storedScorePrefixCurrent (t : Nat)
    (z : HeterogeneousHistoryState Score Seed) : (Iic t → Score) × Seed :=
  (fun j ↦ z.1.2 j.1, z.2)

theorem measurable_storedScorePrefixCurrent (t : Nat) :
    Measurable (storedScorePrefixCurrent (Score := Score) (Seed := Seed) t) := by
  unfold storedScorePrefixCurrent
  fun_prop

def pathScorePrefixCurrent (t : Nat) (omega : Nat → Score × Seed) :
    (Iic t → Score) × Seed :=
  (fun j ↦ (omega j.1).1, (omega t).2)

theorem measurable_pathScorePrefixCurrent (t : Nat) :
    Measurable (pathScorePrefixCurrent (Score := Score) (Seed := Seed) t) := by
  unfold pathScorePrefixCurrent
  fun_prop

def advanceScorePrefix (i : Nat)
    (z : ((Iic i → Score) × Seed) × (Score × Seed)) :
    (Iic (i + 1) → Score) × Seed :=
  (extendIic i (z.1.1, z.2.1), z.2.2)

theorem measurable_advanceScorePrefix (i : Nat) :
    Measurable (advanceScorePrefix (Score := Score) (Seed := Seed) i) := by
  unfold advanceScorePrefix
  exact ((measurable_extendIic i).comp
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd)

theorem storedScorePrefixCurrent_append (i : Nat)
    (z : HeterogeneousHistoryState Score Seed)
    (y : ENNReal × (Score × Seed)) :
    storedScorePrefixCurrent (i + 1) (appendHeterogeneousPhase i (z.1, y)) =
      advanceScorePrefix i (storedScorePrefixCurrent i z, y.2) := by
  apply Prod.ext
  · funext j
    by_cases hj : j.1 ≤ i
    · have hne : j.1 ≠ i + 1 := by omega
      simp [storedScorePrefixCurrent, appendHeterogeneousPhase, advanceScorePrefix,
        extendIic, hj, Function.update, hne]
    · have hle : j.1 ≤ i + 1 := mem_Iic.1 j.2
      have heq : j.1 = i + 1 := by omega
      simp [storedScorePrefixCurrent, appendHeterogeneousPhase, advanceScorePrefix,
        extendIic, hj, Function.update, heq]
  · rfl

noncomputable def scorePrefixStep
    (P : Kernel Seed (Score × Seed)) (i : Nat) :
    Kernel ((Iic i → Score) × Seed) ((Iic (i + 1) → Score) × Seed) :=
  Kernel.map
    ((Kernel.deterministic id measurable_id) ×ₖ
      (Kernel.comap P Prod.snd measurable_snd))
    (advanceScorePrefix i)

instance scorePrefixStep.instIsMarkovKernel
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P] (i : Nat) :
    IsMarkovKernel (scorePrefixStep P i) := by
  unfold scorePrefixStep
  exact Kernel.IsMarkovKernel.map _ (measurable_advanceScorePrefix i)

theorem scorePrefixStep_apply
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (i : Nat) (z : (Iic i → Score) × Seed) :
    scorePrefixStep P i z =
      Measure.map (fun x ↦ advanceScorePrefix i (z, x)) (P z.2) := by
  unfold scorePrefixStep
  rw [Kernel.map_apply _ (measurable_advanceScorePrefix i), Kernel.prod_apply,
    Kernel.deterministic_apply measurable_id, Kernel.comap_apply]
  rw [Measure.dirac_prod,
    Measure.map_map (measurable_advanceScorePrefix i) (by fun_prop)]
  rfl

theorem map_storedScorePrefixCurrent_heterogeneousHistoryKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (hforget : ∀ x, Measure.map Prod.snd (Q x) = P x)
    (i : Nat) (z : HeterogeneousHistoryState Score Seed) :
    Measure.map (storedScorePrefixCurrent (Score := Score) (Seed := Seed) (i + 1))
        (heterogeneousHistoryKernel Q i z) =
      Measure.map (fun x ↦ advanceScorePrefix i
        (storedScorePrefixCurrent i z, x)) (P z.2) := by
  unfold heterogeneousHistoryKernel
  rw [Kernel.map_apply _ (measurable_appendHeterogeneousPhase i),
    Measure.map_map (measurable_storedScorePrefixCurrent (i + 1))
      (measurable_appendHeterogeneousPhase i), Kernel.prod_apply,
    Kernel.deterministic_apply measurable_fst, Kernel.comap_apply]
  have hg : Measurable (fun x : Score × Seed ↦
      advanceScorePrefix i (storedScorePrefixCurrent i z, x)) :=
    (measurable_advanceScorePrefix i).comp (measurable_const.prodMk measurable_id)
  have hf : Measurable
      ((fun x : Score × Seed ↦
        advanceScorePrefix i (storedScorePrefixCurrent i z, x)) ∘
          (Prod.snd : ENNReal × (Score × Seed) → Score × Seed)) :=
    hg.comp (measurable_snd : Measurable
      (Prod.snd : ENNReal × (Score × Seed) → Score × Seed))
  rw [← hforget z.2, Measure.map_map hg
    (measurable_snd : Measurable
      (Prod.snd : ENNReal × (Score × Seed) → Score × Seed))]
  ext A hA
  rw [Measure.map_apply
      ((measurable_storedScorePrefixCurrent (i + 1)).comp
        (measurable_appendHeterogeneousPhase i)) hA,
    Measure.map_apply hf hA, Measure.prod_apply_symm]
  · let E : Set (ENNReal × (Score × Seed)) :=
      (fun y ↦ advanceScorePrefix i (storedScorePrefixCurrent i z, y.2)) ⁻¹' A
    have hE : MeasurableSet E := hA.preimage hf
    have heval : ∀ y : ENNReal × (Score × Seed),
        (Measure.dirac z.1)
            ((fun x ↦ (x, y)) ⁻¹'
              (storedScorePrefixCurrent (i + 1) ∘ appendHeterogeneousPhase i) ⁻¹' A) =
          E.indicator 1 y := by
      intro y
      have hsec : MeasurableSet
          ((fun x : HeterogeneousHistoryPayload Score ↦ (x, y)) ⁻¹'
            (storedScorePrefixCurrent (i + 1) ∘ appendHeterogeneousPhase i) ⁻¹' A) :=
        (hA.preimage ((measurable_storedScorePrefixCurrent (i + 1)).comp
          (measurable_appendHeterogeneousPhase i))).preimage
            (measurable_id.prodMk measurable_const)
      rw [Measure.dirac_apply' _ hsec]
      by_cases hy : y ∈ E
      · simp only [Set.indicator_of_mem hy, Pi.one_apply]
        apply Set.indicator_of_mem
        change storedScorePrefixCurrent (i + 1)
          (appendHeterogeneousPhase i (z.1, y)) ∈ A
        rw [storedScorePrefixCurrent_append]
        exact hy
      · simp only [Set.indicator_of_notMem hy, Pi.one_apply]
        apply Set.indicator_of_notMem
        change storedScorePrefixCurrent (i + 1)
          (appendHeterogeneousPhase i (z.1, y)) ∉ A
        rw [storedScorePrefixCurrent_append]
        exact hy
    rw [lintegral_congr heval, lintegral_indicator_one hE]
    rfl
  · exact hA.preimage
      ((measurable_storedScorePrefixCurrent (i + 1)).comp
        (measurable_appendHeterogeneousPhase i))

def forgetSeedPrefix (t : Nat)
    (z : (Iic t → Score × Seed) × (Score × Seed)) :
    (Iic t → Score) × Seed :=
  (fun j ↦ (z.1 j).1, z.2.2)

theorem measurable_forgetSeedPrefix (t : Nat) :
    Measurable (forgetSeedPrefix (Score := Score) (Seed := Seed) t) := by
  unfold forgetSeedPrefix
  fun_prop

theorem forgetSeedPrefix_pathPrefixCurrent (t : Nat) :
    forgetSeedPrefix (Score := Score) (Seed := Seed) t ∘ pathPrefixCurrent t =
      pathScorePrefixCurrent t := by
  funext omega
  rfl

theorem map_forgetSeedPrefix_prefixCurrentStep
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (i : Nat) (z : (Iic i → Score × Seed) × (Score × Seed)) :
    Measure.map (forgetSeedPrefix (Score := Score) (Seed := Seed) (i + 1))
        (prefixCurrentStep (Kernel.comap P Prod.snd measurable_snd) i z) =
      scorePrefixStep P i (forgetSeedPrefix i z) := by
  rw [prefixCurrentStep_apply, scorePrefixStep_apply]
  rw [Kernel.comap_apply]
  calc
    Measure.map (forgetSeedPrefix (i + 1))
        (Measure.map (fun x ↦ advancePrefixCurrent i (z, x)) (P z.2.2)) =
      Measure.map (forgetSeedPrefix (i + 1) ∘
        (fun x ↦ advancePrefixCurrent i (z, x))) (P z.2.2) := by
          exact Measure.map_map (measurable_forgetSeedPrefix (i + 1))
            ((measurable_advancePrefixCurrent i).comp
              (measurable_const.prodMk measurable_id))
    _ = Measure.map (fun x ↦ advanceScorePrefix i
          (forgetSeedPrefix i z, x)) (P (forgetSeedPrefix i z).2) := by
          apply Measure.map_congr
          filter_upwards with x
          apply Prod.ext
          · funext j
            by_cases hj : j.1 ≤ i
            · have hne : j.1 ≠ i + 1 := by omega
              simp [forgetSeedPrefix, advancePrefixCurrent, advanceScorePrefix,
                extendIic, hj, hne]
            · have hle : j.1 ≤ i + 1 := mem_Iic.1 j.2
              have heq : j.1 = i + 1 := by omega
              simp [forgetSeedPrefix, advancePrefixCurrent, advanceScorePrefix,
                extendIic, hj, heq]
          · rfl

theorem map_pathScorePrefixCurrent_succ
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure (Score × Seed)) [IsProbabilityMeasure mu] (i : Nat) :
    Measure.map (pathScorePrefixCurrent (Score := Score) (Seed := Seed) (i + 1))
        (inhomogeneousPathMeasure (stateScheduleFromSeed P) mu) =
      (Measure.map (pathScorePrefixCurrent i)
        (inhomogeneousPathMeasure (stateScheduleFromSeed P) mu)).bind
        (scorePrefixStep (P i) i) := by
  have hordinary := map_pathPrefixCurrent_succ (X := Score × Seed)
    (stateScheduleFromSeed P) mu i
  rw [← forgetSeedPrefix_pathPrefixCurrent (Score := Score) (Seed := Seed) (i + 1),
    ← Measure.map_map (measurable_forgetSeedPrefix (i + 1))
      (measurable_pathPrefixCurrent (i + 1)), hordinary]
  rw [map_bind_of_pointwise
    (Measure.map (pathPrefixCurrent i)
      (inhomogeneousPathMeasure (stateScheduleFromSeed P) mu))
    (prefixCurrentStep (stateScheduleFromSeed P i) i) (scorePrefixStep (P i) i)
    (forgetSeedPrefix i) (forgetSeedPrefix (i + 1))
    (measurable_forgetSeedPrefix i) (measurable_forgetSeedPrefix (i + 1))]
  · rw [Measure.map_map (measurable_forgetSeedPrefix i)
      (measurable_pathPrefixCurrent i),
      forgetSeedPrefix_pathPrefixCurrent]
  · intro z
    unfold stateScheduleFromSeed
    exact map_forgetSeedPrefix_prefixCurrentStep (P i) i z

/- The terminal retained score-prefix/current-seed law is the ordinary operational
score-prefix/current-seed law. -/
theorem map_storedScorePrefixCurrent_retainedPathLaw
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure (Score × Seed)) [IsProbabilityMeasure mu]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) (t : Nat) :
    Measure.map (storedScorePrefixCurrent (Score := Score) (Seed := Seed) t)
        (retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i)
          (initialHeterogeneousHistoryLaw mu) t) =
      Measure.map (pathScorePrefixCurrent t)
        (inhomogeneousPathMeasure (stateScheduleFromSeed P) mu) := by
  induction t with
  | zero =>
      unfold retainedPathLaw initialHeterogeneousHistoryLaw
      rw [Measure.map_map (measurable_storedScorePrefixCurrent 0)
        measurable_initialHeterogeneousHistoryState]
      have hzero := Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_zero
        (stateScheduleFromSeed P) mu
      calc
        Measure.map (storedScorePrefixCurrent 0 ∘
            initialHeterogeneousHistoryState) mu =
            Measure.map (fun x : Score × Seed ↦ (fun _ : Iic 0 ↦ x.1, x.2)) mu := by
              congr 1
        _ = Measure.map (fun x : Score × Seed ↦
              (fun _ : Iic 0 ↦ x.1, x.2))
              (Measure.map (fun omega : Nat → Score × Seed ↦ omega 0)
                (inhomogeneousPathMeasure (stateScheduleFromSeed P) mu)) := by
              rw [hzero]
        _ = Measure.map
              ((fun x : Score × Seed ↦ (fun _ : Iic 0 ↦ x.1, x.2)) ∘
                (fun omega : Nat → Score × Seed ↦ omega 0))
              (inhomogeneousPathMeasure (stateScheduleFromSeed P) mu) := by
              exact Measure.map_map (by fun_prop) (measurable_pi_apply 0)
        _ = Measure.map (pathScorePrefixCurrent 0)
              (inhomogeneousPathMeasure (stateScheduleFromSeed P) mu) := by
              congr 1
              funext omega
              apply Prod.ext
              · funext j
                have hj : j.1 = 0 := Nat.eq_zero_of_le_zero (mem_Iic.1 j.2)
                simp [pathScorePrefixCurrent, hj]
              · rfl
  | succ i ih =>
      letI : IsProbabilityMeasure
          (retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i)
            (initialHeterogeneousHistoryLaw mu) i) := inferInstance
      rw [retainedPathLaw]
      rw [map_bind_of_pointwise
        (retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i)
          (initialHeterogeneousHistoryLaw mu) i)
        (heterogeneousHistoryKernel (Q i) i) (scorePrefixStep (P i) i)
        (storedScorePrefixCurrent i) (storedScorePrefixCurrent (i + 1))
        (measurable_storedScorePrefixCurrent i)
        (measurable_storedScorePrefixCurrent (i + 1))]
      · rw [ih, ← map_pathScorePrefixCurrent_succ P mu i]
      · intro z
        rw [scorePrefixStep_apply]
        exact map_storedScorePrefixCurrent_heterogeneousHistoryKernel
          (Q i) (P i) (hforget i) i z

noncomputable def independentHeterogeneousRetainedPathLaw
    (k : Nat) (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)] (mu : Measure (Score × Seed)) (t : Nat) :
    Measure (Fin k → HeterogeneousHistoryState Score Seed) :=
  Measure.pi (fun _ : Fin k ↦
    retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i)
      (initialHeterogeneousHistoryLaw mu) t)

instance independentHeterogeneousRetainedPathLaw.instIsProbabilityMeasure
    (k : Nat) (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)] (mu : Measure (Score × Seed))
    [IsProbabilityMeasure mu] (t : Nat) :
    IsProbabilityMeasure (independentHeterogeneousRetainedPathLaw k Q mu t) := by
  unfold independentHeterogeneousRetainedPathLaw
  infer_instance

def independentStoredScorePrefixCurrent {k : Nat} (t : Nat)
    (z : Fin k → HeterogeneousHistoryState Score Seed) :
    Fin k → ((Iic t → Score) × Seed) :=
  fun l ↦ storedScorePrefixCurrent t (z l)

theorem measurable_independentStoredScorePrefixCurrent {k : Nat} (t : Nat) :
    Measurable
      (independentStoredScorePrefixCurrent (Score := Score) (Seed := Seed)
        (k := k) t) := by
  unfold independentStoredScorePrefixCurrent
  apply measurable_pi_lambda
  intro l
  exact (measurable_storedScorePrefixCurrent t).comp (measurable_pi_apply l)

def independentPathScorePrefixCurrent {k : Nat} (t : Nat)
    (omega : Fin k → Nat → Score × Seed) :
    Fin k → ((Iic t → Score) × Seed) :=
  fun l ↦ pathScorePrefixCurrent t (omega l)

theorem measurable_independentPathScorePrefixCurrent {k : Nat} (t : Nat) :
    Measurable
      (independentPathScorePrefixCurrent (Score := Score) (Seed := Seed)
        (k := k) t) := by
  unfold independentPathScorePrefixCurrent
  apply measurable_pi_lambda
  intro l
  exact (measurable_pathScorePrefixCurrent t).comp (measurable_pi_apply l)

/-- Product retained executions and ordinary independent paths have the same finite
score-prefix/current-seed readout law. -/
theorem map_independentStoredScorePrefixCurrent_independentHeterogeneousRetainedPathLaw
    (k : Nat)
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure (Score × Seed)) [IsProbabilityMeasure mu]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) (t : Nat) :
    Measure.map (independentStoredScorePrefixCurrent
        (Score := Score) (Seed := Seed) (k := k) t)
        (independentHeterogeneousRetainedPathLaw k Q mu t) =
      Measure.map (independentPathScorePrefixCurrent
        (Score := Score) (Seed := Seed) (k := k) t)
        (independentPathLaw k (stateScheduleFromSeed P) mu) := by
  let scalarActual :=
    retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i)
      (initialHeterogeneousHistoryLaw mu) t
  let scalarIdeal := inhomogeneousPathMeasure (stateScheduleFromSeed P) mu
  letI : IsProbabilityMeasure scalarActual := inferInstance
  letI : IsProbabilityMeasure scalarIdeal := inferInstance
  letI : ∀ _l : Fin k, SigmaFinite
      (Measure.map (storedScorePrefixCurrent
        (Score := Score) (Seed := Seed) t) scalarActual) := fun _ ↦ by infer_instance
  letI : ∀ _l : Fin k, SigmaFinite
      (Measure.map (pathScorePrefixCurrent
        (Score := Score) (Seed := Seed) t) scalarIdeal) := fun _ ↦ by infer_instance
  unfold independentStoredScorePrefixCurrent independentPathScorePrefixCurrent
  unfold independentHeterogeneousRetainedPathLaw independentPathLaw
  unfold Ttc.CVIndependentStreamMoments.independentStreamLaw
  rw [Measure.pi_map_pi (fun _l ↦
    (measurable_storedScorePrefixCurrent
      (Score := Score) (Seed := Seed) t).aemeasurable)]
  rw [Measure.pi_map_pi (fun _l ↦
    (measurable_pathScorePrefixCurrent
      (Score := Score) (Seed := Seed) t).aemeasurable)]
  congr 1
  funext l
  exact map_storedScorePrefixCurrent_retainedPathLaw Q P mu hforget t

/-- Measurable accuracy events depending only on the finite score prefix/current seed
have identical probabilities under retained execution and the operational path model. -/
theorem independentHeterogeneousRetainedPathLaw_real_preimage_eq
    (k : Nat)
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure (Score × Seed)) [IsProbabilityMeasure mu]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) (t : Nat)
    (G : Set (Fin k → ((Iic t → Score) × Seed))) (hG : MeasurableSet G) :
    (independentHeterogeneousRetainedPathLaw k Q mu t).real
        (independentStoredScorePrefixCurrent t ⁻¹' G) =
      (independentPathLaw k (stateScheduleFromSeed P) mu).real
        (independentPathScorePrefixCurrent t ⁻¹' G) := by
  have hlaw :=
    map_independentStoredScorePrefixCurrent_independentHeterogeneousRetainedPathLaw
      k Q P mu hforget t
  rw [Measure.real, ← Measure.map_apply
      (measurable_independentStoredScorePrefixCurrent
        (Score := Score) (Seed := Seed) (k := k) t) hG,
    hlaw, Measure.map_apply
      (measurable_independentPathScorePrefixCurrent
        (Score := Score) (Seed := Seed) (k := k) t) hG,
    Measure.real]

#print axioms map_storedScorePrefixCurrent_retainedPathLaw
#print axioms
  map_independentStoredScorePrefixCurrent_independentHeterogeneousRetainedPathLaw

end Ttc.CVHeterogeneousRetainedPathLaw

import Ttc.Exec.FiniteContinuingRetryGaussian
import Ttc.Exec.FiniteContinuingRetryGeneralDecomposition

/-! A genuine state-indexed, finite continuing-retry Gaussian phase kernel. -/

namespace Ttc.FiniteContinuingRetryGaussianPhaseKernel

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open scoped ENNReal Classical Pointwise

variable {E : Type*} [MeasurableSpace E]

/-- Kernel composition for a finite time-inhomogeneous schedule. -/
noncomputable def adaptiveKernel (P : Nat → Kernel E E) : Nat → Kernel E E
  | 0 => Kernel.id
  | j + 1 => P j ∘ₖ adaptiveKernel P j

instance adaptiveKernel.isMarkovKernel
    (P : Nat → Kernel E E) [∀ j, IsMarkovKernel (P j)] (L : Nat) :
    IsMarkovKernel (adaptiveKernel P L) := by
  induction L with
  | zero => simp only [adaptiveKernel]; infer_instance
  | succ L ih => simp only [adaptiveKernel]; infer_instance

/-- Binding through the finite schedule kernel is exactly `adaptiveMarginal`. -/
theorem sampleFromKernel_adaptiveKernel
    (P : Nat → Kernel E E) [∀ j, IsMarkovKernel (P j)]
    (mu : Measure E) [IsProbabilityMeasure mu] (L : Nat) :
    sampleFromKernel (adaptiveKernel P L) mu = Arlib.adaptiveMarginal P mu L := by
  induction L with
  | zero =>
      unfold sampleFromKernel
      simp only [adaptiveKernel, Arlib.adaptiveMarginal]
      exact Measure.id_comp
  | succ L ih =>
      simp only [adaptiveKernel, Arlib.adaptiveMarginal]
      unfold sampleFromKernel at ih ⊢
      rw [← Measure.comp_assoc, ih]

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

def initialRetryState (fallback x : State n) : RetryState (State n) (State n) :=
  (x, false, fallback, 0)

theorem measurable_initialRetryState (fallback : State n) :
    Measurable (initialRetryState fallback) := by
  unfold initialRetryState
  fun_prop

/-- Full retry-state kernel after `L` combined attempts. -/
noncomputable def gaussianRetryStateKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback : State n) (L : Nat) :
    Kernel (State n) (RetryState (State n) (State n)) :=
  Kernel.comap
    (adaptiveKernel (gaussianRetrySchedule K hK delta s c hdelta hc steps) L)
    (initialRetryState fallback) (measurable_initialRetryState fallback)

instance gaussianRetryStateKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback : State n) (L : Nat) :
    IsMarkovKernel
      (gaussianRetryStateKernel K hK delta s c hdelta hc steps fallback L) := by
  unfold gaussianRetryStateKernel
  infer_instance

/-- Pointwise kernel law equals the concrete retry marginal from the earlier decomposition. -/
theorem gaussianRetryStateKernel_apply
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback x : State n) (L : Nat) :
    gaussianRetryStateKernel K hK delta s c hdelta hc steps fallback L x =
      Arlib.adaptiveMarginal
        (gaussianRetrySchedule K hK delta s c hdelta hc steps)
        (Measure.dirac (initialRetryState fallback x)) L := by
  unfold gaussianRetryStateKernel
  rw [Kernel.comap_apply]
  have h := sampleFromKernel_adaptiveKernel
    (gaussianRetrySchedule K hK delta s c hdelta hc steps)
    (Measure.dirac (initialRetryState fallback x)) L
  simpa only [sampleFromKernel, Measure.dirac_bind,
    Kernel.measurable] using h

/-- Unbounded-cost finite retry phase, carrying its actual accumulated query count. -/
noncomputable def phaseCostOutput (fallback : State n) (z : RetryState (State n) (State n)) :
    ENNReal × State n :=
  (accumulatedCost z,
    Ttc.FiniteContinuingRetryDecomposition.cutoffOutput fallback z)

theorem measurable_phaseCostOutput (fallback : State n) :
    Measurable (phaseCostOutput fallback) :=
  measurable_accumulatedCost.prodMk
    (Ttc.FiniteContinuingRetryDecomposition.measurable_cutoffOutput fallback)

noncomputable def gaussianFinitePhaseCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback : State n) (L : Nat) : Kernel (State n) (ENNReal × State n) :=
  Kernel.map
    (gaussianRetryStateKernel K hK delta s c hdelta hc steps fallback L)
    (phaseCostOutput fallback)

instance gaussianFinitePhaseCostedKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback : State n) (L : Nat) :
    IsMarkovKernel
      (gaussianFinitePhaseCostedKernel K hK delta s c hdelta hc steps fallback L) := by
  unfold gaussianFinitePhaseCostedKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_phaseCostOutput fallback)

theorem map_snd_gaussianFinitePhaseCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback x : State n) (L : Nat) :
    Measure.map Prod.snd
        (gaussianFinitePhaseCostedKernel K hK delta s c hdelta hc steps fallback L x) =
      Measure.map (Ttc.FiniteContinuingRetryDecomposition.cutoffOutput fallback)
        (Arlib.adaptiveMarginal
          (gaussianRetrySchedule K hK delta s c hdelta hc steps)
          (Measure.dirac (initialRetryState fallback x)) L) := by
  rw [gaussianFinitePhaseCostedKernel,
    Kernel.map_apply _ (measurable_phaseCostOutput fallback),
    Measure.map_map measurable_snd (measurable_phaseCostOutput fallback),
    gaussianRetryStateKernel_apply]
  rfl

/-- Exact phase mean: no rejection overhead is hidden outside the accumulated coordinate. -/
theorem lintegral_fst_gaussianFinitePhaseCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback x : State n) (L : Nat) :
    ∫⁻ z, z.1
        ∂(gaussianFinitePhaseCostedKernel K hK delta s c hdelta hc steps fallback L x) =
      ∫⁻ z, accumulatedCost z
        ∂(Arlib.adaptiveMarginal
          (gaussianRetrySchedule K hK delta s c hdelta hc steps)
          (Measure.dirac (initialRetryState fallback x)) L) := by
  rw [gaussianFinitePhaseCostedKernel,
    Kernel.map_apply _ (measurable_phaseCostOutput fallback),
    lintegral_map measurable_fst (measurable_phaseCostOutput fallback),
    gaussianRetryStateKernel_apply]
  simp only [phaseCostOutput]

/-- Executable outer-cutoff phase: its recorded charge is deterministically at most
`queryCutoff`, independently of all rejection-loop outcomes. -/
noncomputable def cutoffPhaseCostOutput (fallback : State n) (queryCutoff : ENNReal)
    (z : RetryState (State n) (State n)) : ENNReal × State n :=
  (cutoffQueryCharge queryCutoff z, queryCutoffOutput fallback queryCutoff z)

theorem measurable_cutoffPhaseCostOutput (fallback : State n) (queryCutoff : ENNReal) :
    Measurable (cutoffPhaseCostOutput fallback queryCutoff) := by
  apply Measurable.prodMk
  · exact measurable_accumulatedCost.min measurable_const
  · exact measurable_queryCutoffOutput fallback queryCutoff

noncomputable def gaussianCutoffPhaseCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback : State n) (L : Nat) (queryCutoff : ENNReal) :
    Kernel (State n) (ENNReal × State n) :=
  Kernel.map
    (gaussianRetryStateKernel K hK delta s c hdelta hc steps fallback L)
    (cutoffPhaseCostOutput fallback queryCutoff)

instance gaussianCutoffPhaseCostedKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback : State n) (L : Nat) (queryCutoff : ENNReal) :
    IsMarkovKernel
      (gaussianCutoffPhaseCostedKernel K hK delta s c hdelta hc steps
        fallback L queryCutoff) := by
  unfold gaussianCutoffPhaseCostedKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_cutoffPhaseCostOutput fallback queryCutoff)

theorem stepMean_gaussianCutoffPhaseCostedKernel_le
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (fallback x : State n) (L : Nat) (queryCutoff : ENNReal) :
    Ttc.SequentialCost.stepMean
      (fun _ => gaussianCutoffPhaseCostedKernel K hK delta s c hdelta hc steps
        fallback L queryCutoff) 0 x ≤ queryCutoff := by
  unfold Ttc.SequentialCost.stepMean gaussianCutoffPhaseCostedKernel
  rw [Kernel.map_apply _ (measurable_cutoffPhaseCostOutput fallback queryCutoff),
    lintegral_map measurable_fst
      (measurable_cutoffPhaseCostOutput fallback queryCutoff)]
  calc
    (∫⁻ z, cutoffQueryCharge queryCutoff z
      ∂gaussianRetryStateKernel K hK delta s c hdelta hc steps fallback L x) ≤
        ∫⁻ _, queryCutoff
          ∂gaussianRetryStateKernel K hK delta s c hdelta hc steps fallback L x :=
      lintegral_mono (cutoffQueryCharge_le queryCutoff)
    _ = queryCutoff := by simp

#print axioms sampleFromKernel_adaptiveKernel
#print axioms map_snd_gaussianFinitePhaseCostedKernel
#print axioms lintegral_fst_gaussianFinitePhaseCostedKernel
#print axioms stepMean_gaussianCutoffPhaseCostedKernel_le

end Ttc.FiniteContinuingRetryGaussianPhaseKernel

import Ttc.Exec.FiniteContinuingRetryConcreteDecomposition
import Ttc.Exec.CostedPathwisePhaseKernel
import Ttc.Volume.CVCombinedContinuingAccept

/-!
# Operational Gaussian specialization of finite continuing retry

One retry runs the existing stopped-raw, cost-recording implementation of a fixed
number of lazy speedy steps, tensors its endpoint with the independent speedy coin, and
charges the recorded number of membership queries.  Acceptance combines shrink
membership and the speedy coin test; a rejection continues from the raw endpoint.
-/

namespace Ttc.FiniteContinuingRetryGaussian

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.FiniteContinuingRetry Ttc.CostedStatefulSpeedyPhases
open Ttc.CostedWarmPhaseRejection Ttc.SpeedyRejection
open Ttc.CVCombinedContinuingAccept Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev CostedCoin (n : Nat) := ENNReal × (State n × Real)

/-- Add the independent speedy coin to one actual, cost-recording lazy-speedy phase. -/
noncomputable def combinedRoundCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) : Kernel (State n) (CostedCoin n) :=
  let rho := speedyPhaseCostedKernel K hK delta s hdelta t
  Kernel.map
    (Kernel.compProd rho
      (Kernel.const (State n × (ENNReal × State n)) unitCoin))
    (fun p : (ENNReal × State n) × Real => (p.1.1, (p.1.2, p.2)))

instance combinedRoundCostedKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) :
    IsMarkovKernel (combinedRoundCostedKernel K hK delta s hdelta t) := by
  unfold combinedRoundCostedKernel
  dsimp only
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Pointwise identification with the existing costed point/coin law. -/
theorem combinedRoundCostedKernel_apply_eq
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) (x : State n) :
    combinedRoundCostedKernel K hK delta s hdelta t x =
      costedSpeedyRoundLaw (speedyPhaseCostedKernel K hK delta s hdelta t x) := by
  let rho := speedyPhaseCostedKernel K hK delta s hdelta t
  have hprod : (Kernel.compProd rho
      (Kernel.const (State n × (ENNReal × State n)) unitCoin)) x =
      (rho x).prod unitCoin := by
    calc
      _ = (rho x) ⊗ₘ Kernel.const (ENNReal × State n) unitCoin := by
        ext S hS
        rw [Kernel.compProd_apply hS, Measure.compProd_apply hS]
        rfl
      _ = _ := Measure.compProd_const
  rw [combinedRoundCostedKernel, Kernel.map_apply _ (by fun_prop), hprod]
  rfl

/-- Forgetting the cost gives exactly one point drawn from the lazy-speedy iterate,
tensored with the independent uniform coin. -/
theorem map_snd_combinedRoundCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) (x : State n) :
    Measure.map Prod.snd (combinedRoundCostedKernel K hK delta s hdelta t x) =
      proposal (iteratedKernel (lazy (speedyMetropolisGaussian K delta s)) t x) := by
  rw [combinedRoundCostedKernel_apply_eq hK delta s hdelta t x,
    map_snd_costedSpeedyRoundLaw,
    map_snd_speedyPhaseCostedKernel hK delta s hdelta t x]

/-- The coin is free: the expected retry charge is the expected actual membership-query
count of the stopped raw lazy-speedy execution. -/
theorem lintegral_fst_combinedRoundCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) (x : State n) :
    ∫⁻ z, z.1 ∂(combinedRoundCostedKernel K hK delta s hdelta t x) =
      ∫⁻ omega, Ttc.RawGaussianLazyStoppedExecution.actualMembershipQueryCount t omega
        ∂(Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedExecution
          K hK delta s hdelta (Measure.dirac x)) := by
  rw [combinedRoundCostedKernel_apply_eq hK delta s hdelta t x,
    lintegral_fst_costedSpeedyRoundLaw]
  have h := stepMean_speedyPhaseCostedKernel hK delta s hdelta t x
  simpa only [Ttc.SequentialCost.stepMean] using h

/-- Lift the combined acceptance event past the cost coordinate. -/
noncomputable def costedCombinedAccept (K : Set (State n)) (c s : Real) :
    Set (CostedCoin n) := Prod.snd ⁻¹' combinedAccept K c s

theorem measurableSet_costedCombinedAccept
    {K : Set (State n)} (hK : MeasurableSet K) {c s : Real} (hc : c ≠ 0) :
    MeasurableSet (costedCombinedAccept K c s) :=
  (measurableSet_combinedAccept hK hc).preimage measurable_snd

def rejectedNext (z : CostedCoin n) : State n := combinedNext z.2

theorem measurable_rejectedNext : Measurable (rejectedNext : CostedCoin n → State n) :=
  measurable_combinedNext.comp measurable_snd

noncomputable def acceptedOutput (c : Real) (z : CostedCoin n) : State n :=
  combinedOutput c z.2

theorem measurable_acceptedOutput (c : Real) :
    Measurable (acceptedOutput (n := n) c) :=
  (measurable_combinedOutput c).comp measurable_snd

def roundQueryCost (z : CostedCoin n) : ENNReal := z.1

theorem measurable_roundQueryCost : Measurable (roundQueryCost : CostedCoin n → ENNReal) :=
  measurable_fst

/-- The actual finite continuing-retry transition family.  The deadline may grow with
the retry index because conditioning on a smaller survival event inflates warmth. -/
noncomputable def gaussianRetrySchedule
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) :
    Nat → Kernel (RetryState (State n) (State n)) (RetryState (State n) (State n)) :=
  retryStep
    (fun j => combinedRoundCostedKernel K hK delta s hdelta (steps j))
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (acceptedOutput c) (measurable_acceptedOutput c)
    roundQueryCost measurable_roundQueryCost

instance gaussianRetrySchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (j : Nat) :
    IsMarkovKernel (gaussianRetrySchedule K hK delta s c hdelta hc steps j) := by
  unfold gaussianRetrySchedule
  infer_instance

/-- Exact pointwise forget-cost law used by the sequential phase schedule. -/
theorem gaussianRetryCandidate_forgetCost
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (steps : Nat → Nat) (j : Nat) (x : State n) :
    Measure.map Prod.snd
        (combinedRoundCostedKernel K hK delta s hdelta (steps j) x) =
      proposal (iteratedKernel (lazy (speedyMetropolisGaussian K delta s))
        (steps j) x) :=
  map_snd_combinedRoundCostedKernel hK delta s hdelta (steps j) x

/-- Law-level form of cost erasure.  This is the exact seam needed after conditioning a
retry history on survival: averaging the state-indexed costed candidates and then dropping
cost is the same as first taking the lazy-speedy endpoint law and then adding one fresh
independent coin. -/
theorem map_snd_sampleFrom_combinedRoundCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat)
    (nu : Measure (State n)) [IsProbabilityMeasure nu] :
    Measure.map Prod.snd
        (sampleFromKernel (combinedRoundCostedKernel K hK delta s hdelta t) nu) =
      proposal
        (sampleFromKernel
          (iteratedKernel (lazy (speedyMetropolisGaussian K delta s)) t) nu) := by
  ext T hT
  rw [Measure.map_apply measurable_snd hT]
  unfold sampleFromKernel
  rw [Measure.bind_apply (hT.preimage measurable_snd)
    (combinedRoundCostedKernel K hK delta s hdelta t).aemeasurable]
  simp_rw [← Measure.map_apply measurable_snd hT,
    map_snd_combinedRoundCostedKernel hK delta s hdelta t]
  unfold proposal
  rw [Measure.prod_apply hT]
  have hf : Measurable (fun x : State n => unitCoin (Prod.mk x ⁻¹' T)) := by
    simpa only [Kernel.const_apply] using
      (Kernel.measurable_kernel_prodMk_left
        (κ := Kernel.const (State n) unitCoin) hT)
  rw [Measure.lintegral_bind
    (iteratedKernel (lazy (speedyMetropolisGaussian K delta s)) t).aemeasurable
    hf.aemeasurable]
  apply lintegral_congr
  intro x
  rw [Measure.prod_apply hT]

/-! ## A finite outer membership-query cutoff -/

/-- Postprocess a finite retry state by returning its accepted output only when the
recorded query count is below the outer budget.  An executable implementation can stop
as soon as this budget is reached and return the same fallback. -/
noncomputable def queryCutoffOutput (fallback : State n) (cutoff : ENNReal)
    (z : RetryState (State n) (State n)) : State n :=
  if accumulatedCost z < cutoff then
    Ttc.FiniteContinuingRetryDecomposition.cutoffOutput fallback z
  else fallback

theorem measurable_queryCutoffOutput (fallback : State n) (cutoff : ENNReal) :
    Measurable (queryCutoffOutput fallback cutoff) := by
  apply Measurable.ite
  · exact measurableSet_lt measurable_accumulatedCost measurable_const
  · exact Ttc.FiniteContinuingRetryDecomposition.measurable_cutoffOutput fallback
  · exact measurable_const

/-- The actually charged cost of the cutoff implementation. -/
def cutoffQueryCharge (cutoff : ENNReal) (z : RetryState (State n) (State n)) : ENNReal :=
  min (accumulatedCost z) cutoff

theorem cutoffQueryCharge_le (cutoff : ENNReal)
    (z : RetryState (State n) (State n)) : cutoffQueryCharge cutoff z ≤ cutoff :=
  min_le_right _ _

/-- Markov coupling for the whole continuing-retry phase.  Thus a bound on the expected
recorded cost converts to a deterministic finite query budget without changing the
unbounded retry law except on the timeout event. -/
theorem tvLe_queryCutoffOutput_of_lintegral_div_le
    (mu : Measure (RetryState (State n) (State n))) [IsProbabilityMeasure mu]
    (fallback : State n) {cutoff eta : ENNReal}
    (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (hmean : (∫⁻ z, accumulatedCost z ∂mu) / cutoff ≤ eta) :
    TVLe
      (Measure.map (queryCutoffOutput fallback cutoff) mu)
      (Measure.map
        (Ttc.FiniteContinuingRetryDecomposition.cutoffOutput fallback) mu)
      eta := by
  have htimeout : mu {z | cutoff ≤ accumulatedCost z} ≤ eta :=
    (meas_ge_le_lintegral_div measurable_accumulatedCost.aemeasurable
      hcut0 hcuttop).trans hmean
  apply Arlib.tvLe_map_map_of_measure_ne_le
    (measurable_queryCutoffOutput fallback cutoff)
    (Ttc.FiniteContinuingRetryDecomposition.measurable_cutoffOutput fallback)
  exact htimeout.trans' (measure_mono (by
    intro z hz
    change queryCutoffOutput fallback cutoff z ≠
      Ttc.FiniteContinuingRetryDecomposition.cutoffOutput fallback z at hz
    change cutoff ≤ accumulatedCost z
    by_contra hnot
    have hlt : accumulatedCost z < cutoff := lt_of_not_ge hnot
    simp only [queryCutoffOutput, if_pos hlt] at hz
    exact hz rfl))

#print axioms combinedRoundCostedKernel_apply_eq
#print axioms map_snd_combinedRoundCostedKernel
#print axioms lintegral_fst_combinedRoundCostedKernel
#print axioms gaussianRetryCandidate_forgetCost
#print axioms map_snd_sampleFrom_combinedRoundCostedKernel
#print axioms tvLe_queryCutoffOutput_of_lintegral_div_le

end Ttc.FiniteContinuingRetryGaussian

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVHybridExactAccuracy
import Ttc.Volume.CVConcreteEstimatorParameters

/-!
# Concrete estimator parameters for the source hybrid schedule
-/

namespace Ttc.CVHybridSchedule

open Arlib.GaussianCooling
open Ttc.CVAdaptive

noncomputable def estimatorKappa (eps : Real) : Real := varBudget eps / 2

noncomputable def estimatorSampleThreshold
    (n c J : Nat) (eps : Real) : Real :=
  max 42 (max
    (4 * (c : Real) / ((n : Real) * varBudget eps))
    (14 * (J : Real) / varBudget eps))

noncomputable def estimatorSamples (n c J : Nat) (eps : Real) : Nat :=
  ⌈estimatorSampleThreshold n c J eps⌉₊ + 1

theorem estimatorSamples_pos (n c J : Nat) (eps : Real) :
    0 < estimatorSamples n c J eps := by simp [estimatorSamples]

theorem estimatorSampleThreshold_le_cast (n c J : Nat) (eps : Real) :
    estimatorSampleThreshold n c J eps <= (estimatorSamples n c J eps : Real) := by
  have h := Nat.le_ceil (estimatorSampleThreshold n c J eps)
  rw [estimatorSamples]
  push_cast
  linarith

theorem estimatorSamples_ge_42 (n c J : Nat) (eps : Real) :
    42 <= (estimatorSamples n c J eps : Real) :=
  (le_max_left 42 _).trans (estimatorSampleThreshold_le_cast n c J eps)

theorem estimatorSamples_cold_budget {n c J : Nat} (hn : 1 <= n)
    {eps : Real} (heps : 0 < eps) :
    2 * (c : Real) / (n : Real) <=
      (estimatorSamples n c J eps : Real) * estimatorKappa eps := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hV : 0 < varBudget eps := varBudget_pos heps
  have hk := estimatorSampleThreshold_le_cast n c J eps
  have hterm : 4 * (c : Real) / ((n : Real) * varBudget eps) <=
      (estimatorSamples n c J eps : Real) :=
    (le_max_left _ (14 * (J : Real) / varBudget eps)).trans
      ((le_max_right 42 _).trans hk)
  rw [div_le_iff₀ (mul_pos hnR hV)] at hterm
  rw [div_le_iff₀ hnR]
  unfold estimatorKappa
  nlinarith

theorem estimatorSamples_hot_budget {n c J : Nat} {eps : Real} (heps : 0 < eps) :
    7 * (J : Real) <=
      (estimatorSamples n c J eps : Real) * estimatorKappa eps := by
  have hV : 0 < varBudget eps := varBudget_pos heps
  have hk := estimatorSampleThreshold_le_cast n c J eps
  have hterm : 14 * (J : Real) / varBudget eps <=
      (estimatorSamples n c J eps : Real) :=
    (le_max_right (4 * (c : Real) / ((n : Real) * varBudget eps)) _).trans
      ((le_max_right 42 _).trans hk)
  rw [div_le_iff₀ hV] at hterm
  unfold estimatorKappa
  nlinarith

theorem estimator_exp_budget {eps : Real} (heps : 0 < eps) :
    Real.exp (estimatorKappa eps + estimatorKappa eps) - 1 <= eps ^ 2 / 5 := by
  have heq : estimatorKappa eps + estimatorKappa eps = varBudget eps := by
    unfold estimatorKappa
    ring
  rw [heq]
  exact varBudget_spec eps heps

/-- All estimator-side scalar premises for the hybrid exact-accuracy theorem. -/
theorem estimator_parameter_bundle {n c J : Nat} (hn : 1 <= n)
    {eps : Real} (heps : 0 < eps) :
    0 < estimatorSamples n c J eps ∧
    0 <= estimatorKappa eps ∧
    42 <= (estimatorSamples n c J eps : Real) ∧
    2 * (c : Real) / (n : Real) <=
      (estimatorSamples n c J eps : Real) * estimatorKappa eps ∧
    7 * (J : Real) <=
      (estimatorSamples n c J eps : Real) * estimatorKappa eps ∧
    Real.exp (estimatorKappa eps + estimatorKappa eps) - 1 <= eps ^ 2 / 5 := by
  exact ⟨estimatorSamples_pos n c J eps, (by
      unfold estimatorKappa
      positivity [varBudget_pos heps]),
    estimatorSamples_ge_42 n c J eps, estimatorSamples_cold_budget hn heps,
    estimatorSamples_hot_budget heps, estimator_exp_budget heps⟩

/-- Concrete exact-law estimator theorem for the complete hybrid Gaussian block. -/
theorem packed_median_accuracy_exact_concrete {n J : Nat} (hn : 3 <= n)
    {K : Set (Space n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < MeasureTheory.volume K)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : MeasureTheory.volume K ≠ ⊤)
    {C s0 eps p : Real} (hC : 0 < C) (hs0 : 0 < s0) (heps : 0 < eps)
    (hp : 0 < p) (hp1 : p < 1)
    (hbelow : ∀ j < J,
      Arlib.GaussianCooling.Chunked.adaptiveChunkStart
        (C ^ 2 * n) (coldEnd n s0) j <= C ^ 2 * n)
    (hKR : K ⊆ Metric.closedBall 0 (C * Real.sqrt n)) :
    let c := coldPhases n s0
    let k := estimatorSamples n c J eps
    let r := concretePackedReps eps p
    let m := c + Arlib.GaussianCooling.Chunked.adaptiveChunkOffset
      (C ^ 2 * n) (coldEnd n s0) J
    let sched := sigmaSq n (C ^ 2 * n) s0
    let nu : Fin r -> Fin m -> Fin k -> MeasureTheory.Measure (Space n) :=
      fun _ i _ => Arlib.GaussianCooling.coolLaw (m + 1) sched K i
    let g : Fin r -> Fin m -> Fin k -> Space n -> Real :=
      fun _ i _ => Arlib.GaussianCooling.phaseScore (m + 1) sched K i
    1 - p <= (Arlib.Probability.runMeasure
      (Arlib.GaussianCooling.packedPhaseLaw nu)).real
      {omega | Arlib.Probability.medianSel
        (fun t => Arlib.GaussianCooling.chain (m + 1) sched K 0 *
          ∏ i, Ttc.CVPacked.phaseAvg g t i omega)
          ∈ Ttc.relErr eps (Arlib.GaussianCooling.chain (m + 1) sched K m)} := by
  dsimp only
  let c := coldPhases n s0
  let k := estimatorSamples n c J eps
  let r := concretePackedReps eps p
  have hb := estimator_parameter_bundle (c := c) (J := J) (by omega : 1 <= n) heps
  have hrb := concretePackedReps_bundle (eps := eps) hp hp1
  exact packed_median_accuracy_exact hn hb.1 hrb.1 hKc hKcl hKb hvol hball hfin hC hs0
    hb.2.1 hb.2.1 heps hb.2.2.1 hb.2.2.2.1 hbelow hb.2.2.2.2.1 hKR
    hb.2.2.2.2.2 hp hrb.2

end Ttc.CVHybridSchedule

#print axioms Ttc.CVHybridSchedule.estimator_parameter_bundle
#print axioms Ttc.CVHybridSchedule.packed_median_accuracy_exact_concrete

import Ttc.Exec.CVScoreSeedExceptionalCost
import Arlib.Probability.AdaptiveTVTelescopeMixture

/-!
# Exact score/seed reference schedule and hybrid replacement

The ideal transition at phase `i` forgets its input and draws the exact augmented graph
reference for phase `i+1`.  Thus its phase-`i` marginal is literally the phase-`i`
reference.  `TVLe.adaptiveMarginal_of_idealMixture` then reduces a whole dependent
operational path to distributional one-phase comparisons averaged under those exact
reference marginals.  No warmness of an actual finite-retry seed is used.
-/

namespace Ttc.CVScoreSeedReferenceSchedule

open MeasureTheory ProbabilityTheory
open Arlib
open Ttc.CVGaussianScoreSeedPhaseKernel
open scoped ENNReal Classical BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- Input-forgetting exact transition from reference marginal `i` to `i+1`. -/
noncomputable def referenceSchedule (tau : Nat → Measure X) : Nat → Kernel X X :=
  fun i ↦ Kernel.const X (tau (i + 1))

instance referenceSchedule.isMarkovKernel
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)] (i : Nat) :
    IsMarkovKernel (referenceSchedule tau i) := by
  unfold referenceSchedule
  infer_instance

/-- Exact phase marginal of the input-forgetting reference schedule. -/
theorem adaptiveMarginal_referenceSchedule
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)] (i : Nat) :
    Arlib.adaptiveMarginal (referenceSchedule tau) (tau 0) i = tau i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Arlib.adaptiveMarginal, ih]
      unfold referenceSchedule
      rw [MeasureTheory.Measure.const_comp]
      simp

/-- Distributional hybrid replacement.  The only phase premise is the actual operational
kernel averaged under the exact phase-`i` reference law. -/
theorem tvLe_adaptiveMarginal_referenceSchedule
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (phaseError : Nat → ENNReal)
    (hphase : ∀ i, TVLe ((tau i).bind (P i)) (tau (i + 1)) (phaseError i))
    (t : Nat) :
    TVLe (Arlib.adaptiveMarginal P (tau 0) t) (tau t)
      (∑ i ∈ Finset.range t, phaseError i) := by
  have h := TVLe.adaptiveMarginal_of_idealMixture_same P (referenceSchedule tau)
    (tau 0) phaseError (fun i ↦ ?_) t
  · simpa only [adaptiveMarginal_referenceSchedule tau t] using h
  · rw [adaptiveMarginal_referenceSchedule tau i]
    unfold referenceSchedule
    rw [MeasureTheory.Measure.const_comp]
    simpa using hphase i

/-- `k` independently restarted copies of the dependent operational path replace by `k`
copies of the exact terminal score/seed reference at additive cost `k * Σ phaseError`. -/
theorem tvLe_pi_adaptiveMarginal_referenceSchedule
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (phaseError : Nat → ENNReal)
    (hphase : ∀ i, TVLe ((tau i).bind (P i)) (tau (i + 1)) (phaseError i))
    (t k : Nat) :
    TVLe
      (Measure.pi (fun _ : Fin k ↦ Arlib.adaptiveMarginal P (tau 0) t))
      (Measure.pi (fun _ : Fin k ↦ tau t))
      ((k : ENNReal) * (∑ i ∈ Finset.range t, phaseError i)) := by
  letI : ∀ _ : Fin k,
      IsProbabilityMeasure (Arlib.adaptiveMarginal P (tau 0) t) := fun _ ↦ by infer_instance
  letI : ∀ _ : Fin k, IsProbabilityMeasure (tau t) := fun _ ↦ by infer_instance
  have hcoord : ∀ _ : Fin k,
      TVLe (Arlib.adaptiveMarginal P (tau 0) t) (tau t)
        (∑ i ∈ Finset.range t, phaseError i) := fun _ ↦
    tvLe_adaptiveMarginal_referenceSchedule P tau phaseError hphase t
  have hpi := TVLe.pi hcoord
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hpi

/-- Uniform phase-error arithmetic: `k` paths and `t` phases cost exactly `k*t*b`. -/
theorem tvLe_pi_adaptiveMarginal_referenceSchedule_const
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (b : ENNReal)
    (hphase : ∀ i, TVLe ((tau i).bind (P i)) (tau (i + 1)) b)
    (t k : Nat) :
    TVLe
      (Measure.pi (fun _ : Fin k ↦ Arlib.adaptiveMarginal P (tau 0) t))
      (Measure.pi (fun _ : Fin k ↦ tau t))
      (((k * t : Nat) : ENNReal) * b) := by
  have h := tvLe_pi_adaptiveMarginal_referenceSchedule P tau (fun _ ↦ b) hphase t k
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, mul_assoc] using h

/-- The source `1/20` hybrid allocation, separated cleanly from phase execution. -/
theorem tvLe_pi_adaptiveMarginal_referenceSchedule_twentieth
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (b : ENNReal)
    (hphase : ∀ i, TVLe ((tau i).bind (P i)) (tau (i + 1)) b)
    (t k : Nat) (hbudget : (((k * t : Nat) : ENNReal) * b) ≤ 1 / 20) :
    TVLe
      (Measure.pi (fun _ : Fin k ↦ Arlib.adaptiveMarginal P (tau 0) t))
      (Measure.pi (fun _ : Fin k ↦ tau t)) (1 / 20) :=
  (tvLe_pi_adaptiveMarginal_referenceSchedule_const P tau b hphase t k).mono hbudget

/-! The Gaussian specialization is definitionally the exact graph law requested by the
operational phase. -/

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def gaussianReferenceFamily
    (m : Nat) (sigmaSq : Nat → Real) (K : Set (State n)) (c : Real) :
    Nat → Measure (ScoreSeed n) :=
  fun i ↦ scoreSeedReference c (Arlib.GaussianCooling.coolLaw m sigmaSq K i)

theorem gaussianReferenceFamily_apply
    (m : Nat) (sigmaSq : Nat → Real) (K : Set (State n)) (c : Real) (i : Nat) :
    gaussianReferenceFamily m sigmaSq K c i =
      scoreSeedReference c (Arlib.GaussianCooling.coolLaw m sigmaSq K i) := rfl

#print axioms adaptiveMarginal_referenceSchedule
#print axioms tvLe_adaptiveMarginal_referenceSchedule
#print axioms tvLe_pi_adaptiveMarginal_referenceSchedule
#print axioms tvLe_pi_adaptiveMarginal_referenceSchedule_const
#print axioms tvLe_pi_adaptiveMarginal_referenceSchedule_twentieth
#print axioms gaussianReferenceFamily_apply

end Ttc.CVScoreSeedReferenceSchedule

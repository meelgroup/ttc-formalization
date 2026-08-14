import Ttc.Exec.FiniteContinuingRetryInitialMeasure
import Ttc.Volume.ContinuingRejectionSelective

/-! Selective first-hit TV decomposition for an arbitrary incoming law. -/

namespace Ttc.FiniteContinuingRetrySelectiveInitialLaw

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryDecomposition
open Ttc.FiniteContinuingRetryInitialMeasure
open Ttc.FiniteContinuingRetryGeneralDecomposition
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical BigOperators

variable {E C F : Type*} [MeasurableSpace E] [MeasurableSpace C] [MeasurableSpace F]

/-- An arbitrary-law retry phase only needs an accurate accepted law while its survival
mass is at least `eta`.  Exact first-hit conservation charges every later accepted piece,
together with the unresolved tail, by `eta + r^L`. -/
theorem tvLe_cutoffOutput_of_accepted_significant_initialLaw
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (fallback : F) (L : Nat)
    (target : Measure F) [IsProbabilityMeasure target]
    (eta r acceptedError : ENNReal)
    (hs0 : ∀ j, survivalOf candidate A hA next hnext out hout roundCost hcost
      rho fallback j ≠ 0)
    (ha0 : ∀ j, proposalOf candidate A hA next hnext out hout roundCost hcost
      rho fallback j A ≠ 0)
    (haccepted : ∀ i : Fin L,
      eta ≤ survivalOf candidate A hA next hnext out hout roundCost hcost
        rho fallback i →
      TVLe (Measure.map out (condOn
        (proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback i) A))
        target acceptedError)
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ survivalOf candidate A hA next hnext out hout roundCost hcost
      rho fallback j → proposalOf candidate A hA next hnext out hout roundCost hcost
        rho fallback j Aᶜ ≤ r) :
    TVLe
      (Measure.map (cutoffOutput (E := E) fallback)
        (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback L))
      target (acceptedError + (eta + r ^ L)) := by
  let p : Nat → Measure C := fun j ↦
    proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback j
  have hpall : ∀ j, IsProbabilityMeasure (p j) := by
    intro j
    dsimp only [p]
    unfold proposalOf sampleFromKernel
    letI : IsProbabilityMeasure (condOn
        (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j)
        Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ (hs0 j) (measure_ne_top _ _)
    letI : IsProbabilityMeasure ((condOn
        (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j)
        Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    infer_instance
  letI : ∀ j, IsProbabilityMeasure (p j) := hpall
  let w : Fin L → ENNReal := fun i ↦
    survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback i * p i A
  let wN : Nat → ENNReal := fun j ↦
    survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j * p j A
  let q : Fin L → Measure F := fun i ↦ Measure.map out (condOn (p i) A)
  let sN : Nat → ENNReal := fun j ↦
    survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j
  have hqprob : ∀ i, IsProbabilityMeasure (q i) := by
    intro i
    dsimp only [q]
    letI : IsProbabilityMeasure (condOn (p i) A) :=
      Arlib.isProbabilityMeasure_condOn _ (by simpa only [p] using ha0 i)
        (measure_ne_top _ _)
    exact Measure.isProbabilityMeasure_map hout.aemeasurable
  letI : ∀ i, IsProbabilityMeasure (q i) := hqprob
  have houtEq : Measure.map (cutoffOutput (E := E) fallback)
      (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback L) =
      Ttc.ContinuingRejectionSignificant.acceptedMixture L w q (sN L) fallback := by
    have hgeneric := map_cutoffOutput_eq_acceptedMixture_of_apply
      (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback L)
      L w q fallback (by
        intro T hT
        have hacc := acceptedOutputEvent_eq_sum_of candidate A hA next hnext out hout
          roundCost hcost rho fallback L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j) hT
        rw [← Fin.sum_univ_eq_sum_range] at hacc
        simpa only [w, q, p, sN] using hacc)
    simpa only [sN, survivalOf,
      Ttc.FiniteContinuingRetryDecomposition.runningStates,
      Ttc.FiniteContinuingRetry.runningStates] using hgeneric
  have hmass : (∑ i, w i) + sN L = 1 := by
    have hpart := accepted_add_survival_eq_one
      (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback L)
    have hacc := acceptedOutputEvent_eq_sum_of candidate A hA next hnext out hout roundCost
      hcost rho fallback L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j)
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set F))
    rw [hacc, ← Fin.sum_univ_eq_sum_range] at hpart
    simpa only [w, q, p, sN, survivalOf,
      Ttc.FiniteContinuingRetryDecomposition.runningStates,
      Ttc.FiniteContinuingRetry.runningStates,
      measure_univ, mul_one] using hpart
  have hsbase : sN 0 ≤ 1 := prob_le_one
  have hsmono : ∀ j, sN (j + 1) ≤ sN j := by
    intro j
    dsimp only [sN]
    rw [survivalOf_succ candidate A hA next hnext out hout roundCost hcost rho fallback j
      (hs0 j)]
    exact (mul_le_mul_left' prob_le_one _).trans_eq (mul_one _)
  have hscontract : ∀ j, eta ≤ sN j → sN (j + 1) ≤ r * sN j := by
    intro j hj
    dsimp only [sN] at hj ⊢
    rw [survivalOf_succ candidate A hA next hnext out hout roundCost hcost rho fallback j
      (hs0 j)]
    simpa only [p, mul_comm] using
      (mul_le_mul_left' (hreject j hj)
        (survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j))
  have hrec : ∀ j, j < L → wN j + sN (j + 1) = sN j := by
    intro j _hj
    dsimp only [wN, sN]
    rw [survivalOf_succ candidate A hA next hnext out hout roundCost hcost rho fallback j
      (hs0 j), ← mul_add, prob_add_prob_compl hA, mul_one]
  have hbadN := Ttc.ContinuingRejectionSelective.badWeights_add_survival_le_eta_add_pow
    wN sN L eta r hrec hsbase hr hsmono hscontract
  have hbad : (∑ i ∈ (Finset.univ : Finset (Fin L)).filter
      (fun i : Fin L ↦ ¬ eta ≤ sN (i : Nat)), w i) + sN L ≤ eta + r ^ L := by
    rw [Finset.sum_filter] at hbadN ⊢
    rw [← Fin.sum_univ_eq_sum_range] at hbadN
    simpa only [w, wN] using hbadN
  rw [houtEq]
  exact Ttc.ContinuingRejectionSelective.tvLe_acceptedMixture_selective
    L w q target (sN L) acceptedError (eta + r ^ L) fallback
    (fun i ↦ eta ≤ sN i) hmass
    (fun i hi ↦ by simpa only [q, p, sN] using haccepted i hi) hbad

#print axioms tvLe_cutoffOutput_of_accepted_significant_initialLaw

end Ttc.FiniteContinuingRetrySelectiveInitialLaw

import Ttc.Exec.CVExceptionalReferenceGlobalTimeout
import Ttc.Exec.CVIdealAveragePathTelescope
import Ttc.Exec.CVGaussianScoreSeedPhaseKernel

/-!
# Cost-preserving exceptional paths

This file records the strongest abstract route from the Gaussian exceptional-reference
idea to one global timeout.

* TV-close starts remain TV-close after the **same cost-recording kernel**.
* A reset is legitimate if the two joint transition laws have a common restriction on a
  measurable good event and each exceptional complement has small mass.
* Such reset estimates telescope on the full finite history, so one reference expected
  total cost gives one global timeout.

The missing Gaussian input is consequently local and precise: construct the common-good
restriction for the joint `(phase cost, next score/seed)` transition.  A theorem only
about its cost-erased score/seed marginal cannot provide this input.
-/

namespace Ttc.CVCostPreservingGoodPath

open MeasureTheory ProbabilityTheory Set Finset
open Arlib Arlib.Probability
open Ttc.CVSequentialPhaseSampler
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVScoreSeedExceptionalCost
open scoped ENNReal Classical BigOperators

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- Running the same costed experiment from TV-close input laws preserves the TV error
on the complete `(cost, output)` record, not merely on its output projection. -/
theorem tvLe_costedExecution_of_tvLe_start
    {mu nu : Measure E} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ENNReal} (h : TVLe mu nu eps)
    (Q : Kernel E (ENNReal × F)) [IsMarkovKernel Q] :
    TVLe (sampleFromKernel Q mu) (sampleFromKernel Q nu) eps := by
  exact h.bind_kernel Q

/-- Concrete Gaussian phase specialization.  The full next phase cost/output law from
the retained operational seed is close to the corresponding law from the exact graph
seed, with no loss beyond the score/seed replacement error. -/
theorem tvLe_gaussianScoreSeedCosted_of_reference
    {n : Nat}
    {rho : Measure (Ttc.CVGaussianScoreSeedPhaseKernel.ScoreSeed n)}
    [IsProbabilityMeasure rho]
    {mu : Measure (Ttc.CVGaussianScoreSeedPhaseKernel.State n)}
    [IsProbabilityMeasure mu]
    {c : Real} {eps : ENNReal}
    (h : TVLe rho (scoreSeedReference c mu) eps)
    {K : Set (Ttc.CVGaussianScoreSeedPhaseKernel.State n)}
    (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    TVLe
      (sampleFromKernel
        (gaussianScoreSeedCostedKernel K hK delta s c hdelta hc steps L)
        (Measure.map Prod.snd rho))
      (sampleFromKernel
        (gaussianScoreSeedCostedKernel K hK delta s c hdelta hc steps L)
        (Measure.map (fun y ↦ c • y) mu)) eps := by
  exact tvLe_bind_seed_of_scoreSeedReference h
    (gaussianScoreSeedCostedKernel K hK delta s c hdelta hc steps L)

/-- A common good sublaw upgrades to TV control of the full laws.  This is the natural
interface for a cost-preserving reset: on `Good`, cost and next state must agree jointly;
only the two exceptional complements may be discarded. -/
theorem tvLe_of_common_good
    {mu nu : Measure E} {Good : Set E} (hGood : MeasurableSet Good)
    {eps : ENNReal} (heq : mu.restrict Good = nu.restrict Good)
    (hmu : mu Goodᶜ ≤ eps) (hnu : nu Goodᶜ ≤ eps) :
    TVLe mu nu eps := by
  intro S hS
  have hinter : mu (S ∩ Good) = nu (S ∩ Good) := by
    have h := congrArg (fun xi : Measure E ↦ xi (S ∩ Good)) heq
    simpa [Measure.restrict_apply (hS.inter hGood), inter_assoc] using h
  constructor
  · rw [← measure_inter_add_sdiff S hGood, hinter]
    calc
      nu (S ∩ Good) + mu (S \ Good) ≤ nu (S ∩ Good) + eps := by
        gcongr
        exact (measure_mono (by aesop : S \ Good ⊆ Goodᶜ)).trans hmu
      _ ≤ nu S + eps := by
        gcongr
        exact Set.inter_subset_left
  · rw [← measure_inter_add_sdiff S hGood, ← hinter]
    calc
      mu (S ∩ Good) + nu (S \ Good) ≤ mu (S ∩ Good) + eps := by
        gcongr
        exact (measure_mono (by aesop : S \ Good ⊆ Goodᶜ)).trans hnu
      _ ≤ mu S + eps := by
        gcongr
        exact Set.inter_subset_left

variable {X : Type*} [MeasurableSpace X]

/-- Full-history telescope when every exact-reference reset is justified by a common
good restriction of the two *joint history/next-state* transition laws. -/
theorem tvLe_costPath_of_commonGoodReset
    (P Q : Nat → Kernel X X)
    [∀ i, IsMarkovKernel (P i)] [∀ i, IsMarkovKernel (Q i)]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d : ENNReal} (e : Nat → ENNReal) (hinit : TVLe mu nu d)
    (Good : (i : Nat) → Set ((Finset.Iic i → X) × X))
    (hGood : ∀ i, MeasurableSet (Good i))
    (heq : ∀ i,
      let eta := Measure.map (Preorder.frestrictLe i)
        (inhomogeneousPathMeasure Q nu)
      (eta ⊗ₘ inhomogeneousHistoryKernel P i).restrict (Good i) =
        (eta ⊗ₘ inhomogeneousHistoryKernel Q i).restrict (Good i))
    (hPbad : ∀ i,
      let eta := Measure.map (Preorder.frestrictLe i)
        (inhomogeneousPathMeasure Q nu)
      (eta ⊗ₘ inhomogeneousHistoryKernel P i) (Good i)ᶜ ≤ e i)
    (hQbad : ∀ i,
      let eta := Measure.map (Preorder.frestrictLe i)
        (inhomogeneousPathMeasure Q nu)
      (eta ⊗ₘ inhomogeneousHistoryKernel Q i) (Good i)ᶜ ≤ e i)
    (t : Nat) :
    TVLe
      (Measure.map (Preorder.frestrictLe t) (inhomogeneousPathMeasure P mu))
      (Measure.map (Preorder.frestrictLe t) (inhomogeneousPathMeasure Q nu))
      (d + ∑ i ∈ range t, e i) := by
  apply Ttc.CVIdealAveragePathTelescope.tvLe_frestrictLe_inhomogeneous_of_idealAverage
    P Q mu nu e hinit
  intro i
  exact tvLe_of_common_good (hGood i) (heq i) (hPbad i) (hQbad i)

/-- One global cutoff after the common-good cost-path telescope.  The TV errors are paid
once as an additive sum, while Markov's inequality is applied once to the exact reference
total cost. -/
theorem globalTimeout_le_of_commonGoodReset
    (P Q : Nat → Kernel X X)
    [∀ i, IsMarkovKernel (P i)] [∀ i, IsMarkovKernel (Q i)]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d : ENNReal} (e : Nat → ENNReal) (hinit : TVLe mu nu d)
    (Good : (i : Nat) → Set ((Finset.Iic i → X) × X))
    (hGood : ∀ i, MeasurableSet (Good i))
    (heq : ∀ i,
      let eta := Measure.map (Preorder.frestrictLe i)
        (inhomogeneousPathMeasure Q nu)
      (eta ⊗ₘ inhomogeneousHistoryKernel P i).restrict (Good i) =
        (eta ⊗ₘ inhomogeneousHistoryKernel Q i).restrict (Good i))
    (hPbad : ∀ i,
      let eta := Measure.map (Preorder.frestrictLe i)
        (inhomogeneousPathMeasure Q nu)
      (eta ⊗ₘ inhomogeneousHistoryKernel P i) (Good i)ᶜ ≤ e i)
    (hQbad : ∀ i,
      let eta := Measure.map (Preorder.frestrictLe i)
        (inhomogeneousPathMeasure Q nu)
      (eta ⊗ₘ inhomogeneousHistoryKernel Q i) (Good i)ᶜ ≤ e i)
    (t : Nat) (cost : (Finset.Iic t → X) → ENNReal) (hcost : Measurable cost)
    {cutoff budget : ENNReal} (hcut0 : cutoff ≠ 0) (hcutTop : cutoff ≠ ⊤)
    (hmean : (∫⁻ omega, cost omega ∂
      Measure.map (Preorder.frestrictLe t) (inhomogeneousPathMeasure Q nu)) ≤ budget) :
    Measure.map (Preorder.frestrictLe t) (inhomogeneousPathMeasure P mu)
        {omega | cutoff ≤ cost omega} ≤
      budget / cutoff + (d + ∑ i ∈ range t, e i) := by
  letI : IsProbabilityMeasure
      (Measure.map (Preorder.frestrictLe t) (inhomogeneousPathMeasure P mu)) :=
    Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe t).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (Preorder.frestrictLe t) (inhomogeneousPathMeasure Q nu)) :=
    Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe t).aemeasurable
  have hjoint := tvLe_costPath_of_commonGoodReset P Q mu nu e hinit Good
    hGood heq hPbad hQbad t
  exact Ttc.CVExceptionalReferenceGlobalTimeout.globalTimeout_le_of_jointPathTV
    hjoint cost hcost hcut0 hcutTop hmean

#print axioms tvLe_costedExecution_of_tvLe_start
#print axioms tvLe_gaussianScoreSeedCosted_of_reference
#print axioms tvLe_of_common_good
#print axioms tvLe_costPath_of_commonGoodReset
#print axioms globalTimeout_le_of_commonGoodReset

end Ttc.CVCostPreservingGoodPath

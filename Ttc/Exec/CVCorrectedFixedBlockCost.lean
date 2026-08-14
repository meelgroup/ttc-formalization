/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CostedAmbientGaussianRejection
import Ttc.Exec.CostedPackedWarmSchedule
import Ttc.Volume.CVHybridSchedule

/-!
# Correct operational costing of the fixed-rate CV block

Figure `fig:volume-alg` in Cousins--Vempala starts at variance `1/(4n)` and uses the ball
walk in every sampling phase, with

`10^16 * max {sigma^2, 1} * n^2 * log (1/nu)` proper steps.

Consequently every fixed-rate phase (`sigma^2 <= 1`) has the same displayed proper-step
deadline, but it is not a constant-query ambient rejection phase.  The direct ambient
sampler costs at most two membership queries only under the much smaller condition
`4*n*sigma^2 <= 1`.  At the source start this holds only at the initial variance and fails
after the first strict cooling increase.  For the repository's more conservative polynomial
endpoint, it can hold for a short prefix, but never for the entire fixed block.

This file implements that exact operational split.  Eligible coordinates use the traced
ambient rejection law; every other fixed coordinate uses the traced warm-phase law.  The
packed result uses genuinely independent restarts across runs, phases and samples.
-/

namespace Ttc.CVCorrectedFixedBlockCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.CVHybridSchedule Ttc.CostedWarmPhaseRejection
open Ttc.CostedAmbientGaussianRejection Ttc.CostedPackedWarmSchedule
open scoped ENNReal Classical Pointwise

variable {n r k : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The exact condition under which the proved ambient-Gaussian rejection bound is `<=2`. -/
def ambientEligible (n : Nat) (sigmaSq : Real) : Prop :=
  4 * (n : Real) * sigmaSq ≤ 1

noncomputable instance (n : Nat) (sigmaSq : Real) : Decidable (ambientEligible n sigmaSq) :=
  inferInstance

/-- Fixed-rate phase variance. -/
noncomputable def fixedSigmaSq (n : Nat) (s0 : Real) (i : Nat) : Real :=
  geomSchedule s0 (1 / (n : Real)) i

/-- The exact number of fixed phases for which the constant-cost ambient theorem applies. -/
noncomputable def ambientFixedPhases (n : Nat) (s0 : Real) : Nat :=
  ((Finset.univ : Finset (Fin (coldPhases n s0))).filter fun i : Fin (coldPhases n s0) =>
    ambientEligible n (fixedSigmaSq n s0 i.val)).card

/-- Every other fixed-rate phase must be charged as a walk phase. -/
noncomputable def postAmbientFixedPhases (n : Nat) (s0 : Real) : Nat :=
  ((Finset.univ : Finset (Fin (coldPhases n s0))).filter fun i : Fin (coldPhases n s0) =>
    ¬ ambientEligible n (fixedSigmaSq n s0 i.val)).card

theorem ambient_add_postAmbient_fixedPhases (n : Nat) (s0 : Real) :
    ambientFixedPhases n s0 + postAmbientFixedPhases n s0 = coldPhases n s0 := by
  unfold ambientFixedPhases postAmbientFixedPhases
  simpa using (Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (coldPhases n s0))))
    (p := fun i : Fin (coldPhases n s0) =>
      ambientEligible n (fixedSigmaSq n s0 i.val)))

/-- At the paper's source start `1/(4n)`, phase zero is ambient-eligible. -/
theorem source_start_ambientEligible {n : Nat} (hn : 1 ≤ n) :
    ambientEligible n (1 / (4 * (n : Real))) := by
  unfold ambientEligible
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  field_simp
  norm_num

/-- Every later source fixed-rate variance is strictly too large for the ambient `<=2`
certificate.  This formalizes the accounting error in `2*coldPhases`. -/
theorem source_fixed_succ_not_ambientEligible {n i : Nat} (hn : 1 ≤ n) :
    ¬ ambientEligible n (fixedSigmaSq n (1 / (4 * (n : Real))) (i + 1)) := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hrate : 1 < 1 + 1 / (n : Real) := lt_add_of_pos_right 1 (by positivity)
  have hpow : 1 < (1 + 1 / (n : Real)) ^ (i + 1) := one_lt_pow₀ hrate (by omega)
  unfold ambientEligible fixedSigmaSq geomSchedule
  have heq : 4 * (n : Real) * (1 / (4 * (n : Real))) = 1 := by field_simp
  have hcalc : 4 * (n : Real) *
      (1 / (4 * (n : Real)) * (1 + 1 / (n : Real)) ^ (i + 1)) =
      (1 + 1 / (n : Real)) ^ (i + 1) := by
    rw [← mul_assoc, heq, one_mul]
  rw [hcalc]
  exact not_le_of_gt hpow

/-! ## Source Figure deadline audit -/

/-- The proper-step expression printed literally in Figure `fig:volume-alg`. -/
noncomputable def sourceFigureProperSteps (n : Nat) (sigmaSq nu : Real) : Real :=
  10 ^ (16 : Nat) * max sigmaSq 1 * (n : Real) ^ 2 * Real.log (1 / nu)

/-- On the fixed block, the source's displayed deadline is independent of variance. -/
theorem sourceFigureProperSteps_fixed {n : Nat} {sigmaSq nu : Real}
    (hsigma : sigmaSq ≤ 1) :
    sourceFigureProperSteps n sigmaSq nu =
      10 ^ (16 : Nat) * (n : Real) ^ 2 * Real.log (1 / nu) := by
  unfold sourceFigureProperSteps
  rw [max_eq_right hsigma, mul_one]

/-- Coarse fixed-block budget after a uniform post-ambient warm-walk bound `D` is known.
This is the count-level replacement for the invalid `2 * coldPhases` term. -/
noncomputable def correctedFixedPhaseAccounting (n : Nat) (s0 : Real)
    (D : ENNReal) : ENNReal :=
  ∑ i : Fin (coldPhases n s0),
    if ambientEligible n (fixedSigmaSq n s0 i) then 12 else 80 * D

theorem fixedPhaseBudget_le_correctedFixedPhaseAccounting
    {s0 : Real} (steps : Fin (coldPhases n s0) → Nat)
    (M : Fin (coldPhases n s0) → ENNReal) (D : ENNReal)
    (hD : ∀ i, (steps i : ENNReal) * M i ≤ D) :
    (∑ i : Fin (coldPhases n s0),
      if ambientEligible n (fixedSigmaSq n s0 i) then 12
      else 80 * ((steps i : ENNReal) * M i)) ≤
      correctedFixedPhaseAccounting n s0 D := by
  calc
    _ ≤ ∑ i : Fin (coldPhases n s0),
        if ambientEligible n (fixedSigmaSq n s0 i) then 12 else 80 * D := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact le_rfl
      · exact mul_le_mul_left' (hD i) 80
    _ = correctedFixedPhaseAccounting n s0 D := rfl

/-! ## Operationally split fixed-coordinate law -/

/-- Ambient rejection on the genuinely eligible prefix; traced warm walk plus both source
restarts thereafter. -/
noncomputable def fixedCoordinateCostLaw
    (K : Set (State n)) (hK : MeasurableSet K) (s0 : Real)
    (delta : Fin (coldPhases n s0) → Real)
    (hdelta : ∀ i, 0 < delta i)
    (mu0 : Fin (coldPhases n s0) → Measure (State n))
    (steps : Fin (coldPhases n s0) → Nat)
    (j : Fin r) (i : Fin (coldPhases n s0)) (l : Fin k) :
    Measure (ENNReal × State n) :=
  if ambientEligible n (fixedSigmaSq n s0 i) then
    coldPhaseCostLaw K (fixedSigmaSq n s0 i)
  else
    warmPhaseCostLaw K hK (delta i) (fixedSigmaSq n s0 i)
      (hdelta i) (mu0 i) (steps i)

theorem isProbabilityMeasure_fixedCoordinateCostLaw
    (K : Set (State n)) (hK : MeasurableSet K) {s0 : Real} (hs0 : 0 < s0)
    (delta : Fin (coldPhases n s0) → Real) (hdelta : ∀ i, 0 < delta i)
    (mu0 : Fin (coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin (coldPhases n s0) → Nat)
    (j : Fin r) (i : Fin (coldPhases n s0)) (l : Fin k) :
    IsProbabilityMeasure (fixedCoordinateCostLaw K hK s0 delta hdelta mu0 steps j i l) := by
  unfold fixedCoordinateCostLaw
  split_ifs
  · exact isProbabilityMeasure_coldPhaseCostLaw K
      (geomSchedule_pos hs0 (by positivity) i) hK
  · infer_instance

/-- The state marginal honestly reflects the operational split. -/
theorem map_snd_fixedCoordinateCostLaw
    {K : Set (State n)} (hK : MeasurableSet K) {s0 : Real} (hs0 : 0 < s0)
    (delta : Fin (coldPhases n s0) → Real) (hdelta : ∀ i, 0 < delta i)
    (mu0 : Fin (coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin (coldPhases n s0) → Nat)
    (hambientPos : ∀ i : Fin (coldPhases n s0), ambientEligible n (fixedSigmaSq n s0 i) →
      0 < Ttc.CV.ambientGaussianProb (n := n) (fixedSigmaSq n s0 i) K)
    (hshrink : ∀ i : Fin (coldPhases n s0), ¬ ambientEligible n (fixedSigmaSq n s0 i) → 0 <
      (iterate (lazy (speedyMetropolisGaussian K (delta i) (fixedSigmaSq n s0 i)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) • K))
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (hmass : ∀ i : Fin (coldPhases n s0), ¬ ambientEligible n (fixedSigmaSq n s0 i) →
      ((Ttc.SpeedyRejection.phasePointProposal K (delta i) (fixedSigmaSq n s0 i)
        (mu0 i) (steps i)).withDensity (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (fixedSigmaSq n s0 i) x)))
        Set.univ ≠ 0)
    (j : Fin r) (i : Fin (coldPhases n s0)) (l : Fin k) :
    Measure.map Prod.snd
        (fixedCoordinateCostLaw K hK s0 delta hdelta mu0 steps j i l) =
      if ambientEligible n (fixedSigmaSq n s0 i) then
        condOn (Ttc.CV.ambientGaussianProb (n := n) (fixedSigmaSq n s0 i)) K
      else Ttc.CVSampler.phaseLaw K (delta i) (fixedSigmaSq n s0 i)
        (mu0 i) (steps i) := by
  unfold fixedCoordinateCostLaw
  split_ifs with hi
  · exact map_snd_coldPhaseCostLaw hK
      (geomSchedule_pos hs0 (by positivity) i) (hambientPos i hi)
  · exact map_snd_warmPhaseCostLaw_eq_phaseLaw hK (delta i) (hdelta i) (mu0 i)
      (steps i) (hshrink i hi) (geomSchedule_pos hs0 (by positivity) i) hc2 (hmass i hi)

/-- Coordinatewise expected recorded-query bound: `12` after multiplying the ambient
expectation by six, and a supplied bound for the actual traced warm walk/restart law
otherwise.  The intended discharge is
`six_mul_lintegral_warmPhaseCostLaw_le_eighty_mul_adjustable`; keeping that geometric
certificate separate avoids rebuilding it for every packed coordinate. -/
theorem six_mul_lintegral_fixedCoordinateCostLaw_le
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    {s0 : Real} (hs0 : 0 < s0)
    (delta : Fin (coldPhases n s0) → Real) (hdelta : ∀ i, 0 < delta i)
    (M : Fin (coldPhases n s0) → ENNReal)
    (mu0 : Fin (coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin (coldPhases n s0) → Nat)
    (hpost : ∀ i : Fin (coldPhases n s0),
      ¬ ambientEligible n (fixedSigmaSq n s0 i) →
      6 * (∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK (delta i) (fixedSigmaSq n s0 i)
        (hdelta i) (mu0 i) (steps i))) ≤ 80 * ((steps i : ENNReal) * M i))
    (j : Fin r) (i : Fin (coldPhases n s0)) (l : Fin k) :
    6 * (∫⁻ z, z.1 ∂(fixedCoordinateCostLaw K hK s0 delta hdelta mu0 steps j i l)) ≤
      if ambientEligible n (fixedSigmaSq n s0 i) then 12
      else 80 * ((steps i : ENNReal) * M i) := by
  unfold fixedCoordinateCostLaw
  split_ifs with hi
  · have hc := lintegral_fst_coldPhaseCostLaw_le_two hK hn
      (geomSchedule_pos hs0 (by positivity) i) hi hball
    calc
      6 * ∫⁻ z, z.1 ∂(coldPhaseCostLaw K (fixedSigmaSq n s0 i)) ≤ 6 * 2 :=
        mul_le_mul_left' hc 6
      _ = 12 := by norm_num
  · exact hpost i hi

/-- Correct expected membership-query accounting for all independently restarted fixed
coordinates.  Only the eligible prefix receives the ambient constant; every remaining
fixed phase pays its actual walk deadline and warmness factor. -/
theorem six_mul_lintegral_packedFixedBlock_le
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    {s0 : Real} (hs0 : 0 < s0)
    (delta : Fin (coldPhases n s0) → Real) (hdelta : ∀ i, 0 < delta i)
    (M : Fin (coldPhases n s0) → ENNReal)
    (mu0 : Fin (coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin (coldPhases n s0) → Nat)
    (hpost : ∀ i : Fin (coldPhases n s0),
      ¬ ambientEligible n (fixedSigmaSq n s0 i) →
      6 * (∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK (delta i) (fixedSigmaSq n s0 i)
        (hdelta i) (mu0 i) (steps i))) ≤ 80 * ((steps i : ENNReal) * M i)) :
    6 * (∫⁻ omega, totalMembershipQueries omega
      ∂(costedPackedLaw
        (fixedCoordinateCostLaw K hK s0 delta hdelta mu0 steps :
          Fin r → Fin (coldPhases n s0) → Fin k → Measure (ENNReal × State n)))) ≤
      (r : ENNReal) * (k : ENNReal) *
        ∑ i : Fin (coldPhases n s0),
          if ambientEligible n (fixedSigmaSq n s0 i) then 12
          else 80 * ((steps i : ENNReal) * M i) := by
  letI : ∀ j i l, IsProbabilityMeasure
      (fixedCoordinateCostLaw K hK s0 delta hdelta mu0 steps j i l) :=
    fun (j : Fin r) (i : Fin (coldPhases n s0)) (l : Fin k) =>
      @isProbabilityMeasure_fixedCoordinateCostLaw n r k K hK s0 hs0
        delta hdelta mu0 _ steps j i l
  apply six_mul_lintegral_totalMembershipQueries_le_phaseBounds
  exact six_mul_lintegral_fixedCoordinateCostLaw_le hn hK hball hs0 delta hdelta M mu0
    steps hpost

/-! ## Fixed plus accelerated block composition -/

/-- Independent operational execution of the corrected fixed block and an independently
restarted accelerated block.  Keeping the two phase index types separate avoids pretending
that the source fixed-rate and accelerated deadlines are uniform. -/
noncomputable def hybridBlockCostLaw {m : Nat} {s0 : Real}
    (rhoFixed : Fin r → Fin (coldPhases n s0) → Fin k → Measure (ENNReal × State n))
    (rhoAdaptive : Fin r → Fin m → Fin k → Measure (ENNReal × State n)) :
    Measure (CostedPackedSpace n r (coldPhases n s0) k × CostedPackedSpace n r m k) :=
  (costedPackedLaw rhoFixed).prod (costedPackedLaw rhoAdaptive)

/-- Actual recorded membership queries in both independent blocks. -/
noncomputable def totalHybridMembershipQueries {m : Nat} {s0 : Real}
    (omega : CostedPackedSpace n r (coldPhases n s0) k × CostedPackedSpace n r m k) : ENNReal :=
  totalMembershipQueries omega.1 + totalMembershipQueries omega.2

theorem measurable_totalHybridMembershipQueries {m : Nat} {s0 : Real} :
    Measurable (totalHybridMembershipQueries (n := n) (r := r) (k := k) (s0 := s0)
      (m := m)) := by
  exact (measurable_totalMembershipQueries.comp measurable_fst).add
    (measurable_totalMembershipQueries.comp measurable_snd)

/-- Tonelli for the two independently executed blocks. -/
theorem lintegral_totalHybridMembershipQueries {m : Nat} {s0 : Real}
    (rhoFixed : Fin r → Fin (coldPhases n s0) → Fin k → Measure (ENNReal × State n))
    (rhoAdaptive : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rhoFixed j i l)]
    [∀ j i l, IsProbabilityMeasure (rhoAdaptive j i l)] :
    ∫⁻ omega, totalHybridMembershipQueries omega
        ∂(hybridBlockCostLaw rhoFixed rhoAdaptive) =
      (∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rhoFixed)) +
      (∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rhoAdaptive)) := by
  unfold totalHybridMembershipQueries hybridBlockCostLaw
  change (∫⁻ omega,
      ((totalMembershipQueries ∘ Prod.fst) omega +
        (totalMembershipQueries ∘ Prod.snd) omega)
      ∂((costedPackedLaw rhoFixed).prod (costedPackedLaw rhoAdaptive))) = _
  rw [lintegral_add_left
    (measurable_totalMembershipQueries.comp measurable_fst)]
  congr 1
  · exact measurePreserving_fst.lintegral_comp measurable_totalMembershipQueries
  · exact measurePreserving_snd.lintegral_comp measurable_totalMembershipQueries

/-- Correct hybrid expected-query accounting.  Ambient rejection is charged by `12`
(the common factor-six convention) only at eligible fixed phases.  Every other fixed phase
uses its actual traced `warmPhaseCostLaw` certificate, and the accelerated block is charged
by its supplied phase-dependent traced warm-law bounds. -/
theorem six_mul_lintegral_correctedHybridBlock_le {m : Nat}
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    {s0 : Real} (hs0 : 0 < s0)
    (delta : Fin (coldPhases n s0) → Real) (hdelta : ∀ i, 0 < delta i)
    (M : Fin (coldPhases n s0) → ENNReal)
    (mu0 : Fin (coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin (coldPhases n s0) → Nat)
    (hpost : ∀ i : Fin (coldPhases n s0),
      ¬ ambientEligible n (fixedSigmaSq n s0 i) →
      6 * (∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK (delta i) (fixedSigmaSq n s0 i)
        (hdelta i) (mu0 i) (steps i))) ≤ 80 * ((steps i : ENNReal) * M i))
    (rhoAdaptive : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rhoAdaptive j i l)]
    (Badaptive : Fin m → ENNReal)
    (hadaptive : ∀ j i l,
      6 * (∫⁻ z, z.1 ∂(rhoAdaptive j i l)) ≤ Badaptive i) :
    6 * (∫⁻ omega, totalHybridMembershipQueries omega
      ∂(hybridBlockCostLaw
        (fixedCoordinateCostLaw K hK s0 delta hdelta mu0 steps :
          Fin r → Fin (coldPhases n s0) → Fin k → Measure (ENNReal × State n))
        rhoAdaptive)) ≤
      (r : ENNReal) * (k : ENNReal) *
        ((∑ i : Fin (coldPhases n s0),
          if ambientEligible n (fixedSigmaSq n s0 i) then 12
          else 80 * ((steps i : ENNReal) * M i)) +
        ∑ i : Fin m, Badaptive i) := by
  letI : ∀ j i l, IsProbabilityMeasure
      (fixedCoordinateCostLaw K hK s0 delta hdelta mu0 steps j i l) :=
    fun (j : Fin r) (i : Fin (coldPhases n s0)) (l : Fin k) =>
      @isProbabilityMeasure_fixedCoordinateCostLaw n r k K hK s0 hs0
        delta hdelta mu0 _ steps j i l
  rw [lintegral_totalHybridMembershipQueries, mul_add, mul_add]
  exact add_le_add
    (six_mul_lintegral_packedFixedBlock_le hn hK hball hs0 delta hdelta M mu0
      steps hpost)
    (six_mul_lintegral_totalMembershipQueries_le_phaseBounds rhoAdaptive Badaptive hadaptive)

end Ttc.CVCorrectedFixedBlockCost

#print axioms Ttc.CVCorrectedFixedBlockCost.source_fixed_succ_not_ambientEligible
#print axioms Ttc.CVCorrectedFixedBlockCost.sourceFigureProperSteps_fixed
#print axioms Ttc.CVCorrectedFixedBlockCost.map_snd_fixedCoordinateCostLaw
#print axioms Ttc.CVCorrectedFixedBlockCost.six_mul_lintegral_packedFixedBlock_le
#print axioms Ttc.CVCorrectedFixedBlockCost.six_mul_lintegral_correctedHybridBlock_le

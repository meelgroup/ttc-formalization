/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CostedWarmPhaseRejection
import Ttc.Exec.CostedHybridCoordinateSchedule
import Ttc.Volume.AdaptiveTerminalWarmLawAdjustable

/-!
# Costed adjustable terminal phases

This file attaches the recorded raw membership-query execution to the adjustable-radius
phase law used by the public independently-restarted CV oracle.  The source analysis only
proves a quarter lower bound for each of its two rejection stages.  Accordingly the honest
constant here is `16` for the two restarts, and `160/6` after the raw adjustable walk bound;
the stronger `8` constant in `CostedWarmPhaseRejection` requires a half-mass first stage.
-/

namespace Ttc.CostedAdaptiveTerminalWarmQ

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.Probability Arlib.GaussianCooling Arlib.MarkovChains
open Arlib.GaussianCooling.Chunked
open Ttc.CostedWarmPhaseRejection Ttc.SpeedyRejection Ttc.CVAdaptive
open Ttc.RawGaussianLazyStoppedExecution
open scoped ENNReal

variable {n r m k : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Quantitative acceptance bound for the actual post-shrink proposal.  This is the
intermediate `hmassP` calculation inside `tvLe_speedyRejection_target_of`, exposed here
because runtime needs the rejection probability itself. -/
theorem quarter_le_phasePointProposal_acceptance_of_tvLe
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {delta s : Real} (hdelta : 0 < delta) (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hs : 0 < s) {P : Measure (State n)} [IsProbabilityMeasure P] {eps : ENNReal}
    (hP : TVLe P (ellGaussianProb K delta s) eps)
    (heps : eps ≤ ENNReal.ofReal (1 / 32)) :
    ENNReal.ofReal (1 / 4 : Real) ≤
      ((phasePointProposal K delta s P 0).withDensity
        (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s x))) Set.univ := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : Real) < n := by linarith
  have hc0 : 0 < c := by
    dsimp [c]
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdeltaC : delta ≤ 1 - c := by simpa [c] using hdeltan
  have hQhalf : ENNReal.ofReal (1 / 2 : Real) ≤
      ellGaussianProb K delta s (c • K) := by
    rw [ellGaussianProb_eq_condOn]
    exact half_le_speedyProb_shrunken hn hK hKc hball hKvol hdelta hdeltan hs
  have hepsQuarter : eps ≤ ENNReal.ofReal (1 / 4 : Real) :=
    heps.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  have hPc : ENNReal.ofReal (1 / 4 : Real) ≤ P (c • K) :=
    quarter_le_of_tvLe hP (measurableSet_smul_set hK hc0.ne') hQhalf hepsQuarter
  have hPc0 : P (c • K) ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) hPc).ne'
  letI : IsProbabilityMeasure (condOn P (c • K)) :=
    Arlib.isProbabilityMeasure_condOn _ hPc0 (measure_ne_top P _)
  have hsmul : Measurable (fun x : State n => c⁻¹ • x) := measurable_const_smul _
  letI : IsProbabilityMeasure (Measure.map (fun x : State n => c⁻¹ • x)
      (condOn P (c • K))) := Measure.isProbabilityMeasure_map hsmul.aemeasurable
  have hM0 : ellGaussianMeasure K delta s Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0 hc1 hdelta hdeltaC hs
  have hMtop : ellGaussianMeasure K delta s Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs K delta hKvol
  letI : IsProbabilityMeasure (ellGaussianProb K delta s) :=
    isProbabilityMeasure_ellGaussianProb hM0 hMtop
  have hstep1 := Arlib.tvLe_condOn_half hP
    (measurableSet_smul_set hK hc0.ne') hQhalf
  have hcond : condOn (ellGaussianProb K delta s) (c • K) =
      condOn ((volume.restrict K).withDensity (gaussianWeight s)) (c • K) := by
    rw [ellGaussianProb_eq_condOn, Arlib.condOn_condOn_univ _ _ hM0 hMtop]
    exact condOn_ellGaussianMeasure_shrunken hK hKc hball hc0 hc1 hdelta hdeltaC
  rw [hcond] at hstep1
  have hstep2 := hstep1.map hsmul
  rw [map_inv_smul_condOn_shrunken hK hKc
    (hball (mem_ball_self one_pos)) hc0 hc1.le s] at hstep2
  have hs' : 0 < s / c ^ 2 := by positivity
  have hZ0 : ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) univ ≠ 0 := by
    rw [gaussianRestrict_univ]
    exact (lintegral_gaussianWeight_pos hs' one_pos hball).ne'
  have hZtop : ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) univ ≠ ⊤ := by
    rw [gaussianRestrict_univ]
    exact lintegral_gaussianWeight_ne_top hs' hKvol
  letI : IsProbabilityMeasure
      (condOn ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) univ) :=
    Arlib.isProbabilityMeasure_condOn _ hZ0 hZtop
  have hepsTop : eps ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top heps
  have hstep3 := hstep2.withDensity
    (ENNReal.mul_ne_top (by simp) hepsTop)
    (measurable_speedyAcceptReal c s)
    (fun x => (speedyAcceptReal_pos c s x).le)
    (fun x => speedyAcceptReal_le_one hs (by nlinarith) x)
  have htarget :
      (condOn ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) univ).withDensity
          (fun x => ENNReal.ofReal (speedyAcceptReal c s x)) =
        (((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) univ)⁻¹ •
          ((volume.restrict K).withDensity (gaussianWeight s)) := by
    rw [condOn_def, Measure.restrict_univ, Arlib.withDensity_smul_measure,
      withDensity_gaussian_mul_speedyAccept hc0.ne' hs.ne']
  rw [htarget] at hstep3
  have hmassTarget : ENNReal.ofReal (1 / 2 : Real) ≤
      ((((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) univ)⁻¹ •
        ((volume.restrict K).withDensity (gaussianWeight s))) univ := by
    rw [Measure.smul_apply, smul_eq_mul, gaussianRestrict_univ, gaussianRestrict_univ]
    exact (ENNReal.ofReal_le_ofReal (half_le_one_sub_inv_two_mul_pow hn)).trans
      (pow_le_acceptance_ratio hK hKc (hball (mem_ball_self one_pos))
        hc0 hc1.le hs hKvol hball)
  have h8 : 8 * eps ≤ ENNReal.ofReal (1 / 4 : Real) := by
    calc
      8 * eps ≤ 8 * ENNReal.ofReal (1 / 32 : Real) := by gcongr
      _ = ENNReal.ofReal (1 / 4 : Real) := by
        rw [show (8 : ENNReal) = ENNReal.ofReal 8 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 8)]
        norm_num
  have hmass := quarter_le_of_tvLe hstep3 MeasurableSet.univ hmassTarget h8
  simpa only [phasePointProposal, iterate_zero, c] using hmass

/-- Both restart stages cost at most four iid trials when their acceptance masses are at
least one quarter. -/
theorem lintegral_fst_warmPhaseCostLaw_le_sixteen
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) {s : Real}
    (hdelta : 0 < delta) (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat)
    (hquarterShrink : ENNReal.ofReal (1 / 4 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
        ((1 - 1 / (2 * (n : Real))) • K))
    (hquarterAccept : ENNReal.ofReal (1 / 4 : Real) ≤
      ((phasePointProposal K delta s mu0 t).withDensity
        (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s x))) Set.univ)
    (hs : 0 < s) (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    ∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK delta s hdelta mu0 t) ≤
      16 * ∫⁻ omega, actualMembershipQueryCount t omega
        ∂(lazyRawStoppedExecution K hK delta s hdelta mu0) := by
  have hshrinkPos : 0 < (iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
      ((1 - 1 / (2 * (n : Real))) • K) :=
    lt_of_lt_of_le (by norm_num) hquarterShrink
  rw [lintegral_fst_warmPhaseCostLaw hK delta hdelta mu0 t hshrinkPos hs hc2]
  have hiShrink : ((iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
      ((1 - 1 / (2 * (n : Real))) • K))⁻¹ ≤ 4 := by
    calc
      _ ≤ (ENNReal.ofReal (1 / 4 : Real))⁻¹ := ENNReal.inv_le_inv.mpr hquarterShrink
      _ = 4 := by
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 1 / 4)]
        norm_num
  have hiAccept : (((phasePointProposal K delta s mu0 t).withDensity
      (fun x => ENNReal.ofReal
        (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s x))) Set.univ)⁻¹ ≤ 4 := by
    calc
      _ ≤ (ENNReal.ofReal (1 / 4 : Real))⁻¹ := ENNReal.inv_le_inv.mpr hquarterAccept
      _ = 4 := by
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 1 / 4)]
        norm_num
  calc
    _ ≤ 4 * 4 * ∫⁻ omega, actualMembershipQueryCount t omega
        ∂(lazyRawStoppedExecution K hK delta s hdelta mu0) := by gcongr
    _ = 16 * ∫⁻ omega, actualMembershipQueryCount t omega
        ∂(lazyRawStoppedExecution K hK delta s hdelta mu0) := by norm_num

/-- Adjustable-radius actual-query bound with the two source-proved quarter-mass restart
bounds. -/
theorem six_mul_lintegral_warmPhaseCostLaw_le_oneSixty_mul_adjustable
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {q delta sigma R : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {M : ENNReal} {mu0 : Measure (State n)} [IsProbabilityMeasure mu0]
    (hwarm : IsWarm M mu0 (ellGaussianProb K delta (sigma ^ 2))) (t : Nat)
    (hquarterShrink : ENNReal.ofReal (1 / 4 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian K delta (sigma ^ 2))) mu0 t)
        ((1 - 1 / (2 * (n : Real))) • K))
    (hquarterAccept : ENNReal.ofReal (1 / 4 : Real) ≤
      ((phasePointProposal K delta (sigma ^ 2) mu0 t).withDensity
        (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (sigma ^ 2) x))) Set.univ)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    6 * (∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK delta (sigma ^ 2) hdelta mu0 t)) ≤
      160 * ((t : ENNReal) * M) := by
  have h16 := lintegral_fst_warmPhaseCostLaw_le_sixteen hK delta hdelta mu0 t
    hquarterShrink hquarterAccept (sq_pos_of_pos hsigma) hc2
  have hraw := six_mul_expected_actualMembershipQueryCount_le_ten_mul_adjustable
    hn hK hKc hball hq hdelta hsigma hdeltan hdeltaq hR hRsigma hKR hwarm t
  calc
    6 * (∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK delta (sigma ^ 2) hdelta mu0 t)) ≤
        6 * (16 * ∫⁻ omega, actualMembershipQueryCount t omega
          ∂(lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu0)) :=
      mul_le_mul_left' h16 6
    _ = 16 * (6 * ∫⁻ omega, actualMembershipQueryCount t omega
          ∂(lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu0)) := by
      ac_rfl
    _ ≤ 16 * (10 * ((t : ENNReal) * M)) := mul_le_mul_left' hraw 16
    _ = 160 * ((t : ENNReal) * M) := by
      rw [← mul_assoc]
      norm_num

#print axioms lintegral_fst_warmPhaseCostLaw_le_sixteen
#print axioms six_mul_lintegral_warmPhaseCostLaw_le_oneSixty_mul_adjustable
#print axioms quarter_le_phasePointProposal_acceptance_of_tvLe

end Ttc.CostedAdaptiveTerminalWarmQ

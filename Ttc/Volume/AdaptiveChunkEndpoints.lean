/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CousinsVempala
import Arlib.Convexity.GaussianCooling.ColdBallStart
import Arlib.Convexity.GaussianCooling.ChunkedSchedule

/-!
# Endpoint arithmetic for the adaptive chunked Gaussian schedule

The accelerated schedule starts from a finite ambient-Gaussian normalizer and stops at a
finite Gaussian variance.  This file packages the two endpoint comparisons needed by the
biased-end Cousins--Vempala estimator.
-/

namespace Ttc.CV

open MeasureTheory Metric Set Arlib.GaussianCooling
open scoped ENNReal

variable {n : ℕ}

/-- A cold Gaussian restricted to a body containing its concentration ball has between
one half and all of the explicitly known ambient Gaussian normalizer. -/
theorem G_indicator_mem_coldNormalizer_Icc {K : Set (Space n)} (hKm : MeasurableSet K)
    (hfin : volume K ≠ ⊤) (hn : 1 ≤ n) {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (hcold : 4 * (n : ℝ) * s ≤ ρ ^ 2)
    (hballρ : closedBall (0 : Space n) ρ ⊆ K) :
    G (indicator K (1 : Space n → ℝ)) s ∈
      Icc ((1 / 2) * (2 * Real.pi * s) ^ ((n : ℝ) / 2))
        ((2 * Real.pi * s) ^ ((n : ℝ) / 2)) := by
  let ν : Measure (Space n) :=
    (volume : Measure (Space n)).withDensity (Arlib.MarkovChains.gaussianWeight s)
  have hhalf := Arlib.GaussianCooling.half_lintegral_gaussianWeight_univ_le_closedBall
    hn hs hρ hcold
  have hmass : ENNReal.ofReal (1 / 2) * ν Set.univ ≤ ν K := by
    calc
      ENNReal.ofReal (1 / 2) * ν Set.univ ≤ ν (closedBall (0 : Space n) ρ) := by
        simpa [ν, withDensity_apply _ MeasurableSet.univ,
          withDensity_apply _ measurableSet_closedBall] using hhalf
      _ ≤ ν K := measure_mono hballρ
  have hνuniv : ν Set.univ =
      ENNReal.ofReal ((2 * Real.pi * s) ^ ((n : ℝ) / 2)) := by
    simp only [ν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact Arlib.MarkovChains.lintegral_gaussianWeight_univ hs
  have hνK : ν K = ENNReal.ofReal (G (indicator K (1 : Space n → ℝ)) s) := by
    have h := Arlib.MarkovChains.withDensity_gaussianWeight_eq_ofReal_setIntegral
      (n := n) hs hKm hfin (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Space n)))
    rw [Set.univ_inter, setIntegral_univ] at h
    rw [G_indicator_eq K hKm]
    simpa [ν, Arlib.MarkovChains.gaussianWeightReal, integral_indicator hKm] using h
  have hlowENN : ENNReal.ofReal
      ((1 / 2) * (2 * Real.pi * s) ^ ((n : ℝ) / 2)) ≤
      ENNReal.ofReal (G (indicator K (1 : Space n → ℝ)) s) := by
    rw [hνuniv, hνK, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hmass
    exact hmass
  have hG0 : 0 ≤ G (indicator K (1 : Space n → ℝ)) s :=
    Arlib.GaussianCooling.G_indicator_nonneg K s
  constructor
  · exact (ENNReal.ofReal_le_ofReal_iff hG0).mp hlowENN
  · have hupper : G (indicator K (1 : Space n → ℝ)) s ≤
        ∫ x : Space n, Real.exp (-(‖x‖ ^ 2) / (2 * s)) := by
      rw [G_indicator_eq K hKm]
      exact setIntegral_le_integral (integrable_gaussWeight_univ n hs)
        (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le)
    rwa [integral_gaussWeight_univ n hs] at hupper

/-- **Arbitrary-accuracy cold normalizer from the repository's Gaussian Chernoff bound.**
This is the rigorous replacement for the numerically incorrect variance threshold printed
in `lem:starting-gauss`: any `t ∈ (0,1)` whose explicit tail certificate is at most `eps`
times the ambient normalizer yields an `eps`-relative cold endpoint. -/
theorem G_indicator_mem_relErr_ambient_of_chernoff {K : Set (Space n)}
    (hKm : MeasurableSet K) {s ρ t ε : ℝ} (hs : 0 < s) (hρ : 0 ≤ ρ)
    (ht0 : 0 < t) (ht1 : t < 1) (hε0 : 0 ≤ ε)
    (hballρ : closedBall (0 : Space n) ρ ⊆ K)
    (hcert : Real.exp (-(t * ρ ^ 2) / (2 * s)) *
        (2 * Real.pi * (s / (1 - t))) ^ ((n : ℝ) / 2) ≤
      ε * (2 * Real.pi * s) ^ ((n : ℝ) / 2)) :
    G (indicator K (1 : Space n → ℝ)) s ∈
      relErr ε ((2 * Real.pi * s) ^ ((n : ℝ) / 2)) := by
  let w : Space n → ℝ := fun x ↦ Real.exp (-(‖x‖ ^ 2) / (2 * s))
  let T : Set (Space n) := {x | ρ < ‖x‖}
  have hTm : MeasurableSet T := measurableSet_lt measurable_const continuous_norm.measurable
  have hTint : IntegrableOn w T volume := (integrable_gaussWeight_univ n hs).integrableOn
  have htailENN := Arlib.MarkovChains.lintegral_gaussianWeight_norm_gt_le
    (n := n) hs hρ ht0 ht1
  have htailEq : ENNReal.ofReal (∫ x in T, w x) =
      ∫⁻ x in T, Arlib.MarkovChains.gaussianWeight s x := by
    rw [ofReal_integral_eq_lintegral_ofReal hTint
      (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le)]
    rfl
  have htail0 : 0 ≤ ∫ x in T, w x := setIntegral_nonneg hTm fun _ _ ↦
    (Real.exp_pos _).le
  have htailBound0 : 0 ≤ Real.exp (-(t * ρ ^ 2) / (2 * s)) *
      (2 * Real.pi * (s / (1 - t))) ^ ((n : ℝ) / 2) := by positivity
  have htailReal : (∫ x in T, w x) ≤
      Real.exp (-(t * ρ ^ 2) / (2 * s)) *
        (2 * Real.pi * (s / (1 - t))) ^ ((n : ℝ) / 2) := by
    rw [← htailEq] at htailENN
    exact (ENNReal.ofReal_le_ofReal_iff htailBound0).mp htailENN
  have hcompSub : Kᶜ ⊆ T := by
    intro x hx
    have hxnot : x ∉ closedBall (0 : Space n) ρ := fun hxB ↦ hx (hballρ hxB)
    simpa [T, mem_closedBall_zero_iff, not_le] using hxnot
  have hcomp : (∫ x in Kᶜ, w x) ≤ ε * (2 * Real.pi * s) ^ ((n : ℝ) / 2) := by
    calc
      (∫ x in Kᶜ, w x) ≤ ∫ x in T, w x :=
        setIntegral_mono_set hTint
          (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le)
          (Filter.Eventually.of_forall hcompSub)
      _ ≤ Real.exp (-(t * ρ ^ 2) / (2 * s)) *
          (2 * Real.pi * (s / (1 - t))) ^ ((n : ℝ) / 2) := htailReal
      _ ≤ ε * (2 * Real.pi * s) ^ ((n : ℝ) / 2) := hcert
  have hsplit := integral_add_compl hKm (integrable_gaussWeight_univ n hs)
  have hamb : ∫ x : Space n, w x = (2 * Real.pi * s) ^ ((n : ℝ) / 2) := by
    exact integral_gaussWeight_univ n hs
  have hG : G (indicator K (1 : Space n → ℝ)) s = ∫ x in K, w x := by
    rw [G_indicator_eq K hKm]
  simp only [relErr, Set.mem_Icc]
  constructor
  · have hcomp' : (∫ x in Kᶜ, w x) ≤ ε * ∫ x : Space n, w x := by
      rwa [hamb]
    rw [← hsplit, ← hG] at hcomp'
    rw [← hamb, ← hsplit, ← hG]
    linarith
  · have hupper : (∫ x in K, w x) ≤ ∫ x : Space n, w x :=
      setIntegral_le_integral (integrable_gaussWeight_univ n hs)
        (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le)
    rw [hG]
    rw [hamb] at hupper
    have hnorm0 : 0 ≤ (2 * Real.pi * s) ^ ((n : ℝ) / 2) := by positivity
    exact hupper.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ 1 + ε by exact le_add_of_nonneg_right hε0) hnorm0)

/-- The phase-zero rejection sampler is a probability law, is `2`-warm for the exact cold
Gaussian on `K`, and its normalizer is within a factor two of the known ambient one. -/
theorem coldBallStart_endpoint_package {K : Set (Space n)} (hKm : MeasurableSet K)
    (hfin : volume K ≠ ⊤) (hn : 1 ≤ n) {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (hcold : 4 * (n : ℝ) * s ≤ ρ ^ 2)
    (hballρ : closedBall (0 : Space n) ρ ⊆ K) :
    IsProbabilityMeasure (coldBallStart (n := n) s ρ) ∧
      Arlib.IsWarm (ENNReal.ofReal 2) (coldBallStart (n := n) s ρ)
        (Arlib.uniformOn
          ((volume : Measure (Space n)).withDensity (Arlib.MarkovChains.gaussianWeight s)) K) ∧
      G (indicator K (1 : Space n → ℝ)) s ∈
        Icc ((1 / 2) * (2 * Real.pi * s) ^ ((n : ℝ) / 2))
          ((2 * Real.pi * s) ^ ((n : ℝ) / 2)) := by
  exact ⟨Arlib.GaussianCooling.isProbabilityMeasure_coldBallStart hs hρ,
    Arlib.GaussianCooling.isWarm_coldBallStart_gaussian hKm hballρ hn hs hρ hcold,
    G_indicator_mem_coldNormalizer_Icc hKm hfin hn hs hρ hcold hballρ⟩

/-! ## A finite adaptive stopping chunk and the hot endpoint -/

namespace Adaptive

open Arlib.GaussianCooling.Chunked

/-- Powers of two dominate their natural exponent. -/
theorem natCast_le_two_pow (J : ℕ) : (J : ℝ) ≤ 2 ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Nat.cast_succ, pow_succ]
      have hpow : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
      nlinarith

/-- Some finite actual chunk starts at or beyond any positive target variance. -/
theorem exists_target_le_adaptiveChunkStart {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀) :
    ∃ J : ℕ, N ≤ adaptiveChunkStart N s₀ J := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (N / s₀)
  have hJs : N < (J : ℝ) * s₀ := by
    rw [div_lt_iff₀ hs₀] at hJ
    nlinarith
  have hpows : (J : ℝ) * s₀ ≤ (2 : ℝ) ^ J * s₀ :=
    mul_le_mul_of_nonneg_right (natCast_le_two_pow J) hs₀.le
  exact ⟨J, le_trans (le_of_lt (hJs.trans_le hpows))
    (pow_two_mul_le_adaptiveChunkStart hN hs₀ J)⟩

/-- The first chunk whose actual start reaches the target variance. -/
noncomputable def adaptiveTerminalChunk (N s₀ : ℝ) : ℕ := by
  classical
  exact if h : ∃ J : ℕ, N ≤ adaptiveChunkStart N s₀ J then Nat.find h else 0

theorem target_le_adaptiveTerminalChunk {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀) :
    N ≤ adaptiveChunkStart N s₀ (adaptiveTerminalChunk N s₀) := by
  have hex := exists_target_le_adaptiveChunkStart hN hs₀
  rw [adaptiveTerminalChunk, dif_pos hex]
  exact Nat.find_spec hex

/-- Every chunk actually run before the terminal chunk starts below the target variance,
which is exactly the range hypothesis of the accelerated variance product. -/
theorem adaptiveChunkStart_lt_target_of_lt_terminal {N s₀ : ℝ} (hN : 0 < N)
    (hs₀ : 0 < s₀) {j : ℕ} (hj : j < adaptiveTerminalChunk N s₀) :
    adaptiveChunkStart N s₀ j < N := by
  have hex := exists_target_le_adaptiveChunkStart hN hs₀
  rw [adaptiveTerminalChunk, dif_pos hex] at hj
  exact lt_of_not_ge (Nat.find_min hex hj)

/-- At the terminal chunk offset the flattened schedule is exactly the finite terminal
chunk start. -/
theorem adaptiveSigmaSq_terminal_eq {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀) :
    adaptiveSigmaSq N s₀
        (adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀)) =
      adaptiveChunkStart N s₀ (adaptiveTerminalChunk N s₀) :=
  adaptiveSigmaSq_offset hN hs₀ _

/-- **Finite hot endpoint.** The terminal Gaussian of the adaptive schedule has the exact
relative bias supplied by `G_indicator_mem_relErr`. -/
theorem adaptiveTerminal_G_mem_relErr {K : Set (Space n)} (hKm : MeasurableSet K)
    (hfin : volume K ≠ ⊤) {N s₀ R : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hKR : K ⊆ closedBall (0 : Space n) R) :
    G (indicator K (1 : Space n → ℝ))
        (adaptiveSigmaSq N s₀
          (adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀))) ∈
      relErr
        (1 - Real.exp (-(R ^ 2) /
          (2 * adaptiveChunkStart N s₀ (adaptiveTerminalChunk N s₀))))
        (volume K).toReal := by
  rw [adaptiveSigmaSq_terminal_eq hN hs₀]
  exact G_indicator_mem_relErr hKm hfin (adaptiveChunkStart_pos hN hs₀ _) hKR

/-- Choosing target variance `N` makes the finite terminal bias no worse than the explicit
schedule-independent value `1-exp(-R²/(2N))`.  Thus arbitrary endpoint accuracy is reached
by taking `N` large enough; all earlier chunks remain in the range required by the
accelerated variance proof. -/
theorem adaptiveTerminal_G_mem_relErr_target {K : Set (Space n)} (hKm : MeasurableSet K)
    (hfin : volume K ≠ ⊤) {N s₀ R : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hKR : K ⊆ closedBall (0 : Space n) R) :
    G (indicator K (1 : Space n → ℝ))
        (adaptiveSigmaSq N s₀
          (adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀))) ∈
      relErr (1 - Real.exp (-(R ^ 2) / (2 * N))) (volume K).toReal := by
  have hend := adaptiveTerminal_G_mem_relErr hKm hfin hN hs₀ hKR
  have hstart := target_le_adaptiveTerminalChunk hN hs₀
  have hR0 : 0 ≤ R ^ 2 := sq_nonneg R
  have hdenN : 0 < 2 * N := by positivity
  have hspos : 0 < adaptiveChunkStart N s₀ (adaptiveTerminalChunk N s₀) :=
    adaptiveChunkStart_pos hN hs₀ _
  have hdenS : 0 < 2 * adaptiveChunkStart N s₀ (adaptiveTerminalChunk N s₀) := by
    nlinarith
  have hquot : R ^ 2 / (2 * adaptiveChunkStart N s₀ (adaptiveTerminalChunk N s₀)) ≤
      R ^ 2 / (2 * N) := by
    exact div_le_div_of_nonneg_left hR0 hdenN (by nlinarith)
  have hbias : 1 - Real.exp (-(R ^ 2) /
      (2 * adaptiveChunkStart N s₀ (adaptiveTerminalChunk N s₀))) ≤
      1 - Real.exp (-(R ^ 2) / (2 * N)) := by
    have : -(R ^ 2) / (2 * N) ≤
        -(R ^ 2) / (2 * adaptiveChunkStart N s₀ (adaptiveTerminalChunk N s₀)) := by
      rw [neg_div, neg_div]
      linarith
    linarith [Real.exp_le_exp.2 this]
  exact relErr_mono hbias ENNReal.toReal_nonneg hend

end Adaptive

/-! ## Axiom audit -/

#print axioms G_indicator_mem_coldNormalizer_Icc
#print axioms G_indicator_mem_relErr_ambient_of_chernoff
#print axioms coldBallStart_endpoint_package
#print axioms Adaptive.exists_target_le_adaptiveChunkStart
#print axioms Adaptive.adaptiveChunkStart_lt_target_of_lt_terminal
#print axioms Adaptive.adaptiveTerminal_G_mem_relErr_target

end Ttc.CV

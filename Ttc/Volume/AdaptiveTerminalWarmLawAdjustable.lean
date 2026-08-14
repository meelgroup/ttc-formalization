/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptiveTerminalWarmLaw
import Arlib.MarkovChains.Continuous.AdjustableRadiusSampler
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Adjustable-radius adaptive terminal sampler

This is the q-parametric counterpart of `AdaptiveTerminalWarmLaw`.  The operational step is

`min (σ/(max 8 (2q)√n)) (1/(2n))`,

so it simultaneously satisfies adjustable conductance and speedy-rejection constraints.
The mixing deadline is rounded up internally by `ceil + 1`.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Filter Topology
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open scoped ENNReal Pointwise

variable {n r m k : Nat}

noncomputable def adaptiveTerminalDeltaQ (q N s0 : Real) (i : Nat) : Real :=
  min (adaptiveTerminalSigma N s0 i /
    (max 8 (2 * q) * Real.sqrt n)) (1 / (2 * (n : Real)))

noncomputable def adaptiveTerminalDeadlineQ (q N s0 eps : Real) (i : Nat) : Real :=
  4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
      (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / eps)) /
        (adaptiveTerminalDeltaQ (n := n) q N s0 i * Real.log 2) ^ 2 + 1

noncomputable def adaptiveTerminalStepsQ (q N s0 eps : Real) : Fin (m + 1) -> Nat :=
  fun i => ⌈adaptiveTerminalDeadlineQ (n := n) q N s0 eps i⌉₊ + 1

theorem adaptiveTerminalStepsQ_spec (q N s0 eps : Real) (i : Fin (m + 1)) :
    adaptiveTerminalDeadlineQ (n := n) q N s0 eps i <=
      (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i : Real) := by
  have hceil := Nat.le_ceil (adaptiveTerminalDeadlineQ (n := n) q N s0 eps i)
  rw [adaptiveTerminalStepsQ]
  push_cast
  linarith

noncomputable def adaptiveTerminalTruncatedLawQ
    (q N s0 rho eps : Real) (K : Set (Space n))
    (i : Fin (m + 1)) : Measure (Space n) :=
  Ttc.CVSampler.phaseLaw
    (K ∩ closedBall (0 : Space n)
      (q * adaptiveTerminalSigma N s0 i * Real.sqrt n))
    (adaptiveTerminalDeltaQ (n := n) q N s0 i)
    (adaptiveSigmaSq N s0 i)
    (coldBallStart (n := n) s0 rho)
    (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i)

/-- Adjustable terminal law with a caller-selected mixing tolerance. -/
noncomputable def adaptiveTerminalWarmLawQ
    (q N s0 rho eps : Real) (K : Set (Space n))
    (i : Fin (m + 1)) : Measure (Space n) :=
  adaptiveTerminalPhaseSamplerLaw (adaptiveSigmaSq N s0) K i
    (Ttc.CVSampler.phaseLaw
      (K ∩ closedBall (0 : Space n)
        (q * adaptiveTerminalSigma N s0 i * Real.sqrt n))
      (adaptiveTerminalDeltaQ (n := n) q N s0 i)
      (adaptiveSigmaSq N s0 i)
      (coldBallStart (n := n) s0 rho)
      (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i))

noncomputable def adaptiveTerminalWarmLawFamilyQ
    (q N s0 rho eps : Real) (K : Set (Space n)) :
    Fin r -> Fin (m + 1) -> Fin k -> Measure (Space n) :=
  fun _ i _ => adaptiveTerminalWarmLawQ q N s0 rho eps K i

private theorem one_le_q_mul_sqrt_of_warm
    (hn : 1 <= n) {q s : Real} (hq : 2 <= q) (hs : 0 < s)
    (hwarm : ¬ 4 * (n : Real) * s <= 1) :
    1 <= q * Real.sqrt s * Real.sqrt n := by
  have hsn : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hnn : Real.sqrt (n : Real) ^ 2 = (n : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hbase0 : 0 <= 2 * Real.sqrt s * Real.sqrt n := by positivity
  have hgt : 1 < 4 * (n : Real) * s := lt_of_not_ge hwarm
  have htwo : 1 < 2 * Real.sqrt s * Real.sqrt n := by
    nlinarith [sq_nonneg (2 * Real.sqrt s * Real.sqrt n - 1)]
  have hsqrtn : 0 <= Real.sqrt s * Real.sqrt n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hq hsqrtn]

private theorem adaptiveTerminalDeltaQ_pos
    (hn : 1 <= n) {q N s0 : Real} (_hq : 1 < q) (hN : 0 < N) (hs0 : 0 < s0)
    (i : Nat) : 0 < adaptiveTerminalDeltaQ (n := n) q N s0 i := by
  have hs := adaptiveSigmaSq_pos hN hs0 i
  have hsigma : 0 < adaptiveTerminalSigma N s0 i := Real.sqrt_pos.2 hs
  unfold adaptiveTerminalDeltaQ
  positivity

private theorem isWarm_coldBallStart_adaptive_adjustable
    {q N s0 rho : Real} (hq : 2 <= q) (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hn : 21 <= n) (hball : ball (0 : Space n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 <= rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) <= N)
    (i : Fin (m + 1)) (hrad : 1 <= q * adaptiveTerminalSigma N s0 i * Real.sqrt n) :
    Arlib.IsWarm (ENNReal.ofReal (adaptiveRestartWarmConst n i))
      (coldBallStart (n := n) s0 rho)
      (Arlib.MarkovChains.ellGaussianProb
        (K ∩ closedBall (0 : Space n)
          (q * adaptiveTerminalSigma N s0 i * Real.sqrt n))
        (adaptiveTerminalDeltaQ (n := n) q N s0 i)
        (adaptiveSigmaSq N s0 i)) := by
  have hn1 : 1 <= n := by omega
  let K' := K ∩ closedBall (0 : Space n)
    (q * adaptiveTerminalSigma N s0 i * Real.sqrt n)
  have hK'm : MeasurableSet K' := Arlib.MarkovChains.measurableSet_inter_closedBall hKm _
  have hK'c : Convex Real K' := Arlib.MarkovChains.convex_inter_closedBall hKc _
  have hK'ball : ball (0 : Space n) 1 ⊆ K' :=
    Arlib.MarkovChains.unitBall_subset_inter_closedBall hball hrad
  have hK'fin : volume K' ≠ ⊤ := Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  have hc0 : 0 < 1 - 1 / (2 * (n : Real)) := by
    have hnR : (1 : Real) <= n := by exact_mod_cast hn1
    have : 1 / (2 * (n : Real)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    linarith
  have hc1 : 1 - 1 / (2 * (n : Real)) < 1 := by
    have hnR0 : (0 : Real) < n := by positivity
    have hinv : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hδ := adaptiveTerminalDeltaQ_pos hn1 (lt_of_lt_of_le one_lt_two hq) hN hs0 i
  have hδc : adaptiveTerminalDeltaQ (n := n) q N s0 i <=
      1 - (1 - 1 / (2 * (n : Real))) := by
    rw [sub_sub_cancel]
    unfold adaptiveTerminalDeltaQ
    exact min_le_right _ _
  exact isWarm_coldBallStart_adaptive_ellGaussianProb hK'm hK'c hn1 hK'ball hK'fin
    hN hs0 hc0 hc1 hrho hrhoc hcoldStart hδ hδc hbelow i.isLt

theorem mixesWithin_adaptiveTerminalTruncatedLawQ
    (hn : 21 <= n) {q N s0 rho eps : Real} (hq : 2 <= q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 <= rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) <= N)
    (heps0 : 0 < eps) (heps32 : eps <= 1 / 32)
    (i : Fin (m + 1)) (hwarm : ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i <= 1) :
    Arlib.MarkovChains.MixesWithin
      (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian
        (K ∩ closedBall (0 : Space n)
          (q * adaptiveTerminalSigma N s0 i * Real.sqrt n))
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)))
      (Arlib.MarkovChains.ellGaussianProb
        (K ∩ closedBall (0 : Space n)
          (q * adaptiveTerminalSigma N s0 i * Real.sqrt n))
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i))
      (coldBallStart (n := n) s0 rho)
      (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i)
      (ENNReal.ofReal eps) := by
  have hn1 : 1 <= n := by omega
  have hq1 : 1 < q := lt_of_lt_of_le one_lt_two hq
  have hs : 0 < adaptiveSigmaSq N s0 i := adaptiveSigmaSq_pos hN hs0 i
  have hsigma : 0 < adaptiveTerminalSigma N s0 i := Real.sqrt_pos.2 hs
  have hsigmaSq : adaptiveSigmaSq N s0 i = adaptiveTerminalSigma N s0 i ^ 2 :=
    (Real.sq_sqrt hs.le).symm
  have hrad := one_le_q_mul_sqrt_of_warm hn1 hq hs hwarm
  let K' := K ∩ closedBall (0 : Space n)
    (q * adaptiveTerminalSigma N s0 i * Real.sqrt n)
  let δ := adaptiveTerminalDeltaQ (n := n) q N s0 i
  have hδ : 0 < δ := adaptiveTerminalDeltaQ_pos hn1 hq1 hN hs0 i
  have hδq : δ <= adaptiveTerminalSigma N s0 i /
      (max 8 (2 * q) * Real.sqrt n) := min_le_left _ _
  have hK'm : MeasurableSet K' := Arlib.MarkovChains.measurableSet_inter_closedBall hKm _
  have hK'c : Convex Real K' := Arlib.MarkovChains.convex_inter_closedBall hKc _
  have hK'0 : volume K' ≠ 0 := Arlib.MarkovChains.volume_inter_closedBall_ne_zero
    (fun x hx => hball (ball_subset_closedBall hx)) hrad
  have hKR : ∀ x ∈ K', ‖x‖ <= q * adaptiveTerminalSigma N s0 i * Real.sqrt n :=
    fun _ hx => Arlib.MarkovChains.norm_le_of_mem_inter_closedBall hx
  haveI : IsProbabilityMeasure (coldBallStart (n := n) s0 rho) :=
    isProbabilityMeasure_coldBallStart hs0 hrho
  have hw := isWarm_coldBallStart_adaptive_adjustable hq hN hs0 hKm hKc hn
    (fun x hx => hball (ball_subset_closedBall hx)) hrho hrhoc hcoldStart hbelow i hrad
  rw [hsigmaSq] at hw
  have hmix := Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit_adjustable
    hn hq1 hsigma hδ hδq hK'm hK'c hK'0 (by positivity) hKR le_rfl
    (show 1 <= adaptiveRestartWarmConst n i by
      exact one_le_pow₀ (by norm_num)) hw heps0 (heps32.trans (by norm_num))
    (adaptiveTerminalStepsQ_spec (n := n) (m := m) q N s0 eps i)
  rw [hsigmaSq]
  simpa only [K', δ, adaptiveTerminalDeadlineQ] using hmix

theorem isProbabilityMeasure_adaptiveTerminalWarmLawQ
    (hn : 21 <= n) {q N s0 rho eps : Real} (hq : 2 <= q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 <= rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) <= N)
    (heps0 : 0 < eps) (heps32 : eps <= 1 / 32)
    (i : Fin (m + 1)) :
    IsProbabilityMeasure (adaptiveTerminalWarmLawQ q N s0 rho eps K i) := by
  rw [adaptiveTerminalWarmLawQ, adaptiveTerminalPhaseSamplerLaw]
  split_ifs with hcold
  · let proposal := Ttc.CV.ambientGaussianProb (n := n) (adaptiveSigmaSq N s0 i)
    letI : IsProbabilityMeasure proposal :=
      Ttc.CV.isProbabilityMeasure_ambientGaussianProb (adaptiveSigmaSq_pos hN hs0 i)
    exact Measure.isProbabilityMeasure_map
      (Ttc.CV.measurable_firstAcceptedDraw hKm).aemeasurable
  · have hn1 : 1 <= n := by omega
    have hq1 : 1 < q := lt_of_lt_of_le one_lt_two hq
    have hs := adaptiveSigmaSq_pos hN hs0 i
    have hrad := one_le_q_mul_sqrt_of_warm hn1 hq hs hcold
    have hK'm : MeasurableSet (K ∩ closedBall (0 : Space n)
        (q * adaptiveTerminalSigma N s0 i * Real.sqrt n)) :=
      Arlib.MarkovChains.measurableSet_inter_closedBall hKm _
    have hK'c : Convex Real (K ∩ closedBall (0 : Space n)
        (q * adaptiveTerminalSigma N s0 i * Real.sqrt n)) :=
      Arlib.MarkovChains.convex_inter_closedBall hKc _
    have hK'ball : ball (0 : Space n) 1 ⊆
        K ∩ closedBall (0 : Space n)
          (q * adaptiveTerminalSigma N s0 i * Real.sqrt n) :=
      Arlib.MarkovChains.unitBall_subset_inter_closedBall
      (fun x hx => hball (ball_subset_closedBall hx)) hrad
    have hK'fin : volume (K ∩ closedBall (0 : Space n)
        (q * adaptiveTerminalSigma N s0 i * Real.sqrt n)) ≠ ⊤ :=
      Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
    have hδ := adaptiveTerminalDeltaQ_pos hn1 hq1 hN hs0 i
    have hδn : adaptiveTerminalDeltaQ (n := n) q N s0 i <= 1 / (2 * (n : Real)) :=
      min_le_right _ _
    haveI : IsProbabilityMeasure (coldBallStart (n := n) s0 rho) :=
      isProbabilityMeasure_coldBallStart hs0 hrho
    have hmix := mixesWithin_adaptiveTerminalTruncatedLawQ hn hq hN hs0 hKm hKc hball
      hrho hrhoc hcoldStart hbelow heps0 heps32 i hcold
    rw [Arlib.MarkovChains.mixesWithin_iff] at hmix
    exact Ttc.CVSampler.isProbabilityMeasure_phaseLaw hn1 hK'm hK'c hK'ball hK'fin
      hδ hδn hs (coldBallStart (n := n) s0 rho)
      (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i) hmix
      ((ENNReal.ofReal_le_ofReal heps32).trans (by norm_num))

theorem tvLe_adaptiveTerminalWarmLawQ
    (hn : 21 <= n) {q N s0 rho eps : Real} (hq : 2 <= q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 <= rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) <= N)
    (heps0 : 0 < eps) (heps32 : eps <= 1 / 32)
    (i : Fin (m + 1)) :
    TVLe (adaptiveTerminalWarmLawQ q N s0 rho eps K i)
      (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i)
      (64 * ENNReal.ofReal eps +
        ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  apply adaptiveTerminalPhaseSamplerLaw_tv
    (fun j => adaptiveSigmaSq_pos hN hs0 j) hKm hfin (by omega) hball i
  intro hwarm
  have hn1 : 1 <= n := by omega
  have hq1 : 1 < q := lt_of_lt_of_le one_lt_two hq
  have hs := adaptiveSigmaSq_pos hN hs0 i
  have hsigma : 0 < adaptiveTerminalSigma N s0 i := Real.sqrt_pos.2 hs
  have hsigmaSq : adaptiveSigmaSq N s0 i = adaptiveTerminalSigma N s0 i ^ 2 :=
    (Real.sq_sqrt hs.le).symm
  have hrad := one_le_q_mul_sqrt_of_warm hn1 hq hs hwarm
  let K' := K ∩ closedBall (0 : Space n)
    (q * adaptiveTerminalSigma N s0 i * Real.sqrt n)
  let δ := adaptiveTerminalDeltaQ (n := n) q N s0 i
  have hδ := adaptiveTerminalDeltaQ_pos hn1 hq1 hN hs0 i
  have hδn : δ <= 1 / (2 * (n : Real)) := min_le_right _ _
  have hK'm : MeasurableSet K' :=
    Arlib.MarkovChains.measurableSet_inter_closedBall hKm _
  have hK'c : Convex Real K' :=
    Arlib.MarkovChains.convex_inter_closedBall hKc _
  have hK'ball : ball (0 : Space n) 1 ⊆ K' :=
    Arlib.MarkovChains.unitBall_subset_inter_closedBall
    (fun x hx => hball (ball_subset_closedBall hx)) hrad
  have hK'fin : volume K' ≠ ⊤ :=
    Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  haveI : IsProbabilityMeasure (coldBallStart (n := n) s0 rho) :=
    isProbabilityMeasure_coldBallStart hs0 hrho
  have hmix := mixesWithin_adaptiveTerminalTruncatedLawQ hn hq hN hs0 hKm hKc hball
    hrho hrhoc hcoldStart hbelow heps0 heps32 i hwarm
  rw [Arlib.MarkovChains.mixesWithin_iff] at hmix
  have hsampler := Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw hn1
    (fun j => adaptiveSigmaSq_pos hN hs0 j) hK'm hK'c hK'ball hK'fin hδ hδn
    i.isLt hmix (ENNReal.ofReal_le_ofReal heps32)
  have htail := Arlib.MarkovChains.tvLe_coolLaw_inter_closedBall_relative_adjustable
    hn1 hq1 (fun j => adaptiveSigmaSq_pos hN hs0 j) hsigma hKm hKc
    (fun x hx => hball (ball_subset_closedBall hx)) hfin i.isLt hsigmaSq hrad
  simpa only [K', δ, Ttc.CVSampler.phaseLaw] using hsampler.trans htail

theorem isProbabilityMeasure_adaptiveTerminalWarmLawFamilyQ
    (hn : 21 <= n) {q N s0 rho eps : Real} (hq : 2 <= q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 <= rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) <= N)
    (heps0 : 0 < eps) (heps32 : eps <= 1 / 32)
    (t : Fin r) (i : Fin (m + 1)) (l : Fin k) :
    IsProbabilityMeasure (adaptiveTerminalWarmLawFamilyQ q N s0 rho eps K t i l) :=
  isProbabilityMeasure_adaptiveTerminalWarmLawQ hn hq hN hs0 hKm hKc hball hrho hrhoc
    hcoldStart hbelow heps0 heps32 i

theorem tvLe_adaptiveTerminalWarmLawFamilyQ
    (hn : 21 <= n) {q N s0 rho eps : Real} (hq : 2 <= q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 <= rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) <= N)
    (heps0 : 0 < eps) (heps32 : eps <= 1 / 32) :
    ∀ t : Fin r, ∀ i : Fin (m + 1), ∀ l : Fin k,
      TVLe (adaptiveTerminalWarmLawFamilyQ q N s0 rho eps K t i l)
        (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i)
        (64 * ENNReal.ofReal eps +
          ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  intro t i l
  exact tvLe_adaptiveTerminalWarmLawQ hn hq hN hs0 hKm hKc hball hfin hrho hrhoc
    hcoldStart hbelow heps0 heps32 i

/-- The one-coordinate adjustable truncation factor tends to zero as the radius grows. -/
theorem adaptiveRadiusTailBase_tendsto_zero :
    Tendsto (fun q : Real => q * Real.exp (-(q ^ 2 - 1) / 2)) atTop (nhds 0) := by
  have htarget : Tendsto (fun x : Real => Real.exp (-(1 / 2) * x)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(1 / 2) : Real) < 0))
  have hdecay : Tendsto (fun x : Real => x * Real.exp (-(1 / 2) * x ^ 2))
      atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
        (by norm_num : (0 : Real) < 1 / 2) 1).tendsto_zero_of_tendsto htarget
  have hscaled := hdecay.const_mul (Real.exp (1 / 2))
  convert hscaled using 1
  · funext x
    rw [show -(x ^ 2 - 1) / 2 = 1 / 2 + (-(1 / 2) * x ^ 2) by ring,
      Real.exp_add]
    ring
  · simp

/-- For every positive call-count envelope and tail budget, some radius `q ≥ 2` fits.

This existential selector is deliberately over the reals: the sampler and conductance APIs
already take a real radius, and no floor/ceiling loss is needed.
-/
theorem exists_adaptiveTerminalRadiusQ (hn : 1 <= n) {A b : Real}
    (_hA : 0 < A) (hb : 0 < b) :
    ∃ q : Real, 2 <= q ∧ AdjustableRadiusTailFits n A b q := by
  have hpow := adaptiveRadiusTailBase_tendsto_zero.pow n
  have hAdecay := hpow.const_mul A
  have hev : ∀ᶠ q : Real in atTop,
      A * (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n < b :=
    (tendsto_order.1 (by simpa [Nat.ne_of_gt hn] using hAdecay)).2 b hb
  obtain ⟨q, hqb, hq⟩ := (hev.and (eventually_gt_atTop (2 : Real))).exists
  exact ⟨q, hq.le, one_lt_two.trans hq, hqb.le⟩

/-- A tail-fit certificate turns the exact per-draw tail into the budget `b/A`. -/
theorem tvLe_adaptiveTerminalWarmLawFamilyQ_of_tailFits
    (hn : 21 <= n) {q N s0 rho eps A b : Real} (hq : 2 <= q)
    (hA : 0 < A) (hfit : AdjustableRadiusTailFits n A b q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 <= rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) <= N)
    (heps0 : 0 < eps) (heps32 : eps <= 1 / 32) :
    ∀ t : Fin r, ∀ i : Fin (m + 1), ∀ l : Fin k,
      TVLe (adaptiveTerminalWarmLawFamilyQ q N s0 rho eps K t i l)
        (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i)
        (64 * ENNReal.ofReal eps + ENNReal.ofReal (b / A)) := by
  intro t i l
  refine (tvLe_adaptiveTerminalWarmLawFamilyQ hn hq hN hs0 hKm hKc hball hfin
    hrho hrhoc hcoldStart hbelow heps0 heps32 t i l).mono ?_
  exact add_le_add le_rfl
    (ENNReal.ofReal_le_ofReal (adjustableRadiusTail_perCoordinate_le hA hfit))

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.adaptiveTerminalStepsQ_spec
#print axioms Ttc.CVAdaptive.mixesWithin_adaptiveTerminalTruncatedLawQ
#print axioms Ttc.CVAdaptive.isProbabilityMeasure_adaptiveTerminalWarmLawFamilyQ
#print axioms Ttc.CVAdaptive.tvLe_adaptiveTerminalWarmLawFamilyQ
#print axioms Ttc.CVAdaptive.adaptiveRadiusTailBase_tendsto_zero
#print axioms Ttc.CVAdaptive.exists_adaptiveTerminalRadiusQ
#print axioms Ttc.CVAdaptive.tvLe_adaptiveTerminalWarmLawFamilyQ_of_tailFits

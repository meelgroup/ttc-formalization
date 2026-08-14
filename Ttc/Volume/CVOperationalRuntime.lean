/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Volume.CVAdaptiveRuntime
import Ttc.Volume.SpeedyAcceptanceRejection
import Arlib.MarkovChains.Continuous.RadiusFourGaussian
import Arlib.Convexity.GaussianCooling.ChunkedVarianceUnconditional

/-!
# Honest operational runtime bounds for the adaptive CV schedule

This file combines the deterministic parts of the runtime proof: the adaptive phase-count
bound, the independent-restart warmness logarithm, the variance range before the terminal
chunk, and the radius-four speedy mixing deadline.  It also records the numerical accounting
which would result from at most four expected rejection rounds per accepted speedy draw.

It deliberately does not call that accounting an expected membership-query theorem.  The
current `CVTheorem11Implementation` has a deterministic `queryCost : ℕ`, while rejection cost
is represented by an integral on an i.i.d. trajectory space.  No program semantics currently
couples those trajectories to the Markov-chain membership queries, phase/sample loops, and
median repetitions.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive
open Arlib.MarkovChains
open scoped ENNReal

/-- A uniform upper envelope for one radius-four mixing deadline on the preterminal adaptive
schedule. -/
noncomputable def adaptiveRadiusFourMixingEnvelope
    (n : ℕ) (N s₀ epsMix : ℝ) : ℝ :=
  6553600 * (2 * N * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2) *
      ((1 + (n : ℝ) * (5 * N / s₀ + 2)) * Real.log 2 +
        2 * Real.log (1 / epsMix)) / Real.log 2 ^ 2 + 1

/-- Pure numerical accounting for one ambient cold start, `drawsPerPhase` accepted speedy
draws per phase, `runs` independent estimator runs, and the operational rejection factor `4`.
This becomes an expected-query bound only after a cost-composition theorem relates one
rejection round to one execution of the bounded-step Markov sampler. -/
noncomputable def adaptiveOperationalAccountingEnvelope
    (n : ℕ) (N s₀ epsMix runs drawsPerPhase : ℝ) : ℝ :=
  2 + 4 * runs * drawsPerPhase * (5 * N / s₀ + 2) *
    adaptiveRadiusFourMixingEnvelope n N s₀ epsMix

/-- Every flattened phase before the terminal offset has variance below `2N`. -/
theorem adaptiveSigmaSq_lt_two_mul_target {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    {i : ℕ} (hi : i < adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀)) :
    adaptiveSigmaSq N s₀ i < 2 * N := by
  let j := adaptivePhaseChunk N s₀ i
  let t := adaptiveLocalPhase N s₀ i
  have hj : j < adaptiveTerminalChunk N s₀ :=
    adaptivePhaseChunk_lt_of_lt_offset hN hs₀ hi
  have hstart : adaptiveChunkStart N s₀ j < N :=
    adaptiveChunkStart_lt_target_of_lt_terminal hN hs₀ hj
  have ht : t < adaptiveChunkPhases N s₀ j := adaptiveLocalPhase_lt hN hs₀ i
  have hphase := adaptiveChunk_phase_lt_two hN hs₀ ht
  change adaptiveSigmaSq N s₀ i < 2 * N
  unfold adaptiveSigmaSq
  exact hphase.trans (mul_lt_mul_of_pos_left hstart (by norm_num))

/-- The exact algebraic radius-four mixing deadline of each preterminal phase is bounded by
one explicit expression polynomial in `n`, `N/s₀`, `N`, and the mixing logarithm. -/
theorem adaptive_radiusFour_deadline_le_envelope {n : ℕ} (hn : 21 ≤ n)
    {N s₀ epsMix : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (heps0 : 0 < epsMix) (heps1 : epsMix ≤ 1)
    {i : ℕ} (hi : i < adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀)) :
    let u := adaptiveSigmaSq N s₀ i
    let σ := Real.sqrt u
    let M := adaptiveRestartWarmConst n i
    let δ := min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))
    4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) *
          (Real.log M + 2 * Real.log (1 / epsMix)) /
          (δ * Real.log 2) ^ 2 + 1
      ≤ adaptiveRadiusFourMixingEnvelope n N s₀ epsMix := by
  dsimp only
  have hu : 0 < adaptiveSigmaSq N s₀ i := adaptiveSigmaSq_pos hN hs₀ i
  have hσ : 0 < Real.sqrt (adaptiveSigmaSq N s₀ i) := Real.sqrt_pos.2 hu
  have hσsq : Real.sqrt (adaptiveSigmaSq N s₀ i) ^ 2 = adaptiveSigmaSq N s₀ i :=
    Real.sq_sqrt hu.le
  have hM : 1 ≤ adaptiveRestartWarmConst n i := by
    unfold adaptiveRestartWarmConst
    exact one_le_pow₀ (by norm_num)
  have hlogM : 0 ≤ Real.log (adaptiveRestartWarmConst n i) := Real.log_nonneg hM
  have hlogeps : 0 ≤ Real.log (1 / epsMix) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ heps0]
    linarith
  have hX : 0 ≤ Real.log (adaptiveRestartWarmConst n i) +
      2 * Real.log (1 / epsMix) := by positivity
  have hcore := coldStep_deadline_le hn hσ hX
  have huN : adaptiveSigmaSq N s₀ i ≤ 2 * N :=
    (adaptiveSigmaSq_lt_two_mul_target hN hs₀ hi).le
  have hlogBound := log_adaptiveRestartWarmConst_le_terminal_poly (n := n) hN hs₀ hi
  rw [hσsq] at hcore
  rw [hσsq]
  calc
    4 * 640 ^ 2 * adaptiveSigmaSq N s₀ i * (n : ℝ) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix)) /
          (min (Real.sqrt (adaptiveSigmaSq N s₀ i) / (8 * Real.sqrt n))
            (1 / (2 * (n : ℝ))) * Real.log 2) ^ 2 + 1
      ≤ 6553600 * (adaptiveSigmaSq N s₀ i * (n : ℝ) ^ 3 +
            16 * (n : ℝ) ^ 2) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix)) /
          Real.log 2 ^ 2 + 1 := by linarith
    _ ≤ adaptiveRadiusFourMixingEnvelope n N s₀ epsMix := by
      unfold adaptiveRadiusFourMixingEnvelope
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hcoef : 0 ≤ adaptiveSigmaSq N s₀ i * (n : ℝ) ^ 3 +
          16 * (n : ℝ) ^ 2 := by positivity
      have hcoef' : 0 ≤ 2 * N * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2 := by positivity
      have hlog2sq : 0 < Real.log 2 ^ 2 := by
        positivity
      have hcoefLe : adaptiveSigmaSq N s₀ i * (n : ℝ) ^ 3 +
          16 * (n : ℝ) ^ 2 ≤ 2 * N * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2 := by
        gcongr
      have hXLe : Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix) ≤
          (1 + (n : ℝ) * (5 * N / s₀ + 2)) * Real.log 2 +
            2 * Real.log (1 / epsMix) := by linarith
      have hXmax0 : 0 ≤ (1 + (n : ℝ) * (5 * N / s₀ + 2)) * Real.log 2 +
          2 * Real.log (1 / epsMix) := by
        have hratio : 0 < N / s₀ := div_pos hN hs₀
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        positivity
      gcongr

/-- The arithmetic envelope feeds the actual radius-four mixing theorem for every
preterminal adaptive phase.  Warmness is kept explicit because the current truncated
independent-restart adapter is packaged only at radius `2σ√n`; this theorem makes the
remaining radius-four warm-start interface precise. -/
theorem mixesWithin_adaptive_radiusFour_truncated_of_envelope {n : ℕ} (hn : 21 ≤ n)
    {N s₀ epsMix : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (heps0 : 0 < epsMix) (heps1 : epsMix ≤ 1)
    {i : ℕ} (hi : i < adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀))
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : Space n) 1 ⊆ K)
    (hrad : 1 ≤ 4 * Real.sqrt (adaptiveSigmaSq N s₀ i) * Real.sqrt n)
    {mu0 : Measure (Space n)} [IsProbabilityMeasure mu0]
    (hwarm : Arlib.IsWarm (ENNReal.ofReal (adaptiveRestartWarmConst n i)) mu0
      (ellGaussianProb
        (K ∩ closedBall (0 : Space n)
          (4 * Real.sqrt (adaptiveSigmaSq N s₀ i) * Real.sqrt n))
        (min (Real.sqrt (adaptiveSigmaSq N s₀ i) / (8 * Real.sqrt n))
          (1 / (2 * (n : ℝ))))
        (adaptiveSigmaSq N s₀ i)))
    {t : ℕ} (ht : adaptiveRadiusFourMixingEnvelope n N s₀ epsMix ≤ (t : ℝ)) :
    MixesWithin
      (lazy (speedyMetropolisGaussian
        (K ∩ closedBall (0 : Space n)
          (4 * Real.sqrt (adaptiveSigmaSq N s₀ i) * Real.sqrt n))
        (min (Real.sqrt (adaptiveSigmaSq N s₀ i) / (8 * Real.sqrt n))
          (1 / (2 * (n : ℝ))))
        (adaptiveSigmaSq N s₀ i)))
      (ellGaussianProb
        (K ∩ closedBall (0 : Space n)
          (4 * Real.sqrt (adaptiveSigmaSq N s₀ i) * Real.sqrt n))
        (min (Real.sqrt (adaptiveSigmaSq N s₀ i) / (8 * Real.sqrt n))
          (1 / (2 * (n : ℝ))))
        (adaptiveSigmaSq N s₀ i))
      mu0 t (ENNReal.ofReal epsMix) := by
  let u := adaptiveSigmaSq N s₀ i
  let σ := Real.sqrt u
  let δ := min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))
  let K' := K ∩ closedBall (0 : Space n) (4 * σ * Real.sqrt n)
  have hu : 0 < u := adaptiveSigmaSq_pos hN hs₀ i
  have hσ : 0 < σ := Real.sqrt_pos.2 hu
  have hσsq : σ ^ 2 = u := Real.sq_sqrt hu.le
  have hδ : 0 < δ := coldStep_pos (by omega) hσ
  have hδσ : δ ≤ σ / (8 * Real.sqrt n) := min_le_left _ _
  have hK'm : MeasurableSet K' := measurableSet_inter_closedBall hKm _
  have hK'c : Convex ℝ K' := convex_inter_closedBall hKc _
  have hK'0 : volume K' ≠ 0 := volume_inter_closedBall_ne_zero hball (by simpa [u, σ] using hrad)
  have hKR : ∀ x ∈ K', ‖x‖ ≤ 4 * σ * Real.sqrt n :=
    fun _ hx => norm_le_of_mem_inter_closedBall hx
  have hM : 1 ≤ adaptiveRestartWarmConst n i := by
    unfold adaptiveRestartWarmConst
    exact one_le_pow₀ (by norm_num)
  have hdeadline := adaptive_radiusFour_deadline_le_envelope hn hN hs₀ heps0 heps1 hi
  have ht' : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) *
      (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix)) /
        (δ * Real.log 2) ^ 2 + 1 ≤ (t : ℝ) := by
    exact hdeadline.trans ht
  have hmix := mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit_radius_four
    hn hσ hδ hδσ hK'm hK'c hK'0 (by positivity) hKR le_rfl hM
    (by simpa [K', δ, σ, u, hσsq] using hwarm) heps0 heps1 ht'
  simpa [K', δ, σ, u, hσsq] using hmix

/-- The deterministic accounting expression obtained from `J` phases, a per-round bound `q`,
and the expected rejection factor `4` is bounded by the explicit adaptive envelope.  This is
an arithmetic certificate, not yet a theorem about an execution random variable. -/
theorem adaptive_operational_accounting_le
    {n : ℕ} {N s₀ epsMix runs drawsPerPhase q : ℝ}
    (hN : 0 < N) (hs₀ : 0 < s₀) (hruns : 0 ≤ runs) (hdraws : 0 ≤ drawsPerPhase)
    (hq0 : 0 ≤ q) (hq : q ≤ adaptiveRadiusFourMixingEnvelope n N s₀ epsMix) :
    2 + 4 * runs * drawsPerPhase *
          (adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀) : ℝ) * q
      ≤ adaptiveOperationalAccountingEnvelope n N s₀ epsMix runs drawsPerPhase := by
  have hJ := (adaptiveTerminalOffset_lt_five_mul_div_add_two hN hs₀).le
  unfold adaptiveOperationalAccountingEnvelope
  gcongr

/-- The two operational rejection costs needed by the CV pipeline, recorded on their actual
trajectory measures: ambient cold initialization costs at most two draws, and an approximate
speedy acceptance proposal with quarter weighted mass costs at most four rounds.  They remain
separate integrals until an execution semantics supplies a composition theorem. -/
theorem operational_rejection_round_certificates {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hKm : MeasurableSet K)
    {sCold : ℝ} (hsCold : 0 < sCold) (hcold : 4 * (n : ℝ) * sCold ≤ 1)
    (hball : closedBall (0 : Space n) 1 ⊆ K)
    (Q : Measure (Space n)) [IsProbabilityMeasure Q]
    {c s : ℝ} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hquarter : ENNReal.ofReal (1 / 4) ≤
      (Q.withDensity fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ) :
    (∫ omega, (Arlib.Probability.roundCountNat K omega : ℝ)
        ∂(Arlib.Probability.roundsMeasure (Ttc.CV.ambientGaussianProb (n := n) sCold))) ≤ 2 ∧
      (∫ omega,
          (Arlib.Probability.roundCountNat (Ttc.SpeedyRejection.acceptRegion c s) omega : ℝ)
          ∂(Arlib.Probability.roundsMeasure (Ttc.SpeedyRejection.proposal Q))) ≤ 4 := by
  constructor
  · exact Ttc.CV.expected_ambientGaussian_rejection_rounds_le_two
      hKm hn hsCold hcold hball
  · exact Ttc.SpeedyRejection.expected_rejection_rounds_le_four_of_quarter
      Q hs hc2 hquarter

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.adaptiveSigmaSq_lt_two_mul_target
#print axioms Ttc.CVAdaptive.adaptive_radiusFour_deadline_le_envelope
#print axioms Ttc.CVAdaptive.mixesWithin_adaptive_radiusFour_truncated_of_envelope
#print axioms Ttc.CVAdaptive.adaptive_operational_accounting_le
#print axioms Ttc.CVAdaptive.operational_rejection_round_certificates

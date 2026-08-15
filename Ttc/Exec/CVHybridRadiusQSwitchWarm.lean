import Ttc.Exec.CVAdaptiveRadiusQSmallRateWarm
import Ttc.Exec.CVAdaptiveRadiusQAcceptedWarm
import Ttc.Exec.CVGaussianAdaptiveAcceptedWarm
import Ttc.Exec.CVHybridRadiusQRecursiveStep
import Ttc.Exec.CVGlobalRadiusTerminalBody
import Ttc.Volume.CVHybridVarianceBudget
import Arlib.Convexity.GaussianCooling.ChunkedVarianceUnconditional

/-!
# Constant warmth before the adjustable-radius body reaches the source body

The source hybrid variance schedule can be retained.  During an adaptive phase the
chunk rate is its chunk-start variance divided by `2N`, hence is no larger than the
current variance divided by `2N`.  If the radius-`q` truncation is still proper and
`K ⊆ closedBall 0 R`, then `q² s n < R²`.  Under `R² ≤ 2N` this forces the
rate below `1/n`.  Consequently every proper-truncation transition has the universal
`2e` cross-warm factor; after the truncation disappears, the existing full-body hot
machinery applies.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridRadiusQSwitchWarm

open MeasureTheory Metric Set Arlib
open Arlib.MarkovChains Arlib.GaussianCooling Arlib.GaussianCooling.Chunked
open Ttc.CVHybridSchedule Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVAdaptiveRadiusQCrossWarm Ttc.CVAdaptiveRadiusQSmallRateWarm
open Ttc.CVAdaptiveRadiusQAcceptedWarm Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.CVHybridRadiusQRecursiveStep
open Ttc.CVHybridRadiusQFallbackSchedule
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- A hot hybrid phase rate is at most the current variance divided by `2N`. -/
theorem phaseRate_le_sigmaSq_div_two_mul
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {i : Nat} (hi : ¬ i < coldPhases n s0) :
    phaseRate n N s0 i ≤ sigmaSq n N s0 i / (2 * N) := by
  let j := i - coldPhases n s0
  have hstart :
      adaptiveChunkStart N (coldEnd n s0)
          (adaptivePhaseChunk N (coldEnd n s0) j) ≤
        adaptiveSigmaSq N (coldEnd n s0) j := by
    simpa only [adaptiveSigmaSq] using
      (adaptiveChunkStart_le_geom hN (coldEnd_pos hn hs0)
        (adaptivePhaseChunk N (coldEnd n s0) j)
        (adaptiveLocalPhase N (coldEnd n s0) j))
  rw [phaseRate, if_neg hi, sigmaSq, if_neg hi]
  unfold adaptivePhaseRate adaptiveChunkRate
  exact div_le_div_of_nonneg_right hstart (by positivity)

/-- Nonnegativity of every source hybrid rate. -/
theorem phaseRate_nonneg
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (i : Nat) : 0 ≤ phaseRate n N s0 i := by
  rw [phaseRate]
  split
  · positivity
  · exact (adaptiveChunkRate_pos hN (coldEnd_pos hn hs0) _).le

/-- If the adjustable-radius body has not yet become all of `K`, its source hybrid
rate is at most `1/n`.  The proof covers both the literal fixed-rate prefix and the
adaptive chunks which occur before the geometric switch. -/
theorem phaseRate_le_inv_nat_of_radiusQBody_ne
    (hn : 1 ≤ n) {q N s0 R : Real} (hq : 1 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0) (hR0 : 0 ≤ R) (hR2 : R ^ 2 ≤ 2 * N)
    {K : Set (State n)} (houter : K ⊆ closedBall 0 R) (i : Nat)
    (hne : radiusQBody q K (sigmaSq n N s0 i) ≠ K) :
    phaseRate n N s0 i ≤ 1 / (n : Real) := by
  by_cases hi : i < coldPhases n s0
  · rw [phaseRate, if_pos hi]
  · have hs : 0 < sigmaSq n N s0 i := sigmaSq_pos hn hN hs0 i
    have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    have hq0 : 0 ≤ q := hq.trans' zero_le_one
    have hrad0 : 0 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n := by
      positivity
    have hnot : ¬ R ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n := by
      intro hR
      exact hne (radiusQBody_eq_of_outer_radius houter hR)
    have hrad : q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n < R :=
      lt_of_not_ge hnot
    have hsq :
        q ^ 2 * sigmaSq n N s0 i * (n : Real) < R ^ 2 := by
      have := (sq_lt_sq₀ hrad0 hR0).2 hrad
      rw [mul_pow, mul_pow, Real.sq_sqrt hs.le,
        Real.sq_sqrt (show (0 : Real) ≤ n by positivity)] at this
      nlinarith
    have hq2 : 1 ≤ q ^ 2 := by nlinarith
    have hsig : sigmaSq n N s0 i < 2 * N / ((n : Real) * q ^ 2) := by
      rw [lt_div_iff₀ (mul_pos hnR (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hq)))]
      nlinarith
    have hrate := phaseRate_le_sigmaSq_div_two_mul hn hN hs0 hi
    have hdiv : sigmaSq n N s0 i / (2 * N) < 1 / ((n : Real) * q ^ 2) := by
      calc
        sigmaSq n N s0 i / (2 * N) <
            (2 * N / ((n : Real) * q ^ 2)) / (2 * N) :=
          div_lt_div_of_pos_right hsig (by positivity)
        _ = 1 / ((n : Real) * q ^ 2) := by field_simp
    have hqinv : 1 / ((n : Real) * q ^ 2) ≤ 1 / (n : Real) := by
      rw [div_le_div_iff₀ (mul_pos hnR (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hq))) hnR]
      nlinarith
    exact hrate.trans (hdiv.le.trans hqinv)

/-- Universal cross-warm factor throughout the still-truncated prefix. -/
theorem adaptiveRadiusQWarmFactor_hybrid_le_two_exp_of_body_ne
    (hn : 1 ≤ n) {q N s0 R : Real} (hq : 1 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0) (hR0 : 0 ≤ R) (hR2 : R ^ 2 ≤ 2 * N)
    {K : Set (State n)} (houter : K ⊆ closedBall 0 R) (i : Nat)
    (hne : radiusQBody q K (sigmaSq n N s0 i) ≠ K) :
    adaptiveRadiusQWarmFactor n (1 + phaseRate n N s0 i) ≤
      ENNReal.ofReal (2 * Real.exp 1) := by
  exact adaptiveRadiusQWarmFactor_one_add_le_two_exp hn
    (phaseRate_nonneg hn hN hs0 i)
    (phaseRate_le_inv_nat_of_radiusQBody_ne hn hq hN hs0 hR0 hR2 houter i hne)

/-- The exact cross-warm factor used by the switched proof: expanding-support while
the truncation is proper, and the sharper full-body factor after it disappears. -/
noncomputable def switchedRadiusQWarmFactor
    (n : Nat) (q N s0 : Real) (K : Set (State n)) (i : Nat) : ENNReal :=
  if radiusQBody q K (sigmaSq n N s0 i) = K then
    acceleratedSeedWarmFactor n (1 + phaseRate n N s0 i)
  else adaptiveRadiusQWarmFactor n (1 + phaseRate n N s0 i)

/-- Phasewise cross warmth for the geometric switch.  This theorem is deliberately
about the same q-radius kernel on both sides of the switch, so no operational kernel
or schedule replacement is required. -/
theorem isWarm_standardScaled_radiusQ_hybrid_switched
    (hn : 1 ≤ n) {m : Nat} {q N s0 : Real} (hq : 0 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrate0 : 0 ≤ phaseRate n N s0 i)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n) :
    IsWarm (switchedRadiusQWarmFactor n q N s0 K i)
      (Measure.map (fun y : State n ↦ (1 - 1 / (2 * (n : Real))) • y)
        (coolLaw m (sigmaSq n N s0)
          (radiusQBody q K (sigmaSq n N s0 i)) i))
      (ellGaussianProb (radiusQBody q K (sigmaSq n N s0 (i + 1)))
        (radiusQDelta n q (sigmaSq n N s0 (i + 1)))
        (sigmaSq n N s0 (i + 1))) := by
  by_cases hbody : radiusQBody q K (sigmaSq n N s0 i) = K
  · have hsched : sigmaSq n N s0 (i + 1) =
        (1 + phaseRate n N s0 i) * sigmaSq n N s0 i := by
      rw [sigmaSq_succ hn hN hs0 i]
      ring
    have hraw := isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb_ratio
      (m := m) hn (sigmaSq_pos hn hN hs0) hK hKc hball hfin hi
      (show 1 ≤ 1 + phaseRate n N s0 i by linarith) hsched
      (radiusQDelta_pos hn hq (sigmaSq_pos hn hN hs0 (i + 1)))
      (radiusQDelta_le_n n q (sigmaSq n N s0 (i + 1)))
    have hsle : sigmaSq n N s0 i ≤ sigmaSq n N s0 (i + 1) := by
      rw [sigmaSq_succ hn hN hs0 i]
      nlinarith [sigmaSq_pos hn hN hs0 i]
    have hnext : radiusQBody q K (sigmaSq n N s0 (i + 1)) = K := by
      have hsub : K ⊆ closedBall (0 : State n)
          (q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n) := by
        intro x hx
        have hx' : x ∈ radiusQBody q K (sigmaSq n N s0 i) := by
          rw [hbody]
          exact hx
        exact hx'.2
      apply radiusQBody_eq_of_outer_radius hsub
      gcongr
    rw [switchedRadiusQWarmFactor, if_pos hbody]
    simpa only [hbody, hnext] using hraw
  · have hqcross :=
      isWarm_standardScaledTruncated_ellGaussianProb_radiusQ_hybrid
        (m := m) hn hq hN hs0 hK hKc hball hi hrate0 hrad
    rw [switchedRadiusQWarmFactor, if_neg hbody]
    exact hqcross

/-- Accepted first-hit output warmth using the switched factor.  This is the direct
replacement for the all-truncated accepted theorem in the recursive operational step. -/
theorem isWarm_seed_acceptedOutputSubmeasure_radiusQ_hybrid_switched
    (hn : 1 ≤ n) {m : Nat} {q N s0 : Real} (hq : 0 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrate0 : 0 ≤ phaseRate n N s0 i)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    {rho : Measure (State n)} [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho
      (ellGaussianProb (radiusQBody q K (sigmaSq n N s0 i))
        (radiusQDelta n q (sigmaSq n N s0 i)) (sigmaSq n N s0 i)))
    (steps : Nat → Nat) (L : Nat) :
    IsWarm ((L : ENNReal) *
      ((16 * switchedRadiusQWarmFactor n q N s0 K i) * M))
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf
            (radiusQBody q K (sigmaSq n N s0 i))
            (measurableSet_radiusQBody hK)
            (radiusQDelta n q (sigmaSq n N s0 i)) (sigmaSq n N s0 i)
            (1 - 1 / (2 * (n : Real)))
            (radiusQDelta_pos hn hq (sigmaSq_pos hn hN hs0 i))
            (by
              have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            steps
            (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) L)))
      (ellGaussianProb (radiusQBody q K (sigmaSq n N s0 (i + 1)))
        (radiusQDelta n q (sigmaSq n N s0 (i + 1)))
        (sigmaSq n N s0 (i + 1))) := by
  apply isWarm_seed_acceptedOutputSubmeasure_radiusQ_of_cross
    hn hq (sigmaSq_pos hn hN hs0) hK hKc hball hfin hi hrad _
    (isWarm_standardScaled_radiusQ_hybrid_switched hn hq hN hs0 hK hKc
      hball hfin hi hrate0 hrad) hwarm steps L

/-- Accepted coefficient used by the recursive switch-aware warm budget. -/
noncomputable def hybridRadiusQSwitchedAcceptedFactor
    (n : Nat) (q N s0 : Real) (K : Set (State n))
    (retries : Nat → Nat) (i : Nat) : ENNReal :=
  max 1 ((retries i : ENNReal) *
    (16 * switchedRadiusQWarmFactor n q N s0 K i))

theorem one_le_hybridRadiusQSwitchedAcceptedFactor
    (n : Nat) (q N s0 : Real) (K : Set (State n))
    (retries : Nat → Nat) (i : Nat) :
    1 ≤ hybridRadiusQSwitchedAcceptedFactor n q N s0 K retries i :=
  le_max_left _ _

theorem hybridRadiusQSwitchedAcceptedFactor_ne_top
    (n : Nat) (q N s0 : Real) (K : Set (State n))
    (retries : Nat → Nat) (i : Nat) :
    hybridRadiusQSwitchedAcceptedFactor n q N s0 K retries i ≠ ⊤ := by
  unfold hybridRadiusQSwitchedAcceptedFactor switchedRadiusQWarmFactor
  apply max_ne_top
  · simp
  · apply ENNReal.mul_ne_top (by simp)
    apply ENNReal.mul_ne_top (by simp)
    split
    · unfold acceleratedSeedWarmFactor
      exact ENNReal.ofReal_ne_top
    · unfold adaptiveRadiusQWarmFactor
      exact ENNReal.ofReal_ne_top

/-- Dimension-polynomial logarithmic envelope for either side of the switch.  The
truncated side is bounded by `2e`; the full-body accelerated side by `2^(n+1)`.
Only the logarithm of this maximum enters the canonical mixing deadline. -/
theorem switchedRadiusQWarmFactor_le_universalMax
    (hn : 1 ≤ n) {q N s0 R : Real} (hq : 1 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0) (hR0 : 0 ≤ R) (hR2 : R ^ 2 ≤ 2 * N)
    {K : Set (State n)} (houter : K ⊆ closedBall 0 R) (i : Nat)
    (hrateHalf : phaseRate n N s0 i ≤ 1 / 2) :
    switchedRadiusQWarmFactor n q N s0 K i ≤
      max (ENNReal.ofReal (2 * Real.exp 1))
        (ENNReal.ofReal ((2 : Real) ^ (n + 1))) := by
  by_cases hbody : radiusQBody q K (sigmaSq n N s0 i) = K
  · rw [switchedRadiusQWarmFactor, if_pos hbody]
    exact (acceleratedSeedWarmFactor_le_pow_two
      (show 1 ≤ 1 + phaseRate n N s0 i by
        linarith [phaseRate_nonneg hn hN hs0 i])
      (by linarith)).trans (le_max_right _ _)
  · rw [switchedRadiusQWarmFactor, if_neg hbody]
    exact (adaptiveRadiusQWarmFactor_hybrid_le_two_exp_of_body_ne
      hn hq hN hs0 hR0 hR2 houter i hbody).trans (le_max_left _ _)

theorem hybridRadiusQSwitchedAcceptedFactor_le_universalMax
    (hn : 1 ≤ n) {q N s0 R : Real} (hq : 1 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0) (hR0 : 0 ≤ R) (hR2 : R ^ 2 ≤ 2 * N)
    {K : Set (State n)} (houter : K ⊆ closedBall 0 R)
    (retries : Nat → Nat) (i : Nat)
    (hrateHalf : phaseRate n N s0 i ≤ 1 / 2) :
    hybridRadiusQSwitchedAcceptedFactor n q N s0 K retries i ≤
      max 1 ((retries i : ENNReal) *
        (16 * max (ENNReal.ofReal (2 * Real.exp 1))
          (ENNReal.ofReal ((2 : Real) ^ (n + 1))))) := by
  unfold hybridRadiusQSwitchedAcceptedFactor
  apply max_le_max le_rfl
  gcongr
  exact switchedRadiusQWarmFactor_le_universalMax hn hq hN hs0 hR0 hR2
    houter i hrateHalf

/-- Exact seed recurrence with the geometric switch-aware accepted coefficient. -/
theorem isWarm_seed_hybridRadiusQWarmFallbackKernel_switched_step
    (hn : 1 ≤ n) {m : Nat} {q N s0 : Real} (hq : 0 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    {i : Nat} (hi : i + 1 < m)
    (hrate0 : 0 ≤ phaseRate n N s0 i)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (hradNext : 1 ≤ q * Real.sqrt (sigmaSq n N s0 (i + 1)) * Real.sqrt n)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho (hybridRadiusQSeedTarget n q N s0 K i)) :
    IsWarm
      (hybridRadiusQSwitchedAcceptedFactor n q N s0 K retries i * M +
        hybridRadiusQFallbackFactor n q N s0 K i)
      (Measure.map Prod.snd
        (sampleFromKernel
          (sourceHybridRadiusQWarmFallbackSchedule hn q hq hN hs0 K hK
            steps retries scoreScale i) rho))
      (hybridRadiusQSeedTarget n q N s0 K (i + 1)) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusQFallback hn hN hs0 scoreScale j
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc : c ≠ 0 := by
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    dsimp only [c]
    linarith
  have hacc := isWarm_seed_acceptedOutputSubmeasure_radiusQ_hybrid_switched
    hn hq hN hs0 hK hKc hball hfin hi hrate0 hrad hwarm
      (steps i) (retries i)
  have hfb := isWarm_seed_hybridRadiusQFallback_next hn hq hN hs0 hK hKc hball
    hfin i hradNext scoreScale
  have hstep := isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
    (measurableSet_radiusQBody hK)
    (radiusQDelta n q (sigmaSq n N s0 i)) (sigmaSq n N s0 i) c
    (radiusQDelta_pos hn hq (sigmaSq_pos hn hN hs0 i)) hc
    (steps i) (retries i) (hybridRadiusQFallback n N s0 scoreScale i) rho
    (hybridRadiusQSeedTarget n q N s0 K (i + 1)) hacc hfb
  apply hstep.mono
  apply add_le_add _ le_rfl
  calc
    (retries i : ENNReal) *
          ((16 * switchedRadiusQWarmFactor n q N s0 K i) * M) =
        ((retries i : ENNReal) *
          (16 * switchedRadiusQWarmFactor n q N s0 K i)) * M := by ac_rfl
    _ ≤ hybridRadiusQSwitchedAcceptedFactor n q N s0 K retries i * M := by
      apply mul_le_mul_right'
      exact le_max_right _ _

#print axioms phaseRate_le_sigmaSq_div_two_mul
#print axioms phaseRate_le_inv_nat_of_radiusQBody_ne
#print axioms adaptiveRadiusQWarmFactor_hybrid_le_two_exp_of_body_ne
#print axioms isWarm_standardScaled_radiusQ_hybrid_switched
#print axioms isWarm_seed_acceptedOutputSubmeasure_radiusQ_hybrid_switched
#print axioms isWarm_seed_hybridRadiusQWarmFallbackKernel_switched_step
#print axioms switchedRadiusQWarmFactor_le_universalMax
#print axioms hybridRadiusQSwitchedAcceptedFactor_le_universalMax

end Ttc.CVHybridRadiusQSwitchWarm

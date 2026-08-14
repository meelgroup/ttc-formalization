/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptiveTerminalSamplerLaw
import Ttc.Volume.CVSampler
import Arlib.Convexity.GaussianCooling.AdaptiveRestartTruncatedFourAll

/-!
# A concrete radius-four law for adaptive terminal sampling

The warm branch of `adaptiveTerminalPhaseSamplerLaw` is instantiated by the actual
radius-four truncated speedy walk, independently restarted from `coldBallStart`.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open scoped ENNReal Pointwise

variable {n r m k : Nat}

/-- The standard deviation at adaptive phase `i`. -/
noncomputable def adaptiveTerminalSigma (N s0 : Real) (i : Nat) : Real :=
  Real.sqrt (adaptiveSigmaSq N s0 i)

/-- The speedy-walk step used at adaptive phase `i`. -/
noncomputable def adaptiveTerminalDelta (N s0 : Real) (i : Nat) : Real :=
  min (adaptiveTerminalSigma N s0 i / (8 * Real.sqrt n)) (1 / (2 * (n : Real)))

/-- The concrete law supplied to the warm branch: a radius-four truncated speedy phase,
started afresh from the cold ambient-Gaussian rejection law. -/
noncomputable def adaptiveTerminalTruncatedLaw
    (N s0 rho : Real) (K : Set (Space n)) (steps : Fin (m + 1) -> Nat)
    (i : Fin (m + 1)) : Measure (Space n) :=
  Ttc.CVSampler.phaseLaw
    (K ∩ closedBall (0 : Space n)
      (4 * adaptiveTerminalSigma N s0 i * Real.sqrt n))
    (adaptiveTerminalDelta (n := n) N s0 i)
    (adaptiveSigmaSq N s0 i)
    (coldBallStart (n := n) s0 rho) (steps i)

/-- The operational terminal-coordinate law with the concrete truncated walk in its warm
branch and exact ambient rejection in its cold branch. -/
noncomputable def adaptiveTerminalWarmLaw
    (N s0 rho : Real) (K : Set (Space n)) (steps : Fin (m + 1) -> Nat)
    (i : Fin (m + 1)) : Measure (Space n) :=
  adaptiveTerminalPhaseSamplerLaw (adaptiveSigmaSq N s0) K i
    (adaptiveTerminalTruncatedLaw N s0 rho K steps i)

/-- The concrete elementary family in the `Fin r → Fin (m+1) → Fin k` shape used by the
terminal packed sampler.  Coordinates are independent copies of the same phase law. -/
noncomputable def adaptiveTerminalWarmLawFamily
    (N s0 rho : Real) (K : Set (Space n)) (steps : Fin (m + 1) -> Nat) :
    Fin r -> Fin (m + 1) -> Fin k -> Measure (Space n) :=
  fun _ i _ => adaptiveTerminalWarmLaw N s0 rho K steps i

private theorem one_le_four_mul_sqrt_of_warm
    (hn : 1 ≤ n) {s : Real} (hs : 0 < s) (hwarm : ¬ 4 * (n : Real) * s ≤ 1) :
    1 ≤ 4 * Real.sqrt s * Real.sqrt n := by
  have hsn : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hnn : Real.sqrt (n : Real) ^ 2 = (n : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have ha0 : 0 ≤ 4 * Real.sqrt s * Real.sqrt n := by positivity
  have hgt : 1 < 4 * (n : Real) * s := lt_of_not_ge hwarm
  nlinarith [sq_nonneg (4 * Real.sqrt s * Real.sqrt n - 1)]

/-- In every warm coordinate, the raw lazy speedy walk has mixed by the caller-supplied
deadline. -/
theorem mixesWithin_adaptiveTerminalTruncatedLaw
    (hn : 21 ≤ n) {N s0 rho : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    {eps : Real} (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    (steps : Fin (m + 1) -> Nat)
    (hsteps : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / eps)) /
            (adaptiveTerminalDelta (n := n) N s0 i * Real.log 2) ^ 2 + 1
        ≤ (steps i : Real))
    (i : Fin (m + 1)) (hwarm : ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1) :
    Arlib.MarkovChains.MixesWithin
      (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian
        (K ∩ closedBall (0 : Space n)
          (4 * adaptiveTerminalSigma N s0 i * Real.sqrt n))
        (adaptiveTerminalDelta (n := n) N s0 i) (adaptiveSigmaSq N s0 i)))
      (Arlib.MarkovChains.ellGaussianProb
        (K ∩ closedBall (0 : Space n)
          (4 * adaptiveTerminalSigma N s0 i * Real.sqrt n))
        (adaptiveTerminalDelta (n := n) N s0 i) (adaptiveSigmaSq N s0 i))
      (coldBallStart (n := n) s0 rho) (steps i) (ENNReal.ofReal eps) := by
  have hn1 : 1 ≤ n := by omega
  have hs : 0 < adaptiveSigmaSq N s0 i := adaptiveSigmaSq_pos hN hs0 i
  have hsigma : 0 < adaptiveTerminalSigma N s0 i := by
    exact Real.sqrt_pos.2 hs
  have hsigmaSq : adaptiveSigmaSq N s0 i = adaptiveTerminalSigma N s0 i ^ 2 := by
    symm
    exact Real.sq_sqrt hs.le
  have hrad : 1 ≤ 4 * adaptiveTerminalSigma N s0 i * Real.sqrt n :=
    one_le_four_mul_sqrt_of_warm hn1 hs hwarm
  let M : Real := adaptiveRestartWarmConst n i
  have hM : 1 ≤ M := by
    dsimp [M, adaptiveRestartWarmConst]
    exact one_le_pow₀ (by norm_num)
  haveI : IsProbabilityMeasure (coldBallStart (n := n) s0 rho) :=
    isProbabilityMeasure_coldBallStart hs0 hrho
  have hw := isWarm_coldBallStart_adaptive_ellGaussianProb_truncated_four hKm hKc hn
    (fun x hx => hball (ball_subset_closedBall hx)) hN hs0 hsigma hrad hrho hrhoc hcoldStart
    hbelow i.isLt
  rw [hsigmaSq] at hw
  let K' : Set (Space n) :=
    K ∩ closedBall (0 : Space n) (4 * adaptiveTerminalSigma N s0 i * Real.sqrt n)
  have hK'm : MeasurableSet K' :=
    Arlib.MarkovChains.measurableSet_inter_closedBall hKm _
  have hK'c : Convex Real K' :=
    Arlib.MarkovChains.convex_inter_closedBall hKc _
  have hK'0 : volume K' ≠ 0 :=
    Arlib.MarkovChains.volume_inter_closedBall_ne_zero
      (fun x hx => hball (ball_subset_closedBall hx)) hrad
  have hKR : ∀ x ∈ K', ‖x‖ ≤ 4 * adaptiveTerminalSigma N s0 i * Real.sqrt n :=
    fun _ hx => Arlib.MarkovChains.norm_le_of_mem_inter_closedBall hx
  have hdelta : 0 < adaptiveTerminalDelta (n := n) N s0 i := by
    exact Arlib.MarkovChains.coldStep_pos hn1 hsigma
  have hdeltasigma : adaptiveTerminalDelta (n := n) N s0 i ≤
      adaptiveTerminalSigma N s0 i / (8 * Real.sqrt n) := min_le_left _ _
  have hmix :=
    Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit_radius_four
      hn hsigma hdelta hdeltasigma hK'm hK'c hK'0 (by positivity) hKR le_rfl hM hw
        heps0 (le_trans heps32 (by norm_num)) (hsteps i hwarm)
  rw [hsigmaSq]
  simpa only [K'] using hmix

/-- The concrete branch-selected terminal law is a probability measure.  The cold branch
is exact ambient rejection; the warm branch uses the raw mixing theorem to justify every
normalization in `CVSampler.phaseLaw`. -/
theorem isProbabilityMeasure_adaptiveTerminalWarmLaw
    (hn : 21 ≤ n) {N s0 rho : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K) (_hfin : volume K ≠ ⊤)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    {eps : Real} (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    (steps : Fin (m + 1) -> Nat)
    (hsteps : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / eps)) /
            (adaptiveTerminalDelta (n := n) N s0 i * Real.log 2) ^ 2 + 1
        ≤ (steps i : Real))
    (i : Fin (m + 1)) :
    IsProbabilityMeasure (adaptiveTerminalWarmLaw N s0 rho K steps i) := by
  rw [adaptiveTerminalWarmLaw, adaptiveTerminalPhaseSamplerLaw]
  split_ifs with hcold
  · let proposal := Ttc.CV.ambientGaussianProb (n := n) (adaptiveSigmaSq N s0 i)
    letI : IsProbabilityMeasure proposal :=
      Ttc.CV.isProbabilityMeasure_ambientGaussianProb (adaptiveSigmaSq_pos hN hs0 i)
    exact Measure.isProbabilityMeasure_map
      (Ttc.CV.measurable_firstAcceptedDraw hKm).aemeasurable
  · have hn1 : 1 ≤ n := by omega
    have hs : 0 < adaptiveSigmaSq N s0 i := adaptiveSigmaSq_pos hN hs0 i
    have hsigma : 0 < adaptiveTerminalSigma N s0 i := Real.sqrt_pos.2 hs
    have hrad : 1 ≤ 4 * adaptiveTerminalSigma N s0 i * Real.sqrt n :=
      one_le_four_mul_sqrt_of_warm hn1 hs hcold
    have hK'm := Arlib.MarkovChains.measurableSet_inter_closedBall hKm
      (4 * adaptiveTerminalSigma N s0 i * Real.sqrt n)
    have hK'c := Arlib.MarkovChains.convex_inter_closedBall hKc
      (4 * adaptiveTerminalSigma N s0 i * Real.sqrt n)
    have hK'ball := Arlib.MarkovChains.unitBall_subset_inter_closedBall
      (fun x hx => hball (ball_subset_closedBall hx)) hrad
    have hK'fin := Arlib.MarkovChains.volume_inter_closedBall_ne_top K
      (4 * adaptiveTerminalSigma N s0 i * Real.sqrt n)
    have hdelta : 0 < adaptiveTerminalDelta (n := n) N s0 i :=
      Arlib.MarkovChains.coldStep_pos hn1 hsigma
    have hdeltan : adaptiveTerminalDelta (n := n) N s0 i ≤ 1 / (2 * (n : Real)) :=
      min_le_right _ _
    haveI : IsProbabilityMeasure (coldBallStart (n := n) s0 rho) :=
      isProbabilityMeasure_coldBallStart hs0 hrho
    have hmix := mixesWithin_adaptiveTerminalTruncatedLaw hn hN hs0 hKm hKc hball hrho
      hrhoc hcoldStart hbelow heps0 heps32 steps hsteps i hcold
    rw [Arlib.MarkovChains.mixesWithin_iff] at hmix
    exact Ttc.CVSampler.isProbabilityMeasure_phaseLaw hn1 hK'm hK'c hK'ball hK'fin
      hdelta hdeltan hs (coldBallStart (n := n) s0 rho) (steps i) hmix
      (le_trans (ENNReal.ofReal_le_ofReal heps32) (by norm_num))

/-- Exact coordinatewise TV control for the concrete adaptive terminal law. -/
theorem tvLe_adaptiveTerminalWarmLaw
    (hn : 21 ≤ n) {N s0 rho : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    {eps : Real} (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    (steps : Fin (m + 1) -> Nat)
    (hsteps : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / eps)) /
            (adaptiveTerminalDelta (n := n) N s0 i * Real.log 2) ^ 2 + 1
        ≤ (steps i : Real))
    (i : Fin (m + 1)) :
    TVLe (adaptiveTerminalWarmLaw N s0 rho K steps i)
      (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i)
      (64 * ENNReal.ofReal eps +
        ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
  apply adaptiveTerminalPhaseSamplerLaw_tv
    (fun q => adaptiveSigmaSq_pos hN hs0 q) hKm hfin (by omega)
    hball i
  intro hwarm
  have hs : 0 < adaptiveSigmaSq N s0 i := adaptiveSigmaSq_pos hN hs0 i
  have hsigma : 0 < adaptiveTerminalSigma N s0 i := Real.sqrt_pos.2 hs
  have hsigmaSq : adaptiveSigmaSq N s0 i = adaptiveTerminalSigma N s0 i ^ 2 := by
    symm
    exact Real.sq_sqrt hs.le
  have hrad : 1 ≤ 4 * adaptiveTerminalSigma N s0 i * Real.sqrt n :=
    one_le_four_mul_sqrt_of_warm (by omega) hs hwarm
  exact tvLe_speedyRejection_adaptive_coldBallStart_truncated_four_all hKm hKc hn
    (fun x hx => hball (ball_subset_closedBall hx)) hfin hN hs0 hsigma hrad hrho hrhoc
    hcoldStart hbelow i.isLt hsigmaSq heps0 heps32 (hsteps i hwarm)

/-- Every coordinate of the concrete packed family is a probability measure. -/
theorem isProbabilityMeasure_adaptiveTerminalWarmLawFamily
    (hn : 21 ≤ n) {N s0 rho : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    {eps : Real} (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    (steps : Fin (m + 1) -> Nat)
    (hsteps : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / eps)) /
            (adaptiveTerminalDelta (n := n) N s0 i * Real.log 2) ^ 2 + 1
        ≤ (steps i : Real))
    (t : Fin r) (i : Fin (m + 1)) (l : Fin k) :
    IsProbabilityMeasure (adaptiveTerminalWarmLawFamily N s0 rho K steps t i l) := by
  exact isProbabilityMeasure_adaptiveTerminalWarmLaw hn hN hs0 hKm hKc hball hfin hrho
    hrhoc hcoldStart hbelow heps0 heps32 steps hsteps i

/-- Coordinatewise TV in the exact packed-family shape consumed by terminal coupling. -/
theorem tvLe_adaptiveTerminalWarmLawFamily
    (hn : 21 ≤ n) {N s0 rho : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    {eps : Real} (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    (steps : Fin (m + 1) -> Nat)
    (hsteps : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / eps)) /
            (adaptiveTerminalDelta (n := n) N s0 i * Real.log 2) ^ 2 + 1
        ≤ (steps i : Real)) :
    ∀ (t : Fin r) (i : Fin (m + 1)) (l : Fin k),
      TVLe (adaptiveTerminalWarmLawFamily N s0 rho K steps t i l)
        (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i)
        (64 * ENNReal.ofReal eps +
          ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
  intro t i l
  exact tvLe_adaptiveTerminalWarmLaw hn hN hs0 hKm hKc hball hfin hrho hrhoc hcoldStart
    hbelow heps0 heps32 steps hsteps i

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.mixesWithin_adaptiveTerminalTruncatedLaw
#print axioms Ttc.CVAdaptive.isProbabilityMeasure_adaptiveTerminalWarmLaw
#print axioms Ttc.CVAdaptive.tvLe_adaptiveTerminalWarmLaw
#print axioms Ttc.CVAdaptive.isProbabilityMeasure_adaptiveTerminalWarmLawFamily
#print axioms Ttc.CVAdaptive.tvLe_adaptiveTerminalWarmLawFamily

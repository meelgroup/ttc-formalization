import Ttc.Exec.CostedAdaptiveTerminalWarmQ
import Ttc.Exec.CostedPackedJointLaw

/-! Costed cold/warm assembly for the adjustable adaptive terminal sampler. -/

namespace Ttc.CostedAdaptiveTerminalPhaseAssembly

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.Probability Arlib.GaussianCooling Arlib.MarkovChains
open Arlib.GaussianCooling.Chunked
open Ttc.CVAdaptive Ttc.CostedAmbientGaussianRejection
open Ttc.CostedWarmPhaseRejection Ttc.CostedAdaptiveTerminalWarmQ
open scoped ENNReal Classical

variable {n r m k : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def terminalBody (q N s0 : Real) (K : Set (State n)) (i : Nat) :
    Set (State n) :=
  K ∩ closedBall 0 (q * adaptiveTerminalSigma N s0 i * Real.sqrt n)

theorem terminalDelta_pos (hn : 1 ≤ n) {q N s0 : Real} (hN : 0 < N)
    (hs0 : 0 < s0) (i : Nat) :
    0 < adaptiveTerminalDeltaQ (n := n) q N s0 i := by
  have hs := adaptiveSigmaSq_pos hN hs0 i
  have hsigma : 0 < adaptiveTerminalSigma N s0 i := Real.sqrt_pos.2 hs
  unfold adaptiveTerminalDeltaQ
  positivity

/-- The traced warm coordinate used in the warm branch of `adaptiveTerminalWarmLawQ`. -/
noncomputable def terminalWarmCostLaw
    (hn : 1 ≤ n) (q N s0 rho eps : Real) (K : Set (State n))
    (hK : MeasurableSet K) (hN : 0 < N) (hs0 : 0 < s0)
    (i : Fin (m + 1)) : Measure (ENNReal × State n) :=
  warmPhaseCostLaw (terminalBody q N s0 K i)
    (Arlib.MarkovChains.measurableSet_inter_closedBall hK _)
    (adaptiveTerminalDeltaQ (n := n) q N s0 i)
    (adaptiveSigmaSq N s0 i) (terminalDelta_pos hn hN hs0 i)
    (coldBallStart (n := n) s0 rho)
    (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i)

/-- Cold ambient rejection where valid, and the recorded-query truncated walk otherwise. -/
noncomputable def terminalCoordinateCostLaw
    (hn : 1 ≤ n) (q N s0 rho eps : Real) (K : Set (State n))
    (hK : MeasurableSet K) (hN : 0 < N) (hs0 : 0 < s0)
    (j : Fin r) (i : Fin (m + 1)) (l : Fin k) : Measure (ENNReal × State n) :=
  if 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 then
    coldPhaseCostLaw K (adaptiveSigmaSq N s0 i)
  else terminalWarmCostLaw hn q N s0 rho eps K hK hN hs0 i

theorem isProbabilityMeasure_terminalCoordinateCostLaw
    (hn : 1 ≤ n) {q N s0 rho eps : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hrho : 0 < rho) {K : Set (State n)} (hK : MeasurableSet K)
    (j : Fin r) (i : Fin (m + 1)) (l : Fin k) :
    IsProbabilityMeasure
      (terminalCoordinateCostLaw hn q N s0 rho eps K hK hN hs0 j i l) := by
  letI : IsProbabilityMeasure (coldBallStart (n := n) s0 rho) :=
    isProbabilityMeasure_coldBallStart hs0 hrho
  unfold terminalCoordinateCostLaw
  split_ifs
  · exact isProbabilityMeasure_coldPhaseCostLaw K (adaptiveSigmaSq_pos hN hs0 i) hK
  · unfold terminalWarmCostLaw
    infer_instance

theorem map_snd_terminalWarmCostLaw
    (hn : 1 ≤ n) {q N s0 rho eps : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hrho : 0 < rho) {K : Set (State n)} (hK : MeasurableSet K)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (i : Fin (m + 1))
    (hquarterShrink : ENNReal.ofReal (1 / 4 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian (terminalBody q N s0 K i)
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)))
        (coldBallStart (n := n) s0 rho)
        (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i))
        ((1 - 1 / (2 * (n : Real))) • terminalBody q N s0 K i))
    (hquarterAccept : ENNReal.ofReal (1 / 4 : Real) ≤
      ((Ttc.SpeedyRejection.phasePointProposal (terminalBody q N s0 K i)
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)
        (coldBallStart (n := n) s0 rho)
        (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i)).withDensity
          (fun x => ENNReal.ofReal (speedyAcceptReal
            (1 - 1 / (2 * (n : Real))) (adaptiveSigmaSq N s0 i) x))) univ) :
    Measure.map Prod.snd
        (terminalWarmCostLaw hn q N s0 rho eps K hK hN hs0 i) =
      adaptiveTerminalTruncatedLawQ q N s0 rho eps K i := by
  letI : IsProbabilityMeasure (coldBallStart (n := n) s0 rho) :=
    isProbabilityMeasure_coldBallStart hs0 hrho
  apply map_snd_warmPhaseCostLaw_eq_phaseLaw
  · exact lt_of_lt_of_le (by norm_num) hquarterShrink
  · exact adaptiveSigmaSq_pos hN hs0 i
  · exact hc2
  · exact (lt_of_lt_of_le (by norm_num) hquarterAccept).ne'

theorem map_snd_terminalCoordinateCostLaw
    (hn : 1 ≤ n) {q N s0 rho eps : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hrho : 0 < rho) {K : Set (State n)} (hK : MeasurableSet K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (hquarterShrink : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 → ENNReal.ofReal (1 / 4 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian (terminalBody q N s0 K i)
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)))
        (coldBallStart (n := n) s0 rho)
        (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i))
        ((1 - 1 / (2 * (n : Real))) • terminalBody q N s0 K i))
    (hquarterAccept : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 → ENNReal.ofReal (1 / 4 : Real) ≤
      ((Ttc.SpeedyRejection.phasePointProposal (terminalBody q N s0 K i)
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)
        (coldBallStart (n := n) s0 rho)
        (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i)).withDensity
          (fun x => ENNReal.ofReal (speedyAcceptReal
            (1 - 1 / (2 * (n : Real))) (adaptiveSigmaSq N s0 i) x))) univ)
    (j : Fin r) (i : Fin (m + 1)) (l : Fin k) :
    Measure.map Prod.snd
        (terminalCoordinateCostLaw hn q N s0 rho eps K hK hN hs0 j i l) =
      adaptiveTerminalWarmLawQ q N s0 rho eps K i := by
  unfold terminalCoordinateCostLaw adaptiveTerminalWarmLawQ
  rw [adaptiveTerminalPhaseSamplerLaw]
  split_ifs with hi
  · letI : IsProbabilityMeasure
        (Ttc.CV.ambientGaussianProb (n := n) (adaptiveSigmaSq N s0 i)) :=
      Ttc.CV.isProbabilityMeasure_ambientGaussianProb (adaptiveSigmaSq_pos hN hs0 i)
    have hacc := Ttc.CV.ambientGaussianProb_acceptance_ge_half hK hn
      (adaptiveSigmaSq_pos hN hs0 i) hi hball
    have hpos : 0 < Ttc.CV.ambientGaussianProb (n := n)
        (adaptiveSigmaSq N s0 i) K := lt_of_lt_of_le (by norm_num) hacc
    rw [map_snd_coldPhaseCostLaw hK (adaptiveSigmaSq_pos hN hs0 i) hpos]
    exact (Ttc.CV.map_firstAcceptedDraw_eq_condOn _ hK hpos).symm
  · exact map_snd_terminalWarmCostLaw hn hN hs0 hrho hK hc2 i
      (hquarterShrink i hi) (hquarterAccept i hi)

theorem one_le_terminalRadius_of_warm
    (hn : 1 ≤ n) {q N s0 : Real} (hq : 2 ≤ q) (hN : 0 < N) (hs0 : 0 < s0)
    (i : Nat) (hwarm : ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1) :
    1 ≤ q * adaptiveTerminalSigma N s0 i * Real.sqrt n := by
  have hs := adaptiveSigmaSq_pos hN hs0 i
  have hsn : adaptiveTerminalSigma N s0 i ^ 2 = adaptiveSigmaSq N s0 i :=
    Real.sq_sqrt hs.le
  have hnn : Real.sqrt (n : Real) ^ 2 = (n : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hbase0 : 0 ≤ 2 * adaptiveTerminalSigma N s0 i * Real.sqrt n := by
    unfold adaptiveTerminalSigma
    positivity
  have hgt : 1 < 4 * (n : Real) * adaptiveSigmaSq N s0 i := lt_of_not_ge hwarm
  have htwo : 1 < 2 * adaptiveTerminalSigma N s0 i * Real.sqrt n := by
    nlinarith [sq_nonneg (2 * adaptiveTerminalSigma N s0 i * Real.sqrt n - 1)]
  have hsqrtn : 0 ≤ adaptiveTerminalSigma N s0 i * Real.sqrt n := by
    unfold adaptiveTerminalSigma
    positivity
  nlinarith [mul_le_mul_of_nonneg_right hq hsqrtn]

/-- The warm branch's two rejection probabilities are consequences of the very mixing
certificate already used to define `adaptiveTerminalWarmLawQ`; they are not additional
algorithmic hypotheses. -/
theorem terminalWarm_restart_quarters
    (hn : 21 ≤ n) {q N s0 rho eps : Real} (hq : 2 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 →
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    (i : Fin (m + 1)) (hi : ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1) :
    ENNReal.ofReal (1 / 4 : Real) ≤
        (iterate (lazy (speedyMetropolisGaussian (terminalBody q N s0 K i)
          (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)))
          (coldBallStart (n := n) s0 rho)
          (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i))
          ((1 - 1 / (2 * (n : Real))) • terminalBody q N s0 K i) ∧
      ENNReal.ofReal (1 / 4 : Real) ≤
        ((Ttc.SpeedyRejection.phasePointProposal (terminalBody q N s0 K i)
          (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)
          (coldBallStart (n := n) s0 rho)
          (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i)).withDensity
            (fun x => ENNReal.ofReal (speedyAcceptReal
              (1 - 1 / (2 * (n : Real))) (adaptiveSigmaSq N s0 i) x))) univ := by
  letI : IsProbabilityMeasure (coldBallStart (n := n) s0 rho) :=
    isProbabilityMeasure_coldBallStart hs0 hrho
  let K' := terminalBody q N s0 K i
  let δ := adaptiveTerminalDeltaQ (n := n) q N s0 i
  let s := adaptiveSigmaSq N s0 i
  let t := adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i
  have hn1 : 1 ≤ n := by omega
  have hs : 0 < s := adaptiveSigmaSq_pos hN hs0 i
  have hδ : 0 < δ := terminalDelta_pos hn1 hN hs0 i
  have hδn : δ ≤ 1 / (2 * (n : Real)) := by
    unfold δ adaptiveTerminalDeltaQ
    exact min_le_right _ _
  have hrad := one_le_terminalRadius_of_warm hn1 hq hN hs0 i hi
  have hK'm : MeasurableSet K' :=
    Arlib.MarkovChains.measurableSet_inter_closedBall hK _
  have hK'c : Convex Real K' := Arlib.MarkovChains.convex_inter_closedBall hKc _
  have hK'ball : ball (0 : State n) 1 ⊆ K' :=
    Arlib.MarkovChains.unitBall_subset_inter_closedBall
      (Metric.ball_subset_closedBall.trans hball) hrad
  have hK'fin : volume K' ≠ ⊤ := Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  have hmix := mixesWithin_adaptiveTerminalTruncatedLawQ hn hq hN hs0 hK hKc hball
    hrho hrhoc hcoldStart hbelow heps0 heps32 i hi
  have htv : TVLe
      (iterate (lazy (speedyMetropolisGaussian K' δ s))
        (coldBallStart (n := n) s0 rho) t)
      (ellGaussianProb K' δ s) (ENNReal.ofReal eps) := by
    change TVLe _ _ _ at hmix
    simpa only [K', δ, s, t, terminalBody] using hmix
  have htvCond : TVLe
      (iterate (lazy (speedyMetropolisGaussian K' δ s))
        (coldBallStart (n := n) s0 rho) t)
      (condOn (ellGaussianMeasure K' δ s) univ) (ENNReal.ofReal eps) := by
    simpa only [ellGaussianProb_eq_condOn] using htv
  have herrQuarter : ENNReal.ofReal eps ≤ ENNReal.ofReal (1 / 4 : Real) :=
    ENNReal.ofReal_le_ofReal (heps32.trans (by norm_num))
  have hshrink := Arlib.MarkovChains.quarter_le_shrunken_mass hn1 hK'm hK'c hK'ball
    hK'fin hδ hδn hs htvCond herrQuarter
  have haccept := quarter_le_phasePointProposal_acceptance_of_tvLe hn1 hK'm hK'c
    hK'ball hK'fin hδ hδn hs htv (ENNReal.ofReal_le_ofReal heps32)
  constructor
  · simpa only [K', δ, s, t] using hshrink
  · simpa only [K', δ, s, t, Ttc.SpeedyRejection.phasePointProposal,
      iterate_zero] using haccept

/-- The fixed cold-ball restart has the polynomial (logarithmic) warmness constant used in
the adjustable mixing deadline. -/
theorem isWarm_terminalWarmStart
    (hn : 21 ≤ n) {q N s0 rho : Real} (hq : 2 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 →
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    (i : Fin (m + 1)) (hi : ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1) :
    IsWarm (ENNReal.ofReal (adaptiveRestartWarmConst n i))
      (coldBallStart (n := n) s0 rho)
      (ellGaussianProb (terminalBody q N s0 K i)
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)) := by
  have hn1 : 1 ≤ n := by omega
  let K' := terminalBody q N s0 K i
  let c : Real := 1 - 1 / (2 * (n : Real))
  let δ := adaptiveTerminalDeltaQ (n := n) q N s0 i
  have hrad := one_le_terminalRadius_of_warm hn1 hq hN hs0 i hi
  have hK'm : MeasurableSet K' :=
    Arlib.MarkovChains.measurableSet_inter_closedBall hK _
  have hK'c : Convex Real K' := Arlib.MarkovChains.convex_inter_closedBall hKc _
  have hK'ball : ball (0 : State n) 1 ⊆ K' :=
    Arlib.MarkovChains.unitBall_subset_inter_closedBall
      (Metric.ball_subset_closedBall.trans hball) hrad
  have hK'fin : volume K' ≠ ⊤ := Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn1
    have : 1 / (2 * (n : Real)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hδ : 0 < δ := terminalDelta_pos hn1 hN hs0 i
  have hδc : δ ≤ 1 - c := by
    dsimp [δ, c]
    rw [sub_sub_cancel]
    exact min_le_right _ _
  exact isWarm_coldBallStart_adaptive_ellGaussianProb hK'm hK'c hn1 hK'ball hK'fin
    hN hs0 hc0 hc1 hrho hrhoc hcoldStart hδ hδc hbelow i.isLt

/-- Per-coordinate actual membership-query bound.  The common factor six makes the cold
bound `12`; the adjustable traced warm branch is `160 * steps * M`. -/
theorem six_mul_lintegral_terminalCoordinateCostLaw_le
    (hn : 2 ≤ n) {q N s0 rho eps : Real} (hq : 2 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0) (hrho : 0 < rho)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    (M : Fin (m + 1) → ENNReal)
    (hwarm : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 →
      IsWarm (M i) (coldBallStart (n := n) s0 rho)
        (ellGaussianProb (terminalBody q N s0 K i)
          (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)))
    (hquarterShrink : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 →
      ENNReal.ofReal (1 / 4 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian (terminalBody q N s0 K i)
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)))
        (coldBallStart (n := n) s0 rho)
        (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i))
        ((1 - 1 / (2 * (n : Real))) • terminalBody q N s0 K i))
    (hquarterAccept : ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 →
      ENNReal.ofReal (1 / 4 : Real) ≤
      ((Ttc.SpeedyRejection.phasePointProposal (terminalBody q N s0 K i)
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) (adaptiveSigmaSq N s0 i)
        (coldBallStart (n := n) s0 rho)
        (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i)).withDensity
          (fun x => ENNReal.ofReal (speedyAcceptReal
            (1 - 1 / (2 * (n : Real))) (adaptiveSigmaSq N s0 i) x))) univ)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (j : Fin r) (i : Fin (m + 1)) (l : Fin k) :
    6 * (∫⁻ z, z.1 ∂(terminalCoordinateCostLaw
      (by omega : 1 ≤ n) q N s0 rho eps K hK hN hs0 j i l)) ≤
      if 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 then 12
      else 160 * ((adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i : ENNReal) * M i) := by
  letI : IsProbabilityMeasure (coldBallStart (n := n) s0 rho) :=
    isProbabilityMeasure_coldBallStart hs0 hrho
  unfold terminalCoordinateCostLaw
  split_ifs with hi
  · have hc := lintegral_fst_coldPhaseCostLaw_le_two hK (by omega)
      (adaptiveSigmaSq_pos hN hs0 i) hi hball
    exact (mul_le_mul_left' hc 6).trans_eq (by norm_num)
  · have hs := adaptiveSigmaSq_pos hN hs0 i
    have hsigma : 0 < adaptiveTerminalSigma N s0 i := Real.sqrt_pos.2 hs
    have hsq : adaptiveTerminalSigma N s0 i ^ 2 = adaptiveSigmaSq N s0 i :=
      Real.sq_sqrt hs.le
    have hrad := one_le_terminalRadius_of_warm (by omega : 1 ≤ n) hq hN hs0 i hi
    have hcost := six_mul_lintegral_warmPhaseCostLaw_le_oneSixty_mul_adjustable
      hn (Arlib.MarkovChains.measurableSet_inter_closedBall hK _)
      (Arlib.MarkovChains.convex_inter_closedBall hKc _)
      (Arlib.MarkovChains.unitBall_subset_inter_closedBall
        (Metric.ball_subset_closedBall.trans hball) hrad)
      (lt_of_lt_of_le one_lt_two hq)
      (terminalDelta_pos (by omega : 1 ≤ n) hN hs0 i) hsigma
      (min_le_right _ _) (min_le_left _ _) (by positivity) le_rfl
      (fun _ hx => Arlib.MarkovChains.norm_le_of_mem_inter_closedBall hx)
      (by simpa only [terminalBody, hsq] using hwarm i hi)
      (adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i)
      (by simpa only [terminalBody, hsq] using hquarterShrink i hi)
      (by simpa only [terminalBody, hsq] using hquarterAccept i hi) hc2
    simpa [terminalWarmCostLaw, terminalBody, hsq] using hcost

noncomputable def terminalPhaseQueryBound (q N s0 eps : Real)
    (M : Fin (m + 1) → ENNReal) (i : Fin (m + 1)) : ENNReal :=
  if 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 then 12
  else 160 * ((adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i : ENNReal) * M i)

/-- Fully discharged per-coordinate expected-query theorem for the adjustable terminal
sampler.  The only inputs are the same geometry and numerical guards as its semantic law;
warmness and both restart probabilities are derived internally. -/
theorem six_mul_lintegral_terminalCoordinateCostLaw_le_concrete
    (hn : 21 ≤ n) {q N s0 rho eps : Real} (hq : 2 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 →
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    (j : Fin r) (i : Fin (m + 1)) (l : Fin k) :
    6 * (∫⁻ z, z.1 ∂(terminalCoordinateCostLaw
      (by omega : 1 ≤ n) q N s0 rho eps K hK hN hs0 j i l)) ≤
      terminalPhaseQueryBound (n := n) (m := m) q N s0 eps
        (fun i => ENNReal.ofReal (adaptiveRestartWarmConst n i)) i := by
  have hquarters := fun (i : Fin (m + 1))
      (hi : ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1) =>
    terminalWarm_restart_quarters hn hq hN hs0 hK hKc hball hrho hrhoc
      hcoldStart hbelow heps0 heps32 i hi
  have hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1 := by
    have hnR : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hinv : 0 ≤ 1 / (2 * (n : Real)) := by positivity
    have hinv1 : 1 / (2 * (n : Real)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith
  unfold terminalPhaseQueryBound
  exact six_mul_lintegral_terminalCoordinateCostLaw_le (by omega) hq hN hs0 hrho
    hK hKc hball (fun i => ENNReal.ofReal (adaptiveRestartWarmConst n i))
    (fun i hi => isWarm_terminalWarmStart hn hq hN hs0 hK hKc hball hrho hrhoc
      hcoldStart hbelow i hi)
    (fun i hi => (hquarters i hi).1) (fun i hi => (hquarters i hi).2) hc2 j i l

/-- Fully discharged state marginal for the costed coordinate law. -/
theorem map_snd_terminalCoordinateCostLaw_concrete
    (hn : 21 ≤ n) {q N s0 rho eps : Real} (hq : 2 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 →
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    (j : Fin r) (i : Fin (m + 1)) (l : Fin k) :
    Measure.map Prod.snd
        (terminalCoordinateCostLaw (by omega : 1 ≤ n)
          q N s0 rho eps K hK hN hs0 j i l) =
      adaptiveTerminalWarmLawFamilyQ q N s0 rho eps K j i l := by
  have hquarters := fun (i : Fin (m + 1))
      (hi : ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1) =>
    terminalWarm_restart_quarters hn hq hN hs0 hK hKc hball hrho hrhoc
      hcoldStart hbelow heps0 heps32 i hi
  have hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1 := by
    have hnR : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hinv : 0 ≤ 1 / (2 * (n : Real)) := by positivity
    have hinv1 : 1 / (2 * (n : Real)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith
  exact map_snd_terminalCoordinateCostLaw (by omega) hN hs0 hrho hK hball hc2
    (fun i hi => (hquarters i hi).1) (fun i hi => (hquarters i hi).2) j i l

/-- The packed costed execution projects jointly, not just coordinatewise, to the exact
independently restarted adaptive terminal family. -/
theorem map_packed_terminal_state
    (hn : 1 ≤ n) {q N s0 rho eps : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hrho : 0 < rho) {K : Set (State n)} (hK : MeasurableSet K)
    (hstate : ∀ (j : Fin r) (i : Fin (m + 1)) (l : Fin k),
      Measure.map Prod.snd
        (terminalCoordinateCostLaw hn q N s0 rho eps K hK hN hs0 j i l) =
      adaptiveTerminalWarmLawFamilyQ q N s0 rho eps K j i l) :
    Measure.map Ttc.CostedPackedJointLaw.stateProjection
        (Ttc.CostedPackedWarmSchedule.costedPackedLaw
          (terminalCoordinateCostLaw hn q N s0 rho eps K hK hN hs0 :
            Fin r → Fin (m + 1) → Fin k → Measure (ENNReal × State n))) =
      runMeasure (packedPhaseLaw
        (adaptiveTerminalWarmLawFamilyQ q N s0 rho eps K :
          Fin r → Fin (m + 1) → Fin k → Measure (State n))) := by
  letI : ∀ j i l, IsProbabilityMeasure
      (terminalCoordinateCostLaw hn q N s0 rho eps K hK hN hs0 j i l) :=
    fun (j : Fin r) (i : Fin (m + 1)) (l : Fin k) =>
      isProbabilityMeasure_terminalCoordinateCostLaw (r := r) (m := m) (k := k)
        hn hN hs0 hrho hK j i l
  exact Ttc.CostedPackedJointLaw.map_costedPackedLaw_stateProjection_eq _ _ hstate

/-- Summing any established per-phase terminal bound over all independently restarted
coordinates gives the expected actual membership-query bound for the packed execution. -/
theorem six_mul_lintegral_packedTerminal_le
    (hn : 1 ≤ n) {q N s0 rho eps : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hrho : 0 < rho) {K : Set (State n)} (hK : MeasurableSet K)
    (B : Fin (m + 1) → ENNReal)
    (hB : ∀ (j : Fin r) (i : Fin (m + 1)) (l : Fin k),
      6 * (∫⁻ z, z.1 ∂(terminalCoordinateCostLaw
        hn q N s0 rho eps K hK hN hs0 j i l)) ≤ B i) :
    6 * (∫⁻ omega, Ttc.CostedPackedWarmSchedule.totalMembershipQueries omega
      ∂(Ttc.CostedPackedWarmSchedule.costedPackedLaw
        (terminalCoordinateCostLaw hn q N s0 rho eps K hK hN hs0 :
          Fin r → Fin (m + 1) → Fin k → Measure (ENNReal × State n)))) ≤
      (r : ENNReal) * (k : ENNReal) * ∑ i : Fin (m + 1), B i := by
  letI : ∀ j i l, IsProbabilityMeasure
      (terminalCoordinateCostLaw hn q N s0 rho eps K hK hN hs0 j i l) :=
    fun (j : Fin r) (i : Fin (m + 1)) (l : Fin k) =>
      isProbabilityMeasure_terminalCoordinateCostLaw (r := r) (m := m) (k := k)
        hn hN hs0 hrho hK j i l
  exact Ttc.CostedPackedWarmSchedule.six_mul_lintegral_totalMembershipQueries_le_phaseBounds
    _ B hB

/-- Cost and semantic law of the complete independently restarted adjustable terminal
execution.  No warmness or rejection-mass premise remains. -/
theorem packedTerminal_cost_and_state_concrete
    (hn : 21 ≤ n) {q N s0 rho eps : Real} (hq : 2 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m + 1 →
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32) :
    let rhoCost := terminalCoordinateCostLaw (r := r) (m := m) (k := k)
      (by omega : 1 ≤ n) q N s0 rho eps K hK hN hs0
    Measure.map Ttc.CostedPackedJointLaw.stateProjection
        (Ttc.CostedPackedWarmSchedule.costedPackedLaw rhoCost) =
      runMeasure (packedPhaseLaw
        (adaptiveTerminalWarmLawFamilyQ q N s0 rho eps K :
          Fin r → Fin (m + 1) → Fin k → Measure (State n))) ∧
    6 * (∫⁻ omega, Ttc.CostedPackedWarmSchedule.totalMembershipQueries omega
        ∂(Ttc.CostedPackedWarmSchedule.costedPackedLaw rhoCost)) ≤
      (r : ENNReal) * (k : ENNReal) *
        ∑ i : Fin (m + 1), terminalPhaseQueryBound (n := n) q N s0 eps
          (fun i => ENNReal.ofReal (adaptiveRestartWarmConst n i)) i := by
  dsimp only
  let rhoCost := terminalCoordinateCostLaw (r := r) (m := m) (k := k)
    (by omega : 1 ≤ n) q N s0 rho eps K hK hN hs0
  have hstate : ∀ (j : Fin r) (i : Fin (m + 1)) (l : Fin k),
      Measure.map Prod.snd (rhoCost j i l) =
        adaptiveTerminalWarmLawFamilyQ q N s0 rho eps K j i l := by
    intro j i l
    exact map_snd_terminalCoordinateCostLaw_concrete hn hq hN hs0 hK hKc hball
      hrho hrhoc hcoldStart hbelow heps0 heps32 j i l
  constructor
  · exact map_packed_terminal_state (by omega) hN hs0 hrho hK hstate
  · apply six_mul_lintegral_packedTerminal_le (by omega) hN hs0 hrho hK
      (fun i => terminalPhaseQueryBound (n := n) q N s0 eps
        (fun i => ENNReal.ofReal (adaptiveRestartWarmConst n i)) i)
    intro j i l
    exact six_mul_lintegral_terminalCoordinateCostLaw_le_concrete hn hq hN hs0
      hK hKc hball hrho hrhoc hcoldStart hbelow heps0 heps32 j i l

#print axioms map_snd_terminalCoordinateCostLaw
#print axioms six_mul_lintegral_terminalCoordinateCostLaw_le
#print axioms map_packed_terminal_state
#print axioms six_mul_lintegral_packedTerminal_le
#print axioms terminalWarm_restart_quarters
#print axioms isWarm_terminalWarmStart
#print axioms six_mul_lintegral_terminalCoordinateCostLaw_le_concrete
#print axioms map_snd_terminalCoordinateCostLaw_concrete
#print axioms packedTerminal_cost_and_state_concrete

end Ttc.CostedAdaptiveTerminalPhaseAssembly

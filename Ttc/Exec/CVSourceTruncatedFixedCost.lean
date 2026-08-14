import Ttc.Exec.CVCorrectedHybridRuntimeAssembly
import Arlib.Convexity.GaussianCooling.AdaptiveRestartTruncatedFourAll

/-! Source-faithful cost law for the fixed-rate block. -/

namespace Ttc.CVSourceTruncatedFixedCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.CVCorrectedFixedBlockCost Ttc.CostedWarmPhaseRejection
open Ttc.CostedAmbientGaussianRejection
open scoped ENNReal Classical Pointwise

variable {n r k : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def fixedRadiusFourBody (K : Set (State n)) (s : Real) : Set (State n) :=
  K ∩ closedBall 0 (4 * Real.sqrt s * Real.sqrt n)

noncomputable def fixedRadiusFourDelta (n : Nat) (s : Real) : Real :=
  min (Real.sqrt s / (8 * Real.sqrt n)) (1 / (2 * (n : Real)))

/-- Full-body ambient rejection only in its valid regime; otherwise the source's
radius-four truncated traced warm walk. -/
noncomputable def sourceFixedCoordinateCostLaw
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K) {s0 : Real} (hs0 : 0 < s0)
    (mu0 : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Measure (State n))
    (steps : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Nat)
    (j : Fin r) (i : Fin (Ttc.CVHybridSchedule.coldPhases n s0)) (l : Fin k) :
    Measure (ENNReal × State n) :=
  if ambientEligible n (fixedSigmaSq n s0 i) then
    coldPhaseCostLaw K (fixedSigmaSq n s0 i)
  else
    warmPhaseCostLaw (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
      (Arlib.MarkovChains.measurableSet_inter_closedBall hK _)
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)
      (Arlib.MarkovChains.coldStep_pos hn
        (Real.sqrt_pos.2 (geomSchedule_pos hs0 (by positivity) i)))
      (mu0 i) (steps i)

theorem isProbabilityMeasure_sourceFixedCoordinateCostLaw
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K) {s0 : Real} (hs0 : 0 < s0)
    (mu0 : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Nat)
    (j : Fin r) (i : Fin (Ttc.CVHybridSchedule.coldPhases n s0)) (l : Fin k) :
    IsProbabilityMeasure (sourceFixedCoordinateCostLaw hn K hK hs0 mu0 steps j i l) := by
  unfold sourceFixedCoordinateCostLaw
  split_ifs
  · exact isProbabilityMeasure_coldPhaseCostLaw K
      (geomSchedule_pos hs0 (by positivity) i) hK
  · infer_instance

/-! ## Small source geometry facts -/

theorem measurableSet_fixedRadiusFourBody {K : Set (State n)} (hK : MeasurableSet K)
    (s : Real) : MeasurableSet (fixedRadiusFourBody K s) :=
  Arlib.MarkovChains.measurableSet_inter_closedBall hK _

theorem convex_fixedRadiusFourBody {K : Set (State n)} (hK : Convex Real K) (s : Real) :
    Convex Real (fixedRadiusFourBody K s) :=
  Arlib.MarkovChains.convex_inter_closedBall hK _

theorem norm_le_fixedRadiusFour {K : Set (State n)} {s : Real} {x : State n}
    (hx : x ∈ fixedRadiusFourBody K s) :
    ‖x‖ ≤ 4 * Real.sqrt s * Real.sqrt n :=
  Arlib.MarkovChains.norm_le_of_mem_inter_closedBall hx

theorem fixedRadiusFourDelta_pos (hn : 1 ≤ n) {s : Real} (hs : 0 < s) :
    0 < fixedRadiusFourDelta n s := by
  exact Arlib.MarkovChains.coldStep_pos hn (Real.sqrt_pos.2 hs)

theorem fixedRadiusFourDelta_le_n {s : Real} :
    fixedRadiusFourDelta n s ≤ 1 / (2 * (n : Real)) := min_le_right _ _

theorem fixedRadiusFourDelta_le_radius {s : Real} :
    fixedRadiusFourDelta n s ≤ Real.sqrt s / (max 8 (2 * 4) * Real.sqrt n) := by
  have hmax : max (8 : Real) (2 * 4) = 8 := by norm_num
  rw [hmax]
  exact min_le_left _ _

/-! ## State marginal and radius-four transport -/

/-- The state marginal is exact on the ambient branch and is the source's two-stage
radius-four phase law on the walk branch. -/
theorem map_snd_sourceFixedCoordinateCostLaw
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    {s0 : Real} (hs0 : 0 < s0)
    (mu0 : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Nat)
    (hambientPos : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      ambientEligible n (fixedSigmaSq n s0 i) →
      0 < Ttc.CV.ambientGaussianProb (n := n) (fixedSigmaSq n s0 i) K)
    (hshrink : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      ¬ ambientEligible n (fixedSigmaSq n s0 i) → 0 <
      (iterate (lazy (speedyMetropolisGaussian
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) •
          fixedRadiusFourBody K (fixedSigmaSq n s0 i)))
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (hmass : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      ¬ ambientEligible n (fixedSigmaSq n s0 i) →
      ((Ttc.SpeedyRejection.phasePointProposal
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)
        (mu0 i) (steps i)).withDensity (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (fixedSigmaSq n s0 i) x))) univ ≠ 0)
    (j : Fin r) (i : Fin (Ttc.CVHybridSchedule.coldPhases n s0)) (l : Fin k) :
    Measure.map Prod.snd (sourceFixedCoordinateCostLaw hn K hK hs0 mu0 steps j i l) =
      if ambientEligible n (fixedSigmaSq n s0 i) then
        condOn (Ttc.CV.ambientGaussianProb (n := n) (fixedSigmaSq n s0 i)) K
      else Ttc.CVSampler.phaseLaw
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)
        (mu0 i) (steps i) := by
  unfold sourceFixedCoordinateCostLaw
  split_ifs with hi
  · exact map_snd_coldPhaseCostLaw hK (geomSchedule_pos hs0 (by positivity) i)
      (hambientPos i hi)
  · exact map_snd_warmPhaseCostLaw_eq_phaseLaw
      (measurableSet_fixedRadiusFourBody hK _) _
      (fixedRadiusFourDelta_pos hn (geomSchedule_pos hs0 (by positivity) i)) _ _
      (hshrink i hi) (geomSchedule_pos hs0 (by positivity) i) hc2 (hmass i hi)

/-- Source-faithful state law: exact in the ambient regime; in every other fixed phase the
radius-four traced law is within the standard mixing-plus-relative-tail error of the full
cooling law. -/
theorem tvLe_map_snd_sourceFixedCoordinateCostLaw
    (hn : 21 ≤ n) {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {s0 : Real} (hs0 : 0 < s0)
    (mu0 : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (M eps : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Real)
    (steps : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Nat)
    (hambientPos : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      ambientEligible n (fixedSigmaSq n s0 i) →
      0 < Ttc.CV.ambientGaussianProb (n := n) (fixedSigmaSq n s0 i) K)
    (hshrink : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      ¬ ambientEligible n (fixedSigmaSq n s0 i) → 0 <
      (iterate (lazy (speedyMetropolisGaussian
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) •
          fixedRadiusFourBody K (fixedSigmaSq n s0 i)))
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (hmass : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      ¬ ambientEligible n (fixedSigmaSq n s0 i) →
      ((Ttc.SpeedyRejection.phasePointProposal
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)
        (mu0 i) (steps i)).withDensity (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (fixedSigmaSq n s0 i) x))) univ ≠ 0)
    (hrad : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hM : ∀ i, 1 ≤ M i)
    (hwarm : ∀ i, IsWarm (ENNReal.ofReal (M i)) (mu0 i)
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)))
    (heps0 : ∀ i, 0 < eps i) (heps32 : ∀ i, eps i ≤ 1 / 32)
    (hsteps : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      4 * 640 ^ 2 * Real.sqrt (fixedSigmaSq n s0 i) ^ 2 * (n : Real) *
      (Real.log (M i) + 2 * Real.log (1 / eps i)) /
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i) * Real.log 2) ^ 2 + 1 ≤
          (steps i : Real))
    (j : Fin r) (i : Fin (Ttc.CVHybridSchedule.coldPhases n s0)) (l : Fin k) :
    TVLe (Measure.map Prod.snd
      (sourceFixedCoordinateCostLaw (by omega : 1 ≤ n) K hK hs0 mu0 steps j i l))
      (coolLaw (Ttc.CVHybridSchedule.coldPhases n s0)
        (fixedSigmaSq n s0) K i)
      (64 * ENNReal.ofReal (eps i) +
        ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
  rw [map_snd_sourceFixedCoordinateCostLaw (by omega : 1 ≤ n) hK hs0 mu0 steps hambientPos
    hshrink hc2 hmass]
  split_ifs with hi
  · have hsigma : ∀ q, 0 < fixedSigmaSq n s0 q := by
      intro q
      unfold fixedSigmaSq
      exact geomSchedule_pos hs0 (by positivity) q
    rw [Ttc.CV.condOn_ambientGaussianProb_eq_coolLaw
      (m := Ttc.CVHybridSchedule.coldPhases n s0) hsigma hK hball hfin i.isLt]
    exact (TVLe.refl _).mono (by positivity)
  · have hsigma : ∀ q, 0 < fixedSigmaSq n s0 q := by
      intro q
      unfold fixedSigmaSq
      exact geomSchedule_pos hs0 (by positivity) q
    have hs : 0 < fixedSigmaSq n s0 i := hsigma i
    have hphase : fixedSigmaSq n s0 i = Real.sqrt (fixedSigmaSq n s0 i) ^ 2 :=
      (Real.sq_sqrt hs.le).symm
    have hwarm' : IsWarm (ENNReal.ofReal (M i)) (mu0 i)
        (ellGaussianProb
          (K ∩ closedBall (0 : State n)
            (4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n))
          (min (Real.sqrt (fixedSigmaSq n s0 i) / (8 * Real.sqrt n))
            (1 / (2 * (n : Real))))
          (Real.sqrt (fixedSigmaSq n s0 i) ^ 2)) := by
      rw [← hphase]
      exact hwarm i
    have htv :=
      Arlib.GaussianCooling.Chunked.tvLe_speedyRejection_coolLaw_truncated_relative_four_all_of_mixing
        hn hsigma
        (Real.sqrt_pos.2 hs) (hrad i) hK hKc hball hfin i.isLt hphase
        (hM i) hwarm' (heps0 i) (heps32 i) (hsteps i)
    change TVLe (Ttc.CVSampler.phaseLaw
      (K ∩ closedBall (0 : State n)
        (4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n))
      (min (Real.sqrt (fixedSigmaSq n s0 i) / (8 * Real.sqrt n))
        (1 / (2 * (n : Real))))
      (fixedSigmaSq n s0 i) (mu0 i) (steps i))
      (coolLaw (Ttc.CVHybridSchedule.coldPhases n s0) (fixedSigmaSq n s0) K i)
      (64 * ENNReal.ofReal (eps i) +
        ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) at htv
    exact htv

/-! ## Actual query cost via the phase-family theorem -/

/-- Source radius-four warm coordinates discharge the adjustable cost family theorem with
`q=4`.  Factoring through the family theorem avoids elaborating the large scalar theorem
at every fixed phase. -/
theorem sourceFixedWarmCost_le
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) {s0 : Real} (hs0 : 0 < s0)
    (mu0 : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (M : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → ENNReal)
    (steps : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Nat)
    (hwarm : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0), IsWarm (M i) (mu0 i)
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)))
    (hrad : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hhalf : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0), ENNReal.ofReal (1 / 2 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) •
          fixedRadiusFourBody K (fixedSigmaSq n s0 i)))
    (hquarter : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0), ENNReal.ofReal (1 / 4 : Real) ≤
      ((Ttc.SpeedyRejection.phasePointProposal
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)
        (mu0 i) (steps i)).withDensity (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (fixedSigmaSq n s0 i) x))) univ)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    ∀ (j : Fin r) (i : Fin (Ttc.CVHybridSchedule.coldPhases n s0)) (l : Fin k),
      6 * (∫⁻ z, z.1 ∂(warmPhaseCostLaw
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (measurableSet_fixedRadiusFourBody hK _)
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)
        (fixedRadiusFourDelta_pos (by omega : 1 ≤ n)
          (by unfold fixedSigmaSq; exact geomSchedule_pos hs0 (by positivity) i))
        (mu0 i) (steps i))) ≤ 80 * ((steps i : ENNReal) * M i) := by
  let c := Ttc.CVHybridSchedule.coldPhases n s0
  let K' : Fin c → Set (State n) := fun i => fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  let δ : Fin c → Real := fun i => fixedRadiusFourDelta n (fixedSigmaSq n s0 i)
  let σ : Fin c → Real := fun i => Real.sqrt (fixedSigmaSq n s0 i)
  let R : Fin c → Real := fun i => 4 * σ i * Real.sqrt n
  have hs : ∀ i : Fin c, 0 < fixedSigmaSq n s0 i := by
    intro i
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) i
  have hδ : ∀ i : Fin c, 0 < δ i := fun i => fixedRadiusFourDelta_pos
    (by omega) (hs i)
  have hfamily :=
    Ttc.CVCorrectedHybridRuntimeAssembly.varyingWarmCoordinateCost_le_adjustable
      (r := r) (k := k) hn K'
      (fun i => measurableSet_fixedRadiusFourBody hK _)
      (fun i => convex_fixedRadiusFourBody hKc _)
      (fun i => Arlib.MarkovChains.unitBall_subset_inter_closedBall hball (hrad i))
      (fun _ => 4) δ σ R (fun _ => by norm_num) hδ
      (fun i => Real.sqrt_pos.2 (hs i))
      (fun i => fixedRadiusFourDelta_le_n)
      (fun i => fixedRadiusFourDelta_le_radius)
      (fun _ => by positivity) (fun _ => le_rfl)
      (fun i x hx => norm_le_fixedRadiusFour hx) M mu0
      (fun i => by
        have hsq := Real.sq_sqrt (hs i).le
        simpa only [K', δ, σ, hsq] using hwarm i)
      steps (fun i => by
        have hsq := Real.sq_sqrt (hs i).le
        simpa only [K', δ, σ, hsq] using hhalf i)
      (fun i => by
        have hsq := Real.sq_sqrt (hs i).le
        simpa only [K', δ, σ, hsq] using hquarter i) hc2
  intro j i l
  simpa only [Ttc.CVCorrectedHybridRuntimeAssembly.varyingWarmCoordinateLaw,
    K', δ, σ, Real.sq_sqrt (hs i).le] using hfamily j i l

/-- Packed actual-query accounting for the source-faithful fixed block. -/
theorem six_mul_lintegral_packedSourceFixed_le
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hclosedBall : closedBall (0 : State n) 1 ⊆ K) {s0 : Real} (hs0 : 0 < s0)
    (mu0 : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (M : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → ENNReal)
    (steps : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Nat)
    (hwarm : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0), IsWarm (M i) (mu0 i)
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)))
    (hrad : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hhalf : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0), ENNReal.ofReal (1 / 2 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) •
          fixedRadiusFourBody K (fixedSigmaSq n s0 i)))
    (hquarter : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0), ENNReal.ofReal (1 / 4 : Real) ≤
      ((Ttc.SpeedyRejection.phasePointProposal
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)
        (mu0 i) (steps i)).withDensity (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (fixedSigmaSq n s0 i) x))) univ)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    6 * (∫⁻ omega, Ttc.CostedPackedWarmSchedule.totalMembershipQueries omega
      ∂(Ttc.CostedPackedWarmSchedule.costedPackedLaw
        (sourceFixedCoordinateCostLaw (by omega : 1 ≤ n) K hK hs0 mu0 steps :
          Fin r → Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Fin k →
            Measure (ENNReal × State n)))) ≤
      (r : ENNReal) * (k : ENNReal) *
        ∑ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
          if ambientEligible n (fixedSigmaSq n s0 i) then 12
          else 80 * ((steps i : ENNReal) * M i) := by
  letI : ∀ j i l, IsProbabilityMeasure
      (sourceFixedCoordinateCostLaw (by omega : 1 ≤ n) K hK hs0 mu0 steps j i l) :=
    fun (j : Fin r) (i : Fin (Ttc.CVHybridSchedule.coldPhases n s0)) (l : Fin k) =>
      @isProbabilityMeasure_sourceFixedCoordinateCostLaw n r k (by omega) K hK s0 hs0
        mu0 _ steps j i l
  apply Ttc.CostedPackedWarmSchedule.six_mul_lintegral_totalMembershipQueries_le_phaseBounds
  have hwcost := sourceFixedWarmCost_le (r := r) (k := k) hn hK hKc
    (Metric.ball_subset_closedBall.trans hclosedBall) hs0 mu0 M steps hwarm hrad
    hhalf hquarter hc2
  intro j i l
  unfold sourceFixedCoordinateCostLaw
  split_ifs with hi
  · have hc := lintegral_fst_coldPhaseCostLaw_le_two hK (by omega)
      (by unfold fixedSigmaSq; exact geomSchedule_pos hs0 (by positivity) i) hi hclosedBall
    calc
      6 * ∫⁻ z, z.1 ∂(coldPhaseCostLaw K (fixedSigmaSq n s0 i)) ≤ 6 * 2 :=
        mul_le_mul_left' hc 6
      _ = 12 := by norm_num
  · exact hwcost j i l

/-- Complete fixed-plus-accelerated actual-query sum.  The fixed block is the source-faithful
truncated law above; `rhoAdaptive` can be instantiated by the phase-dependent traced warm
family and its bounds by `varyingWarmCoordinateCost_le_adjustable`. -/
theorem six_mul_lintegral_sourceHybrid_le {ma : Nat}
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hclosedBall : closedBall (0 : State n) 1 ⊆ K) {s0 : Real} (hs0 : 0 < s0)
    (mu0 : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (M : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → ENNReal)
    (steps : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Nat)
    (hwarm : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0), IsWarm (M i) (mu0 i)
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)))
    (hrad : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hhalf : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0), ENNReal.ofReal (1 / 2 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) •
          fixedRadiusFourBody K (fixedSigmaSq n s0 i)))
    (hquarter : ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0), ENNReal.ofReal (1 / 4 : Real) ≤
      ((Ttc.SpeedyRejection.phasePointProposal
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)
        (mu0 i) (steps i)).withDensity (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (fixedSigmaSq n s0 i) x))) univ)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (rhoAdaptive : Fin r → Fin ma → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rhoAdaptive j i l)]
    (Badaptive : Fin ma → ENNReal)
    (hadaptive : ∀ j i l, 6 * (∫⁻ z, z.1 ∂(rhoAdaptive j i l)) ≤ Badaptive i) :
    6 * (∫⁻ omega, Ttc.CVCorrectedFixedBlockCost.totalHybridMembershipQueries omega
      ∂(Ttc.CVCorrectedFixedBlockCost.hybridBlockCostLaw
        (sourceFixedCoordinateCostLaw (by omega : 1 ≤ n) K hK hs0 mu0 steps :
          Fin r → Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Fin k →
            Measure (ENNReal × State n)) rhoAdaptive)) ≤
      (r : ENNReal) * (k : ENNReal) *
        ((∑ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
          if ambientEligible n (fixedSigmaSq n s0 i) then 12
          else 80 * ((steps i : ENNReal) * M i)) + ∑ i : Fin ma, Badaptive i) := by
  letI : ∀ j i l, IsProbabilityMeasure
      (sourceFixedCoordinateCostLaw (by omega : 1 ≤ n) K hK hs0 mu0 steps j i l) :=
    fun (j : Fin r) (i : Fin (Ttc.CVHybridSchedule.coldPhases n s0)) (l : Fin k) =>
      @isProbabilityMeasure_sourceFixedCoordinateCostLaw n r k (by omega) K hK s0 hs0
        mu0 _ steps j i l
  rw [Ttc.CVCorrectedFixedBlockCost.lintegral_totalHybridMembershipQueries, mul_add,
    mul_add]
  exact add_le_add
    (six_mul_lintegral_packedSourceFixed_le hn hK hKc hclosedBall hs0 mu0 M steps
      hwarm hrad hhalf hquarter hc2)
    (Ttc.CostedPackedWarmSchedule.six_mul_lintegral_totalMembershipQueries_le_phaseBounds
      rhoAdaptive Badaptive hadaptive)

end Ttc.CVSourceTruncatedFixedCost

#print axioms Ttc.CVSourceTruncatedFixedCost.tvLe_map_snd_sourceFixedCoordinateCostLaw
#print axioms Ttc.CVSourceTruncatedFixedCost.sourceFixedWarmCost_le
#print axioms Ttc.CVSourceTruncatedFixedCost.six_mul_lintegral_packedSourceFixed_le
#print axioms Ttc.CVSourceTruncatedFixedCost.six_mul_lintegral_sourceHybrid_le

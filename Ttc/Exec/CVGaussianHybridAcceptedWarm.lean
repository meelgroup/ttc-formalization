import Ttc.Exec.CVGaussianAdaptiveAcceptedWarm
import Ttc.Volume.CVHybridSchedule

/-! Accepted-sublaw warmth for the complete cold-plus-accelerated hybrid schedule. -/

set_option autoImplicit false

namespace Ttc.CVGaussianHybridAcceptedWarm

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.FiniteContinuingRetryRandomFallback
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def hybridAcceptedBudget
    (n : Nat) (N s0 : Real) (retries : Nat -> Nat)
    (warmBudget : Nat -> ENNReal) (i : Nat) : ENNReal :=
  (retries i : ENNReal) *
    (((16 : ENNReal) * acceleratedSeedWarmFactor n
      (1 + phaseRate n N s0 i)) * warmBudget i)

/-- The exact ratio accepted-warm theorem applies phasewise to the hybrid schedule.
Unlike the older fixed-rate wrapper, it imposes no false `cc <= 1+2/n` bound on the
accelerated block. -/
theorem activeAcceptedWarm_gaussian_hybrid
    (hn : 1 <= n) {m : Nat} {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta <= 1 / (2 * (n : Real)))
    (warmBudget : Nat -> ENNReal) (steps : Nat -> Nat -> Nat)
    (retries : Nat -> Nat) :
    forall i, i + 1 < m -> forall rho : Measure (State n),
      IsProbabilityMeasure rho ->
      IsWarm (warmBudget i) rho
        (ellGaussianProb K delta (sigmaSq n N s0 i)) ->
      IsWarm (hybridAcceptedBudget n N s0 retries warmBudget i)
        (Measure.map Prod.snd
          (acceptedOutputSubmeasure
            (augmentedMarginalOf K hK delta (sigmaSq n N s0 i)
              (1 - 1 / (2 * (n : Real))) hdelta
              (by
                have hnR : (0 : Real) < n := by
                  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
                have hn1 : (1 : Real) <= n := by exact_mod_cast hn
                have hhalf : 1 / (2 * (n : Real)) <= 1 / 2 := by
                  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                  linarith
                linarith)
              (steps i)
              (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho)
              (retries i))))
        (ellGaussianProb K delta (sigmaSq n N s0 (i + 1))) := by
  intro i hi rho hprob hwarm
  letI : IsProbabilityMeasure rho := hprob
  have hsigma : forall j, 0 < sigmaSq n N s0 j :=
    fun j => sigmaSq_pos hn hN hs0 j
  have hrate0 : 0 <= phaseRate n N s0 i := by
    unfold phaseRate
    split_ifs
    · have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
      positivity
    · exact (Arlib.GaussianCooling.Chunked.adaptiveChunkRate_pos hN
        (coldEnd_pos hn hs0) _).le
  have hsched : sigmaSq n N s0 (i + 1) =
      (1 + phaseRate n N s0 i) * sigmaSq n N s0 i := by
    rw [sigmaSq_succ hn hN hs0 i]
    ring
  simpa only [hybridAcceptedBudget] using
    isWarm_seed_acceptedOutputSubmeasure_gaussian_ratio hn hsigma hK hKc hball
      hKvol hi (by linarith) hsched hdelta hdeltan hwarm (steps i) (retries i)

#print axioms activeAcceptedWarm_gaussian_hybrid

end Ttc.CVGaussianHybridAcceptedWarm

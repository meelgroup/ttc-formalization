import Ttc.Exec.CVGaussianScoreAwareSharpScheduleBound
import Ttc.Exec.CVGaussianFactorSevenAssembly
import Ttc.Volume.CVOperationalRuntime
import Ttc.Volume.AdaptivePhaseScoreVariance

/-!
# Fixed phase-moment witness and minimal score-aware warm recurrence

This file removes two quantified choices from the literal score-aware Gaussian runtime
interface.  On every preterminal phase of the adaptive schedule the exact relative second
moment is strictly below three, so the factor-seven transport can use the fixed witness
`C = 3`.  It also defines the least warmness recurrence obtained by taking equality in the
accepted-plus-fallback budget with the constant adjacent-Gaussian fallback warmness `2e`.
-/

namespace Ttc.CVGaussianScoreAwareConcretePhaseWitness

open MeasureTheory Metric Set
open Arlib.GaussianCooling Arlib.GaussianCooling.Chunked
open Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVCorrectedRuntime
open Ttc.CVSourcePolynomialCutoffCapstone
open scoped ENNReal BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The adaptive exact-law phase factor is uniformly below three throughout the actual
preterminal schedule. -/
theorem adaptiveGlobalPhaseVarFactor_lt_three
    {N s₀ : Real} (hN : 0 < N) {i : Nat}
    (hi : adaptiveSigmaSq N s₀ i < 2 * N) :
    adaptiveGlobalPhaseVarFactor 1 N s₀ i < 3 := by
  unfold adaptiveGlobalPhaseVarFactor
  simp only [one_mul]
  have hdiv : adaptiveSigmaSq N s₀ i / N < 2 := by
    rw [div_lt_iff₀ hN]
    exact hi
  linarith

/-- Concrete `C = 3` exact phase-moment witness. -/
theorem adaptivePhaseScore_sq_moment_le_three
    (hn : 2 ≤ n)
    {K : Set (State n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s₀ : Real} {J : Nat} (hC : 0 < C) (hs₀ : 0 < s₀)
    (hbelow : ∀ j < J,
      adaptiveChunkStart (C ^ 2 * n) s₀ j ≤ C ^ 2 * n)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (i : Fin (adaptiveChunkOffset (C ^ 2 * n) s₀ J)) :
    ∫ x, phaseScore (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
          (adaptiveSigmaSq (C ^ 2 * n) s₀) K i x ^ 2
          ∂(coolLaw (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
            (adaptiveSigmaSq (C ^ 2 * n) s₀) K i) ≤
      3 * (∫ x, phaseScore (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
          (adaptiveSigmaSq (C ^ 2 * n) s₀) K i x
          ∂(coolLaw (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
            (adaptiveSigmaSq (C ^ 2 * n) s₀) K i)) ^ 2 := by
  have hN : 0 < C ^ 2 * (n : Real) := by
    have hn0 : 0 < n := by omega
    positivity
  have hfac : adaptiveGlobalPhaseVarFactor 1 (C ^ 2 * n) s₀ i < 3 := by
    apply adaptiveGlobalPhaseVarFactor_lt_three hN
    have hchunk : adaptivePhaseChunk (C ^ 2 * n) s₀ i < J :=
      adaptivePhaseChunk_lt_of_lt_offset hN hs₀ i.isLt
    have ht := adaptiveLocalPhase_lt hN hs₀ (i : Nat)
    have hphase := adaptiveChunk_phase_lt_two hN hs₀ ht
    have hstart := hbelow _ hchunk
    change adaptiveSigmaSq (C ^ 2 * (n : Real)) s₀ i <
      2 * (C ^ 2 * (n : Real))
    unfold adaptiveSigmaSq
    nlinarith
  have hraw := Ttc.CV.adaptivePhaseScore_sq_moment_le hn hKc hKcl hKb hvol
    hball hfin hC hs₀ hbelow hKR i
  exact hraw.trans (mul_le_mul_of_nonneg_right hfac.le (sq_nonneg _))

/-- With the concrete exact factor `3`, the factor-seven slack has a fixed gap four. -/
theorem phaseMomentSlackSeven_three
    (chainLength : Nat) (sigmaSq : Nat → Real) (K : Set (State n)) (i : Nat) :
    phaseMomentSlackSeven chainLength sigmaSq K (fun _ ↦ 3) i =
      4 * (chain chainLength sigmaSq K (i + 1) /
        chain chainLength sigmaSq K i) ^ 2 := by
  unfold phaseMomentSlackSeven
  norm_num

/-- Equality recurrence for the smallest declared warm budget when fallback warmness is
the constant adjacent-Gaussian value `2e`. -/
noncomputable def minimalScoreAwareWarm
    (n : Nat) (N s₀ : Real) (m k : Nat) (eps : Real)
    (slack boundSq : Nat → Real) : Nat → ENNReal
  | 0 => gaussianReferenceWarm
  | i + 1 =>
      (scoreAwareRetries m k eps slack boundSq i : ENNReal) *
          ((16 * acceleratedSeedWarmFactor n (1 + adaptivePhaseRate N s₀ i)) *
            minimalScoreAwareWarm n N s₀ m k eps slack boundSq i) +
        gaussianReferenceWarm

theorem minimalScoreAwareWarm_zero
    (n : Nat) (N s₀ : Real) (m k : Nat) (eps : Real)
    (slack boundSq : Nat → Real) :
    minimalScoreAwareWarm n N s₀ m k eps slack boundSq 0 =
      gaussianReferenceWarm := rfl

theorem minimalScoreAwareWarm_succ
    (n : Nat) (N s₀ : Real) (m k : Nat) (eps : Real)
    (slack boundSq : Nat → Real) (i : Nat) :
    minimalScoreAwareWarm n N s₀ m k eps slack boundSq (i + 1) =
      adaptiveAcceptedBudget n N s₀
          (scoreAwareRetries m k eps slack boundSq)
          (minimalScoreAwareWarm n N s₀ m k eps slack boundSq) i +
        gaussianReferenceWarm := by
  rfl

theorem gaussianReferenceWarm_le_minimalScoreAwareWarm
    (n : Nat) (N s₀ : Real) (m k : Nat) (eps : Real)
    (slack boundSq : Nat → Real) :
    ∀ i, gaussianReferenceWarm ≤
      minimalScoreAwareWarm n N s₀ m k eps slack boundSq i := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
      rw [minimalScoreAwareWarm_succ]
      exact le_add_left le_rfl

/-- A public uniform retry cap yields an explicit exponential upper envelope for the
minimal recurrence.  Its logarithm is therefore only linear in the number of phases. -/
theorem minimalScoreAwareWarm_le_pow_envelope
    {n m k L : Nat} {N s₀ eps : Real} {slack boundSq : Nat → Real}
    (hN : 0 < N) (hs₀ : 0 < s₀)
    (hbelow : ∀ i,
      adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i) ≤ N)
    (hretries : ∀ i, scoreAwareRetries m k eps slack boundSq i ≤ L) :
    ∀ i, minimalScoreAwareWarm n N s₀ m k eps slack boundSq i ≤
      ((L : ENNReal) *
          (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) ^ i *
        gaussianReferenceWarm := by
  intro i
  induction i with
  | zero => simp [minimalScoreAwareWarm]
  | succ i ih =>
      rw [minimalScoreAwareWarm_succ, pow_succ]
      have hfactor := acceleratedSeedWarmFactor_adaptive_le_pow_two
        (n := n) hN hs₀ (hbelow i)
      have href := gaussianReferenceWarm_le_minimalScoreAwareWarm
        n N s₀ m k eps slack boundSq i
      calc
        adaptiveAcceptedBudget n N s₀
              (scoreAwareRetries m k eps slack boundSq)
              (minimalScoreAwareWarm n N s₀ m k eps slack boundSq) i +
            gaussianReferenceWarm ≤
          ((L : ENNReal) *
              (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) *
            minimalScoreAwareWarm n N s₀ m k eps slack boundSq i := by
              unfold adaptiveAcceptedBudget
              calc
                (scoreAwareRetries m k eps slack boundSq i : ENNReal) *
                      ((16 * acceleratedSeedWarmFactor n
                        (1 + adaptivePhaseRate N s₀ i)) *
                        minimalScoreAwareWarm n N s₀ m k eps slack boundSq i) +
                    gaussianReferenceWarm ≤
                  (L : ENNReal) *
                      ((16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) *
                        minimalScoreAwareWarm n N s₀ m k eps slack boundSq i) +
                    minimalScoreAwareWarm n N s₀ m k eps slack boundSq i := by
                      have hr : (scoreAwareRetries m k eps slack boundSq i : ENNReal) ≤ L := by
                        exact_mod_cast hretries i
                      gcongr
                _ = _ := by ring
        _ ≤ ((L : ENNReal) *
              (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) *
            (((L : ENNReal) *
              (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) ^ i *
                gaussianReferenceWarm) := by gcongr
        _ = (((L : ENNReal) *
              (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) ^ i *
                gaussianReferenceWarm) *
            ((L : ENNReal) *
              (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) := by
                ac_rfl
        _ = ((L : ENNReal) *
              (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) ^ i *
            ((L : ENNReal) *
              (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) *
            gaussianReferenceWarm := by ac_rfl

theorem sum_active_const (m : Nat) (c : Real) :
    (∑ i ∈ Finset.range m, if i + 1 < m then c else 0) =
      (m - 1 : Nat) * c := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.add_lt_add_iff_right, lt_self_iff_false, ↓reduceIte,
        add_zero, Nat.add_sub_cancel]
      calc
        (∑ x ∈ Finset.range m, if x < m then c else 0) =
            ∑ _x ∈ Finset.range m, c := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [if_pos (Finset.mem_range.mp hx)]
        _ = (m : Real) * c := by simp

/-- Even after replacing compounding expected warmness by the constant exact-reference
warmness, the literal corrected score-aware schedule performs at least one retry and one
mixing step in every active phase.  This gives the unavoidable `k*(m-1)` lower bound. -/
theorem correctedScoreAwareReferencePhaseSum_lower
    (n m k : Nat) {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (delta : Real) (sigmaSq : Nat → Real)
    (slack boundSq : Nat → Real)
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    (operationalWarm : Nat → ENNReal) :
    10 * (k : Real) * ((m - 1 : Nat) : Real) * (2 * Real.exp 1) ≤
      (k : Real) * ∑ i ∈ Finset.range m,
        Ttc.CVGaussianSourceSharpCost.gaussianActiveMeanEnvelopeReal m
          (fun _ ↦ gaussianReferenceWarm)
          (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq operationalWarm)
          (scoreAwareRetries m k eps slack boundSq) i := by
  rw [sharpReferencePhaseSum_scoreAware_eq]
  have hk0 : (0 : Real) ≤ k := by positivity
  rw [show 10 * (k : Real) * ((m - 1 : Nat) : Real) * (2 * Real.exp 1) =
    (k : Real) * (10 * ((m - 1 : Nat) : Real) * (2 * Real.exp 1)) by ring]
  apply mul_le_mul_of_nonneg_left _ hk0
  calc
    10 * (((m - 1 : Nat) : Real)) * (2 * Real.exp 1) =
        ∑ i ∈ Finset.range m,
          if i + 1 < m then 10 * (2 * Real.exp 1) else 0 := by
            rw [sum_active_const]
            ring
    _ ≤ ∑ i ∈ Finset.range m,
        if i + 1 < m then
          10 * (scoreAwareRetries m k eps slack boundSq i : Real) *
            (adjustableSpeedyDeadline n delta (sigmaSq i)
              ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
              (scoreAwareZeta m k eps slack boundSq i) : Real) *
            (2 * Real.exp 1)
        else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · have hindex := Ttc.CVAdaptive.explicitDyadicTailIndex_pos
          (scoreAwareShare_pos (m := m) (k := k) heps hslack hbound i)
          (scoreAwareShare_lt_one (m := m) (k := k) heps heps1 i)
        have hr : (1 : Real) ≤ scoreAwareRetries m k eps slack boundSq i := by
          rw [scoreAwareRetries]
          push_cast
          have : (1 : Real) ≤ Ttc.CVAdaptive.explicitDyadicTailIndex
              (scoreAwareShare m k eps slack boundSq i) := by exact_mod_cast hindex
          nlinarith
        have hd : (1 : Real) ≤ adjustableSpeedyDeadline n delta (sigmaSq i)
            ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
            (scoreAwareZeta m k eps slack boundSq i) := by
          unfold adjustableSpeedyDeadline
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
        have he : 0 ≤ 2 * Real.exp 1 := by positivity
        calc
          10 * (2 * Real.exp 1) = 10 * 1 * 1 * (2 * Real.exp 1) := by ring
          _ ≤ 10 * (scoreAwareRetries m k eps slack boundSq i : Real) *
              (adjustableSpeedyDeadline n delta (sigmaSq i)
                ((2 * operationalWarm i) /
                  scoreAwareEta m k eps slack boundSq i)
                (scoreAwareZeta m k eps slack boundSq i) : Real) *
              (2 * Real.exp 1) := by gcongr
      · exact le_rfl

/-- Concrete schedule counterexample to any source-envelope theorem that quantifies over
an unrelated phase count `m`.  All steps and retries here are the literal score-aware
definitions; only the absence of a public relation between `m` and `(n,R,eps)` is used. -/
theorem exists_concreteScoreAwarePhaseSum_gt_sourceEnvelope
    (runtimeConstant : Real) (n : Nat) (radius : Real) :
    ∃ m : Nat,
      sourceOneRunQueryEnvelope runtimeConstant n radius 1 <
        let k := correctedRuntimeSamples m (1 / 4)
        (k : Real) * ∑ i ∈ Finset.range m,
          Ttc.CVGaussianSourceSharpCost.gaussianActiveMeanEnvelopeReal m
            (fun _ ↦ gaussianReferenceWarm)
            (scoreAwareGaussianSteps n 1 (fun _ ↦ 1) m k (1 / 4)
              (fun _ ↦ 1) (fun _ ↦ 1)
              (minimalScoreAwareWarm n 1 1 m k (1 / 4)
                (fun _ ↦ 1) (fun _ ↦ 1)))
            (scoreAwareRetries m k (1 / 4) (fun _ ↦ 1) (fun _ ↦ 1)) i := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
    (sourceOneRunQueryEnvelope runtimeConstant n radius 1)
    (by norm_num : (1 : Real) < 2)
  let m := 2 ^ j + 2
  let k := correctedRuntimeSamples m (1 / 4)
  refine ⟨m, ?_⟩
  dsimp only
  have hlower := correctedScoreAwareReferencePhaseSum_lower n m k
    (by norm_num : (0 : Real) < 1 / 4) (by norm_num : (1 / 4 : Real) ≤ 1)
    1 (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1)
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
    (minimalScoreAwareWarm n 1 1 m k (1 / 4) (fun _ ↦ 1) (fun _ ↦ 1))
  have hk : (1 : Real) ≤ k := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2
      (Nat.ne_of_gt (correctedRuntimeSamples_pos m (1 / 4)))
  have hp0 : (0 : Real) ≤ 2 ^ j := by positivity
  have hbase : (2 : Real) ^ j <
      10 * (k : Real) * (((m - 1 : Nat) : Real)) * (2 * Real.exp 1) := by
    have hmcast : (((m - 1 : Nat) : Real)) = (2 : Real) ^ j + 1 := by
      have hmnat : m - 1 = 2 ^ j + 1 := by
        dsimp [m]
      exact_mod_cast hmnat
    rw [hmcast]
    calc
      (2 : Real) ^ j < (2 : Real) ^ j + 1 := by linarith
      _ ≤ 10 * (k : Real) * ((2 : Real) ^ j + 1) * (2 * Real.exp 1) := by
        have hp : 0 ≤ (2 : Real) ^ j + 1 := by positivity
        have he : 1 ≤ 2 * Real.exp 1 := by
          have := Real.exp_one_gt_d9
          nlinarith
        calc
          (2 : Real) ^ j + 1 = 1 * ((2 : Real) ^ j + 1) * 1 := by ring
          _ ≤ 10 * (k : Real) * ((2 : Real) ^ j + 1) * (2 * Real.exp 1) := by
            gcongr
            nlinarith
  exact hj.trans (hbase.trans_le hlower)

#print axioms adaptiveGlobalPhaseVarFactor_lt_three
#print axioms adaptivePhaseScore_sq_moment_le_three
#print axioms phaseMomentSlackSeven_three
#print axioms minimalScoreAwareWarm_le_pow_envelope
#print axioms correctedScoreAwareReferencePhaseSum_lower
#print axioms exists_concreteScoreAwarePhaseSum_gt_sourceEnvelope

end Ttc.CVGaussianScoreAwareConcretePhaseWitness

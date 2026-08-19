import Ttc.Exec.CVRadiusAwareReferenceCostArithmetic
import Ttc.Exec.CVHeterogeneousSourceCertificate

/-!
# Cold/hot reference-cost split for the source CV schedule

The adjustable-radius Gaussian estimate is only a hot-block theorem: its local-radius
hypothesis need not hold at the source cold start.  This file records the cost composition
with two genuinely different phase families.  The cold block can be instantiated by
`CVSourceTruncatedFixedCost`, while the hot block can use the radius-aware retained-history
reference with constant warmness `2e`.

The final theorem also performs the source-sharp sample arithmetic.  In particular, the
number of scalar streams is twice `estimatorSamples`, as required by the sharp weighted
moment bridge, and the only occurrence of the requested accuracy is the advertised
`eps^-2` factor.  No total-phase factor is inserted into the sample count.
-/

set_option autoImplicit false

namespace Ttc.CVColdHotReferenceCost

open Ttc.CVHybridSchedule
open Ttc.CVHybridSourceSharpEnvelope
open Ttc.CVRadiusAwareReferenceCostArithmetic
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVHeterogeneousSourceCertificate
open Ttc.CVSourceReferenceTVCapstone
open Ttc.CVRetainedHistoryReferenceInduction
open Arlib
open Arlib.GaussianCooling.Chunked
open Ttc.CV
open Ttc.CV.Adaptive
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

/-- A phase envelope with separate cold and hot index spaces. -/
noncomputable def coldHotPhaseMeanReal
    (cold hot : Nat) (coldMean hotMean : Nat → Real) (i : Nat) : Real :=
  if i < cold then coldMean i
  else if i < cold + hot then hotMean (i - cold)
  else 0

theorem coldHotPhaseMeanReal_nonneg
    (cold hot : Nat) (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i) (i : Nat) :
    0 ≤ coldHotPhaseMeanReal cold hot coldMean hotMean i := by
  unfold coldHotPhaseMeanReal
  split_ifs
  · exact hcold i
  · exact hhot (i - cold)
  · norm_num

/-- Splitting is exact: there is no fictitious uniform deadline across the boundary. -/
theorem sum_coldHotPhaseMeanReal
    (cold hot : Nat) (coldMean hotMean : Nat → Real) :
    ∑ i ∈ Finset.range (cold + hot),
        coldHotPhaseMeanReal cold hot coldMean hotMean i =
      (∑ i ∈ Finset.range cold, coldMean i) +
        ∑ i ∈ Finset.range hot, hotMean i := by
  induction hot with
  | zero =>
      simp only [Finset.sum_range_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      rw [coldHotPhaseMeanReal, if_pos (Finset.mem_range.mp hi)]
  | succ hot ih =>
      have hprefix :
          (∑ i ∈ Finset.range (cold + hot),
              coldHotPhaseMeanReal cold (hot + 1) coldMean hotMean i) =
            ∑ i ∈ Finset.range (cold + hot),
              coldHotPhaseMeanReal cold hot coldMean hotMean i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < cold + hot := Finset.mem_range.mp hi
        unfold coldHotPhaseMeanReal
        by_cases hic : i < cold
        · rw [if_pos hic, if_pos hic]
        · rw [if_neg hic, if_neg hic, if_pos (by omega), if_pos hi']
      rw [Nat.add_succ, Finset.sum_range_succ, hprefix, ih,
        Finset.sum_range_succ]
      have hnot : ¬ cold + hot < cold := by omega
      have hlt : cold + hot < cold + (hot + 1) := by omega
      rw [coldHotPhaseMeanReal, if_neg hnot, if_pos hlt,
        Nat.add_sub_cancel_left]
      ring

/-- ENNReal version used by the retained-history expected-cost certificate. -/
noncomputable def coldHotPhaseMean
    (cold hot : Nat) (coldMean hotMean : Nat → Real) (i : Nat) : ENNReal :=
  ENNReal.ofReal (coldHotPhaseMeanReal cold hot coldMean hotMean i)

theorem ofReal_coldHotPhaseMeanReal
    (cold hot : Nat) (coldMean hotMean : Nat → Real) (i : Nat) :
    ENNReal.ofReal (coldHotPhaseMeanReal cold hot coldMean hotMean i) =
      coldHotPhaseMean cold hot coldMean hotMean i := rfl

/-- Any ordinary-real cold/hot calculation transfers directly to the source ENNReal
budget.  This is the cost-side constructor consumed by the history reference theorem. -/
theorem coldHotPhaseSum_le_sourceBudget_of_real
    (runtimeConstant : Real) (n streams cold hot : Nat) (radius eps : Real)
    (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i)
    (hreal : (streams : Real) * ∑ i ∈ Finset.range (cold + hot),
        coldHotPhaseMeanReal cold hot coldMean hotMean i ≤
      sourceOneRunQueryEnvelope runtimeConstant n radius eps) :
    (streams : ENNReal) * ∑ i ∈ Finset.range (cold + hot),
        coldHotPhaseMean cold hot coldMean hotMean i ≤
      sourceOneRunQueryBudget runtimeConstant n radius eps := by
  unfold sourceOneRunQueryBudget
  rw [← ENNReal.ofReal_natCast]
  simp_rw [← ofReal_coldHotPhaseMeanReal]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
    coldHotPhaseMeanReal_nonneg cold hot coldMean hotMean hcold hhot i)]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg streams)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The numerator of the source-sharp scalar sample count. -/
noncomputable def weightedSampleNumerator (n cold hotChunks : Nat) : Real :=
  44 + 160 * (cold : Real) / (n : Real) + 560 * (hotChunks : Real)

theorem weightedSampleNumerator_pos
    (n cold hotChunks : Nat) :
    0 < weightedSampleNumerator n cold hotChunks := by
  unfold weightedSampleNumerator
  positivity

/-- The hot-chunk term cannot be suppressed by a bound independent of the radial
schedule.  Any final universal comparison must therefore control the concrete terminal
chunk in terms of parameters that actually occur in the advertised logarithms. -/
theorem not_exists_uniform_weightedSampleNumerator_bound :
    ¬ ∃ D : Real, ∀ J : Nat, weightedSampleNumerator 1 0 J ≤ D := by
  rintro ⟨D, hD⟩
  obtain ⟨J, hJ⟩ := exists_nat_gt D
  have hJ0 : (0 : Real) ≤ J := by positivity
  have hbound := hD J
  unfold weightedSampleNumerator at hbound
  norm_num at hbound
  nlinarith

/-- The concrete terminal hot-chunk index is logarithmic in the terminal variance. -/
theorem hybrid_terminalChunk_cast_lt_two_sourceLog_add_one
    {n : Nat} (hn : 1 ≤ n) {N s0 : Real}
    (hN : 1 ≤ N) (hs0 : 0 < s0) (hs01 : s0 ≤ 1) :
    (adaptiveTerminalChunk N (coldEnd n s0) : Real) <
      2 * sourceLogFactor N + 1 := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  let q : Nat := ⌈Real.log N / Real.log 2⌉₊
  have hqCast : Real.log N / Real.log 2 ≤ (q : Real) := by
    exact Nat.le_ceil _
  have hlogLe : Real.log N ≤ (q : Real) * Real.log 2 := by
    rw [div_le_iff₀ hlog2] at hqCast
    simpa [mul_comm] using hqCast
  have hpow : N ≤ (2 : Real) ^ q := by
    have hexp := Real.exp_le_exp.2 hlogLe
    rw [Real.exp_log hN0, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : Real) < 2)]
      at hexp
    exact hexp
  have hJ : adaptiveTerminalChunk N (coldEnd n s0) ≤ q :=
    hybrid_terminalChunk_le_of_target_le_pow_two hn hN0 hs0 hs01 hpow
  have hceil : (q : Real) < Real.log N / Real.log 2 + 1 := by
    dsimp only [q]
    exact Nat.ceil_lt_add_one (div_nonneg hlogN hlog2.le)
  have hratio : Real.log N / Real.log 2 ≤ 2 * sourceLogFactor N := by
    rw [div_le_iff₀ hlog2]
    have hlogMax : Real.log N ≤ sourceLogFactor N := le_max_right _ _
    have htwoLog : 1 ≤ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hL0 : 0 ≤ sourceLogFactor N := (sourceLogFactor_pos N).le
    calc
      Real.log N ≤ sourceLogFactor N := hlogMax
      _ ≤ 2 * sourceLogFactor N * Real.log 2 := by
        nlinarith [mul_nonneg hL0 (sub_nonneg.2 htwoLog)]
  have hJCast : (adaptiveTerminalChunk N (coldEnd n s0) : Real) ≤ q := by
    exact_mod_cast hJ
  linarith

/-- At the repository's source endpoint `1/(16n)`, the fixed block contributes only one
clipped logarithm after division by `n`. -/
theorem coldPhases_source_div_lt_thirtyThree_log
    {n : Nat} (hn : 1 ≤ n) :
    (coldPhases n (1 / (16 * (n : Real))) : Real) / (n : Real) <
      33 * sourceLogFactor n := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hc := coldPhases_cast_lt_add_one hn (1 / (16 * (n : Real)))
  have hinv : 1 / (1 / (16 * (n : Real))) = 16 * (n : Real) := by
    field_simp
  have hlog0 : 0 ≤ Real.log (16 * (n : Real)) := by
    apply Real.log_nonneg
    nlinarith [show (1 : Real) ≤ n by exact_mod_cast hn]
  rw [hinv, max_eq_right hlog0] at hc
  have hlogmul : Real.log (16 * (n : Real)) =
      Real.log 16 + Real.log (n : Real) := by
    rw [Real.log_mul (by norm_num : (16 : Real) ≠ 0) hn0.ne']
  have hlog16 : Real.log (16 : Real) ≤ 15 := by
    have h := Real.log_le_sub_one_of_pos (x := (16 : Real)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hLn1 : 1 ≤ sourceLogFactor n := le_max_left _ _
  have hlogn : Real.log (n : Real) ≤ sourceLogFactor n := le_max_right _ _
  have hlogBound : Real.log (16 * (n : Real)) ≤ 16 * sourceLogFactor n := by
    rw [hlogmul]
    nlinarith
  have hone : 1 ≤ (n : Real) * sourceLogFactor n := by
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    nlinarith [mul_le_mul hn1 hLn1 (by norm_num : (0 : Real) ≤ 1)
      (by positivity : 0 ≤ (n : Real))]
  rw [div_lt_iff₀ hn0]
  calc
    (coldPhases n (1 / (16 * (n : Real))) : Real) <
        2 * (n : Real) * Real.log (16 * (n : Real)) + 1 := hc
    _ ≤ 33 * sourceLogFactor n * (n : Real) := by
      nlinarith [mul_le_mul_of_nonneg_left hlogBound (by positivity : 0 ≤ 2 * (n : Real))]

/-- Concrete source weighted-sample numerator, now with the necessary terminal-variance
logarithm made explicit. -/
theorem weightedSampleNumerator_source_terminal_le
    {n : Nat} (hn : 1 ≤ n) {N : Real} (hN : 1 ≤ N) :
    weightedSampleNumerator n
        (coldPhases n (1 / (16 * (n : Real))))
        (adaptiveTerminalChunk N
          (coldEnd n (1 / (16 * (n : Real))))) ≤
      7004 * sourceLogFactor n * sourceLogFactor N := by
  have hs0 : 0 < (1 / (16 * (n : Real))) := by
    have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    positivity
  have hs01 : (1 / (16 * (n : Real)) : Real) ≤ 1 := by
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    rw [div_le_one (by positivity : (0 : Real) < 16 * (n : Real))]
    nlinarith
  have hc := coldPhases_source_div_lt_thirtyThree_log hn
  have hJ := hybrid_terminalChunk_cast_lt_two_sourceLog_add_one
    hn hN hs0 hs01
  have hLn1 : 1 ≤ sourceLogFactor n := le_max_left _ _
  have hLN1 : 1 ≤ sourceLogFactor N := le_max_left _ _
  unfold weightedSampleNumerator
  have hc' : 160 *
      (coldPhases n (1 / (16 * (n : Real))) : Real) / (n : Real) ≤
      5280 * sourceLogFactor n := by
    calc
      160 * (coldPhases n (1 / (16 * (n : Real))) : Real) / (n : Real) =
          160 * ((coldPhases n (1 / (16 * (n : Real))) : Real) /
            (n : Real)) := by ring
      _ ≤ 160 * (33 * sourceLogFactor n) :=
        mul_le_mul_of_nonneg_left hc.le (by norm_num)
      _ = 5280 * sourceLogFactor n := by ring
  have hJ' : 560 *
      (adaptiveTerminalChunk N
        (coldEnd n (1 / (16 * (n : Real)))) : Real) ≤
      1680 * sourceLogFactor N := by nlinarith
  have h44 : (44 : Real) ≤ 44 * sourceLogFactor n * sourceLogFactor N := by
    nlinarith [mul_le_mul hLn1 hLN1 (by norm_num : (0 : Real) ≤ 1)
      (sourceLogFactor_pos n).le]
  have hcL : 5280 * sourceLogFactor n ≤
      5280 * sourceLogFactor n * sourceLogFactor N := by
    nlinarith [mul_nonneg (by positivity : (0 : Real) ≤ 5280 * sourceLogFactor n)
      (sub_nonneg.2 hLN1)]
  have hJL : 1680 * sourceLogFactor N ≤
      1680 * sourceLogFactor n * sourceLogFactor N := by
    nlinarith [mul_nonneg (by positivity : (0 : Real) ≤ 1680 * sourceLogFactor N)
      (sub_nonneg.2 hLn1)]
  nlinarith

/-- Put the source weighted sample bound into the literal `eps^-2` form. -/
theorem estimatorSamples_cast_le_weighted_div_epsSq
    {n cold hotChunks : Nat} (hn : 1 ≤ n) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (estimatorSamples n cold hotChunks eps : Real) ≤
      weightedSampleNumerator n cold hotChunks / eps ^ 2 := by
  have hk := estimatorSamples_lt_weighted (c := cold) (J := hotChunks)
    hn heps heps1
  have hepsSq : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hepsSqOne : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg (eps - 1)]
  have hfortyFour : (44 : Real) ≤ 44 / eps ^ 2 := by
    rw [le_div_iff₀ hepsSq]
    nlinarith
  calc
    (estimatorSamples n cold hotChunks eps : Real) ≤
        44 + (160 * (cold : Real) / (n : Real) +
          560 * (hotChunks : Real)) / eps ^ 2 := hk.le
    _ = 44 + (160 * (cold : Real) / (n : Real)) / eps ^ 2 +
        (560 * (hotChunks : Real)) / eps ^ 2 := by ring
    _ ≤ 44 / eps ^ 2 + (160 * (cold : Real) / (n : Real)) / eps ^ 2 +
        (560 * (hotChunks : Real)) / eps ^ 2 := by linarith
    _ = weightedSampleNumerator n cold hotChunks / eps ^ 2 := by
      unfold weightedSampleNumerator
      ring

/-- The source envelope with its unique `eps^-2` factor removed. -/
noncomputable def sourceOneRunQueryCore
    (runtimeConstant : Real) (n : Nat) (radius eps : Real) : Real :=
  runtimeConstant *
    (max (radius ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) *
      sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
        sourceLogFactor ((n : Real) / eps) ^ 2)

/-- **`core / eps²`, written out.**

⚠ This replaces `sourceOneRunQueryEnvelope_eq_core_div`.  Before `PLAN-SHAPE`,
`Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryEnvelope` *was* `core / eps²`, and
that identity was the bridge between this file's `core` layer and the public budget.  The
budget no longer carries the shape, so the identity is false; what the `core` layer actually
needs is only the expansion below, which mentions no budget at all. -/
theorem sourceOneRunQueryCore_div_eq
    (runtimeConstant : Real) (n : Nat) (radius eps : Real) :
    sourceOneRunQueryCore runtimeConstant n radius eps / eps ^ 2 =
      runtimeConstant *
        (max (radius ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
            sourceLogFactor ((n : Real) / eps) ^ 2) := by
  unfold sourceOneRunQueryCore
  ring

/-! ## Concrete source phase envelopes -/

/-- Literal fixed-block mean supplied by the source's radius-four cost theorem.  The
factor `80` is the proved speedy/rejection conversion constant; unlike the hot Gaussian
formula, this definition has no local-radius premise. -/
noncomputable def fixedBlockReferenceMeanReal
    (steps : Nat → Nat) (warm : Nat → ENNReal) (i : Nat) : Real :=
  80 * (steps i : Real) * (warm i).toReal

theorem fixedBlockReferenceMeanReal_nonneg
    (steps : Nat → Nat) (warm : Nat → ENNReal) (i : Nat) :
    0 ≤ fixedBlockReferenceMeanReal steps warm i := by
  unfold fixedBlockReferenceMeanReal
  positivity

/-- Direct adapter from the proved fixed-block cost estimate
`6 * E ≤ 80 * steps * M` to the ordinary-real phase mean used in the split. -/
theorem fixedBlock_mean_le_referenceMean
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure (ENNReal × Omega)) (steps : Nat → Nat)
    (warm : Nat → ENNReal) (i : Nat) (hwarmTop : warm i ≠ ⊤)
    (hcost : 6 * (∫⁻ z, z.1 ∂mu) ≤
      80 * ((steps i : ENNReal) * warm i)) :
    (∫⁻ z, z.1 ∂mu) ≤
      ENNReal.ofReal (fixedBlockReferenceMeanReal steps warm i) := by
  have heq : ENNReal.ofReal (fixedBlockReferenceMeanReal steps warm i) =
      80 * ((steps i : ENNReal) * warm i) := by
    unfold fixedBlockReferenceMeanReal
    rw [show (80 : Real) * (steps i : Real) * (warm i).toReal =
      80 * ((steps i : Real) * (warm i).toReal) by ring]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 80),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (steps i : Real)),
      ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hwarmTop]
    norm_num
  rw [heq]
  calc
    (∫⁻ z, z.1 ∂mu) = 1 * (∫⁻ z, z.1 ∂mu) := by simp
    _ ≤ 6 * (∫⁻ z, z.1 ∂mu) :=
      mul_le_mul_right' (by norm_num : (1 : ENNReal) ≤ 6) _
    _ ≤ 80 * ((steps i : ENNReal) * warm i) := hcost

/-- Literal hot retained-history reference mean.  Radius awareness makes the reference
warmth the constant `2e`; operational warmness occurs only in the chosen deadline. -/
noncomputable def hotRadiusReferenceMeanReal
    (retries steps : Nat → Nat) (i : Nat) : Real :=
  10 * (retries i : Real) * (steps i : Real) * (2 * Real.exp 1)

theorem hotRadiusReferenceMeanReal_nonneg
    (retries steps : Nat → Nat) (i : Nat) :
    0 ≤ hotRadiusReferenceMeanReal retries steps i := by
  unfold hotRadiusReferenceMeanReal
  positivity

/-- The hot definition is exactly the constant-deadline retry envelope used by the
Gaussian retained-history cost theorem. -/
theorem gaussianActiveMeanEnvelopeReal_const_eq_hotRadius
    (m : Nat) (retries steps : Nat → Nat) (i : Nat) :
    Ttc.CVGaussianSourceSharpCost.gaussianActiveMeanEnvelopeReal m
        (fun _ ↦ gaussianReferenceWarm) (fun j _ ↦ steps j) retries i =
      if i + 1 < m then hotRadiusReferenceMeanReal retries steps i else 0 := by
  unfold Ttc.CVGaussianSourceSharpCost.gaussianActiveMeanEnvelopeReal
  split_ifs
  · rw [Ttc.CVGaussianScoreAwareSharpScheduleBound.retryReferenceMeanEnvelope_const,
      gaussianReferenceWarm_toReal]
    unfold hotRadiusReferenceMeanReal
    rfl
  · rfl

/-- Assemble the source shape from the separate fixed and accelerated block estimates.
This is the exact deterministic cold/hot cancellation in
`CVHybridRuntimeAccounting`: fixed phases pay the first summand, while hot phases pay the
variance-weighted second summand. -/
theorem coldHotShape_of_sourceHybridCore
    {runtimeConstant radius eps N s0 q overhead : Real}
    {n J hot : Nat}
    (coldMean hotMean : Nat → Real)
    (hcold :
      (∑ i ∈ Finset.range (coldPhases n s0), coldMean i) ≤
        overhead * (2 * (coldPhases n s0 : Real)))
    (hhot : (∑ i ∈ Finset.range hot, hotMean i) ≤
      overhead * (4 * q ^ 2 * (n : Real) ^ 2 *
        Ttc.CVCorrectedRuntime.adaptiveSourceHotSigmaMass
          N (coldEnd n s0) J))
    (hsourceCore :
      2 * weightedSampleNumerator n (coldPhases n s0) J * overhead *
          sourceHybridProposalCore n N s0 J q ≤
        sourceOneRunQueryCore runtimeConstant n radius eps) :
    2 * weightedSampleNumerator n (coldPhases n s0) J *
        ((∑ i ∈ Finset.range (coldPhases n s0), coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i) ≤
      sourceOneRunQueryCore runtimeConstant n radius eps := by
  have hnum0 : 0 ≤ 2 * weightedSampleNumerator n (coldPhases n s0) J := by
    have hnum := weightedSampleNumerator_pos n (coldPhases n s0) J
    nlinarith
  have hsum :
      (∑ i ∈ Finset.range (coldPhases n s0), coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i ≤
        overhead * sourceHybridProposalCore n N s0 J q := by
    calc
      _ ≤ overhead * (2 * (coldPhases n s0 : Real)) +
          overhead * (4 * q ^ 2 * (n : Real) ^ 2 *
            Ttc.CVCorrectedRuntime.adaptiveSourceHotSigmaMass
              N (coldEnd n s0) J) := add_le_add hcold hhot
      _ = overhead * sourceHybridProposalCore n N s0 J q := by
        unfold sourceHybridProposalCore
        ring
  calc
    2 * weightedSampleNumerator n (coldPhases n s0) J *
        ((∑ i ∈ Finset.range (coldPhases n s0), coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i) ≤
      2 * weightedSampleNumerator n (coldPhases n s0) J *
        (overhead * sourceHybridProposalCore n N s0 J q) := by gcongr
    _ = 2 * weightedSampleNumerator n (coldPhases n s0) J * overhead *
        sourceHybridProposalCore n N s0 J q := by ring
    _ ≤ sourceOneRunQueryCore runtimeConstant n radius eps := hsourceCore

/-- Same assembly after applying the proved `6*N*J` accelerated variance cancellation. -/
theorem coldHotShape_of_cancelledHybridBounds
    {runtimeConstant radius eps N s0 q overhead : Real}
    {n J hot : Nat}
    (coldMean hotMean : Nat → Real)
    (hcold :
      (∑ i ∈ Finset.range (coldPhases n s0), coldMean i) ≤
        overhead * (2 * (coldPhases n s0 : Real)))
    (hhot : (∑ i ∈ Finset.range hot, hotMean i) ≤
      overhead * (24 * q ^ 2 * (n : Real) ^ 2 * N * J))
    (hsourceCore :
      2 * weightedSampleNumerator n (coldPhases n s0) J * overhead *
          (2 * coldPhases n s0 +
            24 * q ^ 2 * (n : Real) ^ 2 * N * J) ≤
        sourceOneRunQueryCore runtimeConstant n radius eps) :
    2 * weightedSampleNumerator n (coldPhases n s0) J *
        ((∑ i ∈ Finset.range (coldPhases n s0), coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i) ≤
      sourceOneRunQueryCore runtimeConstant n radius eps := by
  have hsum := add_le_add hcold hhot
  have hsum' :
      (∑ i ∈ Finset.range (coldPhases n s0), coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i ≤
        overhead * (2 * coldPhases n s0 +
          24 * q ^ 2 * (n : Real) ^ 2 * N * J) := by
    calc
      _ ≤ overhead * (2 * (coldPhases n s0 : Real)) +
          overhead * (24 * q ^ 2 * (n : Real) ^ 2 * N * J) := hsum
      _ = _ := by ring
  have hnum0 : 0 ≤ 2 * weightedSampleNumerator n (coldPhases n s0) J := by
    have hnum := weightedSampleNumerator_pos n (coldPhases n s0) J
    nlinarith
  calc
    2 * weightedSampleNumerator n (coldPhases n s0) J *
        ((∑ i ∈ Finset.range (coldPhases n s0), coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i) ≤
      2 * weightedSampleNumerator n (coldPhases n s0) J *
        (overhead * (2 * coldPhases n s0 +
          24 * q ^ 2 * (n : Real) ^ 2 * N * J)) := by
            exact mul_le_mul_of_nonneg_left hsum' hnum0
    _ = 2 * weightedSampleNumerator n (coldPhases n s0) J * overhead *
        (2 * coldPhases n s0 +
          24 * q ^ 2 * (n : Real) ^ 2 * N * J) := by ring
    _ ≤ sourceOneRunQueryCore runtimeConstant n radius eps := hsourceCore

/-! ## Universal clipped-log comparison -/

/-- The final asymptotic multiplication with an explicit universal coefficient.

This is the precise way the three deterministic estimates in the source proof combine:
the weighted sample numerator and hybrid proposal core each spend one copy of
`log n * log(n/eps)`, while retry/deadline bookkeeping spends `log(1/eps)^2`.
Consequently `2*A*B*C` is a valid universal `runtimeConstant`. -/
theorem universalSourceCoreComparison
    {radius eps overhead : Real} {n cold J : Nat} {hybridCore A B C : Real}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hoverhead0 : 0 ≤ overhead) (hhybrid0 : 0 ≤ hybridCore)
    (hweighted : weightedSampleNumerator n cold J ≤
      A * sourceLogFactor n * sourceLogFactor ((n : Real) / eps))
    (hoverhead : overhead ≤ C * sourceLogFactor (1 / eps) ^ 2)
    (hhybrid : hybridCore ≤
      B * max (radius ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) *
        sourceLogFactor n * sourceLogFactor ((n : Real) / eps)) :
    2 * weightedSampleNumerator n cold J * overhead * hybridCore ≤
      sourceOneRunQueryCore (2 * A * B * C) n radius eps := by
  have hlogn : 0 ≤ sourceLogFactor n := (sourceLogFactor_pos n).le
  have hloge : 0 ≤ sourceLogFactor (1 / eps) :=
    (sourceLogFactor_pos (1 / eps)).le
  have hlogne : 0 ≤ sourceLogFactor ((n : Real) / eps) :=
    (sourceLogFactor_pos ((n : Real) / eps)).le
  have hmax : 0 ≤
      max (radius ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) := by
    exact le_max_of_le_left (by positivity)
  calc
    2 * weightedSampleNumerator n cold J * overhead * hybridCore ≤
      2 * (A * sourceLogFactor n * sourceLogFactor ((n : Real) / eps)) *
        (C * sourceLogFactor (1 / eps) ^ 2) *
        (B * max (radius ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) *
          sourceLogFactor n * sourceLogFactor ((n : Real) / eps)) := by
            gcongr
    _ = sourceOneRunQueryCore (2 * A * B * C) n radius eps := by
      unfold sourceOneRunQueryCore
      ring

/-- Cold/hot source shape with the runtime constant chosen explicitly from three
universal schedule coefficients. -/
theorem coldHotShape_of_universalLogBounds
    {radius eps N s0 q overhead A B C : Real} {n J hot : Nat}
    (coldMean hotMean : Nat → Real)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hoverhead0 : 0 ≤ overhead)
    (hcold :
      (∑ i ∈ Finset.range (coldPhases n s0), coldMean i) ≤
        overhead * (2 * (coldPhases n s0 : Real)))
    (hhot : (∑ i ∈ Finset.range hot, hotMean i) ≤
      overhead * (24 * q ^ 2 * (n : Real) ^ 2 * N * J))
    (hweighted : weightedSampleNumerator n (coldPhases n s0) J ≤
      A * sourceLogFactor n * sourceLogFactor ((n : Real) / eps))
    (hoverhead : overhead ≤ C * sourceLogFactor (1 / eps) ^ 2)
    (hhybrid :
      2 * coldPhases n s0 + 24 * q ^ 2 * (n : Real) ^ 2 * N * J ≤
        B * max (radius ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) *
          sourceLogFactor n * sourceLogFactor ((n : Real) / eps)) :
    2 * weightedSampleNumerator n (coldPhases n s0) J *
        ((∑ i ∈ Finset.range (coldPhases n s0), coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i) ≤
      sourceOneRunQueryCore (2 * A * B * C) n radius eps := by
  apply coldHotShape_of_cancelledHybridBounds coldMean hotMean hcold hhot
  apply universalSourceCoreComparison hA hC hoverhead0
  · positivity
  · exact hweighted
  · exact hoverhead
  · exact hhybrid

/-- Source-sharp combined cold/hot arithmetic for the doubled-stream estimator.

`hcoldHotShape` is independent of the accuracy denominator: it is exactly where the
fixed-block `n^2` deadline sum and the hot-block `R^2 n^2` cancellation are combined.
The theorem supplies the complete `eps^-2` comparison to the public one-run budget. -/
theorem doubledEstimator_coldHotPhaseSum_le_sourceBudget
    {runtimeConstant radius eps : Real} {n cold hot hotChunks : Nat}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i)
    (hcoldHotShape :
      2 * weightedSampleNumerator n cold hotChunks *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) / eps ^ 2 ≤
        runtimeConstant) :
    let k := estimatorSamples n cold hotChunks eps
    (2 * k : ENNReal) * ∑ i ∈ Finset.range (cold + hot),
        coldHotPhaseMean cold hot coldMean hotMean i ≤
      sourceOneRunQueryBudget runtimeConstant n radius eps := by
  dsimp only
  let k := estimatorSamples n cold hotChunks eps
  have hk := estimatorSamples_cast_le_weighted_div_epsSq
    (cold := cold) (hotChunks := hotChunks) hn heps heps1
  have hsum0 : 0 ≤
      (∑ i ∈ Finset.range cold, coldMean i) +
        ∑ i ∈ Finset.range hot, hotMean i := by
    apply add_nonneg
    · exact Finset.sum_nonneg fun i _ ↦ hcold i
    · exact Finset.sum_nonneg fun i _ ↦ hhot i
  have hnum0 : 0 ≤ weightedSampleNumerator n cold hotChunks :=
    (weightedSampleNumerator_pos n cold hotChunks).le
  have hepsSq : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hreal : (((2 * k : Nat) : Real) *
      ∑ i ∈ Finset.range (cold + hot),
        coldHotPhaseMeanReal cold hot coldMean hotMean i) ≤
      sourceOneRunQueryEnvelope runtimeConstant n radius eps := by
    rw [sum_coldHotPhaseMeanReal]
    unfold sourceOneRunQueryEnvelope
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (2 : Real) * (k : Real) *
        ((∑ i ∈ Finset.range cold, coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i) ≤
        2 * (weightedSampleNumerator n cold hotChunks / eps ^ 2) *
        ((∑ i ∈ Finset.range cold, coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i) := by gcongr
      _ = (2 * weightedSampleNumerator n cold hotChunks *
        ((∑ i ∈ Finset.range cold, coldMean i) +
          ∑ i ∈ Finset.range hot, hotMean i)) / eps ^ 2 := by ring
      _ ≤ runtimeConstant := hcoldHotShape
  have hfinal := coldHotPhaseSum_le_sourceBudget_of_real runtimeConstant n (2 * k)
    cold hot radius eps coldMean hotMean hcold hhot hreal
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfinal

/-! ## Retained-history certificate constructor -/

/-- Close the expected-cost field of the retained-history one-run certificate using the
genuine cold/hot split.  The cold phase premise is intended for the source's fixed-block
sampler, and the hot phase premise for the radius-aware constant-`2e` Gaussian reference.
The remaining premises are distributional TV and weighted-estimator accuracy; there is no
additional runtime hypothesis after `hcoldHotShape`. -/
theorem exists_sourceReferenceTVOneRunCertificate_of_coldHotSeedPhases
    {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]
    [StandardBorelSpace Seed] [Nonempty Seed]
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (HeterogeneousHistoryState Score Seed))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (tau i)]
    (e : Nat → ENNReal) {d : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, z.1.1 ∂nu0) ≤ 0)
    (hphaseSeedTV : ∀ i,
      TVLe ((tau i).bind
        (Kernel.map (Q i) (fun y : ENNReal × (Score × Seed) ↦ y.2.2)))
        (tau (i + 1)) (e i))
    {runtimeConstant radius eps : Real} {dim cold hot hotChunks : Nat}
    (hn : 1 ≤ dim) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i)
    (hphaseCost : ∀ i,
      (∫⁻ x, heterogeneousStepMean (Q i) x ∂tau i) ≤
        coldHotPhaseMean cold hot coldMean hotMean i)
    (hcoldHotShape :
      2 * weightedSampleNumerator dim cold hotChunks *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) / eps ^ 2 ≤
        runtimeConstant)
    (value :
      (Fin (2 * estimatorSamples dim cold hotChunks eps) →
        HeterogeneousHistoryState Score Seed) → Real)
    (hvalue : Measurable value) {lo hi : Real}
    (herror :
      (2 * estimatorSamples dim cold hotChunks eps : ENNReal) *
          (d + ∑ i ∈ Finset.range (cold + hot), e i) ≤
        ENNReal.ofReal (1 / 40 : Real))
    (haccuracy : 4 / 5 ≤
      (Measure.pi (fun _ : Fin (2 * estimatorSamples dim cold hotChunks eps) ↦
        retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i) mu0
          (cold + hot))).real
      {omega | value omega ∈ Icc lo hi}) :
    ∃ reference : Measure
        (Fin (2 * estimatorSamples dim cold hotChunks eps) →
          HeterogeneousHistoryState Score Seed),
      SourceReferenceTVOneRunCertificate
        (Measure.pi (fun _ : Fin (2 * estimatorSamples dim cold hotChunks eps) ↦
          retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i) mu0
            (cold + hot)))
        reference (fun omega ↦ ∑ j, (omega j).1.1) value
        runtimeConstant dim radius eps lo hi := by
  have hbudget := doubledEstimator_coldHotPhaseSum_le_sourceBudget
    (runtimeConstant := runtimeConstant) (radius := radius) (n := dim)
    (cold := cold) (hot := hot) (hotChunks := hotChunks)
    hn heps heps1 coldMean hotMean hcold hhot hcoldHotShape
  have herror' :
      ((2 * estimatorSamples dim cold hotChunks eps : Nat) : ENNReal) *
          (d + ∑ i ∈ Finset.range (cold + hot), e i) ≤
        ENNReal.ofReal (1 / 40 : Real) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using herror
  have hbudget' :
      ((2 * estimatorSamples dim cold hotChunks eps : Nat) : ENNReal) *
          ∑ i ∈ Finset.range (cold + hot),
            coldHotPhaseMean cold hot coldMean hotMean i ≤
        sourceOneRunQueryBudget runtimeConstant dim radius eps := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget
  apply exists_sourceReferenceTVOneRunCertificate_of_stationarySeedPhases
    Q mu0 nu0 tau e (coldHotPhaseMean cold hot coldMean hotMean)
      (d := d) (initialBudget := 0) hinitTV hinitState hinitMean
      hphaseSeedTV hphaseCost dim (cold + hot)
      (2 * estimatorSamples dim cold hotChunks eps) value hvalue
      herror'
  · simpa only [zero_add] using hbudget'
  · exact haccuracy

#print axioms sum_coldHotPhaseMeanReal
#print axioms coldHotPhaseSum_le_sourceBudget_of_real
#print axioms estimatorSamples_cast_le_weighted_div_epsSq
#print axioms doubledEstimator_coldHotPhaseSum_le_sourceBudget
#print axioms exists_sourceReferenceTVOneRunCertificate_of_coldHotSeedPhases

end Ttc.CVColdHotReferenceCost

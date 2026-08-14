import Ttc.Exec.CVRadiusAwareReferenceCostArithmetic

/-!
# Logarithmic arithmetic for the concrete minimal score-aware warm recurrence

The operational warm budget compounds, but it occurs in the mixing theorem only under a
logarithm.  This file turns the existing exponential `ENNReal` recurrence bound into the
real logarithmic bound needed by the literal adjustable deadline.
-/

namespace Ttc.CVMinimalScoreAwareWarmLogArithmetic

open MeasureTheory Metric
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVGaussianScoreAwareConcretePhaseWitness
open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVHybridSchedule
open Ttc.CVGaussianFactorSevenAssembly
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open scoped ENNReal

/-- Real base of the exponential upper envelope for the minimal warm recurrence. -/
noncomputable def minimalWarmBaseReal (n L : Nat) : Real :=
  (L : Real) * (16 * (2 : Real) ^ (n + 1)) + 1

/-- The logarithm of the exponential recurrence is affine in the phase index. -/
noncomputable def minimalWarmLogEnvelope (n L i : Nat) : Real :=
  (i : Real) * Real.log (minimalWarmBaseReal n L) +
    Real.log (2 * Real.exp 1)

/-- Explicit log payload passed to the adjustable deadline after substituting the
minimal warm recurrence and the score-aware `eta,zeta` split. -/
noncomputable def minimalWarmDeadlineLogEnvelope
    (n L i : Nat) (share : Real) : Real :=
  minimalWarmLogEnvelope n L i +
    Real.log 2 + 2 * Real.log 32 + 3 * Real.log (1 / share)

/-- Natural deadline obtained by inserting the explicit logarithmic envelope. -/
noncomputable def minimalWarmDeadlineEnvelope
    (n L i : Nat) (delta sigmaSq share : Real) : Nat :=
  ⌈4 * 640 ^ 2 * sigmaSq * (n : Real) *
      minimalWarmDeadlineLogEnvelope n L i share /
        (delta * Real.log 2) ^ 2 + 1⌉₊ + 1

theorem minimalWarmBaseReal_pos (n L : Nat) :
    0 < minimalWarmBaseReal n L := by
  unfold minimalWarmBaseReal
  positivity

/-- `toReal` form of `minimalScoreAwareWarm_le_pow_envelope`. -/
theorem minimalScoreAwareWarm_toReal_le_pow
    {n m k L : Nat} {N s0 eps : Real} {slack boundSq : Nat → Real}
    (hN : 0 < N) (hs0 : 0 < s0)
    (hbelow : ∀ i,
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 i) ≤ N)
    (hretries : ∀ i, scoreAwareRetries m k eps slack boundSq i ≤ L)
    (i : Nat) :
    (minimalScoreAwareWarm n N s0 m k eps slack boundSq i).toReal ≤
      minimalWarmBaseReal n L ^ i * (2 * Real.exp 1) := by
  have hraw := minimalScoreAwareWarm_le_pow_envelope
    (n := n) (m := m) (k := k) (L := L) hN hs0 hbelow hretries i
  have htop :
      ((L : ENNReal) *
          (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) ^ i *
        gaussianReferenceWarm ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.pow_ne_top
      apply (ENNReal.add_ne_top).2
      constructor
      · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
          (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      · norm_num
    · exact gaussianReferenceWarm_ne_top
  have hreal := ENNReal.toReal_mono htop hraw
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add,
    ENNReal.toReal_mul, gaussianReferenceWarm_toReal] at hreal
  simp only [ENNReal.toReal_mul] at hreal
  have hpow0 : 0 ≤ (2 : Real) ^ (n + 1) := by positivity
  rw [ENNReal.toReal_ofReal hpow0] at hreal
  · simpa only [ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, minimalWarmBaseReal, Nat.cast_ofNat]
      using hreal
  all_goals finiteness

/-- Concrete affine logarithmic bound.  In particular the recurrence does not appear as
a multiplicative warm factor in the reference-query cost. -/
theorem log_minimalScoreAwareWarm_toReal_le
    {n m k L : Nat} {N s0 eps : Real} {slack boundSq : Nat → Real}
    (hN : 0 < N) (hs0 : 0 < s0)
    (hbelow : ∀ i,
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 i) ≤ N)
    (hretries : ∀ i, scoreAwareRetries m k eps slack boundSq i ≤ L)
    (i : Nat) :
    Real.log (minimalScoreAwareWarm n N s0 m k eps slack boundSq i).toReal ≤
      minimalWarmLogEnvelope n L i := by
  have href : 0 < gaussianReferenceWarm.toReal := by
    rw [gaussianReferenceWarm_toReal]
    positivity
  have hwarm : 0 <
      (minimalScoreAwareWarm n N s0 m k eps slack boundSq i).toReal := by
    have hle := gaussianReferenceWarm_le_minimalScoreAwareWarm
      n N s0 m k eps slack boundSq i
    have htop : minimalScoreAwareWarm n N s0 m k eps slack boundSq i ≠ ⊤ := by
      have hraw := minimalScoreAwareWarm_le_pow_envelope
        (n := n) (m := m) (k := k) (L := L) hN hs0 hbelow hretries i
      apply ne_top_of_le_ne_top _ hraw
      apply ENNReal.mul_ne_top
      · apply ENNReal.pow_ne_top
        apply (ENNReal.add_ne_top).2
        constructor
        · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
            (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        · norm_num
      · exact gaussianReferenceWarm_ne_top
    have := ENNReal.toReal_mono htop hle
    exact href.trans_le this
  have hpow := minimalScoreAwareWarm_toReal_le_pow
    (n := n) hN hs0 hbelow hretries i
  have hlog := Real.log_le_log hwarm hpow
  have hbase0 : minimalWarmBaseReal n L ≠ 0 :=
    (minimalWarmBaseReal_pos n L).ne'
  have href0 : 2 * Real.exp 1 ≠ 0 := by positivity
  rw [Real.log_mul (pow_ne_zero i hbase0) href0, Real.log_pow] at hlog
  unfold minimalWarmLogEnvelope
  simpa [mul_comm] using hlog

/-- Operational warmness contributes only the affine recurrence logarithm.  The other
three copies of `log (1/share)` are respectively one warm-normalization copy and two
mixing-tolerance copies. -/
theorem minimalScoreAwareWarm_deadlineLogPayload_le
    {n m k L : Nat} {N s0 eps : Real} {slack boundSq : Nat → Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j)
    (hbelow : ∀ j,
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    (hretries : ∀ j, scoreAwareRetries m k eps slack boundSq j ≤ L)
    (i : Nat) :
    let warm := minimalScoreAwareWarm n N s0 m k eps slack boundSq i
    let share := scoreAwareShare m k eps slack boundSq i
    Real.log (((2 * warm) / scoreAwareEta m k eps slack boundSq i).toReal) +
        2 * Real.log (1 / (scoreAwareZeta m k eps slack boundSq i).toReal) ≤
      minimalWarmDeadlineLogEnvelope n L i share := by
  dsimp only
  let warm := minimalScoreAwareWarm n N s0 m k eps slack boundSq i
  let share := scoreAwareShare m k eps slack boundSq i
  have hshare : 0 < share := scoreAwareShare_pos heps hslack hbound i
  have hshare0 : 0 ≤ share := hshare.le
  have hshare32 : 0 ≤ share / 32 := by positivity
  have hlogwarm := log_minimalScoreAwareWarm_toReal_le
    (n := n) (L := L) hN hs0 hbelow hretries i
  have hwarm : 0 < warm.toReal := by
    have href : 0 < gaussianReferenceWarm.toReal := by
      rw [gaussianReferenceWarm_toReal]
      positivity
    have hle := gaussianReferenceWarm_le_minimalScoreAwareWarm
      n N s0 m k eps slack boundSq i
    have htop : warm ≠ ⊤ := by
      have hraw := minimalScoreAwareWarm_le_pow_envelope
        (n := n) (m := m) (k := k) (L := L) hN hs0 hbelow hretries i
      apply ne_top_of_le_ne_top _ hraw
      apply ENNReal.mul_ne_top
      · apply ENNReal.pow_ne_top
        apply (ENNReal.add_ne_top).2
        constructor
        · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
            (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        · norm_num
      · exact gaussianReferenceWarm_ne_top
    exact href.trans_le (ENNReal.toReal_mono htop hle)
  change Real.log (((2 * warm) / ENNReal.ofReal share).toReal) +
      2 * Real.log (1 / (ENNReal.ofReal (share / 32)).toReal) ≤ _
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hshare0, ENNReal.toReal_ofReal hshare32]
  have htwo : (2 : Real) ≠ 0 := by norm_num
  have hthirtytwo : (32 : Real) ≠ 0 := by norm_num
  have hwarm0 : warm.toReal ≠ 0 := hwarm.ne'
  have hshareNe : share ≠ 0 := hshare.ne'
  rw [Real.log_div (mul_ne_zero htwo hwarm0) hshareNe,
    Real.log_mul htwo hwarm0]
  have honeShare : (1 / share : Real) ≠ 0 := one_div_ne_zero hshareNe
  have hshareDiv : share / 32 ≠ 0 := div_ne_zero hshareNe hthirtytwo
  rw [show 1 / (share / 32) = 32 * (1 / share) by field_simp,
    Real.log_mul hthirtytwo honeShare]
  have hlogInv : Real.log (1 / share) = -Real.log share := by
    rw [one_div, Real.log_inv]
  rw [hlogInv]
  unfold minimalWarmDeadlineLogEnvelope
  linarith

/-- The literal adjustable deadline of the concrete minimal recurrence is bounded by the
closed logarithmic expression. -/
theorem adjustableSpeedyDeadline_minimalWarm_le
    {n m k L : Nat} {N s0 eps delta : Real}
    {sigmaSq slack boundSq : Nat → Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps) (hdelta : delta ≠ 0)
    (hsigma : ∀ j, 0 ≤ sigmaSq j)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j)
    (hbelow : ∀ j,
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    (hretries : ∀ j, scoreAwareRetries m k eps slack boundSq j ≤ L)
    (i : Nat) :
    adjustableSpeedyDeadline n delta (sigmaSq i)
        ((2 * minimalScoreAwareWarm n N s0 m k eps slack boundSq i) /
          scoreAwareEta m k eps slack boundSq i)
        (scoreAwareZeta m k eps slack boundSq i) ≤
      minimalWarmDeadlineEnvelope n L i delta (sigmaSq i)
        (scoreAwareShare m k eps slack boundSq i) := by
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  have hpayload := minimalScoreAwareWarm_deadlineLogPayload_le
    (n := n) (L := L) hN hs0 heps hslack hbound hbelow hretries i
  have hcoef : 0 ≤ 4 * 640 ^ 2 * sigmaSq i * (n : Real) := by
    have hsi := hsigma i
    positivity
  have hden : 0 < (delta * Real.log 2) ^ 2 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact sq_pos_of_ne_zero (mul_ne_zero hdelta hlog2.ne')
  unfold adjustableSpeedyDeadlineExpression
  simpa only [add_comm] using add_le_add_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpayload hcoef) hden.le) 1

/-- The concrete minimal recurrence discharges the literal retry/deadline sum up to a
fully explicit finite sum.  This is the strongest deterministic statement available
before relating score shares and phase variances to the hybrid geometry. -/
theorem scoreAwareRetryDeadlineAccounting_minimalWarm_le
    {n m k L : Nat} {N s0 eps delta : Real}
    {sigmaSq slack boundSq : Nat → Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps) (hdelta : delta ≠ 0)
    (hsigma : ∀ j, 0 ≤ sigmaSq j)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j)
    (hbelow : ∀ j,
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    (hretries : ∀ j, scoreAwareRetries m k eps slack boundSq j ≤ L) :
    Ttc.CVRadiusAwareReferenceCostArithmetic.scoreAwareRetryDeadlineAccounting
        n m k eps delta sigmaSq slack boundSq
          (minimalScoreAwareWarm n N s0 m k eps slack boundSq) ≤
      ∑ i ∈ Finset.range m,
        if i + 1 < m then
          (L : Real) *
            minimalWarmDeadlineEnvelope n L i delta (sigmaSq i)
              (scoreAwareShare m k eps slack boundSq i)
        else 0 := by
  unfold Ttc.CVRadiusAwareReferenceCostArithmetic.scoreAwareRetryDeadlineAccounting
  apply Finset.sum_le_sum
  intro i hi
  split_ifs
  · have hr : (scoreAwareRetries m k eps slack boundSq i : Real) ≤ L := by
      exact_mod_cast hretries i
    have hd := adjustableSpeedyDeadline_minimalWarm_le
      (n := n) (m := m) (k := k) (L := L) hN hs0 heps hdelta
      hsigma hslack hbound hbelow hretries i
    have hdR : (adjustableSpeedyDeadline n delta (sigmaSq i)
        ((2 * minimalScoreAwareWarm n N s0 m k eps slack boundSq i) /
          scoreAwareEta m k eps slack boundSq i)
        (scoreAwareZeta m k eps slack boundSq i) : Real) ≤
      minimalWarmDeadlineEnvelope n L i delta (sigmaSq i)
        (scoreAwareShare m k eps slack boundSq i) := by
      exact_mod_cast hd
    have hr0 : (0 : Real) ≤ scoreAwareRetries m k eps slack boundSq i := by
      positivity
    have hd0 : (0 : Real) ≤ adjustableSpeedyDeadline n delta (sigmaSq i)
        ((2 * minimalScoreAwareWarm n N s0 m k eps slack boundSq i) /
          scoreAwareEta m k eps slack boundSq i)
        (scoreAwareZeta m k eps slack boundSq i) := by
      positivity
    exact mul_le_mul hr hdR hd0 (by positivity)
  · exact le_rfl

/-! ## Fixed `C = 3` share gap -/

/-- A nondecreasing positive variance schedule makes every consecutive partition-function
ratio at least one, including the terminal Gaussian-to-uniform step. -/
theorem one_le_chain_ratio_of_sigmaSq_le_succ
    {d m i : Nat} {sigmaSq : Nat → Real}
    {K : Set (EuclideanSpace Real (Fin d))}
    (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hball : Metric.ball (0 : EuclideanSpace Real (Fin d)) 1 ⊆ K)
    (hsigma : ∀ j, 0 < sigmaSq j) (hmono : sigmaSq i ≤ sigmaSq (i + 1)) :
    1 ≤ chain m sigmaSq K (i + 1) / chain m sigmaSq K i := by
  have hchain : chain m sigmaSq K i ≤ chain m sigmaSq K (i + 1) := by
    have hraw := chain_le_mul_of_forall_le (m := m) hKm hfin
      (hsigma i) (hsigma (i + 1))
      (B := (1 : Real)) (i := i) (j := i + 1) (fun x hx ↦ ?_)
    · simpa only [one_mul] using hraw
    · by_cases hi1 : i + 1 < m
      · rw [coolWeight_of_lt hi1, coolWeight_of_lt (Nat.lt_of_succ_lt hi1)]
        simp only [one_mul]
        apply Real.exp_le_exp.2
        have hrecip : 1 / sigmaSq (i + 1) ≤ 1 / sigmaSq i :=
          one_div_le_one_div_of_le (hsigma i) hmono
        have hnorm : 0 ≤ ‖x‖ ^ 2 / 2 := by positivity
        calc
          -‖x‖ ^ 2 / (2 * sigmaSq i) =
              -(‖x‖ ^ 2 / 2) * (1 / sigmaSq i) := by ring
          _ ≤ -(‖x‖ ^ 2 / 2) * (1 / sigmaSq (i + 1)) :=
            mul_le_mul_of_nonpos_left hrecip (neg_nonpos.mpr hnorm)
          _ = -‖x‖ ^ 2 / (2 * sigmaSq (i + 1)) := by ring
      · by_cases hi : i < m
        · rw [coolWeight_of_ge (not_lt.1 hi1), coolWeight_of_lt hi]
          simp only [one_mul]
          apply Real.exp_le_one_iff.mpr
          exact div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg ‖x‖))
            (mul_nonneg (by norm_num) (hsigma i).le)
        · rw [coolWeight_of_ge (not_lt.1 hi),
            coolWeight_of_ge (not_lt.1 hi1)]
          norm_num
  rw [le_div_iff₀ (chain_pos hsigma hball hfin i), one_mul]
  exact hchain

/-- The local radius hypothesis used by the adjustable Gaussian sampler bounds the
transport exponent by `q² n / 2`. -/
theorem radius_sq_div_two_sigmaSq_le
    {n : Nat} {R q sigmaSq : Real}
    (hR : 0 ≤ R) (hq : 0 ≤ q) (hsigma : 0 < sigmaSq)
    (hRsigma : R ≤ q * Real.sqrt sigmaSq * Real.sqrt n) :
    R ^ 2 / (2 * sigmaSq) ≤ q ^ 2 * (n : Real) / 2 := by
  have hsqrtSigma : Real.sqrt sigmaSq ^ 2 = sigmaSq :=
    Real.sq_sqrt hsigma.le
  have hsqrtN : Real.sqrt (n : Real) ^ 2 = (n : Real) :=
    Real.sq_sqrt (by positivity)
  have hright : 0 ≤ q * Real.sqrt sigmaSq * Real.sqrt n := by positivity
  have hsq : R ^ 2 ≤ (q * Real.sqrt sigmaSq * Real.sqrt n) ^ 2 :=
    (sq_le_sq₀ hR hright).2 hRsigma
  have hsq' : R ^ 2 ≤ q ^ 2 * sigmaSq * (n : Real) := by
    calc
      R ^ 2 ≤ (q * Real.sqrt sigmaSq * Real.sqrt n) ^ 2 := hsq
      _ = q ^ 2 * Real.sqrt sigmaSq ^ 2 * Real.sqrt n ^ 2 := by ring
      _ = q ^ 2 * sigmaSq * (n : Real) := by rw [hsqrtSigma, hsqrtN]
  rw [div_le_iff₀ (by positivity : 0 < 2 * sigmaSq)]
  calc
    R ^ 2 ≤ q ^ 2 * sigmaSq * (n : Real) := hsq'
    _ = q ^ 2 * (n : Real) / 2 * (2 * sigmaSq) := by ring

/-- The literal all-phase adjustable-Gaussian route cannot be instantiated on the source
hybrid schedule: already in dimension one, at the source cold start `s0=1/16`, the local
radius premise fails for the benign choices `R=1,q=2`.  The cold block therefore needs its
separate fixed-block sampler/cost analysis; it cannot be charged through the hot Gaussian
`hRsigma` route. -/
theorem not_sourceColdStart_localRadiusCondition :
    ¬ (1 : Real) ≤
      2 * Real.sqrt (sigmaSq 1 1 (1 / 16) 0) * Real.sqrt 1 := by
  have hcold0 : 0 < coldPhases 1 (1 / 16 : Real) := by
    unfold coldPhases
    apply Nat.ceil_pos.2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
    norm_num only [Nat.cast_one, one_div, inv_inv, one_add_one_eq_two, max_eq_left]
    positivity
  have hsigma0 : sigmaSq 1 1 (1 / 16) 0 = (1 / 16 : Real) := by
    rw [sigmaSq, if_pos hcold0]
    simp [geomSchedule]
  have hsqrt16 : Real.sqrt (16 : Real) = 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 16),
      Real.sqrt_nonneg (16 : Real)]
  have hsqrt : Real.sqrt (1 / 16 : Real) = 1 / 4 := by
    rw [one_div, Real.sqrt_inv, hsqrt16]
    norm_num [one_div]
  rw [hsigma0, hsqrt]
  norm_num

/-- The fixed phase factor `C=3` turns the moment slack into a literal factor four.
Given the two geometric inequalities actually needed by the arithmetic (a lower bound on
the chain ratio and an upper bound on the transport exponent), this yields a closed lower
bound for the selected score-aware share. -/
theorem min_blockShare_transportFloor_le_scoreAwareShare_three
    {d m k chainLength : Nat} {eps R A : Real}
    {sigmaSq : Nat → Real} {K : Set (EuclideanSpace Real (Fin d))} {i : Nat}
    (hratio : 1 ≤ chain chainLength sigmaSq K (i + 1) /
      chain chainLength sigmaSq K i)
    (hexponent : R ^ 2 / (2 * sigmaSq i) ≤ A) :
    min (Ttc.CVGaussianBlockRetryParameters.blockShare m k eps)
        (4 / (45 * Real.exp A ^ 2)) ≤
      scoreAwareShare m k eps
        (phaseMomentSlackSeven chainLength sigmaSq K (fun _ ↦ 3))
        (phaseScoreTransportBoundSqSeven R sigmaSq) i := by
  unfold scoreAwareShare
  apply le_min
  · exact min_le_left _ _
  · refine (min_le_right _ _).trans ?_
    rw [phaseMomentSlackSeven_three]
    unfold phaseScoreTransportBoundSqSeven
    norm_num only [Nat.cast_ofNat]
    have he : Real.exp (R ^ 2 / (2 * sigmaSq i)) ≤ Real.exp A :=
      Real.exp_le_exp.2 hexponent
    have he0 : 0 < Real.exp (R ^ 2 / (2 * sigmaSq i)) := Real.exp_pos _
    have heA0 : 0 < Real.exp A := Real.exp_pos _
    have hr2 : 1 ≤
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2 := by nlinarith
    rw [show 3 * (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * 15) =
      45 * Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 by ring]
    rw [div_le_div_iff₀ (by positivity : 0 < 45 * Real.exp A ^ 2)
      (by positivity : 0 < 45 * Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2)]
    have he2 : Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 ≤
        Real.exp A ^ 2 := by nlinarith
    nlinarith

/-- End-to-end adapter for the concrete minimal recurrence.  All operational-warm
arithmetic is discharged; `hgeometry` is exactly the remaining phase-geometry sum and
`hsource` is the final source-shape comparison. -/
theorem sharpReferencePhaseSum_estimatorSamples_minimalWarm_le_sourceBudget
    {runtimeConstant radius : Real} {n J L : Nat} (hn : 1 ≤ n)
    {N s0 eps q delta overhead : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hdelta : delta ≠ 0)
    (hbelowJ : ∀ j, j < J → adaptiveChunkStart N (coldEnd n s0) j ≤ N)
    (m : Nat) (sigmaSq slack boundSq : Nat → Real)
    (hsigma : ∀ j, 0 ≤ sigmaSq j)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j)
    (hbelowAll : ∀ j,
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) ≤ N)
    (hretries : ∀ j,
      scoreAwareRetries m
        (estimatorSamples n (coldPhases n s0) J eps)
        eps slack boundSq j ≤ L)
    (hoverhead0 : 0 ≤ overhead)
    (hgeometry :
      (∑ i ∈ Finset.range m,
          (if i + 1 < m then
            (L : Real) *
              (minimalWarmDeadlineEnvelope n L i delta (sigmaSq i)
                (scoreAwareShare m
                  (estimatorSamples n (coldPhases n s0) J eps)
                  eps slack boundSq i) : Real)
          else 0)) ≤
        overhead *
          Ttc.CVRadiusAwareReferenceCostArithmetic.sourceHybridProposalCore
            n N s0 J q)
    (hsource : 10 * (2 * Real.exp 1) * overhead *
        Ttc.CVHybridSourceSharpEnvelope.sourceSharpProposalEnvelope
          n N s0 eps J 1 q ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryEnvelope
        runtimeConstant n radius eps) :
    let k := estimatorSamples n (coldPhases n s0) J eps
    (k : ENNReal) * ∑ i ∈ Finset.range m,
        Ttc.CVGaussianSourceSharpCost.gaussianActiveMeanEnvelope m
          (fun _ ↦ gaussianReferenceWarm)
          (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq
            (minimalScoreAwareWarm n N s0 m k eps slack boundSq))
          (scoreAwareRetries m k eps slack boundSq) i ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n radius eps := by
  let k := estimatorSamples n (coldPhases n s0) J eps
  have hsum := scoreAwareRetryDeadlineAccounting_minimalWarm_le
    (n := n) (m := m) (k := k) (L := L) hN hs0 heps hdelta
    hsigma hslack hbound hbelowAll hretries
  have hweighted :
      Ttc.CVRadiusAwareReferenceCostArithmetic.scoreAwareRetryDeadlineAccounting
          n m k eps delta sigmaSq slack boundSq
            (minimalScoreAwareWarm n N s0 m k eps slack boundSq) ≤
        overhead *
          Ttc.CVRadiusAwareReferenceCostArithmetic.sourceHybridProposalCore
            n N s0 J q := hsum.trans hgeometry
  exact Ttc.CVRadiusAwareReferenceCostArithmetic.sharpReferencePhaseSum_estimatorSamples_le_sourceBudget
      hn hN hs0 heps heps1
      hbelowJ m sigmaSq slack boundSq
      (minimalScoreAwareWarm n N s0 m k eps slack boundSq)
      hoverhead0 hweighted hsource

#print axioms minimalScoreAwareWarm_toReal_le_pow
#print axioms log_minimalScoreAwareWarm_toReal_le
#print axioms minimalScoreAwareWarm_deadlineLogPayload_le
#print axioms adjustableSpeedyDeadline_minimalWarm_le
#print axioms scoreAwareRetryDeadlineAccounting_minimalWarm_le
#print axioms one_le_chain_ratio_of_sigmaSq_le_succ
#print axioms radius_sq_div_two_sigmaSq_le
#print axioms not_sourceColdStart_localRadiusCondition
#print axioms min_blockShare_transportFloor_le_scoreAwareShare_three
#print axioms sharpReferencePhaseSum_estimatorSamples_minimalWarm_le_sourceBudget

end Ttc.CVMinimalScoreAwareWarmLogArithmetic

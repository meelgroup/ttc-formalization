/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Volume.CVHybridParameters
import Ttc.Volume.CVHybridRuntimeAccounting
import Arlib.MarkovChains.Continuous.SamplerStepCount

/-!
# Source-sharp sample and proposal envelope for the hybrid CV schedule

The source algorithm uses the same sample count in every phase, but that count is charged
against the *weighted* variance budget: `2*coldPhases/n` for the cold block and one constant
per hot doubling chunk.  It is therefore proportional to

`(coldPhases/n + numberOfHotChunks) / eps^2`,

not to the total number of phases.  This file records that distinction at the deterministic
accounting layer and gives the missing elementary logarithmic witness for the number of hot
chunks.

This is the arithmetic route used by `CVHybridExactAccuracy`.  It does not turn the
independently restarted exact-law construction into a sequential sampler; that separate
execution/dependence issue is intentionally not hidden here.
-/

namespace Ttc.CVHybridSourceSharpEnvelope

open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive Ttc.CVAdaptive Ttc.CVHybridSchedule
open Ttc.CVCorrected

/-- Any dyadic exponent whose variance already reaches the target bounds the first terminal
chunk.  This is the exact deterministic form of "there are logarithmically many hot
chunks"; a caller may instantiate `q` by a ceiling of a base-two logarithm. -/
theorem adaptiveTerminalChunk_le_of_target_le_pow_two_mul
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0) {q : Nat}
    (hq : N <= (2 : Real) ^ q * s0) :
    adaptiveTerminalChunk N s0 <= q := by
  have htarget : N <= adaptiveChunkStart N s0 q :=
    hq.trans (pow_two_mul_le_adaptiveChunkStart hN hs0 q)
  have hex := exists_target_le_adaptiveChunkStart hN hs0
  rw [adaptiveTerminalChunk, dif_pos hex]
  exact Nat.find_min' hex htarget

/-- Once the cold block has reached variance one, `N <= 2^q` is enough to stop the hot
schedule by chunk `q`. -/
theorem hybrid_terminalChunk_le_of_target_le_pow_two
    {n : Nat} (hn : 1 <= n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hs01 : s0 <= 1) {q : Nat}
    (hq : N <= (2 : Real) ^ q) :
    adaptiveTerminalChunk N (coldEnd n s0) <= q := by
  have hend0 : 0 < coldEnd n s0 := coldEnd_pos hn hs0
  have hend1 : 1 <= coldEnd n s0 := one_le_coldEnd hn hs0 hs01
  apply adaptiveTerminalChunk_le_of_target_le_pow_two_mul hN hend0
  calc
    N <= (2 : Real) ^ q := hq
    _ <= (2 : Real) ^ q * coldEnd n s0 := by
      have hpow : 0 <= (2 : Real) ^ q := by positivity
      nlinarith

/-- The ceiling in the concrete exact-law hybrid estimator adds less than two to its real
threshold. -/
theorem estimatorSamples_cast_lt (n c J : Nat) {eps : Real} (_heps : 0 < eps) :
    (estimatorSamples n c J eps : Real) <
      estimatorSampleThreshold n c J eps + 2 := by
  have hthreshold : 0 <= estimatorSampleThreshold n c J eps := by
    unfold estimatorSampleThreshold
    exact le_max_of_le_left (by norm_num)
  have hceil := Nat.ceil_lt_add_one hthreshold
  rw [estimatorSamples]
  push_cast
  linarith

/-- Source-shaped bound for the exact-law sample count.  The two schedule statistics are
`c/n` and `J`; the total phase count does not occur. -/
theorem estimatorSamples_lt_weighted
    {n c J : Nat} (hn : 1 <= n) {eps : Real}
    (heps : 0 < eps) (heps1 : eps <= 1) :
    (estimatorSamples n c J eps : Real) <
      44 + (160 * (c : Real) / (n : Real) + 560 * (J : Real)) / eps ^ 2 := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hV : eps ^ 2 / 10 <= Arlib.GaussianCooling.varBudget eps := by
    have hx0 : 0 <= eps ^ 2 / 5 := by positivity
    have hx1 : eps ^ 2 / 5 <= 1 := by nlinarith [sq_nonneg (eps - 1)]
    have hlog := Arlib.GaussianCooling.half_le_log_one_add hx0 hx1
    rw [Arlib.GaussianCooling.varBudget]
    nlinarith
  have hVpos : 0 < Arlib.GaussianCooling.varBudget eps :=
    Arlib.GaussianCooling.varBudget_pos heps
  have hinv : 1 / Arlib.GaussianCooling.varBudget eps <= 40 / eps ^ 2 := by
    rw [div_le_div_iff₀ hVpos heps2]
    nlinarith
  have hA : 4 * (c : Real) /
      ((n : Real) * Arlib.GaussianCooling.varBudget eps) <=
      (160 * (c : Real) / (n : Real)) / eps ^ 2 := by
    calc
      4 * (c : Real) / ((n : Real) * Arlib.GaussianCooling.varBudget eps) =
          (4 * (c : Real) / (n : Real)) *
            (1 / Arlib.GaussianCooling.varBudget eps) := by ring
      _ <= (4 * (c : Real) / (n : Real)) * (40 / eps ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (160 * (c : Real) / (n : Real)) / eps ^ 2 := by ring
  have hB : 14 * (J : Real) / Arlib.GaussianCooling.varBudget eps <=
      (560 * (J : Real)) / eps ^ 2 := by
    calc
      14 * (J : Real) / Arlib.GaussianCooling.varBudget eps =
          (14 * (J : Real)) * (1 / Arlib.GaussianCooling.varBudget eps) := by ring
      _ <= (14 * (J : Real)) * (40 / eps ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (560 * (J : Real)) / eps ^ 2 := by ring
  have hsum0 : 0 <=
      (160 * (c : Real) / (n : Real) + 560 * (J : Real)) / eps ^ 2 := by
    positivity
  have hthreshold : estimatorSampleThreshold n c J eps <=
      42 + (160 * (c : Real) / (n : Real) + 560 * (J : Real)) / eps ^ 2 := by
    unfold estimatorSampleThreshold
    apply max_le
    · exact le_add_of_nonneg_right hsum0
    · apply max_le
      · exact hA.trans (by
          exact div_le_div_of_nonneg_right
            (le_add_of_nonneg_right (by positivity)) heps2.le) |>.trans
          (le_add_of_nonneg_left (by norm_num))
      · exact hB.trans (by
          exact div_le_div_of_nonneg_right
            (le_add_of_nonneg_left (by positivity)) heps2.le) |>.trans
          (le_add_of_nonneg_left (by norm_num))
  have hk := estimatorSamples_cast_lt n c J heps
  calc
    (estimatorSamples n c J eps : Real) <
        estimatorSampleThreshold n c J eps + 2 := hk
    _ <= 44 +
        (160 * (c : Real) / (n : Real) + 560 * (J : Real)) / eps ^ 2 := by
      linarith

/-! ## Exact boundary with the corrected sequential theorem -/

/-- If the source-sharp sample count is fed to the currently formalized corrected
sequential theorem, its `CorrectedSampleBudget` forces this additional phase-count
inequality.  The right side depends only on the weighted cold/chunk statistics, while the
left side depends on every phase.  This is the precise extra premise absent from the
source's sharp variance-product analysis. -/
theorem correctedBudget_estimatorSamples_forces_phase_bound
    {n c J m : Nat} (hn : 1 <= n) {eps : Real}
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hk : CorrectedSampleBudget m (estimatorSamples n c J eps) eps) :
    100000 * ((m : Real) + 1) <
      (44 + (160 * (c : Real) / (n : Real) + 560 * (J : Real)) / eps ^ 2) *
        eps ^ 2 := by
  have hkUpper := estimatorSamples_lt_weighted (c := c) (J := J) hn heps heps1
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  unfold CorrectedSampleBudget at hk
  exact hk.trans_lt (mul_lt_mul_of_pos_right hkUpper heps2)

/-- Conversely, failure of that forced inequality is a compiled certificate that the
current corrected sequential theorem cannot accept the source-sharp exact-law sample
count. -/
theorem not_correctedBudget_estimatorSamples_of_phase_bound
    {n c J m : Nat} (hn : 1 <= n) {eps : Real}
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hlarge :
      (44 + (160 * (c : Real) / (n : Real) + 560 * (J : Real)) / eps ^ 2) *
          eps ^ 2 <= 100000 * ((m : Real) + 1)) :
    ¬ CorrectedSampleBudget m (estimatorSamples n c J eps) eps := by
  intro hk
  have hforced := correctedBudget_estimatorSamples_forces_phase_bound
    (c := c) (J := J) hn heps heps1 hk
  linarith

/-- Deterministic source proposal envelope using the exact-law weighted sample count.
Compared with `correctedSourceProposalEnvelope`, there is no extra copy of the total phase
count inside `k`. -/
noncomputable def sourceSharpProposalEnvelope
    (n : Nat) (N s0 eps : Real) (J r : Nat) (q : Real) : Real :=
  (r : Real) *
    (44 + (160 * (coldPhases n s0 : Real) / (n : Real) +
      560 * (J : Real)) / eps ^ 2) *
    (2 * coldPhases n s0 + 24 * q ^ 2 * (n : Real) ^ 2 * N * J)

/-- The source hybrid accounting with concrete exact-law samples fits the weighted
`eps^-2` envelope. -/
theorem proposalAccounting_estimatorSamples_le_sourceSharp
    {n J r : Nat} (hn : 1 <= n) {N s0 eps q : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps) (heps1 : eps <= 1)
    (hbelow : ∀ j, j < J → adaptiveChunkStart N (coldEnd n s0) j <= N) :
    proposalAccounting n N s0 J
        (estimatorSamples n (coldPhases n s0) J eps) r q <=
      sourceSharpProposalEnvelope n N s0 eps J r q := by
  have haccount := proposalAccounting_le (n := n) (J := J)
    (k := estimatorSamples n (coldPhases n s0) J eps) (r := r)
    (q := q) hn hN hs0 hbelow
  have hk := estimatorSamples_lt_weighted (c := coldPhases n s0) (J := J)
    hn heps heps1
  have hr : 0 <= (r : Real) := by positivity
  have hphase : 0 <=
      2 * (coldPhases n s0 : Real) +
        24 * q ^ 2 * (n : Real) ^ 2 * N * J := by
    positivity
  unfold sourceSharpProposalEnvelope
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hk.le hphase) hr
  exact haccount.trans (by simpa only [mul_assoc] using hmul)

end Ttc.CVHybridSourceSharpEnvelope

#print axioms Ttc.CVHybridSourceSharpEnvelope.adaptiveTerminalChunk_le_of_target_le_pow_two_mul
#print axioms Ttc.CVHybridSourceSharpEnvelope.hybrid_terminalChunk_le_of_target_le_pow_two
#print axioms Ttc.CVHybridSourceSharpEnvelope.estimatorSamples_lt_weighted
#print axioms Ttc.CVHybridSourceSharpEnvelope.correctedBudget_estimatorSamples_forces_phase_bound
#print axioms Ttc.CVHybridSourceSharpEnvelope.not_correctedBudget_estimatorSamples_of_phase_bound
#print axioms Ttc.CVHybridSourceSharpEnvelope.proposalAccounting_estimatorSamples_le_sourceSharp

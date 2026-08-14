/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVCorrectedParameters
import Ttc.Volume.CVRunwiseTailParameters

/-!
# Source runtime arithmetic after corrected `lem:accuracy`

This file records the deterministic accounting in the paragraph following the
source's accuracy lemma, using the repository's *actual* adaptive chunks and
their integer phase counts.  It intentionally separates this arithmetic from
an execution-cost claim: the latter still needs the path/cost-composition seam
documented in `CVOperationalRuntime` and `SequentialWarmCostSeam`.

The source calls phases with variance at most one "cold".  This is only an
accounting partition here.  The repository's proved direct ambient rejection
branch is smaller, namely `4*n*σ² ≤ 1`; no constant rejection cost is asserted
for all phases in the source-cold partition.
-/

namespace Ttc.CVCorrectedRuntime

open MeasureTheory
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive Ttc.CVAdaptive

/-- Number of actual, integer-indexed phases in the source-cold (`σ² ≤ 1`)
part of the first `J` adaptive chunks. -/
noncomputable def adaptiveSourceColdPhases (N s0 : ℝ) (J : ℕ) : ℕ :=
  ∑ j ∈ Finset.range J,
    ((Finset.range (adaptiveChunkPhases N s0 j)).filter fun t =>
      geomSchedule (adaptiveChunkStart N s0 j) (adaptiveChunkRate N s0 j) t ≤ 1).card

/-- Sum of the actual phase variances in the source-hot (`1 < σ²`) part. -/
noncomputable def adaptiveSourceHotSigmaMass (N s0 : ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J,
    ∑ t ∈ Finset.range (adaptiveChunkPhases N s0 j),
      if 1 < geomSchedule (adaptiveChunkStart N s0 j) (adaptiveChunkRate N s0 j) t then
        geomSchedule (adaptiveChunkStart N s0 j) (adaptiveChunkRate N s0 j) t else 0

/-- The source-cold partition contains no more phases than the actual adaptive
schedule. -/
theorem adaptiveSourceColdPhases_le_total (N s0 : ℝ) (J : ℕ) :
    adaptiveSourceColdPhases N s0 J ≤ adaptiveTotalPhases N s0 J := by
  unfold adaptiveSourceColdPhases adaptiveTotalPhases
  apply Finset.sum_le_sum
  intro j hj
  simpa using Finset.card_le_card (Finset.filter_subset
    (fun t : ℕ => geomSchedule (adaptiveChunkStart N s0 j)
      (adaptiveChunkRate N s0 j) t ≤ 1)
    (Finset.range (adaptiveChunkPhases N s0 j)))

/-- Inside one actual chunk, the sum of all local phase variances is bounded by
twice the chunk start times the integer phase count. -/
theorem sum_chunk_sigmaSq_le_mul_phases {N s0 : ℝ} (hN : 0 < N) (hs0 : 0 < s0)
    (j : ℕ) :
    (∑ t ∈ Finset.range (adaptiveChunkPhases N s0 j),
      geomSchedule (adaptiveChunkStart N s0 j) (adaptiveChunkRate N s0 j) t) ≤
      (adaptiveChunkPhases N s0 j : ℝ) * (2 * adaptiveChunkStart N s0 j) := by
  calc
    _ ≤ ∑ _t ∈ Finset.range (adaptiveChunkPhases N s0 j),
        2 * adaptiveChunkStart N s0 j := by
      exact Finset.sum_le_sum fun t ht =>
        (adaptiveChunk_phase_lt_two hN hs0 (Finset.mem_range.mp ht)).le
    _ = _ := by simp

/-- Exact integer-phase version of the hot-chunk cancellation.  The ceiling
correction changes the paper's `4N` to the safe bound `6N`:

`(# phases in chunk j) * (maximum σ² in j) ≤ 6N`.
-/
theorem sum_chunk_sigmaSq_le_six_mul {N s0 : ℝ} (hN : 0 < N) (hs0 : 0 < s0)
    {j : ℕ} (hjN : adaptiveChunkStart N s0 j ≤ N) :
    (∑ t ∈ Finset.range (adaptiveChunkPhases N s0 j),
      geomSchedule (adaptiveChunkStart N s0 j) (adaptiveChunkRate N s0 j) t) ≤ 6 * N := by
  have hs := adaptiveChunkStart_pos hN hs0 j
  have hphase : (adaptiveChunkPhases N s0 j : ℝ) ≤
      2 * N / adaptiveChunkStart N s0 j + 1 := by
    have hceil := Nat.ceil_lt_add_one
      (show 0 ≤ 2 * N / adaptiveChunkStart N s0 j by positivity)
    have hcross := chunkCrossingPhases_le_ceil hN hs
    unfold adaptiveChunkPhases
    exact le_trans (by exact_mod_cast hcross) hceil.le
  calc
    _ ≤ (adaptiveChunkPhases N s0 j : ℝ) *
        (2 * adaptiveChunkStart N s0 j) := sum_chunk_sigmaSq_le_mul_phases hN hs0 j
    _ ≤ (2 * N / adaptiveChunkStart N s0 j + 1) *
        (2 * adaptiveChunkStart N s0 j) := by gcongr
    _ = 4 * N + 2 * adaptiveChunkStart N s0 j := by
      field_simp [ne_of_gt hs]
      <;> ring
    _ ≤ 6 * N := by linarith

/-- Summing the cancellation over the actual chunks gives `6*N*J`.  Filtering
to source-hot phases can only decrease this nonnegative sum. -/
theorem adaptiveSourceHotSigmaMass_le {N s0 : ℝ} (hN : 0 < N) (hs0 : 0 < s0)
    {J : ℕ} (hbelow : ∀ j < J, adaptiveChunkStart N s0 j ≤ N) :
    adaptiveSourceHotSigmaMass N s0 J ≤ 6 * N * J := by
  unfold adaptiveSourceHotSigmaMass
  calc
    _ ≤ ∑ j ∈ Finset.range J,
        ∑ t ∈ Finset.range (adaptiveChunkPhases N s0 j),
          geomSchedule (adaptiveChunkStart N s0 j) (adaptiveChunkRate N s0 j) t := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro t ht
      split_ifs
      · exact le_rfl
      · exact geomSchedule_pos (adaptiveChunkStart_pos hN hs0 j)
          (by linarith [adaptiveChunkRate_pos hN hs0 j]) t |>.le
    _ ≤ ∑ _j ∈ Finset.range J, 6 * N := by
      exact Finset.sum_le_sum fun j hj =>
        sum_chunk_sigmaSq_le_six_mul hN hs0 (hbelow j (Finset.mem_range.mp hj))
    _ = 6 * N * J := by simp [mul_comm]

/-- The source's two-part proposal accounting: charge two proposals for every
source-cold sample and `4*q²*n²*σ²` for a source-hot sample.  The factors `2`
and `4` are kept visible so a future execution theorem can identify them with
ambient rejection and ordinary-step conversion, respectively. -/
noncomputable def adaptiveSourceProposalAccounting
    (n : ℕ) (N s0 : ℝ) (J k r : ℕ) (q : ℝ) : ℝ :=
  (r : ℝ) * k *
    (2 * adaptiveSourceColdPhases N s0 J +
      4 * q ^ 2 * (n : ℝ) ^ 2 * adaptiveSourceHotSigmaMass N s0 J)

/-- Runtime cancellation with the repository's actual counts. -/
theorem adaptiveSourceProposalAccounting_le {n J k r : ℕ} {N s0 q : ℝ}
    (hN : 0 < N) (hs0 : 0 < s0)
    (hbelow : ∀ j < J, adaptiveChunkStart N s0 j ≤ N) :
    adaptiveSourceProposalAccounting n N s0 J k r q ≤
      (r : ℝ) * k *
        (2 * (4 * N / s0 + J) + 24 * q ^ 2 * (n : ℝ) ^ 2 * N * J) := by
  have hcoldNat := adaptiveSourceColdPhases_le_total N s0 J
  have hcoldCast : (adaptiveSourceColdPhases N s0 J : ℝ) ≤
      (adaptiveTotalPhases N s0 J : ℝ) := by exact_mod_cast hcoldNat
  have hcold := hcoldCast.trans (adaptiveTotalPhases_le hN hs0 J)
  have hhot := adaptiveSourceHotSigmaMass_le hN hs0 hbelow
  unfold adaptiveSourceProposalAccounting
  have hrk : 0 ≤ (r : ℝ) * k := by positivity
  apply mul_le_mul_of_nonneg_left _ hrk
  have hqcoef : 0 ≤ 4 * q ^ 2 * (n : ℝ) ^ 2 := by positivity
  calc
    2 * adaptiveSourceColdPhases N s0 J +
        4 * q ^ 2 * (n : ℝ) ^ 2 * adaptiveSourceHotSigmaMass N s0 J ≤
      2 * (4 * N / s0 + J) +
        4 * q ^ 2 * (n : ℝ) ^ 2 * (6 * N * J) := by gcongr
    _ = 2 * (4 * N / s0 + J) + 24 * q ^ 2 * (n : ℝ) ^ 2 * N * J := by ring

/-- The least convenient natural sample count satisfying the corrected
`k*eps² ≥ 100000*(m+1)` requirement, with one extra unit to make positivity
definitionally immediate. -/
noncomputable def correctedRuntimeSamples (m : ℕ) (eps : ℝ) : ℕ :=
  ⌈100000 * ((m : ℝ) + 1) / eps ^ 2⌉₊ + 1

theorem correctedRuntimeSamples_pos (m : ℕ) (eps : ℝ) :
    0 < correctedRuntimeSamples m eps := by
  simp [correctedRuntimeSamples]

theorem correctedRuntimeSamples_budget {m : ℕ} {eps : ℝ} (heps : 0 < eps) :
    Ttc.CVCorrected.CorrectedSampleBudget m (correctedRuntimeSamples m eps) eps := by
  have hceil := Nat.le_ceil (100000 * ((m : ℝ) + 1) / eps ^ 2)
  have he2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  unfold Ttc.CVCorrected.CorrectedSampleBudget correctedRuntimeSamples
  push_cast
  rw [div_le_iff₀ he2] at hceil
  nlinarith

theorem correctedRuntimeSamples_cast_lt {m : ℕ} {eps : ℝ} (heps : 0 < eps) :
    (correctedRuntimeSamples m eps : ℝ) <
      100000 * ((m : ℝ) + 1) / eps ^ 2 + 2 := by
  have harg : 0 ≤ 100000 * ((m : ℝ) + 1) / eps ^ 2 := by positivity
  have hceil := Nat.ceil_lt_add_one harg
  rw [correctedRuntimeSamples]
  push_cast
  linarith

/-- Explicit polynomial envelope in the public parameters.  It uses the
source endpoint branch (`s0=1/(16n)`), the corrected sample budget, and the
runwise median count. -/
noncomputable def correctedSourceProposalEnvelope
    (n : ℕ) (C eps p q : ℝ) : ℝ :=
  (25 / 2 * Real.log (1 / p) + 2) *
    (100000 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) / eps ^ 2 + 2) *
    (2 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) +
      24 * q ^ 2 * (n : ℝ) ^ 2 * (C ^ 2 * n) *
        (16 * C ^ 2 * (n : ℝ) ^ 2 + 2))

/-- Fully concrete source-regime proposal accounting on the repository's
adaptive schedule.  The median factor is exactly the runwise
`ceil((25/2)log(1/p))+1` construction, hence requested confidence appears only
through `log(1/p)`.

This is the strongest honest theorem before the execution-cost seam: its left
side is the explicit source accounting functional above, not a silently
invented runtime random variable.
-/
theorem corrected_adaptive_source_accounting_le_envelope
    {n : ℕ} {C eps p q : ℝ} (hn : 1 ≤ n) (hC : 0 < C)
    (heps : 0 < eps) (hp : 0 < p) (hp1 : p < 1)
    (hsource : (1 / 2 : ℝ) ^ n ≤ eps / 4) :
    let s0 := polynomialEndpointSigmaSq n (eps / 4)
    let J := adaptiveTerminalChunk (C ^ 2 * n) s0
    let m := terminalPhaseCount n C s0
    let k := correctedRuntimeSamples m eps
    let r := concreteRunwiseReps p
    adaptiveSourceProposalAccounting n (C ^ 2 * n) s0 J k r q ≤
      correctedSourceProposalEnvelope n C eps p q := by
  dsimp only
  let s0 := polynomialEndpointSigmaSq n (eps / 4)
  let N : ℝ := C ^ 2 * n
  let J := adaptiveTerminalChunk N s0
  let m := terminalPhaseCount n C s0
  let k := correctedRuntimeSamples m eps
  let r := concreteRunwiseReps p
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hN : 0 < N := by dsimp [N]; positivity
  have hs0 : 0 < s0 := by
    dsimp [s0]
    exact polynomialEndpointSigmaSq_pos hn (by positivity)
  have hbelow : ∀ j < J, adaptiveChunkStart N s0 j ≤ N := by
    intro j hj
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs0 hj).le
  have hcoldNat := adaptiveSourceColdPhases_le_total N s0 J
  have hoff : adaptiveTotalPhases N s0 J = m := by
    rw [← adaptiveChunkOffset_eq_totalPhases]
    rfl
  have hcoldCast : (adaptiveSourceColdPhases N s0 J : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (hoff ▸ hcoldNat)
  have hmBound := concrete_source_phaseCount_lt hn hC hsource
  have hcold : (adaptiveSourceColdPhases N s0 J : ℝ) <
      80 * C ^ 2 * (n : ℝ) ^ 2 + 3 := by
    change ((m + 1 : ℕ) : ℝ) < _ at hmBound
    norm_num at hmBound
    linarith
  have hJ := concrete_source_terminalChunk_lt hn hC hsource
  have hhot := adaptiveSourceHotSigmaMass_le hN hs0 hbelow
  have hrBound := concreteRunwiseReps_cast_lt hp hp1
  have hrLe : (concreteRunwiseReps p : ℝ) ≤ 25 / 2 * Real.log (1 / p) + 2 := by
    norm_num at hrBound ⊢
    linarith
  have hkRaw := correctedRuntimeSamples_cast_lt (m := m) heps
  have hphasePositive : 0 < 80 * C ^ 2 * (n : ℝ) ^ 2 + 3 := by positivity
  have hkBound : (k : ℝ) <
      100000 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) / eps ^ 2 + 2 := by
    dsimp [k] at hkRaw ⊢
    have he2 : 0 < eps ^ 2 := sq_pos_of_pos heps
    have hm1 : (m : ℝ) + 1 < 80 * C ^ 2 * (n : ℝ) ^ 2 + 3 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hmBound
    have hdiv : 100000 * ((m : ℝ) + 1) / eps ^ 2 <
        100000 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) / eps ^ 2 := by gcongr
    linarith
  have hhot' : adaptiveSourceHotSigmaMass N s0 J <
      6 * (C ^ 2 * n) * (16 * C ^ 2 * (n : ℝ) ^ 2 + 2) := by
    have hNdef : N = C ^ 2 * (n : ℝ) := rfl
    rw [hNdef] at hhot
    calc
      _ ≤ 6 * (C ^ 2 * (n : ℝ)) * (J : ℝ) := hhot
      _ < 6 * (C ^ 2 * (n : ℝ)) *
          (16 * C ^ 2 * (n : ℝ) ^ 2 + 2) := by
        gcongr
  unfold adaptiveSourceProposalAccounting correctedSourceProposalEnvelope
  dsimp [N, s0, J, m, k, r] at hcold hhot' hrBound hkBound ⊢
  have hcost0 : 0 ≤ 2 * adaptiveSourceColdPhases (C ^ 2 * ↑n)
      (polynomialEndpointSigmaSq n (eps / 4))
      (adaptiveTerminalChunk (C ^ 2 * ↑n) (polynomialEndpointSigmaSq n (eps / 4))) +
      4 * q ^ 2 * (n : ℝ) ^ 2 *
        adaptiveSourceHotSigmaMass (C ^ 2 * ↑n)
          (polynomialEndpointSigmaSq n (eps / 4))
          (adaptiveTerminalChunk (C ^ 2 * ↑n)
            (polynomialEndpointSigmaSq n (eps / 4))) := by
    have hhot0 : 0 ≤ adaptiveSourceHotSigmaMass (C ^ 2 * ↑n)
        (polynomialEndpointSigmaSq n (eps / 4))
        (adaptiveTerminalChunk (C ^ 2 * ↑n)
          (polynomialEndpointSigmaSq n (eps / 4))) := by
      unfold adaptiveSourceHotSigmaMass
      apply Finset.sum_nonneg
      intro j hj
      apply Finset.sum_nonneg
      intro t ht
      split_ifs
      · exact (geomSchedule_pos
          (adaptiveChunkStart_pos hN hs0 j)
          (by linarith [adaptiveChunkRate_pos hN hs0 j]) t).le
      · norm_num
    positivity
  have hrhsR : 0 ≤ 25 / 2 * Real.log (1 / p) + 2 := by
    have : 0 ≤ Real.log (1 / p) := Real.log_nonneg (by
      rw [le_div_iff₀ hp]
      linarith)
    positivity
  have hrhsK : 0 ≤
      100000 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) / eps ^ 2 + 2 := by positivity
  calc
    _ ≤ (25 / 2 * Real.log (1 / p) + 2) *
        (100000 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) / eps ^ 2 + 2) *
        (2 * adaptiveSourceColdPhases (C ^ 2 * ↑n)
            (polynomialEndpointSigmaSq n (eps / 4))
            (adaptiveTerminalChunk (C ^ 2 * ↑n)
              (polynomialEndpointSigmaSq n (eps / 4))) +
          4 * q ^ 2 * (n : ℝ) ^ 2 *
            adaptiveSourceHotSigmaMass (C ^ 2 * ↑n)
              (polynomialEndpointSigmaSq n (eps / 4))
              (adaptiveTerminalChunk (C ^ 2 * ↑n)
                (polynomialEndpointSigmaSq n (eps / 4)))) := by
      gcongr
    _ ≤ (25 / 2 * Real.log (1 / p) + 2) *
        (100000 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) / eps ^ 2 + 2) *
        (2 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) +
          24 * q ^ 2 * (n : ℝ) ^ 2 * (C ^ 2 * n) *
            (16 * C ^ 2 * (n : ℝ) ^ 2 + 2)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hrhsR hrhsK)
      have hcoldLe : 2 * (adaptiveSourceColdPhases (C ^ 2 * ↑n)
          (polynomialEndpointSigmaSq n (eps / 4))
          (adaptiveTerminalChunk (C ^ 2 * ↑n)
            (polynomialEndpointSigmaSq n (eps / 4))) : ℝ) ≤
          2 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) := by
        exact mul_le_mul_of_nonneg_left hcold.le (by norm_num)
      have hcoef : 0 ≤ 4 * q ^ 2 * (n : ℝ) ^ 2 := by positivity
      have hhotLe := mul_le_mul_of_nonneg_left hhot'.le hcoef
      calc
        _ ≤ 2 * (80 * C ^ 2 * (n : ℝ) ^ 2 + 3) +
            4 * q ^ 2 * (n : ℝ) ^ 2 *
              (6 * (C ^ 2 * (n : ℝ)) *
                (16 * C ^ 2 * (n : ℝ) ^ 2 + 2)) :=
          add_le_add hcoldLe hhotLe
        _ = _ := by ring
    _ = _ := rfl

/-- Markov's inequality gives the source's constant `1/20` cutoff loss once
the deterministic cutoff is twenty times a positive expectation envelope. -/
theorem cutoff_failure_le_one_twentieth {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {B : ℝ}
    (hX0 : ∀ ω, 0 ≤ X ω) (hXint : Integrable X μ)
    (hB : 0 < B) (hmean : (∫ ω, X ω ∂μ) ≤ B) :
    μ.real {ω | 20 * B ≤ X ω} ≤ 1 / 20 := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall hX0) hXint (20 * B)
  nlinarith

/-! Axiom audit. -/

#print axioms adaptiveSourceColdPhases_le_total
#print axioms sum_chunk_sigmaSq_le_six_mul
#print axioms adaptiveSourceHotSigmaMass_le
#print axioms adaptiveSourceProposalAccounting_le
#print axioms correctedRuntimeSamples_budget
#print axioms corrected_adaptive_source_accounting_le_envelope
#print axioms cutoff_failure_le_one_twentieth

end Ttc.CVCorrectedRuntime

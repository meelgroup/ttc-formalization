import Ttc.Exec.CVCombinedContinuingRetryPhaseTV
import Ttc.Volume.LVNormTailExplicitDyadic
import Ttc.Volume.CVCorrectedParameters

/-! Concrete error shares and retry count for the continuing-rejection CV phase. -/

namespace Ttc.CVContinuingRetryParameters

open MeasureTheory
open ProbabilityTheory Set Arlib
open Ttc.CVCorrected Ttc.CVAdaptive
open scoped ENNReal

/-- One eighth of the corrected sequential dependence allowance. -/
noncomputable def continuingShare (m : Nat) (eps : Real) : Real :=
  correctedNu m eps / 8

/-- Point-candidate mixing error: `32 * zeta = correctedNu / 8`. -/
noncomputable def continuingZeta (m : Nat) (eps : Real) : ENNReal :=
  ENNReal.ofReal (correctedNu m eps / 256)

/-- Significant-survival threshold and query-timeout error use one share each. -/
noncomputable def continuingEta (m : Nat) (eps : Real) : ENNReal :=
  ENNReal.ofReal (continuingShare m eps)

noncomputable def continuingTimeout (m : Nat) (eps : Real) : ENNReal :=
  ENNReal.ofReal (continuingShare m eps)

/-- Deterministic membership-query cutoff from a real expected-cost envelope `B`.
The harmless `B+1` makes the cutoff strictly positive even at zero mean. -/
noncomputable def continuingQueryCutoff
    (B : Real) (m : Nat) (eps : Real) : ENNReal :=
  ENNReal.ofReal (8 * (B + 1) / correctedNu m eps)

/-- Actual acceptance is at least `1/16` when ideal joint acceptance is `1/8` and
`zeta <= 1/16`, so retry survival contracts by at most `15/16`. -/
noncomputable def continuingContraction : ENNReal := ENNReal.ofReal (15 / 16 : Real)

theorem correctedNu_pos {m : Nat} {eps : Real} (heps : 0 < eps) :
    0 < correctedNu m eps := by
  unfold correctedNu
  exact div_pos (sq_pos_of_pos heps)
    (mul_pos (mul_pos (by norm_num) (pow_pos (correctedAlpha_pos heps) 4)) (by positivity))

theorem correctedNu_le_one {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    correctedNu m eps ≤ 1 := by
  have ha : 1 ≤ correctedAlpha m eps := one_le_correctedAlpha heps heps1
  have hm0 : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hm : (1 : Real) ≤ (m : Real) + 1 := by linarith
  have he2 : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg eps]
  unfold correctedNu
  have hden : (0 : Real) < 100000 * correctedAlpha m eps ^ 4 * ((m : Real) + 1) := by
    positivity
  rw [div_le_one hden]
  have ha4 : 1 ≤ correctedAlpha m eps ^ 4 := one_le_pow₀ ha
  nlinarith

theorem continuingShare_pos {m : Nat} {eps : Real} (heps : 0 < eps) :
    0 < continuingShare m eps := div_pos (correctedNu_pos heps) (by norm_num)

theorem continuingQueryCutoff_pos {B : Real} {m : Nat} {eps : Real}
    (hB : 0 ≤ B) (heps : 0 < eps) :
    0 < continuingQueryCutoff B m eps := by
  apply ENNReal.ofReal_pos.2
  exact div_pos (mul_pos (by norm_num) (by linarith)) (correctedNu_pos heps)

theorem continuingQueryCutoff_ne_top (B : Real) (m : Nat) (eps : Real) :
    continuingQueryCutoff B m eps ≠ ⊤ := ENNReal.ofReal_ne_top

/-- Markov's ratio at the explicit cutoff consumes exactly the timeout share. -/
theorem expectedCost_div_continuingQueryCutoff_le_timeout
    {B : Real} {m : Nat} {eps : Real} (hB : 0 ≤ B) (heps : 0 < eps) :
    ENNReal.ofReal B / continuingQueryCutoff B m eps ≤ continuingTimeout m eps := by
  have hnu : 0 < correctedNu m eps := correctedNu_pos heps
  have hcutR : 0 < 8 * (B + 1) / correctedNu m eps := by positivity
  rw [continuingQueryCutoff, continuingTimeout, continuingShare,
    ← ENNReal.ofReal_div_of_pos hcutR]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ hcutR (by norm_num : (0 : Real) < 8)]
  field_simp [ne_of_gt hnu]
  nlinarith

/-- Sixteen retries shrink `15/16` survival by at least one dyadic factor. -/
theorem contraction_pow_sixteen_le_half :
    (15 / 16 : Real) ^ 16 ≤ 1 / 2 := by norm_num

/-- We use sixteen retries per dyadic tail level. -/
noncomputable def continuingRetries (m : Nat) (eps : Real) (heps : 0 < eps) : Nat :=
  16 * dyadicTailIndex (continuingShare m eps) (continuingShare_pos heps)

/-- Explicit logarithmic retry count used for the polynomial-runtime capstone. -/
noncomputable def explicitContinuingRetries (m : Nat) (eps : Real) : Nat :=
  16 * explicitDyadicTailIndex (continuingShare m eps)

theorem contraction_pow_continuingRetries_le_share
    {m : Nat} {eps : Real} (heps : 0 < eps) :
    (15 / 16 : Real) ^ continuingRetries m eps heps ≤ continuingShare m eps := by
  let k := dyadicTailIndex (continuingShare m eps) (continuingShare_pos heps)
  have hpow : ((15 / 16 : Real) ^ 16) ^ k ≤ ((1 / 2 : Real)) ^ k :=
    pow_le_pow_left₀ (by positivity) contraction_pow_sixteen_le_half k
  have hdyadic : (1 / 2 : Real) ^ k ≤ continuingShare m eps := by
    simpa only [one_div, inv_pow] using
      (inv_two_pow_dyadicTailIndex_le (continuingShare_pos (m := m) heps))
  rw [continuingRetries, pow_mul]
  exact hpow.trans hdyadic

theorem continuingContraction_pow_retries_le_eta
    {m : Nat} {eps : Real} (heps : 0 < eps) :
    continuingContraction ^ continuingRetries m eps heps ≤ continuingEta m eps := by
  rw [continuingContraction, continuingEta, ← ENNReal.ofReal_pow]
  exact ENNReal.ofReal_le_ofReal
    (contraction_pow_continuingRetries_le_share heps)
  norm_num

theorem continuingShare_lt_one {m : Nat} {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) : continuingShare m eps < 1 := by
  have hnu := correctedNu_le_one (m := m) heps heps1
  dsimp only [continuingShare]
  nlinarith

theorem contraction_pow_explicitContinuingRetries_le_share
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (15 / 16 : Real) ^ explicitContinuingRetries m eps ≤ continuingShare m eps := by
  let k := explicitDyadicTailIndex (continuingShare m eps)
  have hpow : ((15 / 16 : Real) ^ 16) ^ k ≤ ((1 / 2 : Real)) ^ k :=
    pow_le_pow_left₀ (by positivity) contraction_pow_sixteen_le_half k
  have hdyadic : (1 / 2 : Real) ^ k ≤ continuingShare m eps := by
    simpa only [one_div, inv_pow] using
      (inv_two_pow_explicitDyadicTailIndex_le
        (continuingShare_pos (m := m) heps) (continuingShare_lt_one heps heps1))
  rw [explicitContinuingRetries, pow_mul]
  exact hpow.trans hdyadic

theorem continuingContraction_pow_explicitRetries_le_eta
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    continuingContraction ^ explicitContinuingRetries m eps ≤ continuingEta m eps := by
  rw [continuingContraction, continuingEta, ← ENNReal.ofReal_pow]
  exact ENNReal.ofReal_le_ofReal
    (contraction_pow_explicitContinuingRetries_le_share heps heps1)
  norm_num

/-- Machine-checked logarithmic retry-count bound. -/
theorem explicitContinuingRetries_lt_logb
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (explicitContinuingRetries m eps : Real) <
      16 * (Real.logb 2 (1 / continuingShare m eps) + 1) := by
  have hindex := explicitDyadicTailIndex_lt_logb_add_one
    (continuingShare_pos (m := m) heps) (continuingShare_lt_one heps heps1)
  rw [explicitContinuingRetries]
  push_cast
  nlinarith

/-- The point-mixing choice satisfies the `1/16` side condition used by joint
acceptance normalization. -/
theorem continuingZeta_le_sixteenth
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    continuingZeta m eps ≤ ENNReal.ofReal (1 / 16 : Real) := by
  apply ENNReal.ofReal_le_ofReal
  have hnu := correctedNu_le_one (m := m) heps heps1
  nlinarith

/-- An ideal `1/8` acceptance event and candidate TV at most `1/16` imply actual
rejection probability at most `15/16`. -/
theorem rejection_le_continuingContraction_of_tvLe
    {E : Type*} [MeasurableSpace E]
    (mu tau : Measure E) [IsProbabilityMeasure mu] [IsProbabilityMeasure tau]
    {A : Set E} (hA : MeasurableSet A) {zeta : ENNReal}
    (hTV : TVLe mu tau zeta)
    (heighth : ENNReal.ofReal (1 / 8 : Real) ≤ tau A)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    mu Aᶜ ≤ continuingContraction := by
  have hsixteenth : ENNReal.ofReal (1 / 16 : Real) ≤ mu A := by
    refine ENNReal.le_of_add_le_add_right
      (show ENNReal.ofReal (1 / 16 : Real) ≠ ⊤ from ENNReal.ofReal_ne_top) ?_
    calc
      ENNReal.ofReal (1 / 16 : Real) + ENNReal.ofReal (1 / 16 : Real) =
          ENNReal.ofReal (1 / 8 : Real) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
      _ ≤ tau A := heighth
      _ ≤ mu A + zeta := hTV.right hA
      _ ≤ mu A + ENNReal.ofReal (1 / 16 : Real) := by gcongr
  rw [prob_compl_eq_one_sub hA, continuingContraction]
  calc
    1 - mu A ≤ 1 - ENNReal.ofReal (1 / 16 : Real) :=
      tsub_le_tsub_left hsixteenth 1
    _ = ENNReal.ofReal (15 / 16 : Real) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num)]
      norm_num

/-- The four error shares fit exactly one half of `correctedNu`; the outer factor `2`
in `DirectSequentialOperational.dependence_budget` then recovers the full allowance. -/
theorem continuing_total_error_toReal_budget_of_tail
    {m L : Nat} {eps : Real} (heps : 0 < eps)
    (htail : continuingContraction ^ L ≤ continuingEta m eps) :
    2 * (continuingTimeout m eps + 32 * continuingZeta m eps +
      continuingEta m eps +
      continuingContraction ^ L).toReal ≤
        correctedNu m eps := by
  have hnu0 : 0 ≤ correctedNu m eps := (correctedNu_pos heps).le
  have hshare0 : 0 ≤ continuingShare m eps := (continuingShare_pos heps).le
  have hzeta0 : 0 ≤ correctedNu m eps / 256 := div_nonneg hnu0 (by norm_num)
  have hfiniteTimeout : continuingTimeout m eps ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfiniteZeta : continuingZeta m eps ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfinite32 : 32 * continuingZeta m eps ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hfiniteZeta
  have hfiniteEta : continuingEta m eps ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfiniteR : continuingContraction ^ L ≠ ⊤ := by
    intro htop
    rw [htop] at htail
    exact hfiniteEta (top_unique htail)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨
      ENNReal.add_ne_top.2 ⟨hfiniteTimeout, hfinite32⟩, hfiniteEta⟩) hfiniteR,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfiniteTimeout, hfinite32⟩) hfiniteEta,
    ENNReal.toReal_add hfiniteTimeout hfinite32,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  simp only [continuingTimeout, continuingEta, continuingZeta,
    ENNReal.toReal_ofReal hshare0,
    ENNReal.toReal_ofReal hzeta0]
  change 2 * (continuingShare m eps + 32 * (correctedNu m eps / 256) +
    continuingShare m eps +
      (continuingContraction ^ L).toReal) ≤ _
  have htailReal :
      (continuingContraction ^ L).toReal ≤
        continuingShare m eps := by
    simpa only [continuingEta, ENNReal.toReal_ofReal hshare0] using
      ((ENNReal.toReal_le_toReal hfiniteR hfiniteEta).2 htail)
  dsimp only [continuingShare]
  calc
    2 * (correctedNu m eps / 8 + 32 * (correctedNu m eps / 256) +
        correctedNu m eps / 8 +
        (continuingContraction ^ L).toReal) ≤
      2 * (correctedNu m eps / 8 + 32 * (correctedNu m eps / 256) +
        correctedNu m eps / 8 + correctedNu m eps / 8) := by
          gcongr
          simpa only [continuingShare] using htailReal
    _ = correctedNu m eps := by ring

theorem continuing_total_error_toReal_budget
    {m : Nat} {eps : Real} (heps : 0 < eps) :
    2 * (continuingTimeout m eps + 32 * continuingZeta m eps +
      continuingEta m eps +
      continuingContraction ^ continuingRetries m eps heps).toReal ≤
        correctedNu m eps :=
  continuing_total_error_toReal_budget_of_tail heps
    (continuingContraction_pow_retries_le_eta heps)

theorem explicitContinuing_total_error_toReal_budget
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    2 * (continuingTimeout m eps + 32 * continuingZeta m eps +
      continuingEta m eps +
      continuingContraction ^ explicitContinuingRetries m eps).toReal ≤
        correctedNu m eps :=
  continuing_total_error_toReal_budget_of_tail heps
    (continuingContraction_pow_explicitRetries_le_eta heps heps1)

#print axioms contraction_pow_continuingRetries_le_share
#print axioms continuingContraction_pow_retries_le_eta
#print axioms rejection_le_continuingContraction_of_tvLe
#print axioms continuing_total_error_toReal_budget
#print axioms explicitContinuingRetries_lt_logb
#print axioms explicitContinuing_total_error_toReal_budget

end Ttc.CVContinuingRetryParameters

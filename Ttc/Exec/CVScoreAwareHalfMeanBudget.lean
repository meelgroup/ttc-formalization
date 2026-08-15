import Ttc.Exec.CVGaussianScoreAwareMeanBudget

/-! A two-way allocation of the first-moment TV budget.

Running the score-aware mixing parameters at half the requested accuracy reduces
`correctedNu` (and hence `blockShare`) by a factor `1024`.  Consequently its
geometric-mean first-moment allowance is smaller by a factor `32`; in particular it
fits one half of the allowance at the original accuracy.  The other half can be
reserved for the truncation tail.
-/

namespace Ttc.CVScoreAwareHalfMeanBudget

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVGaussianBlockRetryParameters
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVGaussianFactorSevenAssembly
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

theorem blockShare_half_accuracy
    {m k : Nat} {eps : Real} (heps : 0 < eps) :
    blockShare m k (eps / 2) = blockShare m k eps / 1024 := by
  have he : eps ≠ 0 := ne_of_gt heps
  unfold blockShare correctedNu correctedAlpha
  field_simp
  ring

theorem blockShare_succ_le
    {m k : Nat} {eps : Real} (heps : 0 < eps) :
    blockShare (m + 1) k eps ≤ blockShare m k eps := by
  have he2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  unfold blockShare correctedNu correctedAlpha
  have hm : (0 : Real) < (m : Real) + 1 := by positivity
  have hms : (m : Real) + 1 ≤ ((m + 1 : Nat) : Real) + 1 := by norm_num
  gcongr

theorem scoreAwareMeanEta_half_accuracy
    {m k : Nat} {eps : Real} (heps : 0 < eps) :
    scoreAwareMeanEta m k (eps / 2) = scoreAwareMeanEta m k eps / 32 := by
  have hb0 : 0 ≤ (7 / 5 : Real) * blockShare m k eps := by
    exact mul_nonneg (by norm_num) (blockShare_pos heps).le
  unfold scoreAwareMeanEta
  rw [blockShare_half_accuracy heps]
  have hrad : (7 / 5 : Real) * (blockShare m k eps / 1024) =
      ((7 / 5 : Real) * blockShare m k eps) / (32 ^ 2) := by ring
  rw [hrad, Real.sqrt_div hb0, Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) ≤ 32)]

theorem scoreAwareMeanEta_succ_half_accuracy_le
    {m k : Nat} {eps : Real} (heps : 0 < eps) :
    scoreAwareMeanEta (m + 1) k (eps / 2) ≤ scoreAwareMeanEta m k eps / 32 := by
  rw [scoreAwareMeanEta_half_accuracy heps]
  unfold scoreAwareMeanEta
  gcongr
  exact blockShare_succ_le heps

/-- Local mixing at half accuracy consumes at most half of the original
geometric-mean first-moment allowance. -/
theorem scoreAwareMixError_mean_le_half
    {m k chainLength : Nat} {eps R : Real} {sigmaSq : Nat → Real}
    {K : Set (State n)} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7) (i : Nat) :
    Real.exp (R ^ 2 / (2 * sigmaSq i)) *
        (scoreAwareMixError m k (eps / 2)
          (phaseMomentSlackSeven chainLength sigmaSq K C)
          (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal ≤
      (scoreAwareMeanEta m k eps *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i)) / 2 := by
  have hhalf0 : 0 < eps / 2 := by positivity
  have hhalf1 : eps / 2 ≤ 1 := by linarith
  have h := scoreAwareMixError_mean_le (m := m) (k := k)
    (chainLength := chainLength) (eps := eps / 2) (R := R)
    (sigmaSq := sigmaSq) (K := K) (C := C)
    hhalf0 hhalf1 hsigma hball hfin hC0 hC7 i
  rw [scoreAwareMeanEta_half_accuracy heps] at h
  have hr0 : 0 ≤ chain chainLength sigmaSq K (i + 1) /
      chain chainLength sigmaSq K i :=
    (div_pos (chain_pos hsigma hball hfin _) (chain_pos hsigma hball hfin _)).le
  calc
    Real.exp (R ^ 2 / (2 * sigmaSq i)) *
        (scoreAwareMixError m k (eps / 2)
          (phaseMomentSlackSeven chainLength sigmaSq K C)
          (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal
        ≤ (scoreAwareMeanEta m k eps / 32) *
          (chain chainLength sigmaSq K (i + 1) /
            chain chainLength sigmaSq K i) := h
    _ ≤ (scoreAwareMeanEta m k eps *
          (chain chainLength sigmaSq K (i + 1) /
            chain chainLength sigmaSq K i)) / 2 := by
      have heta0 := scoreAwareMeanEta_nonneg m k eps
      nlinarith

/-- The version used by a length-`m+1` active/tail schedule whose readout has `m`
genuine cooling phases. -/
theorem scoreAwareMixError_succ_mean_le_half
    {m k chainLength : Nat} {eps R : Real} {sigmaSq : Nat → Real}
    {K : Set (State n)} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7) (i : Nat) :
    Real.exp (R ^ 2 / (2 * sigmaSq i)) *
        (scoreAwareMixError (m + 1) k (eps / 2)
          (phaseMomentSlackSeven chainLength sigmaSq K C)
          (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal ≤
      (scoreAwareMeanEta m k eps *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i)) / 2 := by
  have hhalf0 : 0 < eps / 2 := by positivity
  have hhalf1 : eps / 2 ≤ 1 := by linarith
  have h := scoreAwareMixError_mean_le (m := m + 1) (k := k)
    (chainLength := chainLength) (eps := eps / 2) (R := R)
    (sigmaSq := sigmaSq) (K := K) (C := C)
    hhalf0 hhalf1 hsigma hball hfin hC0 hC7 i
  have heta := scoreAwareMeanEta_succ_half_accuracy_le
    (m := m) (k := k) heps
  have hr0 : 0 ≤ chain chainLength sigmaSq K (i + 1) /
      chain chainLength sigmaSq K i :=
    (div_pos (chain_pos hsigma hball hfin _) (chain_pos hsigma hball hfin _)).le
  calc
    Real.exp (R ^ 2 / (2 * sigmaSq i)) *
        (scoreAwareMixError (m + 1) k (eps / 2)
          (phaseMomentSlackSeven chainLength sigmaSq K C)
          (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal
        ≤ scoreAwareMeanEta (m + 1) k (eps / 2) *
          (chain chainLength sigmaSq K (i + 1) /
            chain chainLength sigmaSq K i) := h
    _ ≤ (scoreAwareMeanEta m k eps *
          (chain chainLength sigmaSq K (i + 1) /
            chain chainLength sigmaSq K i)) / 2 := by
      have heta0 := scoreAwareMeanEta_nonneg m k eps
      nlinarith

/-- The same split when the operational second-moment slack itself is halved.  This is
the configuration needed to leave the other half of the factor-seven transport budget
for the local-to-full radial tail. -/
theorem scoreAwareMixError_succ_halfSlack_mean_le_half
    {m k chainLength : Nat} {eps R : Real} {sigmaSq : Nat → Real}
    {K : Set (State n)} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7) (i : Nat) :
    Real.exp (R ^ 2 / (2 * sigmaSq i)) *
        (scoreAwareMixError (m + 1) k (eps / 2)
          (fun j ↦ phaseMomentSlackSeven chainLength sigmaSq K C j / 2)
          (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal ≤
      (scoreAwareMeanEta m k eps *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i)) / 2 := by
  let e : Real := Real.exp (R ^ 2 / (2 * sigmaSq i))
  let d : Real := (scoreAwareMixError (m + 1) k (eps / 2)
    (fun j ↦ phaseMomentSlackSeven chainLength sigmaSq K C j / 2)
    (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal
  let bs : Real := blockShare (m + 1) k (eps / 2)
  let b : Real := blockShare m k eps
  let r : Real := chain chainLength sigmaSq K (i + 1) /
    chain chainLength sigmaSq K i
  have he0 : 0 < e := Real.exp_pos _
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hb0 : 0 < b := blockShare_pos heps
  have hbs0 : 0 < bs := blockShare_pos (by positivity : 0 < eps / 2)
  have hr0 : 0 < r := div_pos (chain_pos hsigma hball hfin _)
    (chain_pos hsigma hball hfin _)
  have hslackPos : ∀ j,
      0 < phaseMomentSlackSeven chainLength sigmaSq K C j / 2 := by
    intro j
    exact div_pos (phaseMomentSlackSeven_pos hsigma hball hfin hC7 j) (by norm_num)
  have hboundPos := phaseScoreTransportBoundSqSeven_pos
    (R := R) (sigmaSq := sigmaSq)
  have hshare := scoreAwareMixError_toReal_le_three_share
    (m := m + 1) (k := k) (eps := eps / 2)
    (slack := fun j ↦ phaseMomentSlackSeven chainLength sigmaSq K C j / 2)
    (boundSq := phaseScoreTransportBoundSqSeven R sigmaSq)
    (by positivity) (by linarith) hslackPos hboundPos i
  have hdbs : d ≤ 3 * bs := by
    refine hshare.trans ?_
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  have hmoment := scoreAwareMixError_mul_boundSq_le_slack
    (m := m + 1) (k := k) (eps := eps / 2)
    (slack := fun j ↦ phaseMomentSlackSeven chainLength sigmaSq K C j / 2)
    (boundSq := phaseScoreTransportBoundSqSeven R sigmaSq)
    (by positivity) (by linarith) hslackPos hboundPos i
  have hmoment' : d * (e ^ 2 * 15) ≤ (7 - C i) * r ^ 2 / 2 := by
    have ht := hmoment
    simp only [d, e, r, phaseScoreTransportBoundSqSeven,
      phaseMomentSlackSeven] at ht
    norm_num at ht
    exact ht
  have hright : d * ((7 - C i) * r ^ 2 / 2) ≤
      (3 * bs) * (7 * r ^ 2 / 2) := by
    have hAB : (7 - C i) * r ^ 2 / 2 ≤ 7 * r ^ 2 / 2 := by
      gcongr
      linarith [hC0 i]
    have hB0 : 0 ≤ 7 * r ^ 2 / 2 := by positivity
    exact (mul_le_mul_of_nonneg_left hAB hd0).trans
      (mul_le_mul_of_nonneg_right hdbs hB0)
  have hsq : (e * d) ^ 2 ≤ (7 / 10 : Real) * bs * r ^ 2 := by
    calc
      (e * d) ^ 2 = (d * (d * (e ^ 2 * 15))) / 15 := by ring
      _ ≤ (d * ((7 - C i) * r ^ 2 / 2)) / 15 := by gcongr
      _ ≤ ((3 * bs) * (7 * r ^ 2 / 2)) / 15 := by gcongr
      _ = (7 / 10 : Real) * bs * r ^ 2 := by ring
  have hbs : bs ≤ b / 1024 := by
    rw [show bs = blockShare (m + 1) k eps / 1024 by
      simpa only [bs] using blockShare_half_accuracy (m := m + 1) (k := k) heps]
    gcongr
    exact blockShare_succ_le (m := m) (k := k) heps
  have hetaSq : (scoreAwareMeanEta m k eps) ^ 2 = (7 / 5 : Real) * b := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    exact mul_nonneg (by norm_num) hb0.le
  have heta0 := scoreAwareMeanEta_nonneg m k eps
  have hsq' : (e * d) ^ 2 ≤
      (scoreAwareMeanEta m k eps * r / 2) ^ 2 := by
    calc
      (e * d) ^ 2 ≤ (7 / 10 : Real) * bs * r ^ 2 := hsq
      _ ≤ (7 / 10 : Real) * (b / 1024) * r ^ 2 := by gcongr
      _ ≤ (scoreAwareMeanEta m k eps * r / 2) ^ 2 := by
        change (7 / 10 : Real) * (b / 1024) * r ^ 2 ≤
          (scoreAwareMeanEta m k eps * r / 2) ^ 2
        have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
        nlinarith [hetaSq]
  have hed0 : 0 ≤ e * d := mul_nonneg he0.le hd0
  have htarget0 : 0 ≤ scoreAwareMeanEta m k eps * r / 2 := by positivity
  have hfinal : e * d ≤ scoreAwareMeanEta m k eps * r / 2 := by nlinarith
  simpa only [e, d, r] using hfinal

#print axioms blockShare_half_accuracy
#print axioms scoreAwareMeanEta_half_accuracy
#print axioms scoreAwareMixError_mean_le_half
#print axioms scoreAwareMixError_succ_mean_le_half
#print axioms scoreAwareMixError_succ_halfSlack_mean_le_half

end Ttc.CVScoreAwareHalfMeanBudget

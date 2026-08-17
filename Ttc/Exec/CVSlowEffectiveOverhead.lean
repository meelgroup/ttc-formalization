import Ttc.Exec.CVSlowCanonicalRuntimeComparison
import Ttc.Exec.TtcCircumRadius
import Ttc.Exec.CVSlowUniformShareBounds

/-!
# Input-indexed effective overhead for the uniformly slow canonical route

The frontier slow-canonical certificate leaves `runtimeConstant` implicit, so it may be
chosen per input.  This file makes that choice explicitly: the slow schedule's exact
retained scalar is absorbed by declaring the runtime constant to be the (clipped) slow
overhead envelope itself, and the source-shaped core factor is at least one.

**Which stack to use.** The frontier's `hslackDef`/`hboundDef` binders force the *uniform*
factor-seven slack/boundSq pair, whose share floor is `1/18`, not the canonical `2/33`.
Since `1/18 < 2/33` the canonical floor is not below the share the frontier needs, so the
assembly must consume the `slowUniform*P` family at the end of this file.  The canonical
family is kept intact for callers that are already on it.

The resulting `slowEffectiveP` is exactly the `effective` binder of
`Ttc.CVEffectiveSourceReference.cvShapedExpectedImplementationOfEffectiveFamily`, and
`slowOverheadP` is its `OV`.  The primed family is taken at the assembly's pinned phase
count `slowOperationalPhases n N + 1`; the unprimed family is the same construction at the
raw phase count and is retained for callers that do not add the successor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Ttc.CVSlowEffectiveOverhead

open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSourceTheorem11Arithmetic
open Ttc.CVSlowCanonicalShareBounds
open Ttc.CVSlowCanonicalDeadlineCost
open Ttc.CVSlowCanonicalRuntimeComparison
open Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowGlobalRadiusTailBudget
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVHybridSchedule
open Ttc.CVCorrected
open Ttc.CVCorrectedRuntime
open Ttc.TtcCircumRadius
open Ttc.CVSlowUniformShareBounds
open scoped ENNReal

/-! ### Closed form and monotonicity of the dependence parameter -/

/-- Closed form of the corrected per-transition dependence target.  Unlike
`correctedNu_pos` this is valid at every real accuracy, which matters because the
`effective`-family interface quantifies over unguarded inputs. -/
theorem correctedNu_eq (m : Nat) (eps : Real) :
    correctedNu m eps = eps ^ 10 / (100000 ^ 5 * ((m : Real) + 1) ^ 5) := by
  unfold correctedNu correctedAlpha
  rcases eq_or_ne eps 0 with h | h
  · simp [h]
  · have hm : ((m : Real) + 1) ≠ 0 := by positivity
    field_simp

theorem correctedNu_nonneg_of_even (m : Nat) (eps : Real) :
    0 ≤ correctedNu m eps := by
  rw [correctedNu_eq]
  have h10 : 0 ≤ eps ^ 10 := by
    have : eps ^ 10 = (eps ^ 5) ^ 2 := by ring
    rw [this]; positivity
  positivity

theorem correctedNu_pos_of_ne_zero {m : Nat} {eps : Real} (heps : eps ≠ 0) :
    0 < correctedNu m eps := by
  rw [correctedNu_eq]
  have h5 : eps ^ 5 ≠ 0 := pow_ne_zero 5 heps
  have h10 : 0 < eps ^ 10 := by
    have hrw : eps ^ 10 = (eps ^ 5) ^ 2 := by ring
    rw [hrw]
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h5))
  positivity

theorem correctedNu_antitone_phases {m m' : Nat} (hm : m ≤ m') (eps : Real) :
    correctedNu m' eps ≤ correctedNu m eps := by
  rw [correctedNu_eq, correctedNu_eq]
  have h10 : 0 ≤ eps ^ 10 := by
    have : eps ^ 10 = (eps ^ 5) ^ 2 := by ring
    rw [this]; positivity
  have hmm : ((m : Real) + 1) ≤ ((m' : Real) + 1) := by
    have : (m : Real) ≤ (m' : Real) := by exact_mod_cast hm
    linarith
  have hm0 : (0 : Real) < (m : Real) + 1 := by positivity
  gcongr

/-! ### The canonical share floor -/

theorem blockShare_nonneg (m k : Nat) (eps : Real) : 0 ≤ blockShare m k eps := by
  unfold blockShare
  have := correctedNu_nonneg_of_even m eps
  positivity

theorem blockShare_antitone {m m' k k' : Nat} (hm : m ≤ m') (hk : k ≤ k') (eps : Real) :
    blockShare m' k' eps ≤ blockShare m k eps := by
  unfold blockShare
  have hnu := correctedNu_antitone_phases hm eps
  have hnu0 := correctedNu_nonneg_of_even m' eps
  have hkk : ((k : Real) + 1) ≤ ((k' : Real) + 1) := by
    have : (k : Real) ≤ (k' : Real) := by exact_mod_cast hk
    linarith
  have hk0 : (0 : Real) < 8 * ((k : Real) + 1) := by positivity
  have hnu0' := correctedNu_nonneg_of_even m eps
  gcongr

theorem slowCanonicalShareFloor_nonneg (m k : Nat) (eps R s0 : Real) :
    0 ≤ slowCanonicalShareFloor m k eps R s0 :=
  le_min (blockShare_nonneg m k eps) (by positivity)

theorem slowCanonicalShareFloor_pos_of_ne_zero
    {m k : Nat} {eps : Real} (heps : eps ≠ 0) (R s0 : Real) :
    0 < slowCanonicalShareFloor m k eps R s0 := by
  unfold slowCanonicalShareFloor blockShare
  refine lt_min (div_pos (correctedNu_pos_of_ne_zero heps) (by positivity)) (by positivity)

/-- The floor is below one on every input, with no accuracy guard: the exponential arm
alone is at most `2/33`. -/
theorem slowCanonicalShareFloor_lt_one_of_nonneg
    (m k : Nat) (eps R : Real) {s0 : Real} (hs0 : 0 ≤ s0) :
    slowCanonicalShareFloor m k eps R s0 < 1 := by
  have hx : 0 ≤ R ^ 2 / (2 * s0) := by positivity
  have hexp : (1 : Real) ≤ Real.exp (R ^ 2 / (2 * s0)) := Real.one_le_exp hx
  have hexp2 : (1 : Real) ≤ Real.exp (R ^ 2 / (2 * s0)) ^ 2 := by nlinarith
  have harm : 2 / (33 * Real.exp (R ^ 2 / (2 * s0)) ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  exact lt_of_le_of_lt (min_le_right _ _) harm

theorem slowCanonicalShareFloor_antitone
    {m m' k k' : Nat} {eps R R' s0 : Real}
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0) :
    slowCanonicalShareFloor m' k' eps R' s0 ≤ slowCanonicalShareFloor m k eps R s0 := by
  unfold slowCanonicalShareFloor
  have hsq : R ^ 2 ≤ R' ^ 2 := by nlinarith
  have harm : 2 / (33 * Real.exp (R' ^ 2 / (2 * s0)) ^ 2) ≤
      2 / (33 * Real.exp (R ^ 2 / (2 * s0)) ^ 2) := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; norm_num
    · have hx : R ^ 2 / (2 * s0) ≤ R' ^ 2 / (2 * s0) := by
        apply div_le_div_of_nonneg_right hsq (by positivity)
      have he : Real.exp (R ^ 2 / (2 * s0)) ≤ Real.exp (R' ^ 2 / (2 * s0)) :=
        Real.exp_le_exp.2 hx
      have he0 : (0 : Real) < Real.exp (R ^ 2 / (2 * s0)) := Real.exp_pos _
      gcongr
  exact min_le_min (blockShare_antitone hm hk eps) harm

/-! ### The retry and deadline real envelopes -/

theorem slowCanonicalRetryRealEnvelope_nonneg
    (m k : Nat) (eps R : Real) {s0 : Real} (hs0 : 0 ≤ s0) :
    0 ≤ slowCanonicalRetryRealEnvelope m k eps R s0 := by
  unfold slowCanonicalRetryRealEnvelope
  have h0 := slowCanonicalShareFloor_nonneg m k eps R s0
  have h1 := slowCanonicalShareFloor_lt_one_of_nonneg m k eps R hs0
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]
    norm_num [Real.logb]
  · have : (1 : Real) ≤ 1 / slowCanonicalShareFloor m k eps R s0 := by
      rw [le_div_iff₀ h]; linarith
    have := Real.logb_nonneg (b := 2) (by norm_num) this
    linarith

theorem slowCanonicalRetryRealEnvelope_mono
    {m m' k k' : Nat} {eps R R' s0 : Real} (heps : eps ≠ 0)
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0) :
    slowCanonicalRetryRealEnvelope m k eps R s0 ≤
      slowCanonicalRetryRealEnvelope m' k' eps R' s0 := by
  unfold slowCanonicalRetryRealEnvelope
  have hf0' : 0 < slowCanonicalShareFloor m' k' eps R' s0 :=
    slowCanonicalShareFloor_pos_of_ne_zero heps R' s0
  have hle := slowCanonicalShareFloor_antitone (eps := eps) hm hk hR0 hRR hs0
  have hinv : 1 / slowCanonicalShareFloor m k eps R s0 ≤
      1 / slowCanonicalShareFloor m' k' eps R' s0 :=
    one_div_le_one_div_of_le hf0' hle
  have hf0 : 0 < slowCanonicalShareFloor m k eps R s0 :=
    slowCanonicalShareFloor_pos_of_ne_zero heps R s0
  have hlog := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
    (one_div_pos.mpr hf0) (one_div_pos.mpr hf0')).2 hinv
  linarith

theorem slowCanonicalDeadlinePayload_mono
    {m m' k k' : Nat} {eps R R' s0 : Real} (heps : eps ≠ 0)
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0) :
    slowCanonicalDeadlinePayload m k eps R s0 ≤
      slowCanonicalDeadlinePayload m' k' eps R' s0 := by
  have hf0' : 0 < slowCanonicalShareFloor m' k' eps R' s0 :=
    slowCanonicalShareFloor_pos_of_ne_zero heps R' s0
  have hle := slowCanonicalShareFloor_antitone (eps := eps) hm hk hR0 hRR hs0
  exact slowDeadlinePayload_le_canonical (m := m') (k := k') (eps := eps) (R := R')
    (s0 := s0) (share := slowCanonicalShareFloor m k eps R s0) hf0' hle

theorem slowRadiusTailCalls_mono
    {m m' k k' : Nat} {eps : Real} (heps : eps ≠ 0) (hm : m ≤ m') (hk : k ≤ k') :
    slowRadiusTailCalls m k eps ≤ slowRadiusTailCalls m' k' eps := by
  unfold slowRadiusTailCalls
  have hnu0 : 0 < correctedNu m eps := correctedNu_pos_of_ne_zero heps
  have hnu0' : 0 < correctedNu m' eps := correctedNu_pos_of_ne_zero heps
  have hnu := correctedNu_antitone_phases hm eps
  have hnum : ((m * k : Nat) : Real) ≤ ((m' * k' : Nat) : Real) := by
    exact_mod_cast Nat.mul_le_mul hm hk
  have h4 : 4 * ((m * k : Nat) : Real) / correctedNu m eps ≤
      4 * ((m' * k' : Nat) : Real) / correctedNu m' eps := by
    have hnum0 : (0 : Real) ≤ 4 * ((m * k : Nat) : Real) := by positivity
    gcongr
  exact max_le_max (le_refl 1) h4

theorem slowCanonicalGeometryEnvelope_nonneg
    (n m k : Nat) (eps : Real) {N : Real} (hN : 0 ≤ N) :
    0 ≤ slowCanonicalGeometryEnvelope n m k eps N := by
  unfold slowCanonicalGeometryEnvelope
  have hA : (1 : Real) ≤ slowRadiusTailCalls m k eps := one_le_slowRadiusTailCalls m k eps
  have hlog : 0 ≤ Real.log (20 * slowRadiusTailCalls m k eps) :=
    Real.log_nonneg (by linarith)
  positivity

theorem slowCanonicalGeometryEnvelope_mono
    {n m m' k k' : Nat} {eps N N' : Real} (heps : eps ≠ 0)
    (hm : m ≤ m') (hk : k ≤ k') (hNN : N ≤ N') :
    slowCanonicalGeometryEnvelope n m k eps N ≤
      slowCanonicalGeometryEnvelope n m' k' eps N' := by
  unfold slowCanonicalGeometryEnvelope
  have hA : (1 : Real) ≤ slowRadiusTailCalls m k eps := one_le_slowRadiusTailCalls m k eps
  have hAA := slowRadiusTailCalls_mono heps hm hk
  have hlog : Real.log (20 * slowRadiusTailCalls m k eps) ≤
      Real.log (20 * slowRadiusTailCalls m' k' eps) := by
    apply Real.log_le_log (by linarith)
    linarith
  have hn3 : (0 : Real) ≤ (n : Real) ^ 3 := by positivity
  gcongr

theorem slowCanonicalDeadlineRealEnvelope_nonneg
    (n m k : Nat) {eps R s0 N : Real} (heps : eps ≠ 0) (hs0 : 0 ≤ s0) (hN : 0 ≤ N) :
    0 ≤ slowCanonicalDeadlineRealEnvelope n m k eps R s0 N := by
  unfold slowCanonicalDeadlineRealEnvelope
  have hG := slowCanonicalGeometryEnvelope_nonneg n m k eps hN
  have hP := slowCanonicalDeadlinePayload_nonneg
    (slowCanonicalShareFloor_pos_of_ne_zero (m := m) (k := k) heps R s0)
    (slowCanonicalShareFloor_lt_one_of_nonneg m k eps R hs0)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem slowCanonicalDeadlineRealEnvelope_mono
    {n m m' k k' : Nat} {eps R R' s0 N N' : Real} (heps : eps ≠ 0)
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0)
    (hN : 0 ≤ N) (hNN : N ≤ N') :
    slowCanonicalDeadlineRealEnvelope n m k eps R s0 N ≤
      slowCanonicalDeadlineRealEnvelope n m' k' eps R' s0 N' := by
  unfold slowCanonicalDeadlineRealEnvelope
  have hG := slowCanonicalGeometryEnvelope_nonneg n m k eps hN
  have hGG := slowCanonicalGeometryEnvelope_mono (n := n) heps hm hk hNN
  have hP := slowCanonicalDeadlinePayload_nonneg
    (slowCanonicalShareFloor_pos_of_ne_zero (m := m) (k := k) heps R s0)
    (slowCanonicalShareFloor_lt_one_of_nonneg m k eps R hs0)
  have hPP := slowCanonicalDeadlinePayload_mono heps hm hk hR0 hRR hs0
  have hG' : 0 ≤ slowCanonicalGeometryEnvelope n m' k' eps N' :=
    slowCanonicalGeometryEnvelope_nonneg n m' k' eps (hN.trans hNN)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  gcongr

/-- Monotonicity of the exact retained overhead envelope in the phase count, stream
count, radius, and variance target. -/
theorem slowCanonicalRetainedRealEnvelope_mono
    {n m m' k k' : Nat} {eps R R' s0 N N' : Real} (heps : eps ≠ 0)
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0)
    (hN : 0 ≤ N) (hNN : N ≤ N') :
    slowCanonicalRetainedRealEnvelope n m k eps R s0 N ≤
      slowCanonicalRetainedRealEnvelope n m' k' eps R' s0 N' := by
  unfold slowCanonicalRetainedRealEnvelope
  have hmR : (m : Real) ≤ (m' : Real) := by exact_mod_cast hm
  have hkR : (k : Real) ≤ (k' : Real) := by exact_mod_cast hk
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have hL0 := slowCanonicalRetryRealEnvelope_nonneg m k eps R hs0
  have hLL := slowCanonicalRetryRealEnvelope_mono heps hm hk hR0 hRR hs0
  have hT0 := slowCanonicalDeadlineRealEnvelope_nonneg n m k (R := R) (N := N) heps hs0 hN
  have hTT := slowCanonicalDeadlineRealEnvelope_mono (n := n) heps hm hk hR0 hRR hs0 hN hNN
  have he0 : (0 : Real) ≤ 2 * Real.exp 1 := by positivity
  have hL0' := slowCanonicalRetryRealEnvelope_nonneg m' k' eps R' hs0
  have hm0' : (0 : Real) ≤ (m' : Real) := by positivity
  have hk0' : (0 : Real) ≤ (k' : Real) := by positivity
  gcongr

/-! ### The degenerate accuracy `eps = 0`

The `effective`-family interface quantifies over unguarded accuracies, so the envelope
must also be compared at `eps = 0`.  There every share is zero, hence both logarithmic
factors collapse to constants and only the phase and stream counts remain. -/

theorem slowCanonicalShareFloor_eps_zero (m k : Nat) (R s0 : Real) :
    slowCanonicalShareFloor m k 0 R s0 = 0 := by
  have hnu : correctedNu m (0 : Real) = 0 := by rw [correctedNu_eq]; norm_num
  unfold slowCanonicalShareFloor blockShare
  rw [hnu, zero_div]
  exact min_eq_left (by positivity)

theorem slowCanonicalRetryRealEnvelope_eps_zero (m k : Nat) (R s0 : Real) :
    slowCanonicalRetryRealEnvelope m k 0 R s0 = 16 := by
  unfold slowCanonicalRetryRealEnvelope
  rw [slowCanonicalShareFloor_eps_zero]
  norm_num

theorem slowCanonicalDeadlinePayload_eps_zero (m k : Nat) (R s0 : Real) :
    slowCanonicalDeadlinePayload m k 0 R s0 = 0 := by
  unfold slowCanonicalDeadlinePayload
  rw [slowCanonicalShareFloor_eps_zero]
  norm_num

theorem slowCanonicalDeadlineRealEnvelope_eps_zero (n m k : Nat) (R s0 N : Real) :
    slowCanonicalDeadlineRealEnvelope n m k 0 R s0 N = 3 := by
  unfold slowCanonicalDeadlineRealEnvelope
  rw [slowCanonicalDeadlinePayload_eps_zero]
  norm_num

theorem slowCanonicalRetainedRealEnvelope_eps_zero (n m k : Nat) (R s0 N : Real) :
    slowCanonicalRetainedRealEnvelope n m k 0 R s0 N =
      (k : Real) * (m : Real) * (480 * (2 * Real.exp 1)) := by
  unfold slowCanonicalRetainedRealEnvelope
  rw [slowCanonicalRetryRealEnvelope_eps_zero, slowCanonicalDeadlineRealEnvelope_eps_zero]
  ring

theorem slowCanonicalRetainedRealEnvelope_mono_eps_zero
    {n m m' k k' : Nat} (hm : m ≤ m') (hk : k ≤ k') (R R' s0 s0' N N' : Real) :
    slowCanonicalRetainedRealEnvelope n m k 0 R s0 N ≤
      slowCanonicalRetainedRealEnvelope n m' k' 0 R' s0' N' := by
  rw [slowCanonicalRetainedRealEnvelope_eps_zero, slowCanonicalRetainedRealEnvelope_eps_zero]
  have hmR : (m : Real) ≤ (m' : Real) := by exact_mod_cast hm
  have hkR : (k : Real) ≤ (k' : Real) := by exact_mod_cast hk
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have he0 : (0 : Real) ≤ 480 * (2 * Real.exp 1) := by positivity
  gcongr

/-! ### Step 1 — the source-shaped core factor is at least one -/

theorem one_le_sourceOneRunCore (n : Nat) (hn : 1 ≤ n) {R eps : Real}
    (heps : 0 < eps) (heps1 : eps < 1) :
    1 ≤ max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 *
      sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
      sourceLogFactor ((n : Real) / eps) ^ 2 := by
  unfold sourceLogFactor
  exact one_le_cvBaseClipped hn (sq_nonneg R) heps heps1

theorem le_sourceOneRunQueryEnvelope_of_le
    {rc R eps : Real} {n : Nat} (hn : 1 ≤ n)
    (heps : 0 < eps) (heps1 : eps < 1) (hrc : 0 ≤ rc) :
    rc ≤ sourceOneRunQueryEnvelope rc n R eps := by
  unfold sourceOneRunQueryEnvelope
  exact le_mul_of_one_le_right hrc (one_le_sourceOneRunCore n hn heps heps1)

/-! ### Step 2 — the parameter selection as explicit functions of the input -/

/-- Elementary same-denominator comparison, valid also at a vanishing denominator. -/
theorem div_le_div_of_le_of_nonneg {a b c : Real} (h : a ≤ b) (hc : 0 ≤ c) :
    a / c ≤ b / c := by
  rcases eq_or_lt_of_le hc with h0 | h0
  · rw [← h0]; simp
  · gcongr

theorem coldPhases_eq_zero (x : Real) : coldPhases 0 x = 0 := by
  unfold coldPhases
  norm_num

theorem coldPhases_antitone (n : Nat) {x y : Real} (hx : 0 < x) (hxy : x ≤ y) :
    coldPhases n y ≤ coldPhases n x := by
  unfold coldPhases
  apply Nat.ceil_mono
  have hy : 0 < y := hx.trans_le hxy
  have hlogd : 0 ≤ Real.log (1 + 1 / (n : Real)) := by
    apply Real.log_nonneg
    have : (0 : Real) ≤ 1 / (n : Real) := by positivity
    linarith
  have hinv : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx hxy
  have hlog : Real.log (1 / y) ≤ Real.log (1 / x) :=
    Real.log_le_log (by positivity) hinv
  exact div_le_div_of_le_of_nonneg (max_le_max (le_refl 0) hlog) hlogd

theorem correctedRuntimeSamples_mono {m m' : Nat} (hm : m ≤ m') (eps : Real) :
    correctedRuntimeSamples m eps ≤ correctedRuntimeSamples m' eps := by
  unfold correctedRuntimeSamples
  have hmm : ((m : Real) + 1) ≤ ((m' : Real) + 1) := by
    have : (m : Real) ≤ (m' : Real) := by exact_mod_cast hm
    linarith
  have hnum : 100000 * ((m : Real) + 1) ≤ 100000 * ((m' : Real) + 1) := by linarith
  exact Nat.add_le_add_right
    (Nat.ceil_mono (div_le_div_of_le_of_nonneg hnum (sq_nonneg eps))) 1

theorem slowSourceInitialVariance_nonneg (n : Nat) :
    0 ≤ slowSourceInitialVariance n := by
  unfold slowSourceInitialVariance
  positivity

theorem slowSourceInitialVariance_pos {n : Nat} (hn : 1 ≤ n) :
    0 < slowSourceInitialVariance n := by
  have : (0 : Real) < (n : Real) := by exact_mod_cast hn
  unfold slowSourceInitialVariance
  positivity

/-- Raw phase count declared by the slow route on an input of declared squared radius
`R2`.  The assembly pins the frontier's phase count at the successor `slowPhasesP`. -/
noncomputable def slowPhases (n : Nat) (R2 : Real) : Nat :=
  slowOperationalPhases n (max 1 R2)

/-- Independent stream count declared by the slow route. -/
noncomputable def slowStreams (n : Nat) (R2 eps : Real) : Nat :=
  correctedRuntimeSamples (slowPhases n R2) eps

/-- Uniform retry cap declared by the slow route, at containment radius `R`. -/
noncomputable def slowRetries (n : Nat) (R2 eps R : Real) : Nat :=
  slowCanonicalRetriesCap (slowPhases n R2) (slowStreams n R2 eps) eps R
    (slowSourceInitialVariance n)

/-- Uniform mixing deadline declared by the slow route, at containment radius `R`. -/
noncomputable def slowDeadline (n : Nat) (R2 eps R : Real) : Nat :=
  slowCanonicalDeadlineCap n (slowPhases n R2) (slowStreams n R2 eps) eps R
    (slowSourceInitialVariance n) (max 1 R2)

theorem slowPhases_mono (n : Nat) {R2 R2' : Real} (h : R2 ≤ R2') :
    slowPhases n R2 ≤ slowPhases n R2' := by
  unfold slowPhases slowOperationalPhases slowSourcePhases
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coldPhases_eq_zero, coldPhases_eq_zero]
  · have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
    have hR : (0 : Real) < max 1 R2 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine coldPhases_antitone n (by positivity) ?_
    exact div_le_div_of_nonneg_left hs0.le hR (max_le_max (le_refl 1) h)

theorem slowStreams_mono (n : Nat) (eps : Real) {R2 R2' : Real} (h : R2 ≤ R2') :
    slowStreams n R2 eps ≤ slowStreams n R2' eps :=
  correctedRuntimeSamples_mono (slowPhases_mono n h) eps

/-! ### Step 3 — the overhead envelope and the effective runtime constant -/

set_option linter.unusedVariables false in
/-- The clipped slow-schedule overhead paid by one run at declared squared radius `R2`.
This is the `OV` factor of the effective-family interface, whose shape carries the
confidence argument `p` even though the slow overhead does not depend on it. -/
noncomputable def slowOverhead (n : Nat) (R2 eps p : Real) : Real :=
  max 1 (slowCanonicalRetainedRealEnvelope n (slowPhases n R2) (slowStreams n R2 eps)
    eps (Real.sqrt R2) (slowSourceInitialVariance n) (max 1 R2))

/-- The input-indexed runtime constant chosen by the slow route, taken at the squared
circumradius of the body.  The circumradius is the one radial parameter that both contains
the body (the frontier's `hKR`) and is dominated by the declared `R2` (the interface's
`hrad`); a second-moment radius fails the former. -/
noncomputable def slowEffective (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowOverhead n ((Ttc.TtcCircumRadius.circumR a.1) ^ 2) a.2.1 a.2.2

theorem one_le_slowOverhead (n : Nat) (R2 eps p : Real) : 1 ≤ slowOverhead n R2 eps p :=
  le_max_left _ _

theorem slowOverhead_nonneg (n : Nat) (R2 eps p : Real) : 0 ≤ slowOverhead n R2 eps p :=
  zero_le_one.trans (one_le_slowOverhead n R2 eps p)

theorem slowEffective_nonneg (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    0 ≤ slowEffective n a :=
  slowOverhead_nonneg n _ _ _

/-! ### Step 4 — the `heff` binder, at an unguarded declared radius -/

/-- The overhead is genuinely monotone in the declared squared radius, with no guard on
the dimension or the accuracy. -/
theorem slowOverhead_mono (n : Nat) (eps p : Real) {R2 R2' : Real} (h : R2 ≤ R2') :
    slowOverhead n R2 eps p ≤ slowOverhead n R2' eps p := by
  unfold slowOverhead
  refine max_le_max (le_refl 1) ?_
  rcases eq_or_ne eps 0 with rfl | heps
  · exact slowCanonicalRetainedRealEnvelope_mono_eps_zero
      (slowPhases_mono n h) (slowStreams_mono n 0 h) _ _ _ _ _ _
  · exact slowCanonicalRetainedRealEnvelope_mono heps
      (slowPhases_mono n h) (slowStreams_mono n eps h)
      (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h)
      (slowSourceInitialVariance_nonneg n)
      (zero_le_one.trans (le_max_left _ _)) (max_le_max (le_refl 1) h)

/-- The `heff` binder of `cvShapedExpectedImplementationOfEffectiveFamily`, at
`runtimeConstant = 1`.  It lands as a genuine inequality: `cvAdmBall` bounds the squared
circumradius by the declared `R2`, and the overhead is monotone in that declared radius. -/
theorem slowEffective_le_slowOverhead
    (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real)
    (hK : Ttc.CVShaped.cvAdmBall n K R2) :
    slowEffective n (K, eps, p) ≤ 1 * slowOverhead n R2 eps p := by
  rw [one_mul]
  exact slowOverhead_mono n eps p (circumR_sq_le_of_cvAdmBall hK)

/-! ### Step 5 — the `hscalar` binder of the frontier certificate -/

theorem slowCanonical_hscalar
    (n : Nat) (hn : 1 ≤ n) {eps R requested R2 p : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hR0 : 0 ≤ R) (hRR2 : R ^ 2 ≤ R2) :
    ((slowStreams n R2 eps : Nat) : ENNReal) * ((slowPhases n R2 : Nat) : ENNReal) *
        ENNReal.ofReal
          (10 * (slowRetries n R2 eps R : Real) * (slowDeadline n R2 eps R : Real) *
            (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowOverhead n R2 eps p) n R requested := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hN : (0 : Real) ≤ max 1 R2 := zero_le_one.trans (le_max_left _ _)
  have hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n (slowPhases n R2)
      (slowStreams n R2 eps) eps (max 1 R2) :=
    slowCanonicalGeometryEnvelope_nonneg _ _ _ _ hN
  have hpayload0 : 0 ≤ slowCanonicalDeadlinePayload (slowPhases n R2)
      (slowStreams n R2 eps) eps R (slowSourceInitialVariance n) :=
    slowCanonicalDeadlinePayload_nonneg
      (slowCanonicalShareFloor_pos_of_ne_zero heps.ne' R (slowSourceInitialVariance n))
      (slowCanonicalShareFloor_lt_one_of_nonneg _ _ eps R hs0.le)
  have hreal := slowCanonicalRetainedScalar_le_realEnvelope
    (n := n) (m := slowPhases n R2) (k := slowStreams n R2 eps) (eps := eps)
    (R := R) (s0 := slowSourceInitialVariance n) (N := max 1 R2)
    heps heps1 hs0 hgeom0 hpayload0
  have hRsqrt : R ≤ Real.sqrt R2 := by
    have := Real.sqrt_le_sqrt hRR2
    rwa [Real.sqrt_sq hR0] at this
  have hmono := slowCanonicalRetainedRealEnvelope_mono (n := n)
    (m := slowPhases n R2) (m' := slowPhases n R2)
    (k := slowStreams n R2 eps) (k' := slowStreams n R2 eps)
    (eps := eps) (R := R) (R' := Real.sqrt R2)
    (s0 := slowSourceInitialVariance n) (N := max 1 R2) (N' := max 1 R2)
    heps.ne' (le_refl _) (le_refl _) hR0 hRsqrt hs0.le hN (le_refl _)
  have hover : (slowStreams n R2 eps : Real) * (slowPhases n R2 : Real) *
      (10 * (slowRetries n R2 eps R : Real) * (slowDeadline n R2 eps R : Real) *
        (2 * Real.exp 1)) ≤ slowOverhead n R2 eps p := by
    refine hreal.trans (hmono.trans ?_)
    exact le_max_right _ _
  have hcore : slowOverhead n R2 eps p ≤
      sourceOneRunQueryEnvelope (slowOverhead n R2 eps p) n R requested :=
    le_sourceOneRunQueryEnvelope_of_le hn hreq hreq1 (slowOverhead_nonneg n R2 eps p)
  have hk0 : (0 : Real) ≤ (slowStreams n R2 eps : Nat) := by positivity
  have hm0 : (0 : Real) ≤ (slowPhases n R2 : Nat) := by positivity
  unfold sourceOneRunQueryBudget
  rw [← ENNReal.ofReal_natCast (slowStreams n R2 eps),
    ← ENNReal.ofReal_natCast (slowPhases n R2),
    ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (mul_nonneg hk0 hm0)]
  exact ENNReal.ofReal_le_ofReal (hover.trans hcore)

/-- The form actually consumed by the frontier certificate, whose own phase count `m`
satisfies `m + 1 = slowPhases n R2`: any smaller phase and stream count is still covered. -/
theorem slowCanonical_hscalar_le
    (n : Nat) (hn : 1 ≤ n) {m k : Nat} {eps R requested R2 p : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hR0 : 0 ≤ R) (hRR2 : R ^ 2 ≤ R2)
    (hm : m ≤ slowPhases n R2) (hk : k ≤ slowStreams n R2 eps) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowRetries n R2 eps R : Real) * (slowDeadline n R2 eps R : Real) *
          (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowOverhead n R2 eps p) n R requested := by
  refine le_trans ?_ (slowCanonical_hscalar n hn (p := p) heps heps1 hreq hreq1 hR0 hRR2)
  have hkE : (k : ENNReal) ≤ ((slowStreams n R2 eps : Nat) : ENNReal) := by
    exact_mod_cast hk
  have hmE : (m : ENNReal) ≤ ((slowPhases n R2 : Nat) : ENNReal) := by
    exact_mod_cast hm
  gcongr

/-- The `hscalar` binder at the circumradius: the budget's radial parameter is the very
radius the slow schedule runs at, and its runtime constant is the input's own
`slowEffective`.  Here the `R ^ 2 ≤ R2` side condition is definitional. -/
theorem slowCanonical_hscalar_circumR
    (n : Nat) (hn : 1 ≤ n) {m k : Nat} {K : Set (Ttc.Space n)} {eps requested p : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hm : m ≤ slowPhases n (Ttc.TtcCircumRadius.circumR K ^ 2))
    (hk : k ≤ slowStreams n (Ttc.TtcCircumRadius.circumR K ^ 2) eps) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowRetries n (Ttc.TtcCircumRadius.circumR K ^ 2) eps
            (Ttc.TtcCircumRadius.circumR K) : Real) *
          (slowDeadline n (Ttc.TtcCircumRadius.circumR K ^ 2) eps
            (Ttc.TtcCircumRadius.circumR K) : Real) *
          (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowEffective n (K, eps, p)) n
        (Ttc.TtcCircumRadius.circumR K) requested :=
  slowCanonical_hscalar_le n hn (p := p) (R2 := Ttc.TtcCircumRadius.circumR K ^ 2)
    (R := Ttc.TtcCircumRadius.circumR K) heps heps1 hreq hreq1
    (Ttc.TtcCircumRadius.circumR_nonneg K) (le_refl _) hm hk

/-! ### The successor phase count actually pinned by the assembly

The frontier certificate is instantiated at `slowOperationalPhases n N + 1`: the successor
makes its `0 < m` binder free, and it is the phase count at which
`Ttc.CVSlowCanonicalMomentBinders.slowCanonical_hexact_at_slowPhases` is stated.  Every
declaration below is the corresponding unprimed one with `slowPhases` replaced by
`slowPhasesP`; the envelope monotonicity lemma is already stated at arbitrary phase and
stream counts, so it applies verbatim. -/

/-- Phase count pinned by the assembly. -/
noncomputable def slowPhasesP (n : Nat) (R2 : Real) : Nat := slowPhases n R2 + 1

/-- Independent stream count at the pinned phase count. -/
noncomputable def slowStreamsP (n : Nat) (R2 eps : Real) : Nat :=
  correctedRuntimeSamples (slowPhasesP n R2) eps

/-- Uniform retry cap at the pinned phase count, at containment radius `R`. -/
noncomputable def slowRetriesP (n : Nat) (R2 eps R : Real) : Nat :=
  slowCanonicalRetriesCap (slowPhasesP n R2) (slowStreamsP n R2 eps) eps R
    (slowSourceInitialVariance n)

/-- Uniform mixing deadline at the pinned phase count, at containment radius `R`. -/
noncomputable def slowDeadlineP (n : Nat) (R2 eps R : Real) : Nat :=
  slowCanonicalDeadlineCap n (slowPhasesP n R2) (slowStreamsP n R2 eps) eps R
    (slowSourceInitialVariance n) (max 1 R2)

theorem slowPhasesP_mono (n : Nat) {R2 R2' : Real} (h : R2 ≤ R2') :
    slowPhasesP n R2 ≤ slowPhasesP n R2' :=
  Nat.add_le_add_right (slowPhases_mono n h) 1

theorem slowStreamsP_mono (n : Nat) (eps : Real) {R2 R2' : Real} (h : R2 ≤ R2') :
    slowStreamsP n R2 eps ≤ slowStreamsP n R2' eps :=
  correctedRuntimeSamples_mono (slowPhasesP_mono n h) eps

set_option linter.unusedVariables false in
/-- The clipped slow-schedule overhead at the pinned phase count.  This is the `OV` factor
of the effective-family interface. -/
noncomputable def slowOverheadP (n : Nat) (R2 eps p : Real) : Real :=
  max 1 (slowCanonicalRetainedRealEnvelope n (slowPhasesP n R2) (slowStreamsP n R2 eps)
    eps (Real.sqrt R2) (slowSourceInitialVariance n) (max 1 R2))

/-- The input-indexed runtime constant chosen by the slow route, taken at the squared
circumradius of the body.  The circumradius is the one radial parameter that both contains
the body (the frontier's `hKR`) and is dominated by the declared `R2` (the interface's
`hrad`); a second-moment radius fails the former. -/
noncomputable def slowEffectiveP (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowOverheadP n ((Ttc.TtcCircumRadius.circumR a.1) ^ 2) a.2.1 a.2.2

theorem one_le_slowOverheadP (n : Nat) (R2 eps p : Real) : 1 ≤ slowOverheadP n R2 eps p :=
  le_max_left _ _

theorem slowOverheadP_nonneg (n : Nat) (R2 eps p : Real) : 0 ≤ slowOverheadP n R2 eps p :=
  zero_le_one.trans (one_le_slowOverheadP n R2 eps p)

theorem slowEffectiveP_nonneg (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    0 ≤ slowEffectiveP n a :=
  slowOverheadP_nonneg n _ _ _

theorem slowOverheadP_mono (n : Nat) (eps p : Real) {R2 R2' : Real} (h : R2 ≤ R2') :
    slowOverheadP n R2 eps p ≤ slowOverheadP n R2' eps p := by
  unfold slowOverheadP
  refine max_le_max (le_refl 1) ?_
  rcases eq_or_ne eps 0 with rfl | heps
  · exact slowCanonicalRetainedRealEnvelope_mono_eps_zero
      (slowPhasesP_mono n h) (slowStreamsP_mono n 0 h) _ _ _ _ _ _
  · exact slowCanonicalRetainedRealEnvelope_mono heps
      (slowPhasesP_mono n h) (slowStreamsP_mono n eps h)
      (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h)
      (slowSourceInitialVariance_nonneg n)
      (zero_le_one.trans (le_max_left _ _)) (max_le_max (le_refl 1) h)

/-- The `heff` binder of `cvShapedExpectedImplementationOfEffectiveFamily` at the pinned
phase count and `runtimeConstant = 1`.  It lands as a genuine inequality: `cvAdmBall`
bounds the squared circumradius by the declared `R2`, and the overhead is monotone in that
declared radius. -/
theorem slowEffectiveP_le_slowOverheadP
    (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real)
    (hK : Ttc.CVShaped.cvAdmBall n K R2) :
    slowEffectiveP n (K, eps, p) ≤ 1 * slowOverheadP n R2 eps p := by
  rw [one_mul]
  exact slowOverheadP_mono n eps p (circumR_sq_le_of_cvAdmBall hK)

theorem slowCanonical_hscalarP
    (n : Nat) (hn : 1 ≤ n) {eps R requested R2 p : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hR0 : 0 ≤ R) (hRR2 : R ^ 2 ≤ R2) :
    ((slowStreamsP n R2 eps : Nat) : ENNReal) * ((slowPhasesP n R2 : Nat) : ENNReal) *
        ENNReal.ofReal
          (10 * (slowRetriesP n R2 eps R : Real) * (slowDeadlineP n R2 eps R : Real) *
            (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowOverheadP n R2 eps p) n R requested := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hN : (0 : Real) ≤ max 1 R2 := zero_le_one.trans (le_max_left _ _)
  have hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n (slowPhasesP n R2)
      (slowStreamsP n R2 eps) eps (max 1 R2) :=
    slowCanonicalGeometryEnvelope_nonneg _ _ _ _ hN
  have hpayload0 : 0 ≤ slowCanonicalDeadlinePayload (slowPhasesP n R2)
      (slowStreamsP n R2 eps) eps R (slowSourceInitialVariance n) :=
    slowCanonicalDeadlinePayload_nonneg
      (slowCanonicalShareFloor_pos_of_ne_zero heps.ne' R (slowSourceInitialVariance n))
      (slowCanonicalShareFloor_lt_one_of_nonneg _ _ eps R hs0.le)
  have hreal := slowCanonicalRetainedScalar_le_realEnvelope
    (n := n) (m := slowPhasesP n R2) (k := slowStreamsP n R2 eps) (eps := eps)
    (R := R) (s0 := slowSourceInitialVariance n) (N := max 1 R2)
    heps heps1 hs0 hgeom0 hpayload0
  have hRsqrt : R ≤ Real.sqrt R2 := by
    have := Real.sqrt_le_sqrt hRR2
    rwa [Real.sqrt_sq hR0] at this
  have hmono := slowCanonicalRetainedRealEnvelope_mono (n := n)
    (m := slowPhasesP n R2) (m' := slowPhasesP n R2)
    (k := slowStreamsP n R2 eps) (k' := slowStreamsP n R2 eps)
    (eps := eps) (R := R) (R' := Real.sqrt R2)
    (s0 := slowSourceInitialVariance n) (N := max 1 R2) (N' := max 1 R2)
    heps.ne' (le_refl _) (le_refl _) hR0 hRsqrt hs0.le hN (le_refl _)
  have hover : (slowStreamsP n R2 eps : Real) * (slowPhasesP n R2 : Real) *
      (10 * (slowRetriesP n R2 eps R : Real) * (slowDeadlineP n R2 eps R : Real) *
        (2 * Real.exp 1)) ≤ slowOverheadP n R2 eps p := by
    refine hreal.trans (hmono.trans ?_)
    exact le_max_right _ _
  have hcore : slowOverheadP n R2 eps p ≤
      sourceOneRunQueryEnvelope (slowOverheadP n R2 eps p) n R requested :=
    le_sourceOneRunQueryEnvelope_of_le hn hreq hreq1 (slowOverheadP_nonneg n R2 eps p)
  have hk0 : (0 : Real) ≤ (slowStreamsP n R2 eps : Nat) := by positivity
  have hm0 : (0 : Real) ≤ (slowPhasesP n R2 : Nat) := by positivity
  unfold sourceOneRunQueryBudget
  rw [← ENNReal.ofReal_natCast (slowStreamsP n R2 eps),
    ← ENNReal.ofReal_natCast (slowPhasesP n R2),
    ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (mul_nonneg hk0 hm0)]
  exact ENNReal.ofReal_le_ofReal (hover.trans hcore)

/-- The form actually consumed by the frontier certificate: its own phase count `m`
satisfies `m + 1 = slowPhasesP n R2`, and any smaller phase and stream count is covered. -/
theorem slowCanonical_hscalarP_le
    (n : Nat) (hn : 1 ≤ n) {m k : Nat} {eps R requested R2 p : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hR0 : 0 ≤ R) (hRR2 : R ^ 2 ≤ R2)
    (hm : m ≤ slowPhasesP n R2) (hk : k ≤ slowStreamsP n R2 eps) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowRetriesP n R2 eps R : Real) * (slowDeadlineP n R2 eps R : Real) *
          (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowOverheadP n R2 eps p) n R requested := by
  refine le_trans ?_ (slowCanonical_hscalarP n hn (p := p) heps heps1 hreq hreq1 hR0 hRR2)
  have hkE : (k : ENNReal) ≤ ((slowStreamsP n R2 eps : Nat) : ENNReal) := by
    exact_mod_cast hk
  have hmE : (m : ENNReal) ≤ ((slowPhasesP n R2 : Nat) : ENNReal) := by
    exact_mod_cast hm
  gcongr

/-- `hscalar` at the pinned phase count and the circumradius: the budget's radial parameter
is the radius the schedule actually runs at, and its runtime constant is the input's own
`slowEffectiveP`.  The `R ^ 2 ≤ R2` side condition is definitional here. -/
theorem slowCanonical_hscalarP_circumR
    (n : Nat) (hn : 1 ≤ n) {m k : Nat} {K : Set (Ttc.Space n)} {eps requested p : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hm : m ≤ slowPhasesP n (Ttc.TtcCircumRadius.circumR K ^ 2))
    (hk : k ≤ slowStreamsP n (Ttc.TtcCircumRadius.circumR K ^ 2) eps) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowRetriesP n (Ttc.TtcCircumRadius.circumR K ^ 2) eps
            (Ttc.TtcCircumRadius.circumR K) : Real) *
          (slowDeadlineP n (Ttc.TtcCircumRadius.circumR K ^ 2) eps
            (Ttc.TtcCircumRadius.circumR K) : Real) *
          (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowEffectiveP n (K, eps, p)) n
        (Ttc.TtcCircumRadius.circumR K) requested :=
  slowCanonical_hscalarP_le n hn (p := p) (R2 := Ttc.TtcCircumRadius.circumR K ^ 2)
    (R := Ttc.TtcCircumRadius.circumR K) heps heps1 hreq hreq1
    (Ttc.TtcCircumRadius.circumR_nonneg K) (le_refl _) hm hk

/-! ## The uniform-pair stack

The frontier theorem's `hslackDef` / `hboundDef` binders force the *uniform* factor-seven
slack/boundSq pair of `Ttc.CVSlowCanonicalUniformParameters`, whose exponential share
branch is `1/18` rather than the canonical `2/33`.  Since `1/18 < 2/33`, the canonical
floor is **not** below the share the frontier needs, so the whole overhead construction is
repeated here on `Ttc.CVSlowUniformShareBounds`.  Everything below is the canonical
development above with `slowCanonical*` replaced by `slowUniform*`; only the floor
changes, so every proof is the same argument.

`slowUniformRetainedRealEnvelope` and its workhorse comparison do not exist upstream (the
uniform file stops at the two per-phase cast lemmas), so they are defined here. -/

theorem slowUniformShareFloor_pos_of_ne_zero
    {m k : Nat} {eps : Real} (heps : eps ≠ 0) (R s0 : Real) :
    0 < slowUniformShareFloor m k eps R s0 := by
  unfold slowUniformShareFloor blockShare
  exact lt_min (div_pos (correctedNu_pos_of_ne_zero heps) (by positivity)) (by positivity)

/-- The uniform floor is below one on every input, with no accuracy guard: the
exponential arm alone is at most `1/18`. -/
theorem slowUniformShareFloor_lt_one_of_nonneg
    (m k : Nat) (eps R : Real) {s0 : Real} (hs0 : 0 ≤ s0) :
    slowUniformShareFloor m k eps R s0 < 1 := by
  have hx : 0 ≤ R ^ 2 / (2 * s0) := by positivity
  have hexp : (1 : Real) ≤ Real.exp (R ^ 2 / (2 * s0)) := Real.one_le_exp hx
  have hexp2 : (1 : Real) ≤ Real.exp (R ^ 2 / (2 * s0)) ^ 2 := by nlinarith
  have harm : 1 / (18 * Real.exp (R ^ 2 / (2 * s0)) ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  exact lt_of_le_of_lt (min_le_right _ _) harm

theorem slowUniformShareFloor_antitone
    {m m' k k' : Nat} {eps R R' s0 : Real}
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0) :
    slowUniformShareFloor m' k' eps R' s0 ≤ slowUniformShareFloor m k eps R s0 := by
  unfold slowUniformShareFloor
  have hsq : R ^ 2 ≤ R' ^ 2 := by nlinarith
  have harm : 1 / (18 * Real.exp (R' ^ 2 / (2 * s0)) ^ 2) ≤
      1 / (18 * Real.exp (R ^ 2 / (2 * s0)) ^ 2) := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; norm_num
    · have hx : R ^ 2 / (2 * s0) ≤ R' ^ 2 / (2 * s0) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      have he : Real.exp (R ^ 2 / (2 * s0)) ≤ Real.exp (R' ^ 2 / (2 * s0)) :=
        Real.exp_le_exp.2 hx
      have he0 : (0 : Real) < Real.exp (R ^ 2 / (2 * s0)) := Real.exp_pos _
      gcongr
  exact min_le_min (blockShare_antitone hm hk eps) harm

theorem slowUniformRetryRealEnvelope_nonneg
    (m k : Nat) (eps R : Real) {s0 : Real} (hs0 : 0 ≤ s0) :
    0 ≤ slowUniformRetryRealEnvelope m k eps R s0 := by
  unfold slowUniformRetryRealEnvelope
  have h0 := slowUniformShareFloor_nonneg m k eps R s0
  have h1 := slowUniformShareFloor_lt_one_of_nonneg m k eps R hs0
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]
    norm_num [Real.logb]
  · have hge : (1 : Real) ≤ 1 / slowUniformShareFloor m k eps R s0 := by
      rw [le_div_iff₀ h]; linarith
    have := Real.logb_nonneg (b := 2) (by norm_num) hge
    linarith

theorem slowUniformRetryRealEnvelope_mono
    {m m' k k' : Nat} {eps R R' s0 : Real} (heps : eps ≠ 0)
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0) :
    slowUniformRetryRealEnvelope m k eps R s0 ≤
      slowUniformRetryRealEnvelope m' k' eps R' s0 := by
  unfold slowUniformRetryRealEnvelope
  have hf0' : 0 < slowUniformShareFloor m' k' eps R' s0 :=
    slowUniformShareFloor_pos_of_ne_zero heps R' s0
  have hf0 : 0 < slowUniformShareFloor m k eps R s0 :=
    slowUniformShareFloor_pos_of_ne_zero heps R s0
  have hle := slowUniformShareFloor_antitone (eps := eps) hm hk hR0 hRR hs0
  have hinv : 1 / slowUniformShareFloor m k eps R s0 ≤
      1 / slowUniformShareFloor m' k' eps R' s0 :=
    one_div_le_one_div_of_le hf0' hle
  have hlog := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
    (one_div_pos.mpr hf0) (one_div_pos.mpr hf0')).2 hinv
  linarith

theorem slowUniformDeadlinePayload_mono
    {m m' k k' : Nat} {eps R R' s0 : Real} (heps : eps ≠ 0)
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0) :
    slowUniformDeadlinePayload m k eps R s0 ≤
      slowUniformDeadlinePayload m' k' eps R' s0 :=
  slowDeadlinePayload_le_uniform (m := m') (k := k') (eps := eps) (R := R') (s0 := s0)
    (share := slowUniformShareFloor m k eps R s0)
    (slowUniformShareFloor_pos_of_ne_zero heps R' s0)
    (slowUniformShareFloor_antitone (eps := eps) hm hk hR0 hRR hs0)

theorem slowUniformDeadlineRealEnvelope_nonneg
    (n m k : Nat) {eps R s0 N : Real} (heps : eps ≠ 0) (hs0 : 0 ≤ s0) (hN : 0 ≤ N) :
    0 ≤ slowUniformDeadlineRealEnvelope n m k eps R s0 N := by
  unfold slowUniformDeadlineRealEnvelope
  have hG := slowCanonicalGeometryEnvelope_nonneg n m k eps hN
  have hP := slowUniformDeadlinePayload_nonneg
    (slowUniformShareFloor_pos_of_ne_zero (m := m) (k := k) heps R s0)
    (slowUniformShareFloor_lt_one_of_nonneg m k eps R hs0)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem slowUniformDeadlineRealEnvelope_mono
    {n m m' k k' : Nat} {eps R R' s0 N N' : Real} (heps : eps ≠ 0)
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0)
    (hN : 0 ≤ N) (hNN : N ≤ N') :
    slowUniformDeadlineRealEnvelope n m k eps R s0 N ≤
      slowUniformDeadlineRealEnvelope n m' k' eps R' s0 N' := by
  unfold slowUniformDeadlineRealEnvelope
  have hG := slowCanonicalGeometryEnvelope_nonneg n m k eps hN
  have hGG := slowCanonicalGeometryEnvelope_mono (n := n) heps hm hk hNN
  have hP := slowUniformDeadlinePayload_nonneg
    (slowUniformShareFloor_pos_of_ne_zero (m := m) (k := k) heps R s0)
    (slowUniformShareFloor_lt_one_of_nonneg m k eps R hs0)
  have hPP := slowUniformDeadlinePayload_mono heps hm hk hR0 hRR hs0
  have hG' : 0 ≤ slowCanonicalGeometryEnvelope n m' k' eps N' :=
    slowCanonicalGeometryEnvelope_nonneg n m' k' eps (hN.trans hNN)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  gcongr

/-- Exact explicit overhead paid by all streams and phases of one slow run, at the
uniform slack/boundSq pair. -/
noncomputable def slowUniformRetainedRealEnvelope
    (n m k : Nat) (eps R s0 N : Real) : Real :=
  (k : Real) * (m : Real) * 10 *
    slowUniformRetryRealEnvelope m k eps R s0 *
    slowUniformDeadlineRealEnvelope n m k eps R s0 N *
    (2 * Real.exp 1)

/-- The uniform analogue of
`Ttc.CVSlowCanonicalRuntimeComparison.slowCanonicalRetainedScalar_le_realEnvelope`.
Unlike the canonical one it needs no positivity hypothesis on `s0`. -/
theorem slowUniformRetainedScalar_le_realEnvelope
    {n m k : Nat} {eps R s0 N : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N)
    (hpayload0 : 0 ≤ slowUniformDeadlinePayload m k eps R s0) :
    (k : Real) * (m : Real) *
        (10 * (slowUniformRetriesCap m k eps R s0 : Real) *
          (slowUniformDeadlineCap n m k eps R s0 N : Real) *
          (2 * Real.exp 1)) ≤
      slowUniformRetainedRealEnvelope n m k eps R s0 N := by
  have hL := slowUniformRetriesCap_cast_le_realEnvelope
    (m := m) (k := k) (R := R) (s0 := s0) heps heps1
  have hT := slowUniformDeadlineCap_cast_le_realEnvelope
    (n := n) (m := m) (k := k) (eps := eps) (R := R) (s0 := s0) (N := N)
    hgeom0 hpayload0
  have hL0 : 0 ≤ slowUniformRetryRealEnvelope m k eps R s0 :=
    (by positivity : (0 : Real) ≤ slowUniformRetriesCap m k eps R s0) |>.trans hL
  have hT0 : 0 ≤ slowUniformDeadlineRealEnvelope n m k eps R s0 N :=
    (by positivity : (0 : Real) ≤ slowUniformDeadlineCap n m k eps R s0 N) |>.trans hT
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have hcap0 : (0 : Real) ≤ (slowUniformDeadlineCap n m k eps R s0 N : Real) := by positivity
  unfold slowUniformRetainedRealEnvelope
  calc
    _ = (k : Real) * (m : Real) * 10 *
        (slowUniformRetriesCap m k eps R s0 : Real) *
        (slowUniformDeadlineCap n m k eps R s0 N : Real) *
        (2 * Real.exp 1) := by ring
    _ ≤ (k : Real) * (m : Real) * 10 *
        slowUniformRetryRealEnvelope m k eps R s0 *
        (slowUniformDeadlineCap n m k eps R s0 N : Real) *
        (2 * Real.exp 1) := by gcongr
    _ ≤ (k : Real) * (m : Real) * 10 *
        slowUniformRetryRealEnvelope m k eps R s0 *
        slowUniformDeadlineRealEnvelope n m k eps R s0 N *
        (2 * Real.exp 1) := by gcongr

theorem slowUniformRetainedRealEnvelope_mono
    {n m m' k k' : Nat} {eps R R' s0 N N' : Real} (heps : eps ≠ 0)
    (hm : m ≤ m') (hk : k ≤ k') (hR0 : 0 ≤ R) (hRR : R ≤ R') (hs0 : 0 ≤ s0)
    (hN : 0 ≤ N) (hNN : N ≤ N') :
    slowUniformRetainedRealEnvelope n m k eps R s0 N ≤
      slowUniformRetainedRealEnvelope n m' k' eps R' s0 N' := by
  unfold slowUniformRetainedRealEnvelope
  have hmR : (m : Real) ≤ (m' : Real) := by exact_mod_cast hm
  have hkR : (k : Real) ≤ (k' : Real) := by exact_mod_cast hk
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have hm0' : (0 : Real) ≤ (m' : Real) := by positivity
  have hk0' : (0 : Real) ≤ (k' : Real) := by positivity
  have hL0 := slowUniformRetryRealEnvelope_nonneg m k eps R hs0
  have hL0' := slowUniformRetryRealEnvelope_nonneg m' k' eps R' hs0
  have hLL := slowUniformRetryRealEnvelope_mono heps hm hk hR0 hRR hs0
  have hT0 := slowUniformDeadlineRealEnvelope_nonneg n m k (R := R) (N := N) heps hs0 hN
  have hTT := slowUniformDeadlineRealEnvelope_mono (n := n) heps hm hk hR0 hRR hs0 hN hNN
  have he0 : (0 : Real) ≤ 2 * Real.exp 1 := by positivity
  gcongr

/-! ### The degenerate accuracy `eps = 0`, at the uniform floor

Unchanged in substance: the uniform floor has the same `min (blockShare …) (positive)`
shape, so it still vanishes at `eps = 0` and the two logarithmic factors still collapse to
the same constants `16` and `0`. -/

theorem slowUniformShareFloor_eps_zero (m k : Nat) (R s0 : Real) :
    slowUniformShareFloor m k 0 R s0 = 0 := by
  have hnu : correctedNu m (0 : Real) = 0 := by rw [correctedNu_eq]; norm_num
  unfold slowUniformShareFloor blockShare
  rw [hnu, zero_div]
  exact min_eq_left (by positivity)

theorem slowUniformRetryRealEnvelope_eps_zero (m k : Nat) (R s0 : Real) :
    slowUniformRetryRealEnvelope m k 0 R s0 = 16 := by
  unfold slowUniformRetryRealEnvelope
  rw [slowUniformShareFloor_eps_zero]
  norm_num

theorem slowUniformDeadlinePayload_eps_zero (m k : Nat) (R s0 : Real) :
    slowUniformDeadlinePayload m k 0 R s0 = 0 := by
  unfold slowUniformDeadlinePayload
  rw [slowUniformShareFloor_eps_zero]
  norm_num

theorem slowUniformDeadlineRealEnvelope_eps_zero (n m k : Nat) (R s0 N : Real) :
    slowUniformDeadlineRealEnvelope n m k 0 R s0 N = 3 := by
  unfold slowUniformDeadlineRealEnvelope
  rw [slowUniformDeadlinePayload_eps_zero]
  norm_num

theorem slowUniformRetainedRealEnvelope_eps_zero (n m k : Nat) (R s0 N : Real) :
    slowUniformRetainedRealEnvelope n m k 0 R s0 N =
      (k : Real) * (m : Real) * (480 * (2 * Real.exp 1)) := by
  unfold slowUniformRetainedRealEnvelope
  rw [slowUniformRetryRealEnvelope_eps_zero, slowUniformDeadlineRealEnvelope_eps_zero]
  ring

theorem slowUniformRetainedRealEnvelope_mono_eps_zero
    {n m m' k k' : Nat} (hm : m ≤ m') (hk : k ≤ k') (R R' s0 s0' N N' : Real) :
    slowUniformRetainedRealEnvelope n m k 0 R s0 N ≤
      slowUniformRetainedRealEnvelope n m' k' 0 R' s0' N' := by
  rw [slowUniformRetainedRealEnvelope_eps_zero, slowUniformRetainedRealEnvelope_eps_zero]
  have hmR : (m : Real) ≤ (m' : Real) := by exact_mod_cast hm
  have hkR : (k : Real) ≤ (k' : Real) := by exact_mod_cast hk
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have he0 : (0 : Real) ≤ 480 * (2 * Real.exp 1) := by positivity
  gcongr

/-! ### The uniform `P` family — this is what the assembly consumes -/

/-- Uniform retry cap at the pinned phase count, at containment radius `R`. -/
noncomputable def slowUniformRetriesP (n : Nat) (R2 eps R : Real) : Nat :=
  slowUniformRetriesCap (slowPhasesP n R2) (slowStreamsP n R2 eps) eps R
    (slowSourceInitialVariance n)

/-- Uniform mixing deadline at the pinned phase count, at containment radius `R`. -/
noncomputable def slowUniformDeadlineP (n : Nat) (R2 eps R : Real) : Nat :=
  slowUniformDeadlineCap n (slowPhasesP n R2) (slowStreamsP n R2 eps) eps R
    (slowSourceInitialVariance n) (max 1 R2)

set_option linter.unusedVariables false in
/-- The clipped uniform-pair slow-schedule overhead at the pinned phase count.  This is the
`OV` factor of the effective-family interface for the uniform route. -/
noncomputable def slowUniformOverheadP (n : Nat) (R2 eps p : Real) : Real :=
  max 1 (slowUniformRetainedRealEnvelope n (slowPhasesP n R2) (slowStreamsP n R2 eps)
    eps (Real.sqrt R2) (slowSourceInitialVariance n) (max 1 R2))

/-- The input-indexed runtime constant chosen by the uniform slow route, at the squared
circumradius of the body. -/
noncomputable def slowUniformEffectiveP (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowUniformOverheadP n ((Ttc.TtcCircumRadius.circumR a.1) ^ 2) a.2.1 a.2.2

theorem one_le_slowUniformOverheadP (n : Nat) (R2 eps p : Real) :
    1 ≤ slowUniformOverheadP n R2 eps p := le_max_left _ _

theorem slowUniformOverheadP_nonneg (n : Nat) (R2 eps p : Real) :
    0 ≤ slowUniformOverheadP n R2 eps p :=
  zero_le_one.trans (one_le_slowUniformOverheadP n R2 eps p)

theorem slowUniformEffectiveP_nonneg (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    0 ≤ slowUniformEffectiveP n a :=
  slowUniformOverheadP_nonneg n _ _ _

theorem slowUniformOverheadP_mono (n : Nat) (eps p : Real) {R2 R2' : Real} (h : R2 ≤ R2') :
    slowUniformOverheadP n R2 eps p ≤ slowUniformOverheadP n R2' eps p := by
  unfold slowUniformOverheadP
  refine max_le_max (le_refl 1) ?_
  rcases eq_or_ne eps 0 with rfl | heps
  · exact slowUniformRetainedRealEnvelope_mono_eps_zero
      (slowPhasesP_mono n h) (slowStreamsP_mono n 0 h) _ _ _ _ _ _
  · exact slowUniformRetainedRealEnvelope_mono heps
      (slowPhasesP_mono n h) (slowStreamsP_mono n eps h)
      (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h)
      (slowSourceInitialVariance_nonneg n)
      (zero_le_one.trans (le_max_left _ _)) (max_le_max (le_refl 1) h)

/-- The `heff` binder of `cvShapedExpectedImplementationOfEffectiveFamily` for the uniform
route, at `runtimeConstant = 1`.  A genuine inequality, with no guard on `n`, `eps` or
`p`. -/
theorem slowUniformEffectiveP_le_slowUniformOverheadP
    (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real)
    (hK : Ttc.CVShaped.cvAdmBall n K R2) :
    slowUniformEffectiveP n (K, eps, p) ≤ 1 * slowUniformOverheadP n R2 eps p := by
  rw [one_mul]
  exact slowUniformOverheadP_mono n eps p (circumR_sq_le_of_cvAdmBall hK)

theorem slowUniform_hscalarP
    (n : Nat) (hn : 1 ≤ n) {eps R requested R2 p : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hR0 : 0 ≤ R) (hRR2 : R ^ 2 ≤ R2) :
    ((slowStreamsP n R2 eps : Nat) : ENNReal) * ((slowPhasesP n R2 : Nat) : ENNReal) *
        ENNReal.ofReal
          (10 * (slowUniformRetriesP n R2 eps R : Real) *
            (slowUniformDeadlineP n R2 eps R : Real) * (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowUniformOverheadP n R2 eps p) n R requested := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hN : (0 : Real) ≤ max 1 R2 := zero_le_one.trans (le_max_left _ _)
  have hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n (slowPhasesP n R2)
      (slowStreamsP n R2 eps) eps (max 1 R2) :=
    slowCanonicalGeometryEnvelope_nonneg _ _ _ _ hN
  have hpayload0 : 0 ≤ slowUniformDeadlinePayload (slowPhasesP n R2)
      (slowStreamsP n R2 eps) eps R (slowSourceInitialVariance n) :=
    slowUniformDeadlinePayload_nonneg
      (slowUniformShareFloor_pos_of_ne_zero heps.ne' R (slowSourceInitialVariance n))
      (slowUniformShareFloor_lt_one_of_nonneg _ _ eps R hs0.le)
  have hreal := slowUniformRetainedScalar_le_realEnvelope
    (n := n) (m := slowPhasesP n R2) (k := slowStreamsP n R2 eps) (eps := eps)
    (R := R) (s0 := slowSourceInitialVariance n) (N := max 1 R2)
    heps heps1 hgeom0 hpayload0
  have hRsqrt : R ≤ Real.sqrt R2 := by
    have := Real.sqrt_le_sqrt hRR2
    rwa [Real.sqrt_sq hR0] at this
  have hmono := slowUniformRetainedRealEnvelope_mono (n := n)
    (m := slowPhasesP n R2) (m' := slowPhasesP n R2)
    (k := slowStreamsP n R2 eps) (k' := slowStreamsP n R2 eps)
    (eps := eps) (R := R) (R' := Real.sqrt R2)
    (s0 := slowSourceInitialVariance n) (N := max 1 R2) (N' := max 1 R2)
    heps.ne' (le_refl _) (le_refl _) hR0 hRsqrt hs0.le hN (le_refl _)
  have hover : (slowStreamsP n R2 eps : Real) * (slowPhasesP n R2 : Real) *
      (10 * (slowUniformRetriesP n R2 eps R : Real) *
        (slowUniformDeadlineP n R2 eps R : Real) * (2 * Real.exp 1)) ≤
      slowUniformOverheadP n R2 eps p := by
    refine hreal.trans (hmono.trans ?_)
    exact le_max_right _ _
  have hcore : slowUniformOverheadP n R2 eps p ≤
      sourceOneRunQueryEnvelope (slowUniformOverheadP n R2 eps p) n R requested :=
    le_sourceOneRunQueryEnvelope_of_le hn hreq hreq1 (slowUniformOverheadP_nonneg n R2 eps p)
  have hk0 : (0 : Real) ≤ (slowStreamsP n R2 eps : Nat) := by positivity
  have hm0 : (0 : Real) ≤ (slowPhasesP n R2 : Nat) := by positivity
  unfold sourceOneRunQueryBudget
  rw [← ENNReal.ofReal_natCast (slowStreamsP n R2 eps),
    ← ENNReal.ofReal_natCast (slowPhasesP n R2),
    ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (mul_nonneg hk0 hm0)]
  exact ENNReal.ofReal_le_ofReal (hover.trans hcore)

/-- The form actually consumed by the frontier certificate: its own phase count `m`
satisfies `m + 1 = slowPhasesP n R2`, and any smaller phase and stream count is covered. -/
theorem slowUniform_hscalarP_le
    (n : Nat) (hn : 1 ≤ n) {m k : Nat} {eps R requested R2 p : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hR0 : 0 ≤ R) (hRR2 : R ^ 2 ≤ R2)
    (hm : m ≤ slowPhasesP n R2) (hk : k ≤ slowStreamsP n R2 eps) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowUniformRetriesP n R2 eps R : Real) *
          (slowUniformDeadlineP n R2 eps R : Real) * (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowUniformOverheadP n R2 eps p) n R requested := by
  refine le_trans ?_ (slowUniform_hscalarP n hn (p := p) heps heps1 hreq hreq1 hR0 hRR2)
  have hkE : (k : ENNReal) ≤ ((slowStreamsP n R2 eps : Nat) : ENNReal) := by
    exact_mod_cast hk
  have hmE : (m : ENNReal) ≤ ((slowPhasesP n R2 : Nat) : ENNReal) := by
    exact_mod_cast hm
  gcongr

/-- `hscalar` for the uniform route at the circumradius: the budget's radial parameter is
the radius the schedule actually runs at, and its runtime constant is the input's own
`slowUniformEffectiveP`.  The `R ^ 2 ≤ R2` side condition is definitional here. -/
theorem slowUniform_hscalarP_circumR
    (n : Nat) (hn : 1 ≤ n) {m k : Nat} {K : Set (Ttc.Space n)} {eps requested p : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hm : m ≤ slowPhasesP n (Ttc.TtcCircumRadius.circumR K ^ 2))
    (hk : k ≤ slowStreamsP n (Ttc.TtcCircumRadius.circumR K ^ 2) eps) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowUniformRetriesP n (Ttc.TtcCircumRadius.circumR K ^ 2) eps
            (Ttc.TtcCircumRadius.circumR K) : Real) *
          (slowUniformDeadlineP n (Ttc.TtcCircumRadius.circumR K ^ 2) eps
            (Ttc.TtcCircumRadius.circumR K) : Real) *
          (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowUniformEffectiveP n (K, eps, p)) n
        (Ttc.TtcCircumRadius.circumR K) requested :=
  slowUniform_hscalarP_le n hn (p := p) (R2 := Ttc.TtcCircumRadius.circumR K ^ 2)
    (R := Ttc.TtcCircumRadius.circumR K) heps heps1 hreq hreq1
    (Ttc.TtcCircumRadius.circumR_nonneg K) (le_refl _) hm hk

/-! ## The `Q` layer — the caps at the producer's own argument triple

`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` runs at phase count
`slowCanonicalPhases n R2`, which is definitionally `slowPhasesP n R2`, but its `hretries`
and `hsteps` binders quantify `scoreAwareRetries` at the *shifted* triple

  `(slowPhasesP n R2 + 1,  slowStreamsP n R2 epsP,  epsP / 2)`

— phase count shifted by one, stream count at `epsP`, accuracy slot halved.  The share
floor is antitone in the phase count and increasing in the accuracy argument, so both
shifts enlarge the cap and neither absorbs into the `P` layer by monotonicity.  Hence this
third layer, at exactly the producer's arguments.  Everything is the `P` proof with those
two substitutions. -/

/-- Uniform retry cap at the producer's argument triple. -/
noncomputable def slowUniformRetriesQ (n : Nat) (R2 epsP R : Real) : Nat :=
  slowUniformRetriesCap (slowPhasesP n R2 + 1) (slowStreamsP n R2 epsP) (epsP / 2) R
    (slowSourceInitialVariance n)

/-- Uniform mixing deadline at the producer's argument triple. -/
noncomputable def slowUniformDeadlineQ (n : Nat) (R2 epsP R : Real) : Nat :=
  slowUniformDeadlineCap n (slowPhasesP n R2 + 1) (slowStreamsP n R2 epsP) (epsP / 2) R
    (slowSourceInitialVariance n) (max 1 R2)

set_option linter.unusedVariables false in
/-- The clipped uniform overhead at the producer's argument triple.  This is the `OV`
factor consumed by the assembly. -/
noncomputable def slowUniformOverheadQ (n : Nat) (R2 epsP p : Real) : Real :=
  max 1 (slowUniformRetainedRealEnvelope n (slowPhasesP n R2 + 1) (slowStreamsP n R2 epsP)
    (epsP / 2) (Real.sqrt R2) (slowSourceInitialVariance n) (max 1 R2))

/-- The input-indexed runtime constant chosen by the assembly.  The overhead is evaluated
at `epsP := a.2.1 / 2`, because the construction is run at half the requested accuracy. -/
noncomputable def slowUniformEffectiveQ (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowUniformOverheadQ n ((Ttc.TtcCircumRadius.circumR a.1) ^ 2) (a.2.1 / 2) a.2.2

theorem one_le_slowUniformOverheadQ (n : Nat) (R2 epsP p : Real) :
    1 ≤ slowUniformOverheadQ n R2 epsP p := le_max_left _ _

theorem slowUniformOverheadQ_nonneg (n : Nat) (R2 epsP p : Real) :
    0 ≤ slowUniformOverheadQ n R2 epsP p :=
  zero_le_one.trans (one_le_slowUniformOverheadQ n R2 epsP p)

theorem slowUniformEffectiveQ_nonneg (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    0 ≤ slowUniformEffectiveQ n a :=
  slowUniformOverheadQ_nonneg n _ _ _

theorem slowUniformOverheadQ_mono
    (n : Nat) (epsP p : Real) {R2 R2' : Real} (h : R2 ≤ R2') :
    slowUniformOverheadQ n R2 epsP p ≤ slowUniformOverheadQ n R2' epsP p := by
  unfold slowUniformOverheadQ
  refine max_le_max (le_refl 1) ?_
  have hphase : slowPhasesP n R2 + 1 ≤ slowPhasesP n R2' + 1 :=
    Nat.add_le_add_right (slowPhasesP_mono n h) 1
  rcases eq_or_ne (epsP / 2) 0 with hz | heps
  · rw [hz]
    exact slowUniformRetainedRealEnvelope_mono_eps_zero
      hphase (slowStreamsP_mono n epsP h) _ _ _ _ _ _
  · exact slowUniformRetainedRealEnvelope_mono heps
      hphase (slowStreamsP_mono n epsP h)
      (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h)
      (slowSourceInitialVariance_nonneg n)
      (zero_le_one.trans (le_max_left _ _)) (max_le_max (le_refl 1) h)

/-- The `heff` binder at the producer's argument triple, at `runtimeConstant = 1`.  A
genuine inequality, with no guard on `n`, `eps` or `p`. -/
theorem slowUniformEffectiveQ_le_slowUniformOverheadQ
    (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real)
    (hK : Ttc.CVShaped.cvAdmBall n K R2) :
    slowUniformEffectiveQ n (K, eps, p) ≤ 1 * slowUniformOverheadQ n R2 (eps / 2) p := by
  rw [one_mul]
  exact slowUniformOverheadQ_mono n (eps / 2) p (circumR_sq_le_of_cvAdmBall hK)

theorem slowUniform_hscalarQ
    (n : Nat) (hn : 1 ≤ n) {epsP R requested R2 p : Real}
    (heps : 0 < epsP) (heps1 : epsP ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hR0 : 0 ≤ R) (hRR2 : R ^ 2 ≤ R2) :
    ((slowStreamsP n R2 epsP : Nat) : ENNReal) *
        ((slowPhasesP n R2 : Nat) : ENNReal) *
        ENNReal.ofReal
          (10 * (slowUniformRetriesQ n R2 epsP R : Real) *
            (slowUniformDeadlineQ n R2 epsP R : Real) * (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowUniformOverheadQ n R2 epsP p) n R requested := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hN : (0 : Real) ≤ max 1 R2 := zero_le_one.trans (le_max_left _ _)
  have hhalf : 0 < epsP / 2 := by linarith
  have hhalf1 : epsP / 2 ≤ 1 := by linarith
  have hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n (slowPhasesP n R2 + 1)
      (slowStreamsP n R2 epsP) (epsP / 2) (max 1 R2) :=
    slowCanonicalGeometryEnvelope_nonneg _ _ _ _ hN
  have hpayload0 : 0 ≤ slowUniformDeadlinePayload (slowPhasesP n R2 + 1)
      (slowStreamsP n R2 epsP) (epsP / 2) R (slowSourceInitialVariance n) :=
    slowUniformDeadlinePayload_nonneg
      (slowUniformShareFloor_pos_of_ne_zero hhalf.ne' R (slowSourceInitialVariance n))
      (slowUniformShareFloor_lt_one_of_nonneg _ _ (epsP / 2) R hs0.le)
  have hreal := slowUniformRetainedScalar_le_realEnvelope
    (n := n) (m := slowPhasesP n R2 + 1) (k := slowStreamsP n R2 epsP) (eps := epsP / 2)
    (R := R) (s0 := slowSourceInitialVariance n) (N := max 1 R2)
    hhalf hhalf1 hgeom0 hpayload0
  have hRsqrt : R ≤ Real.sqrt R2 := by
    have := Real.sqrt_le_sqrt hRR2
    rwa [Real.sqrt_sq hR0] at this
  have hmono := slowUniformRetainedRealEnvelope_mono (n := n)
    (m := slowPhasesP n R2 + 1) (m' := slowPhasesP n R2 + 1)
    (k := slowStreamsP n R2 epsP) (k' := slowStreamsP n R2 epsP)
    (eps := epsP / 2) (R := R) (R' := Real.sqrt R2)
    (s0 := slowSourceInitialVariance n) (N := max 1 R2) (N' := max 1 R2)
    hhalf.ne' (le_refl _) (le_refl _) hR0 hRsqrt hs0.le hN (le_refl _)
  have hcap : (slowStreamsP n R2 epsP : Real) * ((slowPhasesP n R2 + 1 : Nat) : Real) *
      (10 * (slowUniformRetriesQ n R2 epsP R : Real) *
        (slowUniformDeadlineQ n R2 epsP R : Real) * (2 * Real.exp 1)) ≤
      slowUniformOverheadQ n R2 epsP p := by
    refine hreal.trans (hmono.trans ?_)
    exact le_max_right _ _
  have hshift : (slowPhasesP n R2 : Real) ≤ ((slowPhasesP n R2 + 1 : Nat) : Real) := by
    push_cast; linarith
  have hrest0 : (0 : Real) ≤ 10 * (slowUniformRetriesQ n R2 epsP R : Real) *
      (slowUniformDeadlineQ n R2 epsP R : Real) * (2 * Real.exp 1) := by positivity
  have hk0 : (0 : Real) ≤ (slowStreamsP n R2 epsP : Nat) := by positivity
  have hover : (slowStreamsP n R2 epsP : Real) * (slowPhasesP n R2 : Real) *
      (10 * (slowUniformRetriesQ n R2 epsP R : Real) *
        (slowUniformDeadlineQ n R2 epsP R : Real) * (2 * Real.exp 1)) ≤
      slowUniformOverheadQ n R2 epsP p := by
    refine le_trans ?_ hcap
    gcongr
  have hcore : slowUniformOverheadQ n R2 epsP p ≤
      sourceOneRunQueryEnvelope (slowUniformOverheadQ n R2 epsP p) n R requested :=
    le_sourceOneRunQueryEnvelope_of_le hn hreq hreq1
      (slowUniformOverheadQ_nonneg n R2 epsP p)
  have hm0 : (0 : Real) ≤ (slowPhasesP n R2 : Nat) := by positivity
  unfold sourceOneRunQueryBudget
  rw [← ENNReal.ofReal_natCast (slowStreamsP n R2 epsP),
    ← ENNReal.ofReal_natCast (slowPhasesP n R2),
    ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (mul_nonneg hk0 hm0)]
  exact ENNReal.ofReal_le_ofReal (hover.trans hcore)

theorem slowUniform_hscalarQ_le
    (n : Nat) (hn : 1 ≤ n) {m k : Nat} {epsP R requested R2 p : Real}
    (heps : 0 < epsP) (heps1 : epsP ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hR0 : 0 ≤ R) (hRR2 : R ^ 2 ≤ R2)
    (hm : m ≤ slowPhasesP n R2) (hk : k ≤ slowStreamsP n R2 epsP) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowUniformRetriesQ n R2 epsP R : Real) *
          (slowUniformDeadlineQ n R2 epsP R : Real) * (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowUniformOverheadQ n R2 epsP p) n R requested := by
  refine le_trans ?_ (slowUniform_hscalarQ n hn (p := p) heps heps1 hreq hreq1 hR0 hRR2)
  have hkE : (k : ENNReal) ≤ ((slowStreamsP n R2 epsP : Nat) : ENNReal) := by
    exact_mod_cast hk
  have hmE : (m : ENNReal) ≤ ((slowPhasesP n R2 : Nat) : ENNReal) := by
    exact_mod_cast hm
  gcongr

/-- `hscalar` at the producer's argument triple and the circumradius.  This is the exact
binder of `Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` at
`runtimeConstant := slowUniformOverheadQ n (circumR K ^ 2) epsP p`. -/
theorem slowUniform_hscalarQ_circumR
    (n : Nat) (hn : 1 ≤ n) {m k : Nat} {K : Set (Ttc.Space n)} {epsP requested p : Real}
    (heps : 0 < epsP) (heps1 : epsP ≤ 1)
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hm : m ≤ slowPhasesP n (Ttc.TtcCircumRadius.circumR K ^ 2))
    (hk : k ≤ slowStreamsP n (Ttc.TtcCircumRadius.circumR K ^ 2) epsP) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowUniformRetriesQ n (Ttc.TtcCircumRadius.circumR K ^ 2) epsP
            (Ttc.TtcCircumRadius.circumR K) : Real) *
          (slowUniformDeadlineQ n (Ttc.TtcCircumRadius.circumR K ^ 2) epsP
            (Ttc.TtcCircumRadius.circumR K) : Real) *
          (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget
        (slowUniformOverheadQ n (Ttc.TtcCircumRadius.circumR K ^ 2) epsP p) n
        (Ttc.TtcCircumRadius.circumR K) requested :=
  slowUniform_hscalarQ_le n hn (p := p) (R2 := Ttc.TtcCircumRadius.circumR K ^ 2)
    (R := Ttc.TtcCircumRadius.circumR K) heps heps1 hreq hreq1
    (Ttc.TtcCircumRadius.circumR_nonneg K) (le_refl _) hm hk

#print axioms one_le_sourceOneRunCore
#print axioms le_sourceOneRunQueryEnvelope_of_le
#print axioms slowPhases_mono
#print axioms slowStreams_mono
#print axioms slowCanonicalRetainedRealEnvelope_mono
#print axioms one_le_slowOverhead
#print axioms slowEffective_nonneg
#print axioms slowOverhead_mono
#print axioms slowEffective_le_slowOverhead
#print axioms slowCanonical_hscalar
#print axioms slowCanonical_hscalar_le
#print axioms slowCanonical_hscalar_circumR
#print axioms slowPhasesP_mono
#print axioms slowStreamsP_mono
#print axioms one_le_slowOverheadP
#print axioms slowOverheadP_nonneg
#print axioms slowEffectiveP_nonneg
#print axioms slowOverheadP_mono
#print axioms slowEffectiveP_le_slowOverheadP
#print axioms slowCanonical_hscalarP
#print axioms slowCanonical_hscalarP_le
#print axioms slowCanonical_hscalarP_circumR

#print axioms slowUniformShareFloor_pos_of_ne_zero
#print axioms slowUniformShareFloor_lt_one_of_nonneg
#print axioms slowUniformShareFloor_antitone
#print axioms slowUniformRetryRealEnvelope_nonneg
#print axioms slowUniformRetryRealEnvelope_mono
#print axioms slowUniformDeadlinePayload_mono
#print axioms slowUniformDeadlineRealEnvelope_nonneg
#print axioms slowUniformDeadlineRealEnvelope_mono
#print axioms slowUniformRetainedScalar_le_realEnvelope
#print axioms slowUniformRetainedRealEnvelope_mono
#print axioms slowUniformRetainedRealEnvelope_eps_zero
#print axioms slowUniformRetainedRealEnvelope_mono_eps_zero
#print axioms slowPhasesP_mono
#print axioms slowStreamsP_mono
#print axioms one_le_slowUniformOverheadP
#print axioms slowUniformOverheadP_nonneg
#print axioms slowUniformEffectiveP_nonneg
#print axioms slowUniformOverheadP_mono
#print axioms slowUniformEffectiveP_le_slowUniformOverheadP
#print axioms slowUniform_hscalarP
#print axioms slowUniform_hscalarP_le
#print axioms slowUniform_hscalarP_circumR

#print axioms one_le_slowUniformOverheadQ
#print axioms slowUniformOverheadQ_nonneg
#print axioms slowUniformEffectiveQ_nonneg
#print axioms slowUniformOverheadQ_mono
#print axioms slowUniformEffectiveQ_le_slowUniformOverheadQ
#print axioms slowUniform_hscalarQ
#print axioms slowUniform_hscalarQ_le
#print axioms slowUniform_hscalarQ_circumR

end Ttc.CVSlowEffectiveOverhead

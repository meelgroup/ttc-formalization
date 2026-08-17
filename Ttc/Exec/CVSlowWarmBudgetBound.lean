import Ttc.Exec.CVSlowRadiusQCanonicalOperational
import Ttc.Exec.CVSlowCanonicalDeadlineCost

/-!
# A uniform bound for the canonical slow warm budget

`Ttc.CVSlowRadiusQCanonicalOperational.slowWarmBudget` is the exact compounding
operational warmness of the uniformly slow schedule.  Nothing in the repository bounded
it, which left the runtime capstone conditional on an unproved warm envelope.

This file closes that gap.  The accepted factor is bounded by its retry cap, the
additive fallback factor is bounded by the explicit hot-refresh radial envelope
evaluated at the terminal variance radius and the initial variance, and the recurrence
is then collapsed to a single geometric power.  The final deliverable is the
logarithmic form
`log (slowWarmBudget …).toReal ≤ log (2e) + i * log (envelope)`,
which is exactly what the speedy-walk mixing deadlines consume.
-/

set_option autoImplicit false

namespace Ttc.CVSlowWarmBudgetBound

open MeasureTheory Metric Set Finset
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVWarmBudgetRecurrence
open Ttc.CVSlowRadiusQRecursiveOperational
open Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVSlowCanonicalDeadlineCost
open Ttc.CVSlowCanonicalShareBounds
open scoped ENNReal BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The radial envelope is monotone in the containing radius. -/
theorem hotRefreshWarmEnvelope_mono_radius
    (n : Nat) {R R' s : Real} (hRR : R ≤ R') :
    hotRefreshWarmEnvelope n R s ≤ hotRefreshWarmEnvelope n R' s := by
  unfold hotRefreshWarmEnvelope
  refine mul_le_mul' le_rfl ?_
  apply ENNReal.ofReal_le_ofReal
  have hmax : max 1 R ≤ max 1 R' := max_le_max le_rfl hRR
  have h0 : (0 : Real) ≤ 4 * max 1 R := by
    have : (0 : Real) < max 1 R := one_pos.trans_le (le_max_left _ _)
    positivity
  exact pow_le_pow_left₀ h0 (by linarith) n

/-- The radial envelope is antitone in the variance: a smaller variance makes the
Gaussian weight on the fixed inner ball smaller, hence the normalizer ratio larger. -/
theorem hotRefreshWarmEnvelope_antitone_variance
    (n : Nat) {R s s' : Real} (hs : 0 < s) (hss : s ≤ s') :
    hotRefreshWarmEnvelope n R s' ≤ hotRefreshWarmEnvelope n R s := by
  unfold hotRefreshWarmEnvelope
  refine mul_le_mul' ?_ le_rfl
  rw [ENNReal.inv_le_inv]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hs' : 0 < s' := hs.trans_le hss
  have hrho : (0 : Real) < hotRefreshRadius ^ 2 := by
    have := hotRefreshRadius_pos
    positivity
  rw [neg_div, neg_div, neg_le_neg_iff]
  apply div_le_div_of_nonneg_left hrho.le (by positivity)
  linarith

/-- A retry cap bounds the accepted compounding factor uniformly over phases.  No
positivity on `L` is needed: the `max 1 _` already absorbs `L = 0`. -/
theorem slowAcceptedFactor_le
    {retries : Nat → Nat} {L : Nat} (hL : ∀ j, retries j ≤ L) (j : Nat) :
    slowAcceptedFactor retries j ≤
      max 1 ((L : ENNReal) * (16 * ENNReal.ofReal (2 * Real.exp 1))) := by
  unfold slowAcceptedFactor
  apply max_le_max le_rfl
  refine mul_le_mul' ?_ le_rfl
  exact_mod_cast Nat.cast_le.2 (hL j)

/-- One radial envelope valid at every phase of a schedule that terminates at `m`.  The
radius is evaluated at the terminal variance (largest body) and the Gaussian weight at
the initial variance (smallest weight on the fixed inner ball). -/
noncomputable def slowFallbackEnvelope (n : Nat) (q s0 : Real) (m : Nat) : ENNReal :=
  hotRefreshWarmEnvelope n (q * Real.sqrt (slowSourceSigmaSq n s0 m) * Real.sqrt n) s0

/-- The additive fallback warmness of every phase before the terminal one is bounded by
the single uniform envelope. -/
theorem slowFallbackFactor_le_envelope
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 ≤ q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    {j m : Nat} (hjm : j + 1 ≤ m) :
    slowFallbackFactor n q s0 K j ≤ slowFallbackEnvelope n q s0 m := by
  have hsig : 0 < slowSourceSigmaSq n s0 (j + 1) := slowSourceSigmaSq_pos hn hs0 (j + 1)
  have hstep : slowFallbackFactor n q s0 K j ≤
      hotRefreshWarmEnvelope n
        (q * Real.sqrt (slowSourceSigmaSq n s0 (j + 1)) * Real.sqrt n)
        (slowSourceSigmaSq n s0 (j + 1)) := by
    unfold slowFallbackFactor
    exact hotRefreshWarmFactor_le_envelope (measurableSet_radiusQBody hK) hsig
      Set.inter_subset_right
  have hradius :
      q * Real.sqrt (slowSourceSigmaSq n s0 (j + 1)) * Real.sqrt n ≤
        q * Real.sqrt (slowSourceSigmaSq n s0 m) * Real.sqrt n := by
    have hle := slowSourceSigmaSq_le_terminal hn hs0 hjm
    have hsqrt : Real.sqrt (slowSourceSigmaSq n s0 (j + 1)) ≤
        Real.sqrt (slowSourceSigmaSq n s0 m) := Real.sqrt_le_sqrt hle
    have hn0 : (0 : Real) ≤ Real.sqrt n := Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hq) hn0
  calc
    slowFallbackFactor n q s0 K j ≤
        hotRefreshWarmEnvelope n
          (q * Real.sqrt (slowSourceSigmaSq n s0 (j + 1)) * Real.sqrt n)
          (slowSourceSigmaSq n s0 (j + 1)) := hstep
    _ ≤ hotRefreshWarmEnvelope n
          (q * Real.sqrt (slowSourceSigmaSq n s0 m) * Real.sqrt n)
          (slowSourceSigmaSq n s0 (j + 1)) :=
        hotRefreshWarmEnvelope_mono_radius n hradius
    _ ≤ slowFallbackEnvelope n q s0 m :=
        hotRefreshWarmEnvelope_antitone_variance n hs0
          (slowSourceSigmaSq_mono_start hn hs0 (j + 1))

/-- One uniform per-phase compounding factor: retry-capped accepted growth plus the
uniform radial fallback envelope. -/
noncomputable def slowWarmFactorEnvelope (n : Nat) (q s0 : Real) (m L : Nat) : ENNReal :=
  max 1 ((L : ENNReal) * (16 * ENNReal.ofReal (2 * Real.exp 1))) +
    slowFallbackEnvelope n q s0 m

theorem one_le_slowReferenceWarm : 1 ≤ slowReferenceWarm := by
  unfold slowReferenceWarm
  rw [ENNReal.one_le_ofReal]
  have h1 : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  linarith

theorem one_le_slowWarmFactorEnvelope (n : Nat) (q s0 : Real) (m L : Nat) :
    1 ≤ slowWarmFactorEnvelope n q s0 m L := by
  unfold slowWarmFactorEnvelope
  exact le_trans (le_max_left _ _) (le_add_of_nonneg_right bot_le)

/-- **The missing bound.**  The exact compounding operational warmness of the canonical
slow schedule grows at most geometrically, with one explicit uniform ratio. -/
theorem slowWarmBudget_le_pow
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 ≤ q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    {retries : Nat → Nat} {L m : Nat} (hL : ∀ j, retries j ≤ L)
    {i : Nat} (hi : i ≤ m) :
    slowWarmBudget slowReferenceWarm n q s0 K retries i ≤
      slowReferenceWarm * (slowWarmFactorEnvelope n q s0 m L) ^ i := by
  unfold slowWarmBudget
  calc
    recursiveWarmBudget slowReferenceWarm (slowAcceptedFactor retries)
          (slowFallbackFactor n q s0 K) i ≤
        slowReferenceWarm * ∏ j ∈ Finset.range i,
          (slowAcceptedFactor retries j + slowFallbackFactor n q s0 K j) :=
      recursiveWarmBudget_le_product one_le_slowReferenceWarm
        (one_le_slowAcceptedFactor retries) i
    _ ≤ slowReferenceWarm * ∏ _j ∈ Finset.range i,
          slowWarmFactorEnvelope n q s0 m L := by
        refine mul_le_mul' le_rfl ?_
        apply Finset.prod_le_prod'
        intro j hj
        have hjm : j + 1 ≤ m := by
          rw [Finset.mem_range] at hj
          omega
        exact add_le_add (slowAcceptedFactor_le hL j)
          (slowFallbackFactor_le_envelope hn hq hs0 hK hjm)
    _ = slowReferenceWarm * (slowWarmFactorEnvelope n q s0 m L) ^ i := by
        rw [Finset.prod_const, Finset.card_range]

theorem hotRefreshWarmEnvelope_ne_top (n : Nat) (R s : Real) :
    hotRefreshWarmEnvelope n R s ≠ ⊤ := by
  unfold hotRefreshWarmEnvelope
  apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
  rw [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero, not_le]
  exact Real.exp_pos _

theorem slowFallbackEnvelope_ne_top (n : Nat) (q s0 : Real) (m : Nat) :
    slowFallbackEnvelope n q s0 m ≠ ⊤ :=
  hotRefreshWarmEnvelope_ne_top _ _ _

theorem slowWarmFactorEnvelope_ne_top (n : Nat) (q s0 : Real) (m L : Nat) :
    slowWarmFactorEnvelope n q s0 m L ≠ ⊤ := by
  unfold slowWarmFactorEnvelope
  refine ENNReal.add_ne_top.2 ⟨?_, slowFallbackEnvelope_ne_top n q s0 m⟩
  finiteness

theorem one_le_slowWarmFactorEnvelope_toReal (n : Nat) (q s0 : Real) (m L : Nat) :
    1 ≤ (slowWarmFactorEnvelope n q s0 m L).toReal := by
  have h := ENNReal.toReal_mono (slowWarmFactorEnvelope_ne_top n q s0 m L)
    (one_le_slowWarmFactorEnvelope n q s0 m L)
  simpa using h

theorem slowWarmBudget_ne_top
    (hn : 1 ≤ n) {q s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    (retries : Nat → Nat) (i : Nat) :
    slowWarmBudget slowReferenceWarm n q s0 K retries i ≠ ⊤ := by
  unfold slowWarmBudget
  refine recursiveWarmBudget_ne_top ?_ ?_ (slowFallbackFactor_ne_top hn hs0 hK) i
  · unfold slowReferenceWarm
    exact ENNReal.ofReal_ne_top
  · intro j
    unfold slowAcceptedFactor
    finiteness

theorem one_le_slowWarmBudget (retries : Nat → Nat) (n : Nat) (q s0 : Real)
    (K : Set (State n)) (i : Nat) :
    1 ≤ slowWarmBudget slowReferenceWarm n q s0 K retries i :=
  one_le_recursiveWarmBudget one_le_slowReferenceWarm
    (one_le_slowAcceptedFactor retries) i

/-- Real-valued geometric envelope for the canonical slow warm budget. -/
theorem slowWarmBudget_toReal_le
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 ≤ q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    {retries : Nat → Nat} {L m : Nat} (hL : ∀ j, retries j ≤ L)
    {i : Nat} (hi : i ≤ m) :
    (slowWarmBudget slowReferenceWarm n q s0 K retries i).toReal ≤
      (2 * Real.exp 1) * ((slowWarmFactorEnvelope n q s0 m L).toReal) ^ i := by
  have hEtop : slowWarmFactorEnvelope n q s0 m L ≠ ⊤ :=
    slowWarmFactorEnvelope_ne_top n q s0 m L
  have hrhs : slowReferenceWarm * (slowWarmFactorEnvelope n q s0 m L) ^ i ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ (ENNReal.pow_ne_top hEtop)
    unfold slowReferenceWarm
    exact ENNReal.ofReal_ne_top
  have hmono := ENNReal.toReal_mono hrhs
    (slowWarmBudget_le_pow hn hq hs0 hK hL hi)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, slowReferenceWarm,
    ENNReal.toReal_ofReal (by positivity)] at hmono

/-- The logarithmic form consumed by the speedy-walk mixing deadline: the compounding
operational warmness costs at most one additive term per phase. -/
theorem log_slowWarmBudget_toReal_le
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 ≤ q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    {retries : Nat → Nat} {L m : Nat} (hL : ∀ j, retries j ≤ L)
    {i : Nat} (hi : i ≤ m) :
    Real.log (slowWarmBudget slowReferenceWarm n q s0 K retries i).toReal ≤
      Real.log (2 * Real.exp 1) +
        (i : Real) * Real.log ((slowWarmFactorEnvelope n q s0 m L).toReal) := by
  have hEone : 1 ≤ (slowWarmFactorEnvelope n q s0 m L).toReal :=
    one_le_slowWarmFactorEnvelope_toReal n q s0 m L
  have hEpos : 0 < (slowWarmFactorEnvelope n q s0 m L).toReal := lt_of_lt_of_le one_pos hEone
  have hbudPos : 0 < (slowWarmBudget slowReferenceWarm n q s0 K retries i).toReal :=
    ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_slowWarmBudget retries n q s0 K i)))
      (slowWarmBudget_ne_top hn hs0 hK retries i)
  have hexp : (0 : Real) < 2 * Real.exp 1 := by positivity
  have hpow : (0 : Real) < ((slowWarmFactorEnvelope n q s0 m L).toReal) ^ i :=
    pow_pos hEpos i
  have hlog := Real.log_le_log hbudPos
    (slowWarmBudget_toReal_le hn hq hs0 hK hL hi)
  rwa [Real.log_mul hexp.ne' hpow.ne', Real.log_pow] at hlog

#print axioms hotRefreshWarmEnvelope_mono_radius
#print axioms hotRefreshWarmEnvelope_antitone_variance
#print axioms slowAcceptedFactor_le
#print axioms slowFallbackFactor_le_envelope
#print axioms one_le_slowWarmFactorEnvelope
#print axioms slowWarmBudget_le_pow
#print axioms slowWarmFactorEnvelope_ne_top
#print axioms slowWarmBudget_ne_top
#print axioms slowWarmBudget_toReal_le
#print axioms log_slowWarmBudget_toReal_le

end Ttc.CVSlowWarmBudgetBound

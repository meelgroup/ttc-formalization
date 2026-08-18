import Ttc.Exec.CVSlowActualDeadline

/-!
# Routing the slow canonical warm budget through the independent refresh

`Ttc.CVSlowRadiusQCanonicalOperational.slowWarmBudget` is the exact compounding
operational warmness

`W (i+1) = slowAcceptedFactor retries i * W i + slowFallbackFactor n q s0 K i`,

whose additive term `slowFallbackFactor` is *already* the independent hot refresh:
`Ttc.CVSlowRadiusQRecursiveOperational.slowFallbackFactor` is literally
`gaussianBallWarmFactor (radiusQBody …) … hotRefreshRadius`, justified at every phase
independently by `Ttc.CVIndependentRefreshSeedLaws.isWarm_hotRefresh_ellGaussianProb`.

The recurrence itself is **not** removable: the phase kernel
`Ttc.CVGaussianWarmFallbackPhaseKernel.gaussianWarmFallbackPhaseKernel` refreshes only the
*unresolved* branch, so the accepted branch genuinely carries the previous phase's law and
its warmness is genuinely `retries · 16 · Ccross · W i`.

What *is* removable is the way the recurrence was being solved.
`Ttc.CVWarmBudgetRecurrence.recursiveWarmBudget_le_product` bounds an **affine** recurrence
by a **product**, `W i ≤ W 0 * ∏ (a j + f j)`, which drags the (large) refresh normalizer
`f` inside the phase product.  Solving the affine recurrence directly gives

`W i ≤ A ^ i * (W 0 + i * F)`,

so the refresh normalizer is paid **once**, additively, and only the accepted factor `A`
compounds.  Taking logarithms:

`log (W i) ≤ i * log A + log (i+1) + log (W 0) + log F`

instead of the previous `log (W 0) + i * log (A + F)`.  Since
`log F = 1/(32 s0) + n * log (4 max 1 R)` exactly
(`Ttc.CVIndependentRefreshSeedLaws.log_hotRefreshWarmEnvelope_toReal`), the dominant
`phaseCount × n log R` product in the runtime overhead disappears.

## Main results

* `recursiveWarmBudget_le_geometric` — the sharp affine solve, for any recurrence.
* `slowWarmBudget_le_geometric` — its canonical-slow specialization.
* `log_slowWarmBudget_toReal_le_refresh` — **the deliverable**: the refresh-routed
  logarithmic envelope `slowRefreshWlog`, in which the radial refresh term appears once.
* `slowCanonicalSteps_le_ceil_of_refresh_log` — the deadline consuming it, through the
  existing bridge `Ttc.CVSlowActualDeadline.slowCanonicalSteps_le_ceil_of_log_le`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVRefreshWarmRoute

open MeasureTheory Metric Set
open Ttc.CVWarmBudgetRecurrence
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowRadiusQRecursiveOperational
open Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVSlowWarmBudgetBound
open Ttc.CVSlowActualDeadline
open scoped ENNReal

variable {n : Nat}

local notation "State" => fun m => EuclideanSpace Real (Fin m)

/-! ## The sharp affine solve -/

/-- **The sharp solve of the warm recurrence.**  An affine recurrence with accepted ratio
at most `A` and additive fallback at most `F` satisfies `W i ≤ A ^ i * (W 0 + i * F)`.

Contrast with `Ttc.CVWarmBudgetRecurrence.recursiveWarmBudget_le_product`, which absorbs
each additive `F` into the multiplicative product and therefore pays `log F` once per
phase.  Here `F` is paid once in total. -/
theorem recursiveWarmBudget_le_geometric
    {initial : ENNReal} {acceptedFactor fallbackFactor : Nat → ENNReal}
    {A F : ENNReal} (hA : 1 ≤ A) :
    ∀ i : Nat, (∀ j, j < i → acceptedFactor j ≤ A) →
      (∀ j, j < i → fallbackFactor j ≤ F) →
      recursiveWarmBudget initial acceptedFactor fallbackFactor i ≤
        A ^ i * (initial + (i : ENNReal) * F) := by
  intro i
  induction i with
  | zero => intro _ _; simp
  | succ i ih =>
      intro ha hf
      have hpow : (1 : ENNReal) ≤ A ^ (i + 1) := one_le_pow_of_one_le' hA (i + 1)
      have h1 := ih (fun j hj ↦ ha j (by omega)) (fun j hj ↦ hf j (by omega))
      rw [recursiveWarmBudget_succ]
      calc
        acceptedFactor i * recursiveWarmBudget initial acceptedFactor fallbackFactor i +
            fallbackFactor i ≤
          A * (A ^ i * (initial + (i : ENNReal) * F)) + F :=
            add_le_add (mul_le_mul' (ha i (by omega)) h1) (hf i (by omega))
        _ = A ^ (i + 1) * (initial + (i : ENNReal) * F) + F := by ring
        _ ≤ A ^ (i + 1) * (initial + (i : ENNReal) * F) + A ^ (i + 1) * F :=
            add_le_add le_rfl (le_mul_of_one_le_left' hpow)
        _ = A ^ (i + 1) * (initial + ((i + 1 : Nat) : ENNReal) * F) := by
            push_cast
            ring

/-! ## The two uniform factors -/

/-- The uniform accepted ratio: the retry-capped accepted compounding factor.  This is the
*only* quantity that compounds along the phases. -/
noncomputable def slowAcceptedCap (L : Nat) : ENNReal :=
  max 1 ((L : ENNReal) * (16 * ENNReal.ofReal (2 * Real.exp 1)))

theorem one_le_slowAcceptedCap (L : Nat) : 1 ≤ slowAcceptedCap L := le_max_left _ _

theorem slowAcceptedCap_ne_top (L : Nat) : slowAcceptedCap L ≠ ⊤ := by
  unfold slowAcceptedCap
  finiteness

theorem one_le_slowAcceptedCap_toReal (L : Nat) : 1 ≤ (slowAcceptedCap L).toReal := by
  have h := ENNReal.toReal_mono (slowAcceptedCap_ne_top L) (one_le_slowAcceptedCap L)
  simpa using h

/-- The refresh normalizer envelope is at least one: the inner Gaussian ball carries at
most the whole Gaussian mass. -/
theorem one_le_hotRefreshWarmEnvelope (n : Nat) {R s : Real} (hs : 0 < s) :
    1 ≤ hotRefreshWarmEnvelope n R s := by
  have hrho : (0 : Real) ≤ hotRefreshRadius ^ 2 := sq_nonneg _
  have hexp : Real.exp (-(hotRefreshRadius ^ 2) / (2 * s)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hfac : ENNReal.ofReal (Real.exp (-(hotRefreshRadius ^ 2) / (2 * s))) ≤ 1 := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hexp
  have hinv : (1 : ENNReal) ≤
      (ENNReal.ofReal (Real.exp (-(hotRefreshRadius ^ 2) / (2 * s))))⁻¹ := by
    have := ENNReal.inv_le_inv.2 hfac
    simpa using this
  have hscale : (1 : ENNReal) ≤ ENNReal.ofReal ((4 * max 1 R) ^ n) := by
    rw [ENNReal.one_le_ofReal]
    exact one_le_pow₀ (by
      have : (1 : Real) ≤ max 1 R := le_max_left _ _
      linarith)
  unfold hotRefreshWarmEnvelope
  calc (1 : ENNReal) = 1 * 1 := (one_mul 1).symm
    _ ≤ _ := mul_le_mul' hinv hscale

theorem one_le_slowFallbackEnvelope
    (n : Nat) (q : Real) {s0 : Real} (hs0 : 0 < s0) (m : Nat) :
    1 ≤ slowFallbackEnvelope n q s0 m :=
  one_le_hotRefreshWarmEnvelope n hs0

theorem one_le_slowFallbackEnvelope_toReal
    (n : Nat) (q : Real) {s0 : Real} (hs0 : 0 < s0) (m : Nat) :
    1 ≤ (slowFallbackEnvelope n q s0 m).toReal := by
  have h := ENNReal.toReal_mono (slowFallbackEnvelope_ne_top n q s0 m)
    (one_le_slowFallbackEnvelope n q hs0 m)
  simpa using h

/-! ## The canonical slow specialization -/

/-- **The sharpened canonical bound.**  The exact compounding operational warmness of the
canonical slow schedule is bounded by a geometric factor in the *retry-capped accepted
ratio alone*, times an additive multiple of the independent refresh envelope.

Compare `Ttc.CVSlowWarmBudgetBound.slowWarmBudget_le_pow`, which raises
`slowAcceptedCap L + slowFallbackEnvelope …` to the `i`-th power. -/
theorem slowWarmBudget_le_geometric
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 ≤ q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    {retries : Nat → Nat} {L m : Nat} (hL : ∀ j, retries j ≤ L)
    {i : Nat} (hi : i ≤ m) :
    slowWarmBudget slowReferenceWarm n q s0 K retries i ≤
      slowAcceptedCap L ^ i *
        (slowReferenceWarm + (i : ENNReal) * slowFallbackEnvelope n q s0 m) := by
  unfold slowWarmBudget
  refine recursiveWarmBudget_le_geometric (one_le_slowAcceptedCap L) i
    (fun j _ ↦ ?_) (fun j hj ↦ ?_)
  · exact slowAcceptedFactor_le hL j
  · exact slowFallbackFactor_le_envelope hn hq hs0 hK (by omega)

/-! ## The refresh-routed logarithmic envelope -/

/-- The containing radius of the terminal slow body, at which the refresh normalizer is
evaluated. -/
noncomputable def slowRefreshRadius (n : Nat) (q s0 : Real) (m : Nat) : Real :=
  q * Real.sqrt (slowSourceSigmaSq n s0 m) * Real.sqrt n

/-- The exact logarithm of the independent-refresh envelope: an inverse-variance term and
one radial term, both paid **once**. -/
theorem log_slowFallbackEnvelope_toReal
    (n : Nat) (q : Real) {s0 : Real} (hs0 : 0 < s0) (m : Nat) :
    Real.log (slowFallbackEnvelope n q s0 m).toReal =
      1 / (32 * s0) +
        (n : Real) * Real.log (4 * max 1 (slowRefreshRadius n q s0 m)) := by
  unfold slowFallbackEnvelope slowRefreshRadius
  rw [log_hotRefreshWarmEnvelope_toReal n hs0]
  have hrho : hotRefreshRadius ^ 2 = (1 / 16 : Real) := by
    norm_num [hotRefreshRadius]
  rw [hrho]
  have : (1 / 16 : Real) / (2 * s0) = 1 / (32 * s0) := by
    field_simp
    norm_num
  rw [this]

/-- **The refresh-routed warmness logarithm.**  Only the accepted ratio compounds; the
independent refresh contributes `1/(32 s0) + n log (4 max 1 R)` once, plus a `log (i+1)`
from the additive accumulation. -/
noncomputable def slowRefreshWlog (n : Nat) (q s0 : Real) (m L i : Nat) : Real :=
  (i : Real) * Real.log (slowAcceptedCap L).toReal +
    Real.log ((i : Real) + 1) + Real.log (2 * Real.exp 1) +
    (1 / (32 * s0) +
      (n : Real) * Real.log (4 * max 1 (slowRefreshRadius n q s0 m)))

/-- Elementary real inequality behind the additive accumulation: `a + i b ≤ (i+1) a b`. -/
theorem log_add_nsmul_le
    {a b : Real} (ha : 1 ≤ a) (hb : 1 ≤ b) (i : Nat) :
    Real.log (a + (i : Real) * b) ≤
      Real.log ((i : Real) + 1) + Real.log a + Real.log b := by
  have hi0 : (0 : Real) ≤ (i : Real) := Nat.cast_nonneg i
  have ha0 : (0 : Real) < a := lt_of_lt_of_le one_pos ha
  have hb0 : (0 : Real) < b := lt_of_lt_of_le one_pos hb
  have h1 : a ≤ a * b := le_mul_of_one_le_right ha0.le hb
  have h2 : (i : Real) * b ≤ (i : Real) * (a * b) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hb0.le ha) hi0
  have hkey : a + (i : Real) * b ≤ ((i : Real) + 1) * (a * b) := by nlinarith
  have hpos : 0 < a + (i : Real) * b := by nlinarith
  have h := Real.log_le_log hpos hkey
  rwa [Real.log_mul (by positivity) (by positivity),
    Real.log_mul ha0.ne' hb0.ne', ← add_assoc] at h

theorem slowReferenceWarm_toReal : slowReferenceWarm.toReal = 2 * Real.exp 1 := by
  rw [slowReferenceWarm, ENNReal.toReal_ofReal]
  positivity

/-- **The deliverable.**  The canonical slow schedule's compounding operational warmness
has a logarithm in which the independent-refresh normalizer is paid once, not once per
phase.

Compare `Ttc.CVSlowWarmBudgetBound.log_slowWarmBudget_toReal_le`, whose bound is
`log (2e) + i * log (slowAcceptedCap L + slowFallbackEnvelope …)`: there the whole radial
refresh logarithm `n log (4 max 1 R)` is multiplied by the phase index. -/
theorem log_slowWarmBudget_toReal_le_refresh
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 ≤ q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    {retries : Nat → Nat} {L m : Nat} (hL : ∀ j, retries j ≤ L)
    {i : Nat} (hi : i ≤ m) :
    Real.log (slowWarmBudget slowReferenceWarm n q s0 K retries i).toReal ≤
      slowRefreshWlog n q s0 m L i := by
  have hFtop : slowFallbackEnvelope n q s0 m ≠ ⊤ := slowFallbackEnvelope_ne_top n q s0 m
  have hAtop : slowAcceptedCap L ≠ ⊤ := slowAcceptedCap_ne_top L
  have hW0top : slowReferenceWarm ≠ ⊤ := by
    unfold slowReferenceWarm
    exact ENNReal.ofReal_ne_top
  have hsum : slowReferenceWarm + (i : ENNReal) * slowFallbackEnvelope n q s0 m ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨hW0top, ENNReal.mul_ne_top ?_ hFtop⟩
    exact ENNReal.natCast_ne_top i
  have hrhs : slowAcceptedCap L ^ i *
      (slowReferenceWarm + (i : ENNReal) * slowFallbackEnvelope n q s0 m) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hAtop) hsum
  have hAone : 1 ≤ (slowAcceptedCap L).toReal := one_le_slowAcceptedCap_toReal L
  have hApos : 0 < (slowAcceptedCap L).toReal := lt_of_lt_of_le one_pos hAone
  have hFone : 1 ≤ (slowFallbackEnvelope n q s0 m).toReal :=
    one_le_slowFallbackEnvelope_toReal n q hs0 m
  have hFpos : 0 < (slowFallbackEnvelope n q s0 m).toReal := lt_of_lt_of_le one_pos hFone
  have hW0one : 1 ≤ (2 * Real.exp 1 : Real) := by
    have h1 : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hbudPos : 0 < (slowWarmBudget slowReferenceWarm n q s0 K retries i).toReal :=
    ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_slowWarmBudget retries n q s0 K i)))
      (slowWarmBudget_ne_top hn hs0 hK retries i)
  have hmono := ENNReal.toReal_mono hrhs
    (slowWarmBudget_le_geometric hn hq hs0 hK hL hi)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add hW0top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hFtop),
    ENNReal.toReal_mul, ENNReal.toReal_natCast, slowReferenceWarm_toReal] at hmono
  have hsumPos : 0 < (2 * Real.exp 1 : Real) +
      (i : Real) * (slowFallbackEnvelope n q s0 m).toReal := by positivity
  have hlog := Real.log_le_log hbudPos hmono
  rw [Real.log_mul (by positivity) hsumPos.ne', Real.log_pow] at hlog
  refine hlog.trans ?_
  unfold slowRefreshWlog
  rw [← log_slowFallbackEnvelope_toReal n q hs0 m]
  have htail := log_add_nsmul_le (a := (2 * Real.exp 1 : Real))
    (b := (slowFallbackEnvelope n q s0 m).toReal) hW0one hFone i
  linarith

/-- The refresh-routed payload is monotone in the phase index, so it can be padded to the
terminal phase and used uniformly (this is the shape
`Ttc.CVSlowActualSteps.slowActualWlog` is consumed in). -/
theorem slowRefreshWlog_mono
    (n : Nat) (q s0 : Real) (m L : Nat) {i j : Nat} (hij : i ≤ j) :
    slowRefreshWlog n q s0 m L i ≤ slowRefreshWlog n q s0 m L j := by
  have hij' : (i : Real) ≤ (j : Real) := Nat.cast_le.2 hij
  have hA : 0 ≤ Real.log (slowAcceptedCap L).toReal :=
    Real.log_nonneg (one_le_slowAcceptedCap_toReal L)
  have hi0 : (0 : Real) ≤ (i : Real) := Nat.cast_nonneg i
  have hfirst : (i : Real) * Real.log (slowAcceptedCap L).toReal ≤
      (j : Real) * Real.log (slowAcceptedCap L).toReal :=
    mul_le_mul_of_nonneg_right hij' hA
  have hsecond : Real.log ((i : Real) + 1) ≤ Real.log ((j : Real) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  unfold slowRefreshWlog
  linarith

/-- Phase-index-free form: one refresh-routed payload valid simultaneously at every active
phase of a schedule terminating at `m`. -/
theorem log_slowWarmBudget_toReal_le_refresh_uniform
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 ≤ q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    {retries : Nat → Nat} {L m : Nat} (hL : ∀ j, retries j ≤ L)
    {i : Nat} (hi : i ≤ m) :
    Real.log (slowWarmBudget slowReferenceWarm n q s0 K retries i).toReal ≤
      slowRefreshWlog n q s0 m L m :=
  (log_slowWarmBudget_toReal_le_refresh hn hq hs0 hK hL hi).trans
    (slowRefreshWlog_mono n q s0 m L hi)

/-- Both envelopes are available simultaneously, so the deadline may consume whichever is
smaller.  The product envelope is smaller only in the first phases (it has not yet paid
`log F`); from the phase where the refresh route wins it wins by a factor growing like the
phase index. -/
theorem log_slowWarmBudget_toReal_le_min
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 ≤ q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    {retries : Nat → Nat} {L m : Nat} (hL : ∀ j, retries j ≤ L)
    {i : Nat} (hi : i ≤ m) :
    Real.log (slowWarmBudget slowReferenceWarm n q s0 K retries i).toReal ≤
      min (Real.log (2 * Real.exp 1) +
            (i : Real) *
              Real.log ((slowWarmFactorEnvelope n q s0 m L).toReal))
        (slowRefreshWlog n q s0 m L i) :=
  le_min (log_slowWarmBudget_toReal_le hn hq hs0 hK hL hi)
    (log_slowWarmBudget_toReal_le_refresh hn hq hs0 hK hL hi)

/-! ## The deadline consuming the refresh-routed envelope -/

/-- **The deadline deliverable.**  The canonical slow schedule's per-phase mixing deadline
is capped through the existing bridge, at the refresh-routed logarithmic payload
`slowRefreshWlog` in place of the product payload
`log (2e) + i * log (slowAcceptedCap L + slowFallbackEnvelope …)`.

The deadline argument itself is unchanged — `slowCanonicalSteps` is *not* modified, and no
operational proof is touched.  Only the envelope solving its warm recurrence is sharper. -/
theorem slowCanonicalSteps_le_ceil_of_refresh_log
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    {retries : Nat → Nat} {eta zeta : Nat → ENNReal} {L m i : Nat}
    (hL : ∀ j, retries j ≤ L) (hi : i ≤ m)
    {Elog Zlog Ebound : Real}
    (heta : eta i ≠ 0) (heta' : eta i ≠ ⊤)
    (hElog : Real.log (1 / (eta i).toReal) ≤ Elog)
    (hZlog : Real.log (1 / (zeta i).toReal) ≤ Zlog)
    (hE : slowActualDeadlineExpression n (radiusQDelta n q (slowSourceSigmaSq n s0 i))
      (slowSourceSigmaSq n s0 i) (slowRefreshWlog n q s0 m L i) Elog Zlog ≤ Ebound) :
    slowCanonicalSteps slowReferenceWarm n q s0 K retries eta zeta i 0 ≤
      ⌈Ebound⌉₊ + 1 := by
  refine slowCanonicalSteps_le_ceil_of_log_le hn hq hs0
    (slowWarmBudget_ne_top hn hs0 hK retries i) ?_ heta heta'
    (log_slowWarmBudget_toReal_le_refresh hn hq.le hs0 hK hL hi) hElog hZlog hE
  exact ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_slowWarmBudget retries n q s0 K i)))
    (slowWarmBudget_ne_top hn hs0 hK retries i)

#print axioms recursiveWarmBudget_le_geometric
#print axioms one_le_hotRefreshWarmEnvelope
#print axioms slowWarmBudget_le_geometric
#print axioms log_slowFallbackEnvelope_toReal
#print axioms log_slowWarmBudget_toReal_le_refresh
#print axioms slowRefreshWlog_mono
#print axioms log_slowWarmBudget_toReal_le_refresh_uniform
#print axioms log_slowWarmBudget_toReal_le_min
#print axioms slowCanonicalSteps_le_ceil_of_refresh_log

end Ttc.CVRefreshWarmRoute

import Ttc.Exec.CVSlowEffectiveOverhead

/-!
# The cost layer for the *actual* (compounding-warmness) slow deadline

`Ttc.CVSlowEffectiveOverhead`'s `Q` layer bounds the retained scalar of one slow run
through the *reference-warm* caps `slowUniformRetriesQ` / `slowUniformDeadlineQ`.  The
runtime assembly, however, has to pay for the **actual** per-phase retry and step counts of
the recursive warm schedule, which compound and are therefore larger than the reference
ones.

This file is the cost layer that consumes whatever bound the actual-deadline analysis
produces.  It is deliberately *pure bookkeeping over real envelopes*: the actual per-run
retry count `L` and per-phase deadline `T` enter only through two **real** parameters
`Lenv`, `Tenv` together with the two casts `(L : Real) ≤ Lenv` and `(T : Real) ≤ Tenv`.
Nothing here mentions `slowWarmBudget`, `adjustableSpeedyDeadline` or
`gaussianBallWarmFactor`; those live in the files that produce `hL` and `hT`.

Everything below mirrors the `Q` layer of `Ttc.CVSlowEffectiveOverhead`:

* `slowActualRetainedRealEnvelope` is `slowUniformRetainedRealEnvelope` with the two
  logarithmic factors replaced by the opaque envelopes `Lenv`, `Tenv`;
* `slowActualOverhead` is `slowUniformOverheadQ`, i.e. the same `max 1 (…)` clip at the
  same pinned phase/stream counts `(slowPhasesP n R2 + 1, slowStreamsP n R2 epsP)`, so it
  is a drop-in replacement modulo the two trailing real arguments;
* `slowActual_hscalar` is `slowUniform_hscalarQ_le`, and `slowActualEffective` /
  `slowActualEffective_le_slowActualOverhead` are `slowUniformEffectiveQ` /
  `slowUniformEffectiveQ_le_slowUniformOverheadQ`.

One genuine simplification over the `Q` layer: the accuracy slot `epsP` now enters only as
an index of `slowStreamsP`, and `slowStreamsP_mono` holds at *every* accuracy, so none of
the degenerate `eps = 0` case splits of the `Q` layer are needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVSlowActualCostEnvelope

open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSlowEffectiveOverhead
open Ttc.TtcCircumRadius
open scoped ENNReal

/-! ## Step 1 — the retained real envelope at opaque per-phase envelopes -/

/-- The overhead paid by all `k` streams and all `m` phases of one slow run, when the
actual per-run retry count is bounded by the real envelope `Lenv` and the actual per-phase
mixing deadline by the real envelope `Tenv`.  This is
`Ttc.CVSlowEffectiveOverhead.slowUniformRetainedRealEnvelope` with its two closed-form
logarithmic factors replaced by the two opaque envelopes. -/
noncomputable def slowActualRetainedRealEnvelope
    (m k : Nat) (Lenv Tenv : Real) : Real :=
  (k : Real) * (m : Real) * 10 * Lenv * Tenv * (2 * Real.exp 1)

theorem slowActualRetainedRealEnvelope_nonneg
    (m k : Nat) {Lenv Tenv : Real} (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) :
    0 ≤ slowActualRetainedRealEnvelope m k Lenv Tenv := by
  unfold slowActualRetainedRealEnvelope
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have he0 : (0 : Real) ≤ 2 * Real.exp 1 := by positivity
  positivity

set_option linter.unusedVariables false in
/-- **Deliverable 1.**  The exact retained scalar of one slow run, at the actual per-run
retry count `L` and actual per-phase deadline `T`, is below the retained real envelope at
any pair of real bounds for them. -/
theorem slowActualRetainedScalar_le_realEnvelope
    {m k : Nat} {L T : Nat} {Lenv Tenv : Real}
    (hL : (L : Real) ≤ Lenv) (hT : (T : Real) ≤ Tenv)
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) :
    (k : Real) * (m : Real) * (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      slowActualRetainedRealEnvelope m k Lenv Tenv := by
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have hL0 : (0 : Real) ≤ (L : Real) := by positivity
  have hT0 : (0 : Real) ≤ (T : Real) := by positivity
  have he0 : (0 : Real) ≤ 2 * Real.exp 1 := by positivity
  unfold slowActualRetainedRealEnvelope
  calc
    (k : Real) * (m : Real) * (10 * (L : Real) * (T : Real) * (2 * Real.exp 1))
        = (k : Real) * (m : Real) * 10 * (L : Real) * (T : Real) * (2 * Real.exp 1) := by
          ring
    _ ≤ (k : Real) * (m : Real) * 10 * Lenv * (T : Real) * (2 * Real.exp 1) := by gcongr
    _ ≤ (k : Real) * (m : Real) * 10 * Lenv * Tenv * (2 * Real.exp 1) := by gcongr

/-- Monotone in the phase count, the stream count and both real envelopes. -/
theorem slowActualRetainedRealEnvelope_mono
    {m m' k k' : Nat} {Lenv Lenv' Tenv Tenv' : Real}
    (hm : m ≤ m') (hk : k ≤ k')
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv)
    (hLL : Lenv ≤ Lenv') (hTT : Tenv ≤ Tenv') :
    slowActualRetainedRealEnvelope m k Lenv Tenv ≤
      slowActualRetainedRealEnvelope m' k' Lenv' Tenv' := by
  unfold slowActualRetainedRealEnvelope
  have hmR : (m : Real) ≤ (m' : Real) := by exact_mod_cast hm
  have hkR : (k : Real) ≤ (k' : Real) := by exact_mod_cast hk
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have hL0' : (0 : Real) ≤ Lenv' := hLenv.trans hLL
  have hT0' : (0 : Real) ≤ Tenv' := hTenv.trans hTT
  have he0 : (0 : Real) ≤ 2 * Real.exp 1 := by positivity
  gcongr

/-! ## Step 2 — the clipped overhead

The clip and the pinned phase/stream counts are exactly those of
`Ttc.CVSlowEffectiveOverhead.slowUniformOverheadQ`: the frontier certificate runs at phase
count `slowPhasesP n R2` but quantifies its retry/step binders at the shifted count
`slowPhasesP n R2 + 1`, and at stream count `slowStreamsP n R2 epsP`.  Only the two
logarithmic caps are replaced by `Lenv`, `Tenv`.  The confidence slot `p` is carried for
signature compatibility with the `OV` interface and is not used. -/

set_option linter.unusedVariables false in
/-- **The overhead envelope of the actual (compounding-warmness) slow schedule.**  A
drop-in replacement for `Ttc.CVSlowEffectiveOverhead.slowUniformOverheadQ n R2 epsP p`,
with the actual per-run retry and per-phase deadline envelopes `Lenv`, `Tenv` supplied by
the caller. -/
noncomputable def slowActualOverhead
    (n : Nat) (R2 epsP p : Real) (Lenv Tenv : Real) : Real :=
  max 1 (slowActualRetainedRealEnvelope (slowPhasesP n R2 + 1) (slowStreamsP n R2 epsP)
    Lenv Tenv)

theorem one_le_slowActualOverhead (n : Nat) (R2 epsP p Lenv Tenv : Real) :
    1 ≤ slowActualOverhead n R2 epsP p Lenv Tenv := le_max_left _ _

theorem slowActualOverhead_nonneg (n : Nat) (R2 epsP p Lenv Tenv : Real) :
    0 ≤ slowActualOverhead n R2 epsP p Lenv Tenv :=
  zero_le_one.trans (one_le_slowActualOverhead n R2 epsP p Lenv Tenv)

/-- Monotone in the declared squared radius.  Unlike the `Q` layer this needs no
`eps = 0` case split: the accuracy slot only indexes `slowStreamsP`, whose monotonicity
holds at every accuracy. -/
theorem slowActualOverhead_mono_R2
    (n : Nat) (epsP p : Real) {R2 R2' Lenv Tenv : Real}
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) (h : R2 ≤ R2') :
    slowActualOverhead n R2 epsP p Lenv Tenv ≤
      slowActualOverhead n R2' epsP p Lenv Tenv := by
  unfold slowActualOverhead
  refine max_le_max (le_refl 1) ?_
  exact slowActualRetainedRealEnvelope_mono
    (Nat.add_le_add_right (slowPhasesP_mono n h) 1) (slowStreamsP_mono n epsP h)
    hLenv hTenv (le_refl _) (le_refl _)

/-- Monotone in both per-phase envelopes simultaneously. -/
theorem slowActualOverhead_mono_env
    (n : Nat) (R2 epsP p : Real) {Lenv Lenv' Tenv Tenv' : Real}
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) (hLL : Lenv ≤ Lenv') (hTT : Tenv ≤ Tenv') :
    slowActualOverhead n R2 epsP p Lenv Tenv ≤
      slowActualOverhead n R2 epsP p Lenv' Tenv' :=
  max_le_max (le_refl 1)
    (slowActualRetainedRealEnvelope_mono (le_refl _) (le_refl _) hLenv hTenv hLL hTT)

/-- Monotone in the retry envelope. -/
theorem slowActualOverhead_mono_Lenv
    (n : Nat) (R2 epsP p : Real) {Lenv Lenv' Tenv : Real}
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) (hLL : Lenv ≤ Lenv') :
    slowActualOverhead n R2 epsP p Lenv Tenv ≤
      slowActualOverhead n R2 epsP p Lenv' Tenv :=
  slowActualOverhead_mono_env n R2 epsP p hLenv hTenv hLL (le_refl _)

/-- Monotone in the deadline envelope. -/
theorem slowActualOverhead_mono_Tenv
    (n : Nat) (R2 epsP p : Real) {Lenv Tenv Tenv' : Real}
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) (hTT : Tenv ≤ Tenv') :
    slowActualOverhead n R2 epsP p Lenv Tenv ≤
      slowActualOverhead n R2 epsP p Lenv Tenv' :=
  slowActualOverhead_mono_env n R2 epsP p hLenv hTenv (le_refl _) hTT

/-! ## Step 3 — the `hscalar` binder at the actual envelope -/

/-- **Deliverable 3.**  The `hscalar` binder of the frontier certificate, at the *actual*
per-run retry count `L` and per-phase deadline `T`, and at
`runtimeConstant := slowActualOverhead n R2 epsP p Lenv Tenv`.

No guard on the accuracy slot `epsP` and no sign condition on `R` are needed: the accuracy
enters only as an index of `slowStreamsP`, and the Theorem-1.1 core factor is at least one
for every real radius (`Ttc.CVSlowEffectiveOverhead.one_le_sourceOneRunCore`, whose radial
term is a square).  The `requested` accuracy is the one the core's `0 < eps < 1` guard
refers to. -/
theorem slowActual_hscalar
    (n : Nat) (hn : 1 ≤ n) {m k L T : Nat} {R requested R2 epsP p Lenv Tenv : Real}
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hm : m ≤ slowPhasesP n R2) (hk : k ≤ slowStreamsP n R2 epsP)
    (hL : (L : Real) ≤ Lenv) (hT : (T : Real) ≤ Tenv)
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowActualOverhead n R2 epsP p Lenv Tenv) n R requested := by
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hreal := slowActualRetainedScalar_le_realEnvelope
    (m := m) (k := k) (L := L) (T := T) (Lenv := Lenv) (Tenv := Tenv)
    hL hT hLenv hTenv
  have hmono := slowActualRetainedRealEnvelope_mono
    (m := m) (m' := slowPhasesP n R2 + 1) (k := k) (k' := slowStreamsP n R2 epsP)
    (Lenv := Lenv) (Lenv' := Lenv) (Tenv := Tenv) (Tenv' := Tenv)
    (hm.trans (Nat.le_succ _)) hk hLenv hTenv (le_refl _) (le_refl _)
  have hover : (k : Real) * (m : Real) *
      (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      slowActualOverhead n R2 epsP p Lenv Tenv := by
    refine hreal.trans (hmono.trans ?_)
    exact le_max_right _ _
  have hcore : slowActualOverhead n R2 epsP p Lenv Tenv ≤
      sourceOneRunQueryEnvelope (slowActualOverhead n R2 epsP p Lenv Tenv) n R requested :=
    le_sourceOneRunQueryEnvelope_of_le hn hreq hreq1
      (slowActualOverhead_nonneg n R2 epsP p Lenv Tenv)
  unfold sourceOneRunQueryBudget
  rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_natCast m,
    ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (mul_nonneg hk0 hm0)]
  exact ENNReal.ofReal_le_ofReal (hover.trans hcore)

/-! ## Step 4 — the circumradius-keyed effective constant -/

/-- The per-input effective runtime constant of the actual slow route: the overhead at the
body's own squared circumradius, at half the requested accuracy (the construction is run at
`eps / 2`), and at the caller's per-phase envelopes. -/
noncomputable def slowActualEffective
    (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) (Lenv Tenv : Real) : Real :=
  slowActualOverhead n ((Ttc.TtcCircumRadius.circumR a.1) ^ 2) (a.2.1 / 2) a.2.2 Lenv Tenv

theorem slowActualEffective_nonneg
    (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) (Lenv Tenv : Real) :
    0 ≤ slowActualEffective n a Lenv Tenv :=
  slowActualOverhead_nonneg n _ _ _ _ _

/-- `hscalar` at the circumradius: the budget's radial parameter is the radius the schedule
actually runs at, and its runtime constant is the input's own `slowActualEffective`.  The
`R ^ 2 ≤ R2` side condition is definitional here. -/
theorem slowActual_hscalar_circumR
    (n : Nat) (hn : 1 ≤ n) {m k L T : Nat} {K : Set (Ttc.Space n)}
    {requested eps p Lenv Tenv : Real}
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hm : m ≤ slowPhasesP n (Ttc.TtcCircumRadius.circumR K ^ 2))
    (hk : k ≤ slowStreamsP n (Ttc.TtcCircumRadius.circumR K ^ 2) (eps / 2))
    (hL : (L : Real) ≤ Lenv) (hT : (T : Real) ≤ Tenv)
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowActualEffective n (K, eps, p) Lenv Tenv) n
        (Ttc.TtcCircumRadius.circumR K) requested :=
  slowActual_hscalar n hn (R2 := Ttc.TtcCircumRadius.circumR K ^ 2) (epsP := eps / 2)
    (p := p) (R := Ttc.TtcCircumRadius.circumR K) hreq hreq1 hm hk hL hT hLenv hTenv

/-- **Deliverable 4 — the `heff` binder**, at `runtimeConstant = 1`: the only
input-dependent factor is the overhead, and it is monotone in the declared squared radius.
Both sides are evaluated at the *same* pair of per-phase envelopes `(Lenv, Tenv)`. -/
theorem slowActualEffective_le_slowActualOverhead
    (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 Lenv Tenv : Real)
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv)
    (hK : Ttc.CVShaped.cvAdmBall n K R2) :
    slowActualEffective n (K, eps, p) Lenv Tenv ≤
      1 * slowActualOverhead n R2 (eps / 2) p Lenv Tenv := by
  rw [one_mul]
  exact slowActualOverhead_mono_R2 n (eps / 2) p hLenv hTenv
    (circumR_sq_le_of_cvAdmBall hK)

#print axioms slowActualRetainedRealEnvelope_nonneg
#print axioms slowActualRetainedScalar_le_realEnvelope
#print axioms slowActualRetainedRealEnvelope_mono
#print axioms one_le_slowActualOverhead
#print axioms slowActualOverhead_nonneg
#print axioms slowActualOverhead_mono_R2
#print axioms slowActualOverhead_mono_env
#print axioms slowActualOverhead_mono_Lenv
#print axioms slowActualOverhead_mono_Tenv
#print axioms slowActual_hscalar
#print axioms slowActualEffective_nonneg
#print axioms slowActual_hscalar_circumR
#print axioms slowActualEffective_le_slowActualOverhead

end Ttc.CVSlowActualCostEnvelope

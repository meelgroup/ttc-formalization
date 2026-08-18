import Ttc.Exec.CVSlowUniformShareBounds

/-!
# The sharp phase-score transport bound on the slow schedule

The development's score transport bound is
`Ttc.CVGaussianFactorSevenAssembly.phaseScoreTransportBoundSqSeven R sigmaSq i
  = exp (R^2 / (2 * sigmaSq i))^2 * (1 + 2*7)`,
which is the square of `Arlib.GaussianCooling.phaseScore_le`'s sup
`exp (R^2 / (2 * sigmaSq i))`.  That sup is the *terminal-step* value of `coolRatio`
(`coolRatio_of_last`), where the next cooling weight is the constant `1`.  At every
**interior** step `i + 1 < m` the ratio is much smaller:

`coolRatio m σsq i x = exp (‖x‖^2 / 2 * (1/σsq i - 1/σsq (i+1)))`,

and on the slow schedule `σsq = slowSourceSigmaSq n s0 = geomSchedule s0 (1/n)` we have
`σ_{i+1} = σ_i (1 + 1/n)`, so

`1/σ_i - 1/σ_{i+1} = 1/(σ_i (n+1))`,

i.e. the true interior sup on `‖x‖ ≤ R` is `exp (R^2 / (2 σ_i (n+1)))`, a factor `n + 1`
smaller *in the exponent*.  At the cold end `σ_0 = 1/(16 n)` the loose bound is
`exp (8 n R^2)` where the truth is `exp (8 n R^2 / (n+1)) ≤ exp (8 R^2)`: the loose bound
carries a full factor of `n` in the exponent that the sharp one does not.

This file:

* proves the sharp interior ratio bound (`coolRatio_le_of_norm_le`) and its slow-schedule
  specialisation (`coolRatio_slowSource_le`), together with the sharp sup of the score
  itself (`phaseScore_slowSource_le`);
* records the *boundary* obstruction honestly: at `i + 1 = m` the sharp bound is simply
  false, and the best available statement is `coolRatio_le_of_last_of_sq_le`, which needs
  `R^2 ≤ σsq i` (available at the hot end, where `N ≤ σ_{m-1}` and `R^2 ≤ N`) and yields
  the constant `exp (1/2)`;
* defines the sharpened transport bound `phaseScoreTransportBoundSqSharp` with its
  positivity and the safety-net comparison
  `phaseScoreTransportBoundSqSharp ≤ phaseScoreTransportBoundSqSeven`;
* lands the payoff at the share layer: `slowSharpShareFloor_le_scoreAwareShare` replaces
  the dimension-dependent floor `1/(18 * exp (R^2/(2 s0))^2) = 1/(18 * exp (8 n R^2)^2)`
  of `Ttc.CVSlowUniformShareBounds.slowUniformShareFloor` by the **dimension-free**
  `1/(18 * exp (8 R^2)^2)`.

Nothing here weakens an existing statement; `phaseScoreTransportBoundSqSharp_le_seven` is
the explicit safety net that everything proved at the old bound still applies.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVSharpScoreTransport

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowCanonicalShareBounds
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVMinimalScoreAwareWarmLogArithmetic

variable {n : Nat}

/-! ## Step 1 — the sharp interior ratio bound -/

/-- **The sharp interior phase-ratio bound.**  At an interior step `i + 1 < m` the phase
ratio on a body of radius `R` is at most `exp (R^2/2 * (1/σ_i - 1/σ_{i+1}))`.

The hypothesis `i + 1 < m` is essential and not a technicality: at `i + 1 = m` the next
cooling weight is the constant `1` rather than a Gaussian, `coolRatio` degenerates to
`exp (‖x‖^2 / (2 σ_i))` (`Arlib.GaussianCooling.coolRatio_of_last`), and the bound below
is false there — see `coolRatio_le_of_last_of_sq_le`. -/
theorem coolRatio_le_of_norm_le
    {m : Nat} {σsq : Nat → Real} {i : Nat} (him : i + 1 < m)
    (hσ : 0 < σsq i) (hmono : σsq i ≤ σsq (i + 1))
    {R : Real} {x : EuclSpace n} (hx : ‖x‖ ≤ R) :
    Arlib.GaussianCooling.coolRatio m σsq i x ≤
      Real.exp (R ^ 2 / 2 * (1 / σsq i - 1 / σsq (i + 1))) := by
  have hσ1 : 0 < σsq (i + 1) := lt_of_lt_of_le hσ hmono
  have hgap : 0 ≤ 1 / σsq i - 1 / σsq (i + 1) := by
    have := one_div_le_one_div_of_le hσ hmono
    linarith
  have hR0 : (0 : Real) ≤ R := le_trans (norm_nonneg x) hx
  have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := by
    have := norm_nonneg x
    nlinarith
  rw [coolRatio_of_succ_lt him]
  exact Real.exp_le_exp.2 (by nlinarith)

/-! ### The boundary case, stated honestly

At the terminal step the sharp bound genuinely fails; the ratio really is
`exp (‖x‖^2/(2 σ_i))`.  What *is* available there is that the terminal variance is large:
on the canonical slow schedule `N ≤ σ_{m-1}` and the body radius satisfies `R^2 ≤ N`, so
the terminal sup is the absolute constant `exp (1/2)`. -/

/-- **The terminal step.**  At `i + 1 = m` the ratio is `exp (‖x‖^2/(2 σ_i))`, which on
`‖x‖ ≤ R` with `R^2 ≤ σsq i` is at most the absolute constant `exp (1/2)`. -/
theorem coolRatio_le_of_last_of_sq_le
    {m : Nat} {σsq : Nat → Real} {i : Nat} (h : i < m) (h' : m ≤ i + 1)
    (hσ : 0 < σsq i) {R : Real} (hRσ : R ^ 2 ≤ σsq i)
    {x : EuclSpace n} (hx : ‖x‖ ≤ R) :
    Arlib.GaussianCooling.coolRatio m σsq i x ≤ Real.exp (1 / 2) := by
  have hR0 : (0 : Real) ≤ R := le_trans (norm_nonneg x) hx
  have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := by
    have := norm_nonneg x
    nlinarith
  rw [coolRatio_of_last h h' x]
  refine Real.exp_le_exp.2 ?_
  rw [div_le_div_iff₀ (by linarith : (0 : Real) < 2 * σsq i) (by norm_num : (0 : Real) < 2)]
  nlinarith

/-! ## Step 1b — the slow-schedule specialisation -/

/-- On the slow schedule the reciprocal gap is exactly `1/(σ_i (n+1))`. -/
theorem slowSourceSigmaSq_inv_gap
    {n : Nat} (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    1 / slowSourceSigmaSq n s0 i - 1 / slowSourceSigmaSq n s0 (i + 1) =
      1 / (slowSourceSigmaSq n s0 i * ((n : Real) + 1)) := by
  have hn0 : (0 : Real) < (n : Real) := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hσ : 0 < slowSourceSigmaSq n s0 i := slowSourceSigmaSq_pos hn hs0 i
  rw [slowSourceSigmaSq_succ]
  field_simp
  ring

/-- **The sharp interior ratio bound on the slow source schedule.**  The exponent carries
the full `1/(n+1)` factor that `phaseScoreTransportBoundSqSeven` drops. -/
theorem coolRatio_slowSource_le
    {n : Nat} (hn : 1 ≤ n) {s0 R : Real} (hs0 : 0 < s0) {m i : Nat} (him : i + 1 < m)
    {x : EuclSpace n} (hx : ‖x‖ ≤ R) :
    Arlib.GaussianCooling.coolRatio m (slowSourceSigmaSq n s0) i x ≤
      Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i * ((n : Real) + 1))) := by
  have hσ : 0 < slowSourceSigmaSq n s0 i := slowSourceSigmaSq_pos hn hs0 i
  have hmono : slowSourceSigmaSq n s0 i ≤ slowSourceSigmaSq n s0 (i + 1) :=
    slowSourceSigmaSq_mono_succ hn hs0 i
  refine (coolRatio_le_of_norm_le him hσ hmono hx).trans_eq ?_
  rw [slowSourceSigmaSq_inv_gap hn hs0 i]
  congr 1
  field_simp

/-- **The sharp sup of the phase score on the slow schedule.**  This is the statement in
the shape the transport lemmas consume it (`|phaseScore| ≤ B` with the sharp `B`), and it
is what makes `phaseScoreTransportBoundSqSharp` a genuine transport bound rather than a
smaller number. -/
theorem phaseScore_slowSource_le
    {n : Nat} (hn : 1 ≤ n) {s0 R : Real} (hs0 : 0 < s0) {m i : Nat} (him : i + 1 < m)
    {K : Set (EuclSpace n)} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    (x : EuclSpace n) :
    Arlib.GaussianCooling.phaseScore m (slowSourceSigmaSq n s0) K i x ≤
      Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i * ((n : Real) + 1))) := by
  by_cases hx : x ∈ K
  · rw [phaseScore_of_mem hx]
    exact coolRatio_slowSource_le hn hs0 him
      (by simpa using mem_closedBall_zero_iff.1 (hKR hx))
  · rw [phaseScore, Set.indicator_of_notMem hx]
    exact (Real.exp_pos _).le

/-! ## Step 2 — the sharpened transport bound -/

/-- **The sharpened score transport bound.**  Identical in shape to
`Ttc.CVGaussianFactorSevenAssembly.phaseScoreTransportBoundSqSeven` but with the
`1/(n+1)` factor that the interior ratio actually enjoys on the slow schedule
(`coolRatio_slowSource_le`, `phaseScore_slowSource_le`). -/
noncomputable def phaseScoreTransportBoundSqSharp
    (n : Nat) (R : Real) (sigmaSq : Nat → Real) (i : Nat) : Real :=
  Real.exp (R ^ 2 / (2 * sigmaSq i * ((n : Real) + 1))) ^ 2 * (1 + 2 * 7)

theorem phaseScoreTransportBoundSqSharp_pos
    {n : Nat} {R : Real} {sigmaSq : Nat → Real} (i : Nat) :
    0 < phaseScoreTransportBoundSqSharp n R sigmaSq i := by
  unfold phaseScoreTransportBoundSqSharp
  positivity

/-- **The safety net.**  The sharpened bound is never larger than the bound the
development already uses, so every statement proved at
`phaseScoreTransportBoundSqSeven` remains available; the sharpening only removes slack. -/
theorem phaseScoreTransportBoundSqSharp_le_seven
    {n : Nat} {R : Real} {sigmaSq : Nat → Real} {i : Nat} (hσ : 0 < sigmaSq i) :
    phaseScoreTransportBoundSqSharp n R sigmaSq i ≤
      Ttc.CVGaussianFactorSevenAssembly.phaseScoreTransportBoundSqSeven R sigmaSq i := by
  have hn0 : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
  have hexp : R ^ 2 / (2 * sigmaSq i * ((n : Real) + 1)) ≤ R ^ 2 / (2 * sigmaSq i) := by
    refine div_le_div_of_nonneg_left (sq_nonneg R) (by positivity) ?_
    nlinarith [mul_nonneg hσ.le hn0]
  have hsq : Real.exp (R ^ 2 / (2 * sigmaSq i * ((n : Real) + 1))) ^ 2 ≤
      Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.2 hexp) 2
  unfold phaseScoreTransportBoundSqSharp
    Ttc.CVGaussianFactorSevenAssembly.phaseScoreTransportBoundSqSeven
  exact mul_le_mul_of_nonneg_right hsq (by norm_num)

/-! ## Step 4 — the payoff at the share layer -/

/-- The sharpened bound at the canonical slow schedule and initial variance. -/
noncomputable def slowSharpBoundSq (n : Nat) (R : Real) : Nat → Real :=
  phaseScoreTransportBoundSqSharp n R
    (slowSourceSigmaSq n (slowSourceInitialVariance n))

theorem slowSharpBoundSq_pos {n : Nat} {R : Real} (i : Nat) :
    0 < slowSharpBoundSq n R i :=
  phaseScoreTransportBoundSqSharp_pos i

/-- The sharpened bound is below the one `Ttc.CVSlowCanonicalUniformParameters` selects. -/
theorem slowSharpBoundSq_le_slowUniformBoundSq
    {n : Nat} (hn : 1 ≤ n) {R : Real} (i : Nat) :
    slowSharpBoundSq n R i ≤ slowUniformBoundSq n R i :=
  phaseScoreTransportBoundSqSharp_le_seven
    (slowSourceSigmaSq_pos hn (slowSourceInitialVariance_pos hn) i)

/-- **The dimension-free share floor.**  Compare
`Ttc.CVSlowUniformShareBounds.slowUniformShareFloor`, whose exponential branch is
`1/(18 * exp (R^2/(2 s0))^2)`; at `s0 = slowSourceInitialVariance n = 1/(16 n)` that is
`1/(18 * exp (8 n R^2)^2)`.  Here the exponent is `8 R^2`, with **no `n`**. -/
noncomputable def slowSharpShareFloor (m k : Nat) (eps R : Real) : Real :=
  min (blockShare m k eps) (1 / (18 * Real.exp (8 * R ^ 2) ^ 2))

theorem slowSharpShareFloor_pos {m k : Nat} {eps R : Real} (heps : 0 < eps) :
    0 < slowSharpShareFloor m k eps R := by
  unfold slowSharpShareFloor
  exact lt_min (blockShare_pos heps) (by positivity)

theorem slowSharpShareFloor_lt_one {m k : Nat} {eps R : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    slowSharpShareFloor m k eps R < 1 :=
  (min_le_left _ _).trans_lt (blockShare_lt_one heps heps1)

theorem slowSharpShareFloor_nonneg (m k : Nat) (eps R : Real) :
    0 ≤ slowSharpShareFloor m k eps R := by
  unfold slowSharpShareFloor blockShare Ttc.CVCorrected.correctedNu
  refine le_min ?_ (by positivity)
  positivity

/-- **The improvement, quantified.**  The sharp floor is never below the floor the
development currently uses: the exponential branch improves from `exp (8 n R^2)^2` to
`exp (8 R^2)^2`, a factor `n` removed from the exponent. -/
theorem slowUniformShareFloor_le_slowSharpShareFloor
    {n : Nat} (hn : 1 ≤ n) (m k : Nat) (eps R : Real) :
    Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
        (slowSourceInitialVariance n) ≤
      slowSharpShareFloor m k eps R := by
  have hn1 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hn0 : (0 : Real) < (n : Real) := by linarith
  have hs0 : slowSourceInitialVariance n = 1 / (16 * (n : Real)) := rfl
  have hval : R ^ 2 / (2 * slowSourceInitialVariance n) = 8 * (n : Real) * R ^ 2 := by
    rw [hs0]
    field_simp
    ring
  have hexp : 8 * R ^ 2 ≤ R ^ 2 / (2 * slowSourceInitialVariance n) := by
    rw [hval]
    nlinarith [sq_nonneg R]
  have hsq : Real.exp (8 * R ^ 2) ^ 2 ≤
      Real.exp (R ^ 2 / (2 * slowSourceInitialVariance n)) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.2 hexp) 2
  unfold Ttc.CVSlowUniformShareBounds.slowUniformShareFloor slowSharpShareFloor
  refine le_min (min_le_left _ _) ((min_le_right _ _).trans ?_)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **The payoff.**  The sharp analogue of
`Ttc.CVSlowUniformShareBounds.slowUniformShareFloor_le_scoreAwareShare`: at the
sharpened transport bound the score-aware share of every slow phase is bounded below by
the **dimension-free** floor `min (blockShare m k eps) (1 / (18 * exp (8 R^2)^2))`.

The slack is unchanged (`slowUniformSlack`, i.e. `C = 2`); only `boundSq` is sharpened.
The arithmetic is the canonical one with `A := 8 R^2` in place of
`A := R^2/(2 * slowSourceInitialVariance n) = 8 n R^2`, which is legitimate because the
sharp exponent `R^2/(2 σ_i (n+1))` is at most `8 n R^2/(n+1) ≤ 8 R^2`. -/
theorem slowSharpShareFloor_le_scoreAwareShare
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {eps R : Real}
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : Nat) :
    slowSharpShareFloor m k eps R ≤
      scoreAwareShare m k eps
        (Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack n chainLength K)
        (slowSharpBoundSq n R) i := by
  have hn1 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  set s0 := slowSourceInitialVariance n with hs0def
  set sched := slowSourceSigmaSq n s0 with hscheddef
  set r := chain chainLength sched K (i + 1) / chain chainLength sched K i with hrdef
  set x := R ^ 2 / (2 * sched i * ((n : Real) + 1)) with hxdef
  have hsched : 0 < sched i := slowSourceSigmaSq_pos hn hs0 i
  have hratio : 1 ≤ r := by
    rw [hrdef, hscheddef]
    exact one_le_chain_ratio_of_sigmaSq_le_succ hK hfin hball
      (slowSourceSigmaSq_pos hn hs0) (slowSourceSigmaSq_mono_succ hn hs0 i)
  -- the sharp exponent is at most `8 R^2`, with no `n`
  have hexponent : x ≤ 8 * R ^ 2 := by
    have hlow : (1 : Real) / 8 ≤ 2 * sched i * ((n : Real) + 1) := by
      have hstart : s0 ≤ sched i := slowSourceSigmaSq_mono_start hn hs0 i
      have hs0eq : s0 = 1 / (16 * (n : Real)) := rfl
      have hn0 : (0 : Real) < (n : Real) := by linarith
      have h1 : 2 * s0 * ((n : Real) + 1) ≤ 2 * sched i * ((n : Real) + 1) := by
        nlinarith
      refine le_trans ?_ h1
      rw [hs0eq, div_le_iff₀ (by norm_num : (0 : Real) < 8)]
      rw [show 2 * (1 / (16 * (n : Real))) * ((n : Real) + 1) * 8
          = ((n : Real) + 1) / (n : Real) by field_simp; ring]
      rw [le_div_iff₀ hn0]
      linarith
    rw [hxdef, div_le_iff₀ (by linarith : (0 : Real) < 2 * sched i * ((n : Real) + 1))]
    nlinarith [sq_nonneg R]
  unfold slowSharpShareFloor scoreAwareShare
  refine le_min (min_le_left _ _) ((min_le_right _ _).trans ?_)
  unfold Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack slowSharpBoundSq
    phaseScoreTransportBoundSqSharp
  change 1 / (18 * Real.exp (8 * R ^ 2) ^ 2) ≤
    ((7 - 2) * r ^ 2 / 2) / (3 * (Real.exp x ^ 2 * (1 + 2 * 7)))
  have he : Real.exp x ≤ Real.exp (8 * R ^ 2) := Real.exp_le_exp.2 hexponent
  have he2 : Real.exp x ^ 2 ≤ Real.exp (8 * R ^ 2) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos x).le he 2
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  rw [show (7 - 2 : Real) * r ^ 2 / 2 = 5 * r ^ 2 / 2 by ring,
    show 3 * (Real.exp x ^ 2 * (1 + 2 * 7)) = 45 * Real.exp x ^ 2 by ring]
  rw [div_le_div_iff₀ (by positivity : (0 : Real) < 18 * Real.exp (8 * R ^ 2) ^ 2)
    (by positivity : (0 : Real) < 45 * Real.exp x ^ 2)]
  nlinarith [Real.exp_pos (8 * R ^ 2), Real.exp_pos x]

#print axioms coolRatio_le_of_norm_le
#print axioms coolRatio_le_of_last_of_sq_le
#print axioms slowSourceSigmaSq_inv_gap
#print axioms coolRatio_slowSource_le
#print axioms phaseScore_slowSource_le
#print axioms phaseScoreTransportBoundSqSharp
#print axioms phaseScoreTransportBoundSqSharp_pos
#print axioms phaseScoreTransportBoundSqSharp_le_seven
#print axioms slowSharpBoundSq
#print axioms slowSharpBoundSq_pos
#print axioms slowSharpBoundSq_le_slowUniformBoundSq
#print axioms slowSharpShareFloor
#print axioms slowSharpShareFloor_pos
#print axioms slowSharpShareFloor_lt_one
#print axioms slowSharpShareFloor_nonneg
#print axioms slowUniformShareFloor_le_slowSharpShareFloor
#print axioms slowSharpShareFloor_le_scoreAwareShare

end Ttc.CVSharpScoreTransport

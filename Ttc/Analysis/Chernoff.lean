/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `lem:chernoff`: the Poisson tail bound

The paper cites this to Soos et al. (Lemma 1) and uses it twice — once for the
`Noise` branch (`Pr[𝒳 > Thresh]`) and once for the `Err` branch (the two-sided
deviation of `|𝒳|` from its mean). Mathlib has `poissonMeasure` but no moment
generating function for it, so the whole estimate is built here:

  `Pr[N − λ ≥ ζ] ≤ exp(−ζ²/(2λ+ζ))`   and   `Pr[|N − λ| ≥ ζ] ≤ 2exp(−ζ²/(2λ+ζ))`.

## The route

1. `Ttc.mgf_poissonMeasure` — `E[e^{tN}] = exp(λ(e^t − 1))`, from
   `integral_poissonMeasure` and the exponential series.
2. The Chernoff bound `ProbabilityTheory.measure_ge_le_exp_mul_mgf` at the
   **optimal** `t = log(1 + ζ/λ)`, at which `λ(e^t − 1) = ζ` exactly, so the
   exponent collapses to Bennett's `−λ·h(ζ/λ)` with `h(u) = (1+u)log(1+u) − u`.
3. `Ttc.bennett_le` — `h(u) ≥ u²/(2+u)`, which turns Bennett into the paper's
   form. Substituting `s = log(1+u)`, `a = eˢ`, this is *exactly*
   `s(a+1) ≥ 2(a−1)` (`Ttc.two_mul_exp_sub_one_le`) — the only place calculus is
   needed, and only one derivative, because its own derivative condition
   `eˢ ≤ 1 + s·eˢ` follows from `Real.add_one_le_exp` with no calculus at all
   (`Ttc.exp_le_one_add_mul_exp`).
4. The lower tail is the same computation at `t = log(1 − ζ/λ) < 0`, whose scalar
   input `(1−u)log(1−u) + u ≥ u²/2` (`Ttc.bennett_lower_le`) again needs one
   derivative, its condition being `Real.log_le_sub_one_of_pos`.

The paper's constant `ζ²/(2λ+ζ)` is weaker than the standard Bernstein
`ζ²/(2λ+2ζ/3)`, so this proves what the paper uses.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-! ## The scalar inequalities -/

/-- **`eˢ ≤ 1 + s·eˢ` for `s ≥ 0`** — the derivative condition of
`Ttc.two_mul_exp_sub_one_le`, provable without calculus: for `s < 1` it is
`Real.add_one_le_exp` at `−s` multiplied by `eˢ`, and for `s ≥ 1` the term
`(s−1)eˢ` is already nonnegative. -/
theorem exp_le_one_add_mul_exp {s : ℝ} (_hs : 0 ≤ s) :
    Real.exp s ≤ 1 + s * Real.exp s := by
  rcases le_or_gt 1 s with h1 | h1
  · nlinarith [Real.exp_pos s]
  · have h := Real.add_one_le_exp (-s)
    have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos s).le
    have hexp : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos s]

/-- **`2(eˢ − 1) ≤ s(eˢ + 1)` for `s ≥ 0`.**

Equivalently `tanh(s/2) ≤ s/2`: the `(1,1)`-Padé lower bound for the logarithm.
It is genuinely second-order — no combination of first-order bounds like
`Real.add_one_le_exp` gives it — so this is the one derivative argument here. The
function `g s = s·eˢ + s − 2eˢ + 2` vanishes at `0` and has
`g' s = s·eˢ − eˢ + 1 ≥ 0` by `Ttc.exp_le_one_add_mul_exp`. -/
theorem two_mul_exp_sub_one_le {s : ℝ} (hs : 0 ≤ s) :
    2 * (Real.exp s - 1) ≤ s * (Real.exp s + 1) := by
  set g : ℝ → ℝ := fun x => x * Real.exp x + x - 2 * Real.exp x + 2 with hg
  have hderiv : ∀ x : ℝ, HasDerivAt g (x * Real.exp x - Real.exp x + 1) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y * Real.exp y)
        (1 * Real.exp x + x * Real.exp x) x :=
      (hasDerivAt_id x).mul (Real.hasDerivAt_exp x)
    have h2 : HasDerivAt (fun y : ℝ => 2 * Real.exp y) (2 * Real.exp x) x :=
      (Real.hasDerivAt_exp x).const_mul 2
    have h3 := ((h1.add (hasDerivAt_id x)).sub h2).add_const 2
    have heq : x * Real.exp x - Real.exp x + 1
        = 1 * Real.exp x + x * Real.exp x + 1 - 2 * Real.exp x := by ring
    rw [heq]
    exact h3
  have hdiff : Differentiable ℝ g := fun x => (hderiv x).differentiableAt
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn fun x hx => ?_
    rw [(hderiv x).deriv]
    have hx0 : (0:ℝ) ≤ x := le_of_lt (by simpa using hx)
    linarith [exp_le_one_add_mul_exp hx0]
  have hle := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
  simp only [hg, Real.exp_zero] at hle
  norm_num at hle
  linarith

/-- **Bennett's function dominates the Bernstein one**: for `u ≥ 0`,
`(1+u)·log(1+u) − u ≥ u²/(2+u)`.

This is `Ttc.two_mul_exp_sub_one_le` after the substitution `s = log(1+u)`: with
`a = eˢ = 1+u`, clearing the denominator turns the claim into
`a·(s(a+1) − 2(a−1)) ≥ 0`. -/
theorem bennett_le {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / (2 + u) ≤ (1 + u) * Real.log (1 + u) - u := by
  have hpos : (0:ℝ) < 1 + u := by linarith
  set s : ℝ := Real.log (1 + u) with hsdef
  have hs0 : 0 ≤ s := Real.log_nonneg (by linarith)
  have ha : Real.exp s = 1 + u := Real.exp_log hpos
  have hkey := two_mul_exp_sub_one_le hs0
  rw [ha] at hkey
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 + u)]
  nlinarith [hkey, hs0, hu]

/-- **The lower-tail scalar inequality**: `(1−u)log(1−u) + u ≥ u²/2` on `[0,1)`.
Stronger than the `u²/(2+u)` the upper tail gives, which is why the two-sided
bound can use a single constant. Its derivative condition is `−log(1−u) ≥ u`,
i.e. `Real.log_le_sub_one_of_pos`. -/
theorem bennett_lower_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u ^ 2 / 2 ≤ (1 - u) * Real.log (1 - u) + u := by
  set φ : ℝ → ℝ := fun x => (1 - x) * Real.log (1 - x) + x - x ^ 2 / 2 with hφ
  have hderiv : ∀ x : ℝ, x < 1 → HasDerivAt φ (-Real.log (1 - x) - x) x := by
    intro x hx
    have hpos : (0:ℝ) < 1 - x := by linarith
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-(1 - x)⁻¹) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_log hpos.ne').comp x hsub
    have hprod : HasDerivAt (fun y : ℝ => (1 - y) * Real.log (1 - y))
        (-1 * Real.log (1 - x) + (1 - x) * -(1 - x)⁻¹) x := hsub.mul hlog
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    have h := (hprod.add (hasDerivAt_id x)).sub hsq
    have heq : -Real.log (1 - x) - x
        = -1 * Real.log (1 - x) + (1 - x) * -(1 - x)⁻¹ + 1 - x := by
      field_simp
      try ring
    rw [heq]
    exact h
  have hcont : ContinuousOn φ (Set.Ico 0 1) := by
    refine ContinuousOn.sub (ContinuousOn.add ?_ continuousOn_id) (by fun_prop)
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.log (by fun_prop) ?_)
    intro x hx
    simp only [Set.mem_Ico] at hx
    intro h
    linarith [hx.2]
  have hmono : MonotoneOn φ (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1) hcont ?_ ?_
    · intro x hx
      rw [interior_Ico] at hx
      exact (hderiv x hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hderiv x hx.2).deriv]
      have hpos : (0:ℝ) < 1 - x := by linarith [hx.2]
      linarith [Real.log_le_sub_one_of_pos hpos]
  have hle := hmono (Set.mem_Ico.2 ⟨le_rfl, one_pos⟩) (Set.mem_Ico.2 ⟨hu0, hu1⟩) hu0
  simp only [hφ] at hle
  norm_num at hle
  linarith

/-! ## The moment generating function -/

/-- The exponential series, as a `tsum`. -/
theorem tsum_pow_div_factorial (x : ℝ) :
    ∑' n : ℕ, x ^ n / (n.factorial : ℝ) = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- Rewriting one term of the Poisson MGF's series: the rate and the exponential
combine into `(λeᵗ)ⁿ/n!`. -/
theorem poisson_mgf_term (r : ℝ≥0) (t : ℝ) (n : ℕ) :
    (Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ)) * Real.exp (t * n)
      = Real.exp (-r) * (((r : ℝ) * Real.exp t) ^ n / (n.factorial : ℝ)) := by
  have hexp : Real.exp (t * n) = Real.exp t ^ n := by
    rw [mul_comm, Real.exp_nat_mul]
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast n.factorial_pos
  rw [hexp, mul_pow]
  field_simp
  try ring

/-- **`E[e^{tN}] = exp(λ(eᵗ − 1))`** for `N ~ Pois(λ)`. -/
theorem mgf_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure r) t
      = Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
  rw [mgf, integral_poissonMeasure]
  calc ∑' n : ℕ, (Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ)) • Real.exp (t * (n : ℝ))
      = ∑' n : ℕ, Real.exp (-r) * (((r : ℝ) * Real.exp t) ^ n / (n.factorial : ℝ)) := by
        refine tsum_congr fun n => ?_
        rw [smul_eq_mul]
        exact poisson_mgf_term r t n
    _ = Real.exp (-r) * ∑' n : ℕ, ((r : ℝ) * Real.exp t) ^ n / (n.factorial : ℝ) :=
        tsum_mul_left
    _ = Real.exp (-r) * Real.exp ((r : ℝ) * Real.exp t) := by
        rw [tsum_pow_div_factorial]
    _ = Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
        rw [← Real.exp_add]; congr 1; ring

/-- The exponential is integrable against a Poisson law — its series is the
exponential series at `λeᵗ`. -/
theorem integrable_exp_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    Integrable (fun n : ℕ => Real.exp (t * n)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hcongr : ∀ n : ℕ,
      Real.exp (-r) * (((r : ℝ) * Real.exp t) ^ n / (n.factorial : ℝ))
        = Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) * ‖Real.exp (t * n)‖ := by
    intro n
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (poisson_mgf_term r t n).symm
  exact Summable.congr ((Real.summable_pow_div_factorial _).mul_left _) hcongr

/-! ## The tail bounds -/

/-- **`lem:chernoff`(ii), in Bennett form.** For `N ~ Pois(λ)` with `λ > 0` and
`ζ > 0`, `Pr[N ≥ λ + ζ] ≤ exp(ζ − (λ+ζ)log(1+ζ/λ))`, i.e. `exp(−λ·h(ζ/λ))`.

The Chernoff bound is evaluated at the optimal `t = log(1 + ζ/λ)`, at which
`λ(eᵗ − 1) = ζ` exactly. -/
theorem poisson_bennett {r : ℝ≥0} (hr : 0 < (r : ℝ)) {ζ : ℝ} (hζ : 0 < ζ) :
    (poissonMeasure r).real {k : ℕ | (r : ℝ) + ζ ≤ (k : ℝ)}
      ≤ Real.exp (ζ - ((r : ℝ) + ζ) * Real.log (1 + ζ / r)) := by
  set u : ℝ := ζ / r with hu
  have hu0 : 0 < u := div_pos hζ hr
  set t : ℝ := Real.log (1 + u) with ht
  have ht0 : 0 ≤ t := Real.log_nonneg (by linarith)
  have hexpt : Real.exp t = 1 + u := Real.exp_log (by linarith)
  have hrate : (r : ℝ) * (Real.exp t - 1) = ζ := by
    rw [hexpt, hu]; field_simp; try ring
  have hmain := measure_ge_le_exp_mul_mgf (X := fun k : ℕ => (k : ℝ))
    (μ := poissonMeasure r) ((r : ℝ) + ζ) ht0 (integrable_exp_poissonMeasure r t)
  rw [mgf_poissonMeasure, hrate] at hmain
  refine le_trans hmain (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  ring

/-- **`lem:chernoff`(ii).** `Pr[N − λ ≥ ζ] ≤ exp(−ζ²/(2λ+ζ))`.

Bennett's bound with `Ttc.bennett_le` substituted: `λ·h(ζ/λ) ≥ ζ²/(2λ+ζ)`. -/
theorem poisson_tail {r : ℝ≥0} (hr : 0 < (r : ℝ)) {ζ : ℝ} (hζ : 0 < ζ) :
    (poissonMeasure r).real {k : ℕ | (r : ℝ) + ζ ≤ (k : ℝ)}
      ≤ Real.exp (-(ζ ^ 2 / (2 * r + ζ))) := by
  refine le_trans (poisson_bennett hr hζ) (Real.exp_le_exp.2 ?_)
  have hu0 : (0:ℝ) ≤ ζ / r := (div_pos hζ hr).le
  have hscale := mul_le_mul_of_nonneg_left (bennett_le hu0) hr.le
  have hlhs : (r : ℝ) * ((ζ / r) ^ 2 / (2 + ζ / r)) = ζ ^ 2 / (2 * r + ζ) := by
    rw [eq_div_iff (by positivity)]
    field_simp
    try ring
  have hrhs : (r : ℝ) * ((1 + ζ / r) * Real.log (1 + ζ / r) - ζ / r)
      = ((r : ℝ) + ζ) * Real.log (1 + ζ / r) - ζ := by
    field_simp
    try ring
  rw [hlhs, hrhs] at hscale
  linarith

/-- **`lem:chernoff`, lower tail.** `Pr[N ≤ λ − ζ] ≤ exp(−ζ²/(2λ+ζ))`.

For `ζ > λ` the event is empty and for `ζ = λ` it is `{0}`; the main case is the
Chernoff bound at `t = log(1 − ζ/λ) < 0`, where `Ttc.bennett_lower_le` gives the
stronger exponent `−ζ²/(2λ)`. -/
theorem poisson_lower_tail {r : ℝ≥0} (hr : 0 < (r : ℝ)) {ζ : ℝ} (hζ : 0 < ζ) :
    (poissonMeasure r).real {k : ℕ | (k : ℝ) ≤ (r : ℝ) - ζ}
      ≤ Real.exp (-(ζ ^ 2 / (2 * r + ζ))) := by
  rcases lt_or_ge ζ (r : ℝ) with hlt | hge
  · set u : ℝ := ζ / r with hu
    have hu0 : 0 < u := div_pos hζ hr
    have hu1 : u < 1 := by rw [hu, div_lt_one hr]; exact hlt
    set t : ℝ := Real.log (1 - u) with ht
    have hpos : (0:ℝ) < 1 - u := by linarith
    have ht0 : t ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have hexpt : Real.exp t = 1 - u := Real.exp_log hpos
    have hrate : (r : ℝ) * (Real.exp t - 1) = -ζ := by
      rw [hexpt, hu]; field_simp; try ring
    have hmain := measure_le_le_exp_mul_mgf (X := fun k : ℕ => (k : ℝ))
      (μ := poissonMeasure r) ((r : ℝ) - ζ) ht0 (integrable_exp_poissonMeasure r t)
    rw [mgf_poissonMeasure, hrate] at hmain
    refine le_trans hmain ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hscale := mul_le_mul_of_nonneg_left (bennett_lower_le hu0.le hu1) hr.le
    have hlhs : (r : ℝ) * (u ^ 2 / 2) = ζ ^ 2 / (2 * r) := by
      rw [hu, eq_div_iff (by positivity)]
      field_simp
      try ring
    have hrhs : (r : ℝ) * ((1 - u) * Real.log (1 - u) + u)
        = -(((r : ℝ) - ζ) * Real.log (1 - u)) * (-1) + ζ := by
      rw [hu]
      field_simp
      try ring
    rw [hlhs, hrhs] at hscale
    have hcmp : ζ ^ 2 / (2 * r + ζ) ≤ ζ ^ 2 / (2 * r) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith
  · rcases eq_or_lt_of_le hge with heq | hlt
    · -- `ζ = λ`: the event is `{0}`, of mass `e^{−λ}`, and `λ²/(3λ) = λ/3 ≤ λ`
      have hset : {k : ℕ | (k : ℝ) ≤ (r : ℝ) - ζ} = {0} := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, ← heq, sub_self]
        constructor
        · intro h
          have : (k : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg k)
          exact_mod_cast this
        · rintro rfl; norm_num
      rw [hset, poissonMeasure_real_singleton]
      have hsimp : Real.exp (-(r : ℝ)) * (r : ℝ) ^ (0:ℕ) / ((0:ℕ).factorial : ℝ)
          = Real.exp (-(r : ℝ)) := by norm_num
      rw [hsimp]
      refine Real.exp_le_exp.2 ?_
      rw [neg_le_neg_iff, ← heq, show (2:ℝ) * r + r = 3 * r by ring,
        div_le_iff₀ (by linarith)]
      nlinarith
    · -- `ζ > λ`: the event is empty
      have hset : {k : ℕ | (k : ℝ) ≤ (r : ℝ) - ζ} = ∅ := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        linarith [Nat.cast_nonneg (α := ℝ) k]
      rw [hset, measureReal_empty]
      positivity

/-- **`lem:chernoff`(i).** The two-sided form:
`Pr[N ≤ λ − ζ] + Pr[N ≥ λ + ζ] ≤ 2exp(−ζ²/(2λ+ζ))`. -/
theorem poisson_tail_two_sided {r : ℝ≥0} (hr : 0 < (r : ℝ)) {ζ : ℝ} (hζ : 0 < ζ) :
    (poissonMeasure r).real {k : ℕ | (r : ℝ) + ζ ≤ (k : ℝ)}
        + (poissonMeasure r).real {k : ℕ | (k : ℝ) ≤ (r : ℝ) - ζ}
      ≤ 2 * Real.exp (-(ζ ^ 2 / (2 * r + ζ))) := by
  linarith [poisson_tail hr hζ, poisson_lower_tail hr hζ]

/-! ## The paper's two applications

`lem:numlattice` uses `lem:chernoff` exactly twice, and both uses are the
specialisations below. Proving them here means the epoch skeleton of
`Analysis/Sketch` consumes numbers that are *derived*, not posited.
-/

/-- **The `Noise` branch's estimate**: `Pr[N > Thresh] ≤ exp(−Thresh/6)` whenever
the rate is at most `Thresh/2`.

This is the paper's "`Thresh − λ > Thresh/2`, so `Pr[𝒳 > Thresh] ≤ exp(−Thresh/6)`"
(`analysis.tex:289`); the constant `6` is exactly right, since with `ζ = Thresh − λ`
one has `2λ + ζ = λ + Thresh ≤ 3Thresh/2` and `ζ ≥ Thresh/2`, giving
`ζ²/(2λ+ζ) ≥ Thresh/6`. -/
theorem poisson_overflow {r : ℝ≥0} (hr : 0 < (r : ℝ)) {Thresh : ℝ}
    (hT : 2 * (r : ℝ) ≤ Thresh) :
    (poissonMeasure r).real {k : ℕ | Thresh ≤ (k : ℝ)}
      ≤ Real.exp (-(Thresh / 6)) := by
  have hT0 : 0 < Thresh := by linarith
  set ζ : ℝ := Thresh - r with hζdef
  have hζ : 0 < ζ := by rw [hζdef]; linarith
  have hset : {k : ℕ | Thresh ≤ (k : ℝ)} = {k : ℕ | (r : ℝ) + ζ ≤ (k : ℝ)} := by
    rw [hζdef]; ext k; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  rw [hset]
  refine le_trans (poisson_tail hr hζ) (Real.exp_le_exp.2 ?_)
  rw [neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by rw [hζdef]; linarith)]
  rw [hζdef]
  nlinarith

/-- **The `Err` branch's estimate**: `Pr[|N − λ| ≥ ε'λ] ≤ 2exp(−ε'²λ/3)` for
`0 < ε' ≤ 1`.

This is the paper's `Pr[err(j)] ≤ 2exp(−ε'²|S|p̃_j/3)` (`analysis.tex:293`); the
constant `3` is exactly right, since `ζ = ε'λ` gives
`ζ²/(2λ+ζ) = ε'²λ/(2+ε') ≥ ε'²λ/3`. -/
theorem poisson_relative {r : ℝ≥0} (hr : 0 < (r : ℝ)) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (poissonMeasure r).real {k : ℕ | (r : ℝ) + ε * r ≤ (k : ℝ)}
        + (poissonMeasure r).real {k : ℕ | (k : ℝ) ≤ (r : ℝ) - ε * r}
      ≤ 2 * Real.exp (-(ε ^ 2 * r / 3)) := by
  have hζ : 0 < ε * (r : ℝ) := by positivity
  refine le_trans (poisson_tail_two_sided hr hζ) ?_
  have hexp : Real.exp (-((ε * (r : ℝ)) ^ 2 / (2 * r + ε * r)))
      ≤ Real.exp (-(ε ^ 2 * r / 3)) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by nlinarith)]
    nlinarith
  linarith

end Ttc

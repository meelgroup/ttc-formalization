/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.SamplerCost

/-!
# The per-sample price with the accuracy `ε'` left explicit

`Ttc.SamplerCost.samplePrice_le_quartic` (`Ttc/Exec/SamplerCost.lean:765`) carries a regime
hypothesis `hepsn : 1/2ⁿ ≤ ε'`.  That hypothesis is **not** needed for the price to be
finite or for the walk to be correct: it exists solely to absorb the `log(1/ε')` that the
Lovász–Vempala log argument `8M/ν²` contains into the `n·log(2R)` that the volume bound
contributes, so that the printed bound mentions only `n`, `R` and `γ`.

**This file removes `hepsn` by declining to perform that absorption.**  The price of the
removal is exactly one visible term: the bound now reads

```
samplePrice n γ R M ε' rfac  ≤  2⁶² · n³ · rfac · (R²/γ²) · (n·log(2R) + log(1/ε'))
```

with `log(1/ε')` explicit on the right-hand side.  This is the shape the paper's own
appendix uses before it specialises (`sections/proof-appendix.tex:194`, the walk taking
`O(n³·(R²/γ²)·(n·log R + log(1/ε)))` steps), and it is `O(n⁴)` in exactly the regime
`hepsn` describes — but it is now a *theorem about all `0 < ε' ≤ 1`*, not only about
`ε' ≥ 2⁻ⁿ`.

Nothing is lost downstream: `Ttc.SamplerCost.samplePrice_le_quartic_of_eps` re-derives the
`hepsn` form (at `2⁶³` rather than `2⁶²`, the factor `2` being `L ≤ 2n·log(2R)`) from the
`ε'`-explicit one, so any consumer of the old statement can be served from here.

**No new definitions.**  Every declaration below is a theorem over the `def`s already in
`Ttc/Exec/SamplerCost.lean`; the cost model itself is untouched, so this file adds no new
modelling assumption to the audit surface.

⚠ As with the whole of `Ttc/Exec/SamplerCost.lean`, these bounds are **conditional on
`H : Ttc.HitAndRunTheorem11Input`** for their *meaning*; as numbers they are unconditional
arithmetic.
-/

namespace Ttc.SamplerCost

open Real

set_option maxRecDepth 100000

/-! ## The log argument, with `1/ε'` kept as a factor

The `hepsn`-free counterpart of `Ttc.SamplerCost.logArg_le`.  That lemma pushes `1/ε'` up
into `(2R)ⁿ` using `ε' ≥ 2⁻ⁿ`; here the factor simply stays where it is. -/

/-- **`8M/ν² ≤ (2R)^{3n+7} · (1/ε')²`.**

`8M/ν² = 128·M·(2R)^{2n}·(1/ε')²` (the same `field_simp` identity as
`Ttc.SamplerCost.logArg_le`), and now only `128 ≤ (2R)⁷` and `M ≤ (2R)ⁿ` are used: the
`(1/ε')²` is carried along untouched.  **No lower bound on `ε'` is required.** -/
theorem logArg_le_eps (n : ℕ) {M R epsPrime : ℝ} (hR1 : 1 ≤ R)
    (hM1 : 1 ≤ M) (hMB : M ≤ (2 * R) ^ n) (heps0 : 0 < epsPrime) :
    8 * M / worstTol n epsPrime R ^ 2 ≤ (2 * R) ^ (3 * n + 7) * (1 / epsPrime) ^ 2 := by
  have hB2 : (2 : ℝ) ≤ 2 * R := by linarith
  have hB1 : (1 : ℝ) ≤ 2 * R := by linarith
  have hB0 : (0 : ℝ) < 2 * R := by linarith
  have hX0 : (0 : ℝ) < (2 * R) ^ n := by positivity
  have heq : 8 * M / worstTol n epsPrime R ^ 2
      = 128 * M * ((2 * R) ^ n) ^ 2 * (1 / epsPrime) ^ 2 := by
    unfold worstTol
    field_simp
    ring
  rw [heq]
  have hinv0 : (0 : ℝ) ≤ 1 / epsPrime := by positivity
  have h128 : (128 : ℝ) ≤ (2 * R) ^ 7 := by
    calc (128 : ℝ) = 2 ^ 7 := by norm_num
      _ ≤ (2 * R) ^ 7 := pow_le_pow_left₀ (by norm_num) hB2 7
  have hstep : 128 * M * ((2 * R) ^ n) ^ 2 * (1 / epsPrime) ^ 2
      ≤ (2 * R) ^ 7 * (2 * R) ^ n * ((2 * R) ^ n) ^ 2 * (1 / epsPrime) ^ 2 := by
    gcongr
  refine hstep.trans ?_
  have hpow : (2 * R) ^ 7 * (2 * R) ^ n * ((2 * R) ^ n) ^ 2
      = (2 * R) ^ (3 * n + 7) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hpow]

/-- **`log(8M/ν²) ≤ 10·n·log(2R) + 2·log(1/ε')`.**

The `hepsn`-free counterpart of `Ttc.SamplerCost.log_logArg_le`.  The exponent bookkeeping
is `3n + 7 ≤ 10n` for `n ≥ 1`; the `2·log(1/ε')` is the term that `hepsn` was there to
absorb, and it is now simply printed. -/
theorem log_logArg_le_eps (n : ℕ) {M R epsPrime : ℝ} (hn : 1 ≤ n) (hR1 : 1 ≤ R)
    (hM1 : 1 ≤ M) (hMB : M ≤ (2 * R) ^ n) (heps0 : 0 < epsPrime) :
    Real.log (8 * M / worstTol n epsPrime R ^ 2)
      ≤ 10 * (n : ℝ) * Real.log (2 * R) + 2 * Real.log (1 / epsPrime) := by
  have hB0 : (0 : ℝ) < 2 * R := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hw0 : 0 < worstTol n epsPrime R := by unfold worstTol; positivity
  have hnum : (0 : ℝ) < 8 * M / worstTol n epsPrime R ^ 2 :=
    div_pos (by linarith) (pow_pos hw0 2)
  have h := Real.log_le_log hnum (logArg_le_eps n hR1 hM1 hMB heps0)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
  push_cast at h
  have hcoef : (3 * (n : ℝ) + 7) * Real.log (2 * R) ≤ 10 * (n : ℝ) * Real.log (2 * R) :=
    mul_le_mul_of_nonneg_right (by linarith) hlog0
  linarith

/-! ## The transition count, with `log(1/ε')` separate -/

/-- **The uniform transition count is `O(n²·(R²/γ²)·(n·log(2R) + log(1/ε')))`** —
explicitly, `10·2⁵⁶·n²·(R²/γ²)·(n·log(2R) + log(1/ε')) + 1`.

The `hepsn`-free counterpart of `Ttc.SamplerCost.stepsPrice_le`.  In the regime
`ε' ≥ 2⁻ⁿ` the bracket is `O(n·log(2R))` and this is the old `O(n³·(R²/γ²)·log(2R))`; for
smaller `ε'` the second term takes over, which is precisely what `hepsn` forbade. -/
theorem stepsPrice_le_eps (n : ℕ) {γ R M epsPrime : ℝ} (hn : 1 ≤ n) (hR1 : 1 ≤ R)
    (hγ0 : 0 < γ) (hM1 : 1 ≤ M) (hMB : M ≤ (2 * R) ^ n) (heps0 : 0 < epsPrime)
    (heps1 : epsPrime ≤ 1) :
    (stepsPrice n γ R M epsPrime : ℝ)
      ≤ 10 * 2 ^ 56 * ((n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2)
          * ((n : ℝ) * Real.log (2 * R) + Real.log (1 / epsPrime))) + 1 := by
  have hB1 : (1 : ℝ) ≤ 2 * R := by linarith
  have hXn : (1 : ℝ) ≤ (2 * R) ^ n := one_le_pow₀ hB1
  have hw0 : 0 < worstTol n epsPrime R := by unfold worstTol; positivity
  have ht1 : worstTol n epsPrime R ≤ 1 := by
    unfold worstTol
    rw [div_le_one (by positivity)]
    linarith
  have hlogarg : (1 : ℝ) ≤ 8 * M / worstTol n epsPrime R ^ 2 := by
    rw [le_div_iff₀ (pow_pos hw0 2)]
    nlinarith [hw0.le]
  have hlog0 : 0 ≤ Real.log (8 * M / worstTol n epsPrime R ^ 2) := Real.log_nonneg hlogarg
  have hlogeps0 : (0 : ℝ) ≤ Real.log (1 / epsPrime) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ heps0]
    linarith
  have hgeo0 : (0 : ℝ) ≤ 2 ^ 56 * (n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2) :=
    mul_nonneg (by positivity) (by positivity)
  have hthr0 : 0 ≤ hitAndRunTheorem11Threshold n γ R M (worstTol n epsPrime R) := by
    unfold hitAndRunTheorem11Threshold
    exact mul_nonneg (div_nonneg (by positivity) (by positivity)) hlog0
  have hbig : Real.log (8 * M / worstTol n epsPrime R ^ 2)
      ≤ 10 * ((n : ℝ) * Real.log (2 * R) + Real.log (1 / epsPrime)) := by
    have h := log_logArg_le_eps n hn hR1 hM1 hMB heps0
    linarith
  have hthr : hitAndRunTheorem11Threshold n γ R M (worstTol n epsPrime R)
      ≤ 10 * 2 ^ 56 * ((n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2)
          * ((n : ℝ) * Real.log (2 * R) + Real.log (1 / epsPrime))) := by
    unfold hitAndRunTheorem11Threshold
    rw [mul_div_assoc]
    calc 2 ^ 56 * (n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2)
            * Real.log (8 * M / worstTol n epsPrime R ^ 2)
        ≤ 2 ^ 56 * (n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2)
            * (10 * ((n : ℝ) * Real.log (2 * R) + Real.log (1 / epsPrime))) :=
          mul_le_mul_of_nonneg_left hbig hgeo0
      _ = 10 * 2 ^ 56 * ((n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2)
            * ((n : ℝ) * Real.log (2 * R) + Real.log (1 / epsPrime))) := by ring
  unfold stepsPrice hitAndRunTheorem11Steps
  push_cast
  have hfl := Nat.floor_le hthr0
  linarith

/-! ## The headline: the per-sample price without the regime hypothesis -/

/-- **THE `hepsn`-FREE PER-SAMPLE PRICE.**

```
samplePrice n γ R M ε' rfac  ≤  2⁶² · n³ · rfac · (R²/γ²) · (n·log(2R) + log(1/ε'))
```

This is `Ttc.SamplerCost.samplePrice_le_quartic` with the hypothesis `hepsn : 2⁻ⁿ ≤ ε'`
**deleted** and nothing else changed — same constant `2⁶²`, same remaining hypotheses:

* `hn : 1 ≤ n`, `hrfac : 1 ≤ rfac` — the facet count is not suppressed;
* `hR1 : 1 ≤ R`, `hγ0 : 0 < γ`, `hγR : γ ≤ R` — `R²/γ²` is not suppressed;
* `hM1 : 1 ≤ M`, `hMB : M ≤ (2R)ⁿ` — the warmness of the start, still a genuine open
  hypothesis (nothing in this repository constructs a warm start);
* `heps0 : 0 < ε'`, `heps1 : ε' ≤ 1` — well-definedness only, no regime.

Suppressing `rfac`, `R²/γ²` and `log R` leaves `O(n³·(n + log(1/ε')))` operations per
sample, which is the paper's own pre-absorption count
(`sections/proof-appendix.tex:194`) and is `O(n⁴)` as soon as `log(1/ε') = O(n)`. -/
theorem samplePrice_le_quartic_eps (n : ℕ) {γ R M epsPrime rfac : ℝ} (hn : 1 ≤ n)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ) (hγR : γ ≤ R)
    (hM1 : 1 ≤ M) (hMB : M ≤ (2 * R) ^ n) (heps0 : 0 < epsPrime) (heps1 : epsPrime ≤ 1) :
    (samplePrice n γ R M epsPrime rfac : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 3 * rfac * (R ^ 2 / γ ^ 2)
          * ((n : ℝ) * Real.log (2 * R) + Real.log (1 / epsPrime)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0.69 : ℝ) ≤ Real.log (2 * R) := by
    have h := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log (2 * R) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * R) := by linarith
  have hlogeps0 : (0 : ℝ) ≤ Real.log (1 / epsPrime) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ heps0]
    linarith
  have hRg : (1 : ℝ) ≤ R ^ 2 / γ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have hS := stepsPrice_le_eps n hn hR1 hγ0 hM1 hMB heps0 heps1
  set L : ℝ := (n : ℝ) * Real.log (2 * R) + Real.log (1 / epsPrime) with hLdef
  have hL069 : (0.69 : ℝ) ≤ L := by
    have : (0.69 : ℝ) ≤ (n : ℝ) * Real.log (2 * R) := by nlinarith
    rw [hLdef]; linarith
  set T : ℝ := (n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2) * L with hT
  have hT069 : (0.69 : ℝ) ≤ T := by
    have h1 : (1 : ℝ) * 1 ≤ (n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2) :=
      mul_le_mul hn2 hRg (by norm_num) (by linarith)
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ L)
    rw [hT]
    nlinarith
  have h3 : (3 : ℝ) ≤ 10 * 2 ^ 56 * T := by
    have hmul : 10 * (2 : ℝ) ^ 56 * 0.69 ≤ 10 * 2 ^ 56 * T :=
      mul_le_mul_of_nonneg_left hT069 (by positivity)
    have hnum : (3 : ℝ) ≤ 10 * (2 : ℝ) ^ 56 * 0.69 := by norm_num
    linarith
  have hstep2 : (stepsPrice n γ R M epsPrime : ℝ) + 2 ≤ 20 * 2 ^ 56 * T := by linarith
  have hC : ((stepOpCharge n rfac : ℕ) : ℝ) ≤ 2 * (n : ℝ) * rfac := by
    unfold stepOpCharge
    have h1 : ((⌈(n : ℝ) * rfac⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) * rfac + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    nlinarith
  have hC0 : (0 : ℝ) ≤ ((stepOpCharge n rfac : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ 20 * 2 ^ 56 * T := by
    have : (0 : ℝ) ≤ T := by linarith
    positivity
  have hfinal : (samplePrice n γ R M epsPrime rfac : ℝ)
      ≤ 20 * 2 ^ 56 * T * (2 * (n : ℝ) * rfac) := by
    unfold samplePrice drawOpCharge
    push_cast
    exact mul_le_mul hstep2 hC hC0 hb0
  refine hfinal.trans ?_
  have hQ0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 * rfac * (R ^ 2 / γ ^ 2) * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity))
      (by linarith)
  have hconst : (40 : ℝ) * 2 ^ 56 ≤ 2 ^ 62 := by norm_num
  calc 20 * 2 ^ 56 * T * (2 * (n : ℝ) * rfac)
      = 40 * 2 ^ 56 * ((n : ℝ) ^ 3 * rfac * (R ^ 2 / γ ^ 2) * L) := by
        rw [hT]; ring
    _ ≤ 2 ^ 62 * ((n : ℝ) ^ 3 * rfac * (R ^ 2 / γ ^ 2) * L) :=
        mul_le_mul_of_nonneg_right hconst hQ0
    _ = 2 ^ 62 * (n : ℝ) ^ 3 * rfac * (R ^ 2 / γ ^ 2) * L := by ring

/-- **The old `hepsn` form, recovered from the `ε'`-explicit one.**

In the regime `ε' ≥ 2⁻ⁿ` we have `log(1/ε') ≤ n·log 2 ≤ n·log(2R)` (using `R ≥ 1`), so the
bracket `n·log(2R) + log(1/ε')` is at most `2n·log(2R)` and the bound collapses to
`2⁶³·n⁴·rfac·(R²/γ²)·log(2R)`.

The constant is `2⁶³`, one doubling above `Ttc.SamplerCost.samplePrice_le_quartic`'s `2⁶²`
— that factor `2` is exactly the `L ≤ 2n·log(2R)` step and is the only thing this route
costs.  The *exponent*, which is the finding, is unchanged.  Nothing downstream of
`samplePrice_le_quartic` needs a bound tighter than a constant factor, so this corollary
can stand in for it **up to the printed constant**: a consumer that quotes `2⁶²`
literally in its own statement (e.g. `Ttc/Exec/PolyRun.lean:584`) must print `2⁶³`
instead. -/
theorem samplePrice_le_quartic_of_eps (n : ℕ) {γ R M epsPrime rfac : ℝ} (hn : 1 ≤ n)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ) (hγR : γ ≤ R)
    (hM1 : 1 ≤ M) (hMB : M ≤ (2 * R) ^ n) (heps0 : 0 < epsPrime) (heps1 : epsPrime ≤ 1)
    (hepsn : 1 / 2 ^ n ≤ epsPrime) :
    (samplePrice n γ R M epsPrime rfac : ℝ)
      ≤ 2 ^ 63 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2 : Real.log 2 ≤ Real.log (2 * R) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * R) := le_trans (Real.log_nonneg (by norm_num)) hlog2
  -- `1/ε' ≤ 2ⁿ`, hence `log(1/ε') ≤ n·log 2 ≤ n·log(2R)`.
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hinv : 1 / epsPrime ≤ 2 ^ n := by
    rw [div_le_iff₀ h2n] at hepsn
    rw [div_le_iff₀ heps0]
    linarith
  have hlogeps : Real.log (1 / epsPrime) ≤ (n : ℝ) * Real.log (2 * R) := by
    have h1 : Real.log (1 / epsPrime) ≤ Real.log ((2 : ℝ) ^ n) :=
      Real.log_le_log (by positivity) hinv
    rw [Real.log_pow] at h1
    have h2 : (n : ℝ) * Real.log 2 ≤ (n : ℝ) * Real.log (2 * R) :=
      mul_le_mul_of_nonneg_left hlog2 (by linarith)
    linarith
  have hbase := samplePrice_le_quartic_eps n hn hrfac hR1 hγ0 hγR hM1 hMB heps0 heps1
  refine hbase.trans ?_
  have hK0 : (0 : ℝ) ≤ 2 ^ 62 * (n : ℝ) ^ 3 * rfac * (R ^ 2 / γ ^ 2) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  calc 2 ^ 62 * (n : ℝ) ^ 3 * rfac * (R ^ 2 / γ ^ 2)
          * ((n : ℝ) * Real.log (2 * R) + Real.log (1 / epsPrime))
      ≤ 2 ^ 62 * (n : ℝ) ^ 3 * rfac * (R ^ 2 / γ ^ 2) * (2 * ((n : ℝ) * Real.log (2 * R))) :=
        mul_le_mul_of_nonneg_left (by linarith) hK0
    _ = 2 ^ 63 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) := by ring

/-! ## Axiom profile -/

#print axioms logArg_le_eps
#print axioms log_logArg_le_eps
#print axioms stepsPrice_le_eps
#print axioms samplePrice_le_quartic_eps
#print axioms samplePrice_le_quartic_of_eps

end Ttc.SamplerCost

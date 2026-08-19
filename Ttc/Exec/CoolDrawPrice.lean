/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.MetropolisConductanceSharp
import Arlib.MarkovChains.Continuous.ConductanceToTV
import Ttc.Exec.VolumePriceCV
import Mathlib.Analysis.Asymptotics.Defs

/-!
# `Exec/CoolDrawPrice`: a price for **one draw** from a cooled Gaussian phase

> ## ⚠ THIS FILE IS NOT A MIXING-TIME THEOREM AND NOT AN `O*(n³)` CLAIM ⚠
>
> Everything below is **conditional on `hiso`**, Cousins–Vempala's `thm:iso`
> (arXiv:1409.6011), which is a *binder* of
> `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`
> (`Arlib/MarkovChains/Continuous/MetropolisConductanceSharp.lean:431`) and is **not proved
> anywhere in this repository**.  It is additionally conditional on the local-conductance
> floor `hell`/`hfloor` of that theorem, which is a genuine restriction on `K`, and on a
> **visible warmness parameter `M`** that nothing here bounds (see § *Warmness* below).
> Nothing in this file may be quoted as a mixing-time bound, as an `O*(n³)` bound, or as
> evidence that TTC runs in polynomial time.

## What this file is for

`Ttc.CVCost.cvVolumeOpsPrice n L κ c p q = q · Ttc.CVCost.cvVolumeSamplePrice n L κ c p`
(`Ttc/Exec/VolumePriceCV.lean:169`) carries a parameter `q` — "the arithmetic (or
membership-query) charge of producing **one** sample from the cooled Gaussian of a phase" —
and that file's docstring records that **this repository does not bound `q`**.  This file
supplies a candidate bound for `q`, together with the mixing statement that makes the number
a *price* rather than an arbitrary constant.

## The route, and where each factor comes from

1. **Conductance.** `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge` at the
   **largest step allowed by its own `hδσ`**, namely `δ = σ/8`.  That hypothesis reads
   `hδσ : δ ≤ σ / 8` — *not* `δ ≤ σ/(8√n)`; the `√n` that the Cousins–Vempala regime puts on
   the step is nowhere in that theorem's binder list.  At `δ = σ/8` its conclusion
   `δ·log 2/(640·σ·n)` becomes `log 2/(5120·n)` — **`σ` cancels**, so the price below is the
   same for every phase of the cooling schedule regardless of that phase's temperature.
   That is `Ttc.CoolCost.coolPhi`.
2. **The `√n` caveat, which costs a factor `n` in `q`.**  That theorem lands at
   `Ω(δ·log 2/(σ·n))` and not at `Ω(δ·log 2/(σ·√n))`, because it inherits the `δ/n`
   separation of `Arlib.MarkovChains.volume_lens_inter_ge_max`; its own docstring
   (`MetropolisConductanceSharp.lean:~404`) says so.  A `√n`-sharp conductance would make
   `1/Φ²` linear rather than quadratic in `n` and would take `q` from `n³` to `n²`.
3. **Laziness.** `Arlib.MarkovChains.ofReal_half_le_conductance_lazy` — exactly a factor `2`
   in `Φ`, hence a factor `4` in the deadline.  Bundled inside
   `Arlib.MarkovChains.tvLe_iterate_lazy_of_exceptional`.
4. **Mixing.** `Arlib.MarkovChains.ls_lazy` (Lovász–Simonovits 1993, Corollary 1.5, *proved*
   here) via `Arlib.MarkovChains.tvLe_iterate_lazy_of_exceptional`, whose deadline is
   `4·lsThreshold M Φ ε = 4·log(8M/ε²)/Φ²`.
5. **Per-step charge.**  `Ttc.CoolCost.coolStepOpCharge n rfac = ⌈n·rfac⌉₊`, a **modelling
   definition** mirroring `Ttc.SamplerCost.stepOpCharge`, and carried through
   `Ttc.CoolCost.coolDrawPrice` as an opaque parameter `w : ℕ` so that a reader who rejects
   the model can substitute their own.  The lazy coin flip is absorbed into it.

## The exponent, derived

`Φ = log 2/(5120·n)` gives `4/Φ² ≤ 2²⁸·n²` (because `log 2 ≥ 5/8`, so
`(log 2)² ≥ 25/64`, and `4·5120² = 2²²·25`); hence

```
coolDrawSteps ≤ 2²⁸·n²·log(8M/ε²) + 2                (Ttc.CoolCost.coolDrawSteps_le)
coolDrawPrice ≤ 2²⁹·n²·log(8M/ε²)·w                  (Ttc.CoolCost.coolDrawPrice_le)
q := coolDrawPrice … (coolStepOpCharge n rfac)
     ≤ (2²⁹·(rfac+1)·log(8M/ε²))·n³                  (Ttc.CoolCost.coolDrawPrice_le_cubic)
     ≤ 2²⁹·n³·((rfac+1)·log(8M/ε²))                  (Ttc.CoolCost.coolDrawPrice_le_bridge)
```

so **`kq = 3`, `Cq = 2²⁹`, `qFac = (rfac + 1)·log(8M/ε²)`** — the last line is literally the
`hq : (q : ℝ) ≤ Cq · (n : ℝ) ^ kq · qFac` that `Ttc.cvVolumeOpsPrice_le_poly`
(`Exec/TheoremPoly`, deleted 2026-08-19) and `Ttc.isBigO_ttc_runtime_cv` used to consume, so the
composition needs no glue, and it gives `kv = kq + 1 = 4`.  (The capstone
`Ttc.PolyComplexity.ttcComplexity_le_poly` takes the *volume* bound `hcVol`, not `hq`;
`Ttc.cvVolumeOpsPrice_le_poly` is what turns one into the other.)

## Warmness — an explicit, **unbounded** hypothesis

`M` is the warmness of the start of a phase relative to that phase's stationary law.  It
enters only through `log(8M/ε²)`, and it is what decides the exponent:

* `log M = O(1)` (the *design intent* of Gaussian cooling — consecutive phases are meant to
  be `O(1)`-warm) ⟹ the `n`-exponent of `q` is **3**;
* a cold start, `log M = Θ(n)` ⟹ the `n`-exponent of `q` is **4**.

**This repository proves neither.**  A search of `Arlib/Convexity/GaussianCooling/` (all
files) finds *no* declaration — not even prose — relating `Arlib.IsWarm` to the cooling
schedule.  The nearest proved object is
`Arlib.GaussianCooling.coolRatio_le_exp`
(`Arlib/Convexity/GaussianCooling/PhaseVar.lean:323`), a *pointwise density-ratio* bound
`coolRatio ≤ exp(R²/(2σᵢ²))` — not an `Arlib.IsWarm` statement, and its constant is **not**
`O(1)` (in the regime `σᵢ² ≍ R²/n` it is `e^{Θ(n)}`).  The `√e`-per-phase warmness of
Cousins–Vempala §4.2 appears only as a docstring remark at
`Arlib/MarkovChains/Continuous/Warmness.lean:150`.  So `M` stays a binder here, and the
exponent `3` is **conditional on `log M = O(1)`**, which is assumed and not proved.

## A regime warning about `hfloor` (a finding, not a theorem)

At `δ = σ/8` the floor `hfloor : 1 ≤ 20·e^{−(2Rδ+δ²)/(2σ²)}·(1−1/n)ⁿ·θ` with `θ ≤ 1`
(forced, since `ell ≤ 1`) and `(1−1/n)ⁿ < 1/e` needs the acceptance factor to be `≳ e/20`,
i.e. `R/(8σ) + 1/128 ≲ 2`, i.e. `R = O(σ)`.  The Cousins–Vempala regime is `R ≍ σ√n`, where
`δ = σ/8` therefore **cannot** satisfy `hfloor`; there one is pushed back to `δ ≍ σ/√n` and
`q` degrades by a further factor `n`.  The `n³` price below lives in the `R = O(σ)` regime —
which is exactly the regime of the repository's own witness
(`Arlib.MarkovChains.exists_conductance_metropolisGaussian_sharp_witness`: `R = 1/2`,
`σ = 8`).  All of this is carried as *binders*, so nothing below is unsound; but the reader
must not read `n³` as unconditional.
-/

namespace Ttc.CoolCost

open MeasureTheory ProbabilityTheory Arlib.MarkovChains

/-! ## Section 1 — the composed conductance floor -/

/-- **The conductance floor of the Metropolis–Gaussian walk at step `δ = σ/8`.**

`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge` concludes
`δ·log 2/(640·σ·n) ≤ Φ`; at `δ = σ/8` — the largest step its `hδσ : δ ≤ σ/8` allows — the
`σ` cancels and this is what is left.  A plain arithmetic `def`; the lemma that ties it to
the conductance is `Ttc.CoolCost.coolPhi_le_conductance`. -/
noncomputable def coolPhi (n : ℕ) : ℝ := Real.log 2 / (5120 * (n : ℝ))

/-- `coolPhi` is positive at every `n ≥ 1`. -/
theorem coolPhi_pos {n : ℕ} (hn : 1 ≤ n) : 0 < coolPhi n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have := Real.log_two_gt_d9
  unfold coolPhi
  apply div_pos (by linarith)
  linarith

/-- `coolPhi ≤ 1` at every `n ≥ 1` — needed by every mixing theorem downstream. -/
theorem coolPhi_le_one {n : ℕ} (hn : 1 ≤ n) : coolPhi n ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  unfold coolPhi
  rw [div_le_one (by linarith)]
  linarith

/-- **`δ = σ/8` turns the sharp bound's constant into `coolPhi`.**  Pure algebra; `σ`
cancels, which is why the price is the same at every phase temperature. -/
theorem sharp_const_eq_coolPhi {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    σ / 8 * Real.log 2 / (640 * σ * (n : ℝ)) = coolPhi n := by
  unfold coolPhi
  rcases eq_or_ne ((n : ℝ)) 0 with h | h
  · simp [h]
  · field_simp
    ring

/-! ## Section 2 — the step count, and its `n²` bound -/

/-- **THE NUMBER OF LAZY METROPOLIS–GAUSSIAN TRANSITIONS PER DRAW.**

`⌈4·lsThreshold M Φ ε⌉₊ + 1` at `Φ = Ttc.CoolCost.coolPhi n`, i.e. the deadline of
`Arlib.MarkovChains.tvLe_iterate_lazy_of_exceptional` rounded up.  The factor `4` is exactly
what laziness costs (`Arlib.MarkovChains.lsThreshold_half`); the trailing `+ 1` is house
style (`Ttc.CVCost.cvRuns`, `Ttc.SamplerCost.stepsPrice`) and buys positivity at every
parameter.

A plain arithmetic `def`: its name asserts nothing.
`Ttc.CoolCost.coolDraw_tvLe` is the lemma that makes it a deadline. -/
noncomputable def coolDrawSteps (n : ℕ) (M epsDraw : ℝ) : ℕ :=
  ⌈4 * lsThreshold M (coolPhi n) epsDraw⌉₊ + 1

/-- The step count is positive at every parameter. -/
theorem coolDrawSteps_pos (n : ℕ) (M epsDraw : ℝ) : 0 < coolDrawSteps n M epsDraw :=
  Nat.succ_pos _

/-- **The deadline really is met by the count** — `Nat.le_ceil`, unconditionally. -/
theorem le_coolDrawSteps (n : ℕ) (M epsDraw : ℝ) :
    4 * lsThreshold M (coolPhi n) epsDraw ≤ (coolDrawSteps n M epsDraw : ℝ) := by
  unfold coolDrawSteps
  push_cast
  linarith [Nat.le_ceil (4 * lsThreshold M (coolPhi n) epsDraw)]

/-- **`log(8M/ε²) ≥ 2`** whenever `1 ≤ M` and `0 < ε ≤ 1`.  Used twice below to absorb
additive constants; `log 8 = 3·log 2 ≥ 2.079`. -/
theorem two_le_log_deadline {M epsDraw : ℝ} (hM : 1 ≤ M) (heps0 : 0 < epsDraw)
    (heps1 : epsDraw ≤ 1) : 2 ≤ Real.log (8 * M / epsDraw ^ 2) := by
  have hlog := Real.log_two_gt_d9
  have h8 : (8 : ℝ) ≤ 8 * M / epsDraw ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hstep : Real.log 8 ≤ Real.log (8 * M / epsDraw ^ 2) :=
    Real.log_le_log (by norm_num) h8
  have h8eq : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  rw [h8eq] at hstep
  linarith

/-- **The arithmetic heart: `4/Φ² ≤ 2²⁸·n²`.**

`Φ = log 2/(5120·n)`, so `2²⁸·n²·Φ² = 2²⁸·(log 2)²/5120² = 10.24·(log 2)²`, and
`log 2 ≥ 5/8` gives `(log 2)² ≥ 25/64`, hence `10.24·(log 2)² ≥ 4`.  (The constant `2²⁸` is
not slack: `4·5120² = 2²²·25` and `2²²·25/(25/64) = 2²⁸` exactly.) -/
theorem four_le_pow_mul_coolPhi_sq {n : ℕ} (hn : 1 ≤ n) :
    (4 : ℝ) ≤ 2 ^ 28 * (n : ℝ) ^ 2 * coolPhi n ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hne : ((n : ℝ)) ≠ 0 := by linarith
  have hrw : 2 ^ 28 * (n : ℝ) ^ 2 * coolPhi n ^ 2 = 2 ^ 28 * Real.log 2 ^ 2 / 5120 ^ 2 := by
    unfold coolPhi
    field_simp
  rw [hrw]
  nlinarith [Real.log_two_gt_d9]

/-- **The deadline is `O(n²·log(8M/ε²))`, with the constant explicit.**

`4·lsThreshold M (coolPhi n) ε ≤ 2²⁸·n²·log(8M/ε²)`.  Every hypothesis is visible; `M` in
particular is *not* bounded here (see the module docstring, § *Warmness*). -/
theorem four_lsThreshold_le {n : ℕ} {M epsDraw : ℝ} (hn : 1 ≤ n) (hM : 1 ≤ M)
    (heps0 : 0 < epsDraw) (heps1 : epsDraw ≤ 1) :
    4 * lsThreshold M (coolPhi n) epsDraw
      ≤ 2 ^ 28 * (n : ℝ) ^ 2 * Real.log (8 * M / epsDraw ^ 2) := by
  have hA : 2 ≤ Real.log (8 * M / epsDraw ^ 2) := two_le_log_deadline hM heps0 heps1
  have hkey : (4 : ℝ) ≤ 2 ^ 28 * (n : ℝ) ^ 2 * coolPhi n ^ 2 := four_le_pow_mul_coolPhi_sq hn
  have hphi : 0 < coolPhi n := coolPhi_pos hn
  have hphi2 : 0 < coolPhi n ^ 2 := by positivity
  rw [lsThreshold, ← mul_div_assoc, div_le_iff₀ hphi2]
  nlinarith [hkey, hA, hphi2]

/-- **The step count, bounded explicitly.**  `⌈x⌉₊ + 1 ≤ x + 2`. -/
theorem coolDrawSteps_le {n : ℕ} {M epsDraw : ℝ} (hn : 1 ≤ n) (hM : 1 ≤ M)
    (heps0 : 0 < epsDraw) (heps1 : epsDraw ≤ 1) :
    (coolDrawSteps n M epsDraw : ℝ)
      ≤ 2 ^ 28 * (n : ℝ) ^ 2 * Real.log (8 * M / epsDraw ^ 2) + 2 := by
  have hA : 2 ≤ Real.log (8 * M / epsDraw ^ 2) := two_le_log_deadline hM heps0 heps1
  have hphi : 0 < coolPhi n := coolPhi_pos hn
  have hnn : (0 : ℝ) ≤ 4 * lsThreshold M (coolPhi n) epsDraw := by
    rw [lsThreshold]
    have : (0 : ℝ) ≤ Real.log (8 * M / epsDraw ^ 2) := by linarith
    positivity
  have hc := Nat.ceil_lt_add_one hnn
  have := four_lsThreshold_le hn hM heps0 heps1
  unfold coolDrawSteps
  push_cast
  linarith

/-! ## Section 3 — the per-step charge and the price

The charge is carried as an **opaque parameter `w : ℕ`** through
`Ttc.CoolCost.coolDrawPrice`, so that the exponent below is a statement about the *step
count* and nothing else.  `Ttc.CoolCost.coolStepOpCharge` is the natural instantiation and
is a **modelling definition, not a theorem** — see its docstring. -/

/-- **The arithmetic charge of one lazy Metropolis–Gaussian transition, as a MODELLING
DEFINITION.**

`⌈n·rfac⌉₊`, mirroring `Ttc.SamplerCost.stepOpCharge` verbatim.  One transition draws a
point of `B(x, δ)` (`n` coordinates), evaluates the Gaussian weight `e^{−‖y‖²/(2σ²)}` (`n`
multiply-adds), and tests `y ∈ K`, which for a body presented by `rfac` facets is `rfac`
inner products of `n` terms each — the `O(n·rfac)` that dominates.  The lazy coin flip
(`Arlib.MarkovChains.lazy`) is `O(1)` and is absorbed here.

**This is not a theorem and its name does not claim one.**  No executable
Metropolis–Gaussian step exists in this repository, so nothing measures it; it is the cost
model, stated openly so that a reader can reject it (`CLAUDE.md` §11).  Every result below
that mentions it is also available with an arbitrary `w : ℕ` in its place. -/
noncomputable def coolStepOpCharge (n : ℕ) (rfac : ℝ) : ℕ := ⌈(n : ℝ) * rfac⌉₊

/-- **THE PRICE OF ONE DRAW FROM A COOLED GAUSSIAN PHASE**, in units of `w`, the charge of
one transition.

`(steps + 2)·w`: the transitions themselves, plus two extra units paying for the
initial-point setup and the final coordinate rounding, exactly as
`Ttc.SamplerCost.drawOpCharge` does for hit-and-run.

A plain arithmetic `def`.  `Ttc.CoolCost.coolDraw_tvLe` — which shows the chain really is
within `epsDraw` in total variation after `coolDrawSteps` transitions — is what makes it a
*price*. -/
noncomputable def coolDrawPrice (n : ℕ) (M epsDraw : ℝ) (w : ℕ) : ℕ :=
  (coolDrawSteps n M epsDraw + 2) * w

/-- The price is positive whenever the per-step charge is. -/
theorem coolDrawPrice_pos {w : ℕ} (n : ℕ) (M epsDraw : ℝ) (hw : 0 < w) :
    0 < coolDrawPrice n M epsDraw w :=
  Nat.mul_pos (by omega) hw

/-- The price, unfolded: it **is** `(steps + 2)·w`, and nothing else. -/
theorem coolDrawPrice_eq (n : ℕ) (M epsDraw : ℝ) (w : ℕ) :
    coolDrawPrice n M epsDraw w = (coolDrawSteps n M epsDraw + 2) * w := rfl

/-- **THE PRICE, BOUNDED — `2²⁹·n²·log(8M/ε²)·w`.**  The additive `+ 4` from the two
roundings and the two setup units is absorbed into the doubling of `2²⁸`, using
`log(8M/ε²) ≥ 2` and `n ≥ 1` (so `2²⁸·n²·log(8M/ε²) ≥ 2²⁹ ≥ 4`). -/
theorem coolDrawPrice_le {n : ℕ} {M epsDraw : ℝ} (w : ℕ) (hn : 1 ≤ n) (hM : 1 ≤ M)
    (heps0 : 0 < epsDraw) (heps1 : epsDraw ≤ 1) :
    (coolDrawPrice n M epsDraw w : ℝ)
      ≤ 2 ^ 29 * (n : ℝ) ^ 2 * Real.log (8 * M / epsDraw ^ 2) * (w : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hA : 2 ≤ Real.log (8 * M / epsDraw ^ 2) := two_le_log_deadline hM heps0 heps1
  have hs := coolDrawSteps_le hn hM heps0 heps1
  have hw0 : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg _
  have habs : (coolDrawSteps n M epsDraw : ℝ) + 2
      ≤ 2 ^ 29 * (n : ℝ) ^ 2 * Real.log (8 * M / epsDraw ^ 2) := by
    nlinarith [hs, hA, hn1, sq_nonneg ((n : ℝ) - 1)]
  unfold coolDrawPrice
  push_cast
  exact mul_le_mul_of_nonneg_right habs hw0

/-- **The modelled per-step charge is at most `n·(rfac + 1)`.**  `⌈n·rfac⌉₊ ≤ n·rfac + 1`
and `1 ≤ n`. -/
theorem coolStepOpCharge_le {n : ℕ} {rfac : ℝ} (hn : 1 ≤ n) (hr : 0 ≤ rfac) :
    (coolStepOpCharge n rfac : ℝ) ≤ (n : ℝ) * (rfac + 1) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (n : ℝ) * rfac)
  unfold coolStepOpCharge
  nlinarith [hc, hn1]

/-- **THE EXPONENT: `q ≤ Cq·n³` with `Cq = 2²⁹·(rfac + 1)·log(8M/ε²)`.**

This is the **derivation form**: the exponent `3` and the constant, as they fall out.
`Ttc.CoolCost.coolDrawPrice_le_bridge` is the same bound re-associated into the capstone's
exact `hq : (q : ℝ) ≤ Cq · (n : ℝ) ^ kq · qFac` shape (`Exec/TheoremPoly`, deleted) —
quote *that* one when composing.  Either way `kq = 3`, hence `kv = kq + 1 = 4`.

**The `n`-exponent is `3` only because `Cq` is `n`-free, and `Cq` is `n`-free only if
`log M` is.**  Nothing in this repository bounds `M`; see the module docstring,
§ *Warmness*.  Under a cold start `log M = Θ(n)` the honest reading is `q = Θ(n⁴·rfac)`. -/
theorem coolDrawPrice_le_cubic {n : ℕ} {M epsDraw rfac : ℝ} (hn : 1 ≤ n) (hM : 1 ≤ M)
    (heps0 : 0 < epsDraw) (heps1 : epsDraw ≤ 1) (hr : 0 ≤ rfac) :
    (coolDrawPrice n M epsDraw (coolStepOpCharge n rfac) : ℝ)
      ≤ 2 ^ 29 * (rfac + 1) * Real.log (8 * M / epsDraw ^ 2) * (n : ℝ) ^ 3 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hA : 2 ≤ Real.log (8 * M / epsDraw ^ 2) := two_le_log_deadline hM heps0 heps1
  have h1 := coolDrawPrice_le (coolStepOpCharge n rfac) hn hM heps0 heps1
  have h2 := coolStepOpCharge_le hn hr
  refine h1.trans ?_
  have hfac : (0 : ℝ) ≤ 2 ^ 29 * (n : ℝ) ^ 2 * Real.log (8 * M / epsDraw ^ 2) := by
    have : (0 : ℝ) ≤ Real.log (8 * M / epsDraw ^ 2) := by linarith
    positivity
  refine (mul_le_mul_of_nonneg_left h2 hfac).trans (le_of_eq ?_)
  ring

/-! ## Section 4 — what makes the number a *price*: the mixing statement

`Ttc.SamplerCost.samplePrice` is a price because `Ttc.SamplerCost.drawWork_le_samplePrice`
exists.  The analogue here is `Ttc.CoolCost.coolDraw_tvLe`: after `coolDrawSteps` lazy
Metropolis–Gaussian transitions the law really is within `epsDraw` of the phase's
stationary measure.  Every open input is a **binder** — `hiso` above all. -/

/-- **The stationary law of a cooling phase**: the Gaussian `∝ e^{−‖x‖²/(2σ²)}` restricted to
`K` and normalised.  This is literally the measure
`Arlib.MarkovChains.isReversible_metropolisGaussian` is stated at; it is an abbreviation for
readability and asserts nothing on its own.  `Ttc.CoolCost.invariant_coolPi` is the lemma
that says the walk preserves it. -/
@[reducible] noncomputable def coolPi (n : ℕ) (σ : ℝ) (K : Set (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
    (gaussianWeight (σ ^ 2))) K

/-- **`coolPi` is invariant for the walk** — `Arlib.MarkovChains.invariant_metropolisGaussian`,
so the name `coolPi` is not standing in for an unproved identification. -/
theorem invariant_coolPi {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (σ δ : ℝ) : Kernel.Invariant (metropolisGaussian K δ (σ ^ 2)) (coolPi n σ K) :=
  invariant_metropolisGaussian hK δ (σ ^ 2)

/-- **The composed conductance floor, `hiso` visible.**

`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge` at `δ = σ/8` — *the largest
step its own `hδσ : δ ≤ σ/8` permits*.  `Ttc.CoolCost.sharp_const_eq_coolPhi` is the one
line of algebra that turns its constant into `coolPhi n`; the `σ` cancels.

⚠ `hiso` is Cousins–Vempala's `thm:iso` and is **not proved in this repository**.  `hell`
and `hfloor` are the local-conductance floor and are a genuine restriction on `K` — at
`δ = σ/8` they force `R = O(σ)` (module docstring, § *A regime warning*). -/
theorem coolPhi_le_conductance {n : ℕ} (hn : 2 ≤ n) {σ R θ : ℝ} (hσ : 0 < σ) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K (σ / 8) x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * (σ / 8) + (σ / 8) ^ 2) / (2 * σ ^ 2))
      * (1 - 1 / (n : ℝ)) ^ n * θ)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      Arlib.IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        σ / 8 / Real.sqrt n * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (σ / 8 / Real.sqrt n * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ Arlib.densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) →
      σ / 8 / Real.sqrt n * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x) :
    ENNReal.ofReal (coolPhi n)
      ≤ conductance (metropolisGaussian K (σ / 8) (σ ^ 2)) (coolPi n σ K) := by
  rw [← sharp_const_eq_coolPhi hσ n]
  exact conductance_metropolisGaussian_sharp_ge hn hσ (by positivity) le_rfl hR hK hKc hKR
    hKtop hK0 hell hfloor hiso

/-- **THE PRICE IS A PRICE: after `coolDrawSteps` lazy transitions the draw is `epsDraw`-good.**

`Arlib.MarkovChains.tvLe_iterate_lazy_of_exceptional` at the exceptional set `S = ∅` (so its
`hdom` is plain `M`-warmness), at `Φ = Ttc.CoolCost.coolPhi n`, and at
`m = Ttc.CoolCost.coolDrawSteps n M epsDraw`, whose defining `Nat.ceil` clears the deadline
by `Ttc.CoolCost.le_coolDrawSteps`.

Reversibility is `Arlib.MarkovChains.isReversible_metropolisGaussian`; laziness supplies the
spectral hypothesis (`Arlib.MarkovChains.hasNonnegSpectrum_lazy`), which is *not* removable —
see `HitAndRunMixing.lean`, `§ What is assumed`, item (A).

**Residual binders**, all visible: `hcond` (the conductance floor — supplied by
`Ttc.CoolCost.coolPhi_le_conductance`, which is conditional on `hiso`), `hwarm` (the
warmness of the start, with `M` unbounded here), `hsmall` (a measurable set of `coolPi`-mass
in `(0, 1/2]`), and `hpi` (that `coolPi` really is a probability measure, i.e. that the
Gaussian mass of `K` is neither `0` nor `∞`). -/
theorem coolDraw_tvLe {n : ℕ} {σ M epsDraw : ℝ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {mu : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu]
    (hK : MeasurableSet K) (hpi : IsProbabilityMeasure (coolPi n σ K))
    (hsmall : (SmallSets (coolPi n σ K) (1 / 2)).Nonempty)
    (hn : 1 ≤ n) (hM : 1 ≤ M) (heps0 : 0 < epsDraw) (heps1 : epsDraw ≤ 1)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu (coolPi n σ K))
    (hcond : ENNReal.ofReal (coolPhi n)
      ≤ conductance (metropolisGaussian K (σ / 8) (σ ^ 2)) (coolPi n σ K)) :
    Arlib.TVLe
      (iterate (lazy (metropolisGaussian K (σ / 8) (σ ^ 2))) mu (coolDrawSteps n M epsDraw))
      (coolPi n σ K) (ENNReal.ofReal epsDraw) := by
  haveI := hpi
  refine tvLe_iterate_lazy_of_exceptional
    (isReversible_metropolisGaussian hK (σ / 8) (σ ^ 2)) hsmall hM (coolPhi_pos hn)
    (coolPhi_le_one hn) heps0 heps1 MeasurableSet.empty (by simp) ?_ hcond
    (le_coolDrawSteps n M epsDraw)
  intro A hA
  rw [Set.sdiff_empty]
  exact hwarm A hA

/-- **THE BRIDGE LEMMA, IN THE CAPSTONE'S EXACT SHAPE `Cq · n³ · qFac`.**

`Ttc.cvVolumeOpsPrice_le_poly` / `Ttc.PolyComplexity.ttcComplexity_le_poly` consume
`hq : (q : ℝ) ≤ Cq * (n : ℝ) ^ kq * qFac` — **one** parenthesised `n`-free trailing factor.
This is `Ttc.CoolCost.coolDrawPrice_le_cubic` re-associated into that term, so the caller
closes the seam with `exact` and no `ring_nf`:

* `Cq  = 2²⁹`  (a numeral: `2²⁸` from `4/Φ²` at `Φ = log 2/(5120·n)`, doubled to absorb the
  two roundings and the ceiling);
* `kq  = 3`    (`n²` from `1/Φ²`, `n` from the per-step charge `⌈n·rfac⌉₊`);
* `qFac = (rfac + 1)·log(8·M/ε_draw²)`, the `n`-free factor: the facet count of the body and
  the mixing deadline's logarithm.

`kq = 3` gives `kv = kq + 1 = 4` on the volume side, matching the sampler side's `n⁴`.

⚠ **`qFac` is `n`-free only if `M` is.**  `M` is a *binder* — the warmness of the phase
start — and nothing in this repository bounds it (module docstring, § *Warmness*).  Under a
cold start `log M = Θ(n)` this is an `n⁴` bound on `q`, not `n³`.

**No `1 ≤ n` hypothesis**, deliberately: `Ttc.isBigO_ttc_runtime_cv`'s `hq` is quantified
over *all* `N : ℕ`, including `N = 0`, where both sides are `0` (the per-step charge
`⌈0·rfac⌉₊` is `0`).  So this lemma is usable at that `∀ N` slot verbatim.
`Ttc.CoolCost.coolQFac_nonneg` supplies the accompanying `hqFac`, and `hCq` is `0 ≤ 2²⁹`. -/
theorem coolDrawPrice_le_bridge {n : ℕ} {M epsDraw rfac : ℝ} (hM : 1 ≤ M)
    (heps0 : 0 < epsDraw) (heps1 : epsDraw ≤ 1) (hr : 0 ≤ rfac) :
    (coolDrawPrice n M epsDraw (coolStepOpCharge n rfac) : ℝ)
      ≤ 2 ^ 29 * (n : ℝ) ^ 3 * ((rfac + 1) * Real.log (8 * M / epsDraw ^ 2)) := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    simp [coolDrawPrice, coolStepOpCharge]
  · exact (coolDrawPrice_le_cubic hn hM heps0 heps1 hr).trans (le_of_eq (by ring))

/-- **`qFac ≥ 0`** — the `hqFac` side condition of `Ttc.isBigO_ttc_runtime_cv`, discharged. -/
theorem coolQFac_nonneg {M epsDraw rfac : ℝ} (hM : 1 ≤ M) (heps0 : 0 < epsDraw)
    (heps1 : epsDraw ≤ 1) (hr : 0 ≤ rfac) :
    (0 : ℝ) ≤ (rfac + 1) * Real.log (8 * M / epsDraw ^ 2) := by
  have := two_le_log_deadline hM heps0 heps1
  nlinarith

/-! ## Section 5 — the volume-side composition: `kv = 4`

`Ttc.CVCost.cvVolumeOpsPrice_le` (`Ttc/Exec/VolumePriceCV.lean:550`) reads
`cvVolumeOpsPrice n L κ c p q ≤ q · (2¹³·n·L⁴·log(1/p)/κ³)`; `Ttc.CoolCost.coolDrawPrice_le_cubic`
is already in the shape its `q` slot wants, so the composition is one `trans`.  The `n`
exponent is `3 + 1 = 4`. -/

/-- **THE `n⁴` STATEMENT — the CV volume oracle's operation count at this file's `q`.**

`Ttc.CVCost.cvVolumeOpsPrice` at `q = Ttc.CoolCost.coolDrawPrice … (coolStepOpCharge n rfac)`:

```
cvVolumeOpsPrice ≤ 2⁴²·(rfac+1)·log(8M/ε_draw²) · n⁴ · (L⁴·log(1/p)/κ³)
```

`2⁴² = 2¹³·2²⁹`.  This is `Ttc.cvVolumeOpsPrice_le_poly`'s conclusion at `kq = 3`,
`Cq = 2²⁹·(rfac+1)·log(8M/ε_draw²)`, `kv = 4` — reproved here directly from
`Ttc.CVCost.cvVolumeOpsPrice_le` so that this file does not depend on
`Ttc/Exec/TheoremPoly.lean` (deleted 2026-08-19).

⚠ The exponent `4` is `4` **only because `log M` is treated as `n`-free**, and because
`hiso`, `hell`/`hfloor` are binders upstream.  Read the module docstring before quoting this. -/
theorem cvVolumeOpsPrice_le_cool {n : ℕ} {L κ c p M epsDraw rfac : ℝ}
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hc1 : 1 ≤ c)
    (hc : c ≤ 1 + 2 / (n : ℝ)) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2)
    (hM : 1 ≤ M) (heps0 : 0 < epsDraw) (heps1 : epsDraw ≤ 1) (hr : 0 ≤ rfac) :
    (CVCost.cvVolumeOpsPrice n L κ c p
        (coolDrawPrice n M epsDraw (coolStepOpCharge n rfac)) : ℝ)
      ≤ 2 ^ 42 * (rfac + 1) * Real.log (8 * M / epsDraw ^ 2)
          * (n : ℝ) ^ 4 * (L ^ 4 * Real.log (1 / p) / κ ^ 3) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2le : (2 : ℝ) ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have hlogp : (0 : ℝ) ≤ Real.log (1 / p) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2le
    have := Real.log_two_gt_d9
    linarith
  have hW : (0 : ℝ) ≤ 2 ^ 13 * (n : ℝ) * L ^ 4 * Real.log (1 / p) / κ ^ 3 := by
    refine div_nonneg ?_ (by positivity)
    exact mul_nonneg (by positivity) hlogp
  refine (CVCost.cvVolumeOpsPrice_le hn hL hκ0 hκ1 hc1 hc hp0 hp1).trans ?_
  refine (mul_le_mul_of_nonneg_right
    (coolDrawPrice_le_cubic hn hM heps0 heps1 hr) hW).trans (le_of_eq ?_)
  field_simp

/-! ## Section 6 — the asymptotic form, with the regime hypotheses visible

The warmness bound `Mbound` and the facet bound `rbound` are **explicit uniform binders**,
not constants hidden inside the `O(·)`.  That is precisely the `log M = O(1)` assumption the
module docstring flags as unproved: it is what makes the exponent `3` rather than `4`. -/

/-- **The `IsBigO` form — `O(n³)` operations per draw, in the bounded-warmness regime.**

`Mbound` is the assumption.  Instantiating it with a *sequence* `M n = e^{Θ(n)}` (a cold
start) is not possible here — that is the point of making it a uniform bound — and in that
regime the correct exponent is `4`, not `3`. -/
theorem isBigO_coolDrawPrice_cubic {M rfac : ℕ → ℝ} {epsDraw Mbound rbound : ℝ}
    (heps0 : 0 < epsDraw) (heps1 : epsDraw ≤ 1)
    (hM1 : ∀ n, 1 ≤ M n) (hMb : ∀ n, M n ≤ Mbound)
    (hr0 : ∀ n, 0 ≤ rfac n) (hrb : ∀ n, rfac n ≤ rbound) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (coolDrawPrice n (M n) epsDraw (coolStepOpCharge n (rfac n)) : ℝ))
      (fun n : ℕ => (n : ℝ) ^ 3) := by
  have hMb1 : (1 : ℝ) ≤ Mbound := le_trans (hM1 0) (hMb 0)
  have hrb0 : (0 : ℝ) ≤ rbound := le_trans (hr0 0) (hrb 0)
  refine Asymptotics.IsBigO.of_bound
    (2 ^ 29 * (rbound + 1) * Real.log (8 * Mbound / epsDraw ^ 2)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hMn0 : (0 : ℝ) < 8 * M n / epsDraw ^ 2 :=
    div_pos (by linarith [hM1 n]) (by positivity)
  have hlogmono : Real.log (8 * M n / epsDraw ^ 2) ≤ Real.log (8 * Mbound / epsDraw ^ 2) :=
    Real.log_le_log hMn0 (by have h := hMb n; gcongr)
  have hA : 2 ≤ Real.log (8 * M n / epsDraw ^ 2) :=
    two_le_log_deadline (hM1 n) heps0 heps1
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)]
  refine (coolDrawPrice_le_cubic hn (hM1 n) heps0 heps1 (hr0 n)).trans ?_
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hnn
  have h1 : 2 ^ 29 * (rfac n + 1) * Real.log (8 * M n / epsDraw ^ 2)
      ≤ 2 ^ 29 * (rbound + 1) * Real.log (8 * M n / epsDraw ^ 2) := by
    have := hrb n
    nlinarith [hA]
  nlinarith [h1, hlogmono, hrb0, hA]

/-! ## Section 7 — non-vacuity (`CLAUDE.md` §11)

Two witnesses.  Neither exhibits `hiso`, which is not provable here; the second says so
in its own statement. -/

/-- **Non-vacuity of the arithmetic bundle.**  The hypotheses of
`Ttc.CoolCost.coolDrawPrice_le_cubic` are jointly satisfiable, and at the witness the priced
quantity is **strictly positive** — so the bound is not the trivial `0 ≤ _`.

Witness: `n = 2`, `M = 1` (a stationary start), `ε_draw = 1`, `rfac = 1`. -/
theorem exists_coolDrawPrice_le_cubic_witness :
    ∃ (n : ℕ) (M epsDraw rfac : ℝ),
      1 ≤ n ∧ 1 ≤ M ∧ 0 < epsDraw ∧ epsDraw ≤ 1 ∧ 0 ≤ rfac ∧
      0 < coolDrawPrice n M epsDraw (coolStepOpCharge n rfac) ∧
      (coolDrawPrice n M epsDraw (coolStepOpCharge n rfac) : ℝ)
        ≤ 2 ^ 29 * (rfac + 1) * Real.log (8 * M / epsDraw ^ 2) * (n : ℝ) ^ 3 := by
  refine ⟨2, 1, 1, 1, by norm_num, le_refl _, one_pos, le_refl _, zero_le_one, ?_,
    coolDrawPrice_le_cubic (by norm_num) le_rfl one_pos le_rfl zero_le_one⟩
  refine coolDrawPrice_pos 2 1 1 ?_
  rw [coolStepOpCharge]
  exact Nat.ceil_pos.2 (by norm_num)

/-- **The composed volume-side count is positive**, so
`Ttc.CoolCost.cvVolumeOpsPrice_le_cool` is not a bound on `0`.  Both factors of
`Ttc.CVCost.cvVolumeOpsPrice` are positive: the per-sample charge by
`Ttc.CoolCost.coolDrawPrice_pos` (at a body with at least one facet), the sample count by
`Ttc.CVCost.cvVolumeSamplePrice_pos`. -/
theorem cvVolumeOpsPrice_cool_pos {n : ℕ} {L κ M epsDraw rfac : ℝ} (c p : ℝ) (hn : 1 ≤ n)
    (hL : 1 ≤ L) (hκ0 : 0 < κ) (hr : 0 < rfac) :
    0 < CVCost.cvVolumeOpsPrice n L κ c p
      (coolDrawPrice n M epsDraw (coolStepOpCharge n rfac)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine Nat.mul_pos (coolDrawPrice_pos n M epsDraw ?_) (CVCost.cvVolumeSamplePrice_pos c p hL hκ0)
  rw [coolStepOpCharge]
  exact Nat.ceil_pos.2 (by positivity)

/-- **Non-vacuity of `Ttc.CoolCost.coolPhi_le_conductance`, EXCEPT `hiso`.**

Every hypothesis of that theorem other than `hiso` is jointly satisfiable at `n = 2`,
`K = B(0, 1/2) ⊆ ℝ²`, `σ = 8` (so the step is `δ = σ/8 = 1`, the extreme allowed by the
sharp theorem's `hδσ`), `R = 1/2`, `θ = 1/4`; and the conclusion there is not the trivial
`0 ≤ _`, since `coolPhi 2 > 0`.  This is the same body, radius and floor as
`Arlib.MarkovChains.exists_conductance_metropolisGaussian_sharp_witness`, so the two are
directly comparable — and note that it is an `R = O(σ)` witness, the regime the module
docstring flags.

**What this does NOT certify.**  `hiso` is Cousins–Vempala's `thm:iso`, is a binder of
`Ttc.CoolCost.coolPhi_le_conductance`, and is **not exhibited here and not proved anywhere
in this repository**.  So this shows the theorem is not vacuous *for reasons of its
discharged hypotheses*; it does **not** show it has an unconditional instance, and it is
**not** evidence for any mixing-time or `O*(n³)` claim. -/
theorem exists_coolPhi_le_conductance_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))) (σ R θ : ℝ),
      0 < σ ∧ 0 ≤ R ∧ MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
      volume K ≠ ⊤ ∧ volume K ≠ 0 ∧
      (∀ x ∈ K, ENNReal.ofReal θ ≤ ell K (σ / 8) x) ∧
      1 ≤ 20 * Real.exp (-(2 * R * (σ / 8) + (σ / 8) ^ 2) / (2 * σ ^ 2))
        * (1 - 1 / ((2 : ℕ) : ℝ)) ^ (2 : ℕ) * θ ∧
      0 < coolPhi 2 := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 (1 / 2) with hKdef
  have hVpos : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hKvol : volume K ≠ 0 := (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hKtop : volume K ≠ ⊤ := measure_ball_lt_top.ne
  have hKR : ∀ x ∈ K, ‖x‖ ≤ 1 / 2 := by
    intro x hx
    rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx
    exact hx.le
  -- `ℓ ≡ 1/4` on `K`: `K ⊆ B(x,1)` for every `x ∈ K`, and `vol K = (1/4)·vol B(0,1)`.
  have hell : ∀ x ∈ K, ell K (1 : ℝ) x = ENNReal.ofReal (1 / 4) := by
    intro x hx
    have hxnorm : ‖x‖ < 1 / 2 := by
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx; exact hx
    have hsub : K ⊆ Metric.ball x 1 := by
      intro y hy
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hy
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
        _ < 1 := by linarith
    have hball : volume K
        = ENNReal.ofReal (1 / 4) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      rw [hKdef, Measure.addHaar_ball_of_pos volume 0 (by norm_num : (0:ℝ) < 1 / 2),
        finrank_euclideanSpace_fin]
      norm_num
    rw [ell_apply, Set.inter_eq_self_of_subset_right hsub, hball, volume_ball_eq x 1]
    exact ENNReal.mul_div_cancel_right hVpos hVtop
  have hexpge : (63 : ℝ) / 64
      ≤ Real.exp (-(2 * (1 / 2 : ℝ) * ((8 : ℝ) / 8) + ((8 : ℝ) / 8) ^ 2) / (2 * (8 : ℝ) ^ 2)) := by
    have h := Real.add_one_le_exp (-(1 : ℝ) / 64)
    have heq : -(2 * (1 / 2 : ℝ) * ((8 : ℝ) / 8) + ((8 : ℝ) / 8) ^ 2) / (2 * (8 : ℝ) ^ 2)
        = -(1 : ℝ) / 64 := by norm_num
    rw [heq]; linarith
  refine ⟨K, 8, 1 / 2, 1 / 4, by norm_num, by norm_num, measurableSet_ball, convex_ball _ _,
    hKR, hKtop, hKvol, ?_, ?_, coolPhi_pos (by norm_num)⟩
  · intro x hx
    rw [show (8 : ℝ) / 8 = 1 by norm_num, hell x hx]
  · have hcast : (1 - 1 / ((2 : ℕ) : ℝ)) ^ (2 : ℕ) = 1 / 4 := by norm_num
    rw [hcast]
    linarith

end Ttc.CoolCost

/-! ### Axiom audit (`CLAUDE.md` §4)

Every declaration of this file, in order.  The target profile is exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms Ttc.CoolCost.coolPhi_pos
#print axioms Ttc.CoolCost.coolPhi_le_one
#print axioms Ttc.CoolCost.sharp_const_eq_coolPhi
#print axioms Ttc.CoolCost.coolDrawSteps_pos
#print axioms Ttc.CoolCost.le_coolDrawSteps
#print axioms Ttc.CoolCost.two_le_log_deadline
#print axioms Ttc.CoolCost.four_le_pow_mul_coolPhi_sq
#print axioms Ttc.CoolCost.four_lsThreshold_le
#print axioms Ttc.CoolCost.coolDrawSteps_le
#print axioms Ttc.CoolCost.coolDrawPrice_le
#print axioms Ttc.CoolCost.coolDrawPrice_le_cubic
#print axioms Ttc.CoolCost.coolDrawPrice_le_bridge
#print axioms Ttc.CoolCost.coolQFac_nonneg
#print axioms Ttc.CoolCost.coolPhi_le_conductance
#print axioms Ttc.CoolCost.coolDraw_tvLe
#print axioms Ttc.CoolCost.cvVolumeOpsPrice_le_cool
#print axioms Ttc.CoolCost.isBigO_coolDrawPrice_cubic
#print axioms Ttc.CoolCost.exists_coolDrawPrice_le_cubic_witness
#print axioms Ttc.CoolCost.cvVolumeOpsPrice_cool_pos
#print axioms Ttc.CoolCost.exists_coolPhi_le_conductance_witness
#print axioms Ttc.CoolCost.coolDrawPrice_pos
#print axioms Ttc.CoolCost.coolDrawPrice_eq
#print axioms Ttc.CoolCost.coolStepOpCharge_le
#print axioms Ttc.CoolCost.invariant_coolPi

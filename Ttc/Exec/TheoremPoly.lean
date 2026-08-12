/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Theorem
import Ttc.Exec.PolyComplexity
import Ttc.Exec.VolumePriceCV
import Ttc.Witness.FullTwoCube

/-!
# `Exec/TheoremPoly`: `Ttc.ttc_volume_estimate` with the runtime side priced

> ## ⚠ NOTHING IN THIS FILE PROVES THAT `TTC` RUNS IN `O(m·n⁵)` — OR IN ANY TIME AT ALL ⚠
>
> Every runtime statement below is an **implication**.  It takes the two per-call oracle
> prices `cVol`, `cSample` as *given numbers* satisfying *given* polynomial hypotheses and
> concludes a polynomial bound on the **charged** cost.  It does **not** assert that any
> oracle achieves those prices.  Four separate reasons the antecedent is not discharged
> anywhere in this repository, and one that cannot be:
>
> 1. **The sampling price** `2⁶²·n⁴·rfac·(R²/γ²)·log(2R)` is
>    `Ttc.SamplerCost.samplePrice_le_quartic`, meaningful **only given**
>    `Ttc.HitAndRunTheorem11Input` (Lovász–Vempala Theorem 1.1) — an *assumed* structure,
>    inhabited nowhere, whose own proof would rest on `hLS` (Lovász–Simonovits 1993,
>    Corollary 1.5), also unproved here.
> 2. **A polynomial volume price** needs the Cousins–Vempala oracle, whose instantiation
>    `Ttc.VolumeAlgorithm.cousinsVempala` still carries the two unproved sampler
>    hypotheses `hphase_mean` and `hphase_var` (`Ttc/Volume/CVInstantiate.lean`).
> 3. **`q` is unbounded.**  `Ttc.CVCost.cvVolumeSamplePrice_le` bounds a **sample count**,
>    not an operation count.  The operation count `Ttc.CVCost.cvVolumeOpsPrice` carries a
>    per-sample charge `q` — the cost of producing ONE draw from the cooled Gaussian
>    `coolLaw` of a phase — which **is bounded nowhere in this repository**.  It is a
>    *different law* from the near-uniform law `cSample` prices, so `cSample` cannot stand
>    in for it.  §1 below therefore carries `q`'s exponent as an explicit hypothesis and
>    the volume-side exponent comes out as `kv = kq + 1`, never as `1`.
> 4. **The charged cost is an undercount.**  `Ttc.ttc`'s cost coordinate charges one unit
>    per oracle call and nothing else — it prices at zero the arithmetic inside a call, the
>    rejection rounds, and `alg:ttc`'s lines 32–42 `while` loops.
>
> **And the one that cannot be discharged by more work here — the ORACLE MISMATCH.**
> `Ttc.ttc`'s accuracy conjunct is proved for the **Monte Carlo** volume estimator and the
> **lazy ball walk** (`Ttc.algOracles` is a closed term over `Ttc.mcVol`), whose own prices
> are *exponential* in `n` (`Ttc/Exec/PriceList.lean`).  The polynomial prices assumed
> below are achievable only with the **Cousins–Vempala** oracle and the **hit-and-run**
> sampler.  Pricing them against the same run is coherent only because `cVol` and `cSample`
> are per-call **unit prices** while the call **counts** are oracle-independent (`m` volume
> calls, `≤ Θ+1` samples each) — and that is *all* it is.  **No theorem here says the run
> executes the CV / hit-and-run oracles**, and none may be read that way.  Changing
> `Ttc.ttc`'s oracle bundle would be a different theorem, and is deliberately not attempted:
> not one declaration below mentions `Ttc.algOracles`, `Ttc.mcVol` or `Ttc.ttcOracleBundle`.

## What this file adds to `Ttc.ttc_volume_estimate`

`Ttc.ttc_volume_estimate` (`Ttc/Model/Theorem.lean:60`) has runtime conjunct

```
cost ≤ m · (cVol + cSample·(Θ + 1))
```

with `cVol`, `cSample` opaque.  The theorems here keep the **accuracy conjunct literally
unchanged** — it is the same proposition, copied character for character — and replace the
runtime right-hand side by `m · n^K · (…)` at `K = max(kv, 4)`, the prices discharged at
their assumed upper bounds.  Nothing is weakened and nothing is added to the accuracy side.

| theorem | runtime exponent | what it is |
| --- | --- | --- |
| `Ttc.ttc_volume_estimate_poly` | `K`, any `K ≥ max(kv,4)` | the general form |
| `Ttc.ttc_volume_estimate_quartic` | `4` | **the TIGHT form**, when `kv ≤ 4` |
| `Ttc.ttc_volume_estimate_quintic` | `5` | the paper's `m·O(n⁵)`; **LOOSE by a factor `n`** whenever `kv ≤ 4` |
| `Ttc.ttc_volume_estimate_poly_cv` | `K` | the general form with `cVol` bounded by the CV price and `q`'s exponent visible |
| `Ttc.ttc_volume_estimate_quartic_cv` | `4` | the same at `K = 4`, i.e. under `kq ≤ 3` |
| `Ttc.isBigO_ttc_runtime_cv` | `O(N^K)` | the asymptotic form; `m`, `ε`, `δ`, `rfac`, `R/γ`, `L`, `κ`, `p`, `q` all visible hypotheses |

**Which one is the result.**  `n⁴` is what this development supports and `n⁵` is the weaker
statement the paper currently prints.  The sampling side is *already* `n⁴`
(`Ttc.SamplerCost.samplePrice_le_quartic`, itself one factor of `n` below the paper) and the
threshold factor is `n`-free, so the whole exponent is decided by the volume side.  Both
forms are proved side by side so that the relationship lives in the development, not in
prose.  **No lower bound on the cost is proved anywhere**, so "tight" here means *the least
exponent this argument delivers*, never *attained*.

## §1 — where `kv` comes from, and why it is not `1`

`Ttc.CVCost.cvVolumeSamplePrice_le` gives `2¹³·n·L⁴·log(1/p)/κ³` **samples** per volume
call.  `Ttc.CVCost.cvVolumeOpsPrice n L κ c p q = q · cvVolumeSamplePrice n L κ c p` is the
operation count, and `Ttc.cvVolumeOpsPrice_le_poly` below converts it into the `hcVol`
shape `Cv·n^kv·volFac`:

```
q ≤ Cq·n^kq·qFac  ⟹  cvVolumeOpsPrice n L κ c p q ≤ (2¹³·Cq)·n^(kq+1)·(qFac·L⁴·log(1/p)/κ³)
```

so

```
    kv = kq + 1                    (volume-side OPERATION exponent)
    K  = max(kv, 4) = max(kq+1, 4) (whole-algorithm exponent)
```

* the tight `n⁴` needs `kq ≤ 3` — **one draw from `coolLaw` must cost `O(n³)`**;
* the paper's `n⁵` needs only `kq ≤ 4`;
* under Cousins–Vempala's own `O*(n²)` per-sample mixing claim one would have `kq = 2`,
  hence `kv = 3` and still `K = 4` — the quartic form saturates at `kq = 3` and the
  sampling side takes over below that.  That claim is not proved here
  (`Ttc/Volume/CVTheorem11.lean` is declaration-only), which is exactly why `kq` stays a
  hypothesis.

`kq = 0` — "one draw costs `O(1)`" — would give `kv = 1` and is the assumption this file
refuses to make silently: it would assume away the open half of the CV cost.

The extra `n`-free factor `qFac` is carried so that a `q`-bound of the natural shape
`Cq·n^kq·(n-free stuff)` composes with `Ttc.cvVolumeOpsPrice_le_poly`; see that lemma's
docstring for the exact associativity a glue-free `exact` needs.

## §6 — non-vacuity

`Ttc.ttc_volume_estimate_poly_two_cube` inhabits the **whole** hypothesis bundle at once
(model side *and* price side) on the two-cube witness of `Ttc/Witness/TwoCube.lean`, and
proves the accuracy bound `1/2 ≤ Pr[…]` there — so the measure of the good event is
strictly positive and finite, and the `All[…]` conjunct is not a statement about the zero
measure.  `Ttc.one_le_ttcNumCubes` gives `1 ≤ m` **unconditionally**, so the runtime bound
is not the degenerate `cost ≤ 0`.

This is strictly more than `Ttc.PolyComplexity.ttcCost_le_poly` has: that theorem carries
`hterm : Ttc.ttcTerminates …` and could not be witnessed at `φ = ⊤` (its `hpos` fails,
`Ttc.PolyComplexity.volSol_tt_eq_zero`).  The route taken here goes through
`Ttc.ttc_volume_estimate`, which has **no** `hterm` binder — the absorption loops halt
`Ttc.ttc`-almost surely — and whose `hφ`/`hpos` the two-cube data discharges.

## What is NOT here

* `Ttc.lean` is **not** wired to this file; the root re-export is the caller's decision.
* No bound on `q`, on `Ttc.HitAndRunTheorem11Input`, or on Cousins–Vempala's
  `hphase_mean`/`hphase_var` — all three remain open, and any two of them alone would not
  suffice.
* No lower bound, hence no claim that any exponent here is attained.
-/

namespace Ttc

open MeasureTheory Set
open Ttc.Monadic

set_option maxRecDepth 100000

/-! ## §1 — the volume-side bridge: `cvVolumeOpsPrice` in the `hcVol` shape -/

/-- **The `q`-bridge: `kv = kq + 1`.**

`Ttc.CVCost.cvVolumeOpsPrice_le` gives `q · (2¹³·n·L⁴·log(1/p)/κ³)`.  Feeding it a bound
`q ≤ Cq·n^kq·qFac` on the **per-sample charge** produces exactly the shape
`Ttc.PolyComplexity.ttcComplexity_le_poly`'s `hcVol` wants,

```
(cVol : ℝ) ≤ Cv · n^kv · volFac    with   Cv = 2¹³·Cq,  kv = kq + 1,
                                          volFac = qFac · (L⁴·log(1/p)/κ³).
```

`qFac` is a free `n`-independent factor, carried so that a `q`-bound of the natural shape
`Cq·n^kq·(n-free stuff)` composes.  ⚠ To compose by `exact`, the supplier's bound must end
in **one** parenthesised `n`-free factor — literally `Cq * (n : ℝ) ^ kq * qFac`.  A
left-associated chain `((C * n^kq) * r) * log(1/ε)` is *not* that term for any
instantiation and needs one `mul_assoc`/`ring_nf` of glue.  `qFac` is **not** required to
be nonnegative here; downstream `0 ≤ volFac` is, and callers supply `0 ≤ qFac`.

⚠ **`hq` is an ASSUMPTION, and the open half of the Cousins–Vempala cost.**  `q` is the
charge for producing one draw from the cooled Gaussian `coolLaw` of a phase.  Nothing in
this repository bounds it: the only mixing input available,
`Ttc.HitAndRunTheorem11Input.at_steps`, is itself assumed and targets the *uniform* law,
not the cooled Gaussian (`Ttc/Exec/VolumePriceCV.lean`, module docstring).  In particular
`cSample` — which prices the near-uniform law — is **not** a bound for `q`.

The `+ 1` in `kq + 1` is the sample count's own linear factor of `n`, and it is why the
volume side's operation exponent can never be read off `Ttc.CVCost.cvVolumeSamplePrice_le`
alone.

No sign hypothesis on `Cq` is needed here (the step is `q·W ≤ (Cq·n^kq)·W` at `W ≥ 0`);
`0 ≤ Cv = 2¹³·Cq` *is* needed downstream, and callers supply it there. -/
theorem cvVolumeOpsPrice_le_poly {n : ℕ} {L κ c p : ℝ} {q kq : ℕ} {Cq qFac : ℝ}
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hc1 : 1 ≤ c) (hc : c ≤ 1 + 2 / (n : ℝ)) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2)
    (hq : (q : ℝ) ≤ Cq * (n : ℝ) ^ kq * qFac) :
    (CVCost.cvVolumeOpsPrice n L κ c p q : ℝ)
      ≤ 2 ^ 13 * Cq * (n : ℝ) ^ (kq + 1) * (qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2le : (2 : ℝ) ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have hlog : (0 : ℝ) ≤ Real.log (1 / p) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2le
    have := Real.log_two_gt_d9
    linarith
  have hW : (0 : ℝ) ≤ 2 ^ 13 * (n : ℝ) * L ^ 4 * Real.log (1 / p) / κ ^ 3 := by
    refine div_nonneg ?_ (by positivity)
    have h0 : (0 : ℝ) ≤ 2 ^ 13 * (n : ℝ) * L ^ 4 := by positivity
    exact mul_nonneg h0 hlog
  refine (CVCost.cvVolumeOpsPrice_le (q := q) hn hL hκ0 hκ1 hc1 hc hp0 hp1).trans ?_
  refine (mul_le_mul_of_nonneg_right hq hW).trans ?_
  rw [pow_succ]
  apply le_of_eq
  field_simp
  ring

/-! ## §2 — the capstone: `Ttc.ttc_volume_estimate` with the runtime side priced -/

/-- **THE CAPSTONE — `thm:volumettc` + `thm:runtime`, at polynomial per-call prices.**

Literally `Ttc.ttc_volume_estimate` (`Ttc/Model/Theorem.lean:60`) with one change: the
runtime right-hand side `m·(cVol + cSample·(Θ+1))` is replaced by

```
m · n^K · ( Cv·volFac + 2⁶²·rfac·(R²/γ²)·log(2R) · (Θ + 1) )
```

with `cVol` and `cSample` discharged at their assumed upper bounds.  Same binder order,
same `Pr[…]`/`All[…]`, same measure `Ttc.ttcCharged atoms φ ε δ cVol cSample`, and — this is the
point — **the accuracy conjunct is the same proposition, character for character**.  Both
conjuncts still speak about the *same* run.

**The two priced hypotheses are HYPOTHESES.**

* `hcSample` is exactly the conclusion of `Ttc.SamplerCost.samplePrice_le_quartic` (its
  `2⁶²` is that theorem's own numeral), meaningful only under
  `Ttc.HitAndRunTheorem11Input`;
* `hcVol` carries a free constant `Cv`, a free exponent `kv` and a free `n`-independent
  factor `volFac`.  §1's `Ttc.cvVolumeOpsPrice_le_poly` is what supplies that shape from
  the Cousins–Vempala route, at `kv = kq + 1` where `kq` is the exponent of the
  **unbounded** per-sample charge `q`.

Neither hypothesis is discharged anywhere in this repository, and neither says anything
about *which* oracles the run executes: `cVol` and `cSample` are the per-call unit prices
of the cost model, the run's own oracle bundle is untouched, and its Monte-Carlo /
ball-walk prices are exponential.  See the module docstring's boxed warning — especially
the ORACLE MISMATCH paragraph.

`K = max(kv, 4)` is the least exponent this argument delivers: the threshold factor
`Θ + 1` is `n`-free (`Ttc.PolyComplexity.ttcComplexity_eq`), so the only inequalities spent
are `n^kv ≤ n^K` and `n⁴ ≤ n^K`.

⚠ `m = (toDNFd (preprocess atoms φ)).length` is the DNF cube count, **exponential in `|φ|`
in the worst case**, and is carried as an explicit factor here and everywhere below. -/
theorem ttc_volume_estimate_poly {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (cVol cSample : ℕ)
    (Cv volFac rfac R γ : ℝ) (K kv : ℕ)
    (hkv : kv ≤ K) (h4K : 4 ≤ K)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ kv * volFac)
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    -- (accuracy) the estimate is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[r ← ttcCharged atoms φ ε δ cVol cSample;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) almost every run is charged at most `m·n^K·(Cv·volFac + 2⁶²·…·(Θ+1))`
    (All[r ← ttcCharged atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ K
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                      + 15 * (Real.log (15 / (2 * δ))
                          + Real.log ((toDNFd (preprocess atoms φ)).length))
                      + 1))]) := by
  obtain ⟨hacc, hrun⟩ :=
    ttc_volume_estimate_parametric atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos cVol cSample
  refine ⟨hacc, ?_⟩
  have hb := PolyComplexity.ttcComplexity_le_poly atoms φ ε δ cVol cSample K kv hn hkv h4K
    hCv hvolFac hrfac hR1 hγ0 hε0 hε1 hδ0 hδ1 hcVol hcSample
  filter_upwards [hrun] with r hr
  exact hr.trans hb

/-- **`K = 4` — the TIGHT form, when the volume side is `kv ≤ 4`.**

The sampling side is `n⁴` (`Ttc.SamplerCost.samplePrice_le_quartic`) and the threshold
factor is `n`-free, so as soon as the volume oracle's *operation* count is `O(n⁴)` the whole
charged cost is `m·O(n⁴)` — no `n⁵` anywhere.  Via §1's bridge, `kv ≤ 4` means `kq ≤ 3`:
**one draw from the cooled Gaussian must cost `O(n³)`**.

This is `Ttc.ttc_volume_estimate_poly` at `K = 4`. -/
theorem ttc_volume_estimate_quartic {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (cVol cSample : ℕ)
    (Cv volFac rfac R γ : ℝ) (kv : ℕ)
    (hkv : kv ≤ 4)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ kv * volFac)
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    (1 - δ ≤
      Pr[r ← ttcCharged atoms φ ε δ cVol cSample;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    (All[r ← ttcCharged atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                      + 15 * (Real.log (15 / (2 * δ))
                          + Real.log ((toDNFd (preprocess atoms φ)).length))
                      + 1))]) :=
  ttc_volume_estimate_poly atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos cVol cSample Cv volFac
    rfac R γ 4 kv hkv le_rfl hCv hvolFac hrfac hR1 hγ0 hcVol hcSample

/-- **`K = 5` — the paper's `m·O(n⁵)`, and it is LOOSE whenever `kv ≤ 4`.**

Stated at `kv ≤ 5` so it composes with whatever the volume side turns out to be.  If
`kv ≤ 4` then `Ttc.ttc_volume_estimate_quartic` applies and *this* bound is a factor of `n`
too big.  Nothing in this repository establishes a matching `n⁵` **lower** bound; "tight"
is never claimed for this one.

Via §1's bridge, `kv ≤ 5` means `kq ≤ 4`: one draw from the cooled Gaussian must cost
`O(n⁴)`.  Under Cousins–Vempala's own (unproved here) `O*(n²)` per-sample claim `kq = 2`,
so `kv = 3` and `Ttc.ttc_volume_estimate_quartic` would be the operative statement. -/
theorem ttc_volume_estimate_quintic {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (cVol cSample : ℕ)
    (Cv volFac rfac R γ : ℝ) (kv : ℕ)
    (hkv : kv ≤ 5)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ kv * volFac)
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    (1 - δ ≤
      Pr[r ← ttcCharged atoms φ ε δ cVol cSample;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    (All[r ← ttcCharged atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 5
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                      + 15 * (Real.log (15 / (2 * δ))
                          + Real.log ((toDNFd (preprocess atoms φ)).length))
                      + 1))]) :=
  ttc_volume_estimate_poly atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos cVol cSample Cv volFac
    rfac R γ 5 kv hkv (by norm_num) hCv hvolFac hrfac hR1 hγ0 hcVol hcSample

/-! ## §3 — the same capstone with the volume price routed through Cousins–Vempala

`hcVolCV` below bounds the **number** `cVol` — the cost model's per-volume-call unit price
— by the Cousins–Vempala operation price.  It is a hypothesis about a natural number and
**not** a claim that `Ttc.ttc` calls the CV oracle: the run's oracle bundle is `Ttc.algOracles`
over `Ttc.mcVol` and is nowhere mentioned here.  See the module docstring's ORACLE MISMATCH
paragraph. -/

/-- **The capstone with `Cv`, `kv`, `volFac` supplied by the CV route** — `kv = kq + 1`
made visible in the statement.

Every factor the `O(·)` would hide is a named hypothesis: the cooling logarithm `L`, the
variance budget `κ`, the confidence `p`, §5.1's second moment `c`, the facet count `rfac`,
the roundness `R/γ`, the FPRAS parameters `ε, δ`, the cube count `m` (as an explicit
factor), **and the per-sample charge exponent `kq`, its constant `Cq` and its `n`-free
factor `qFac`**.

⚠ `hq : (q : ℝ) ≤ Cq·n^kq·qFac` is the open half of the Cousins–Vempala cost — see
`Ttc.cvVolumeOpsPrice_le_poly`.  `hcSample` is `Ttc.SamplerCost.samplePrice_le_quartic`'s
conclusion, conditional on `Ttc.HitAndRunTheorem11Input`. -/
theorem ttc_volume_estimate_poly_cv {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (cVol cSample : ℕ)
    (L κ c p Cq qFac rfac R γ : ℝ) (q kq K : ℕ)
    (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hc1 : 1 ≤ c) (hc : c ≤ 1 + 2 / (n : ℝ))
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) (hCq : 0 ≤ Cq) (hqFac : 0 ≤ qFac)
    (hq : (q : ℝ) ≤ Cq * (n : ℝ) ^ kq * qFac)
    (hkq : kq + 1 ≤ K) (h4K : 4 ≤ K)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hcVolCV : (cVol : ℝ) ≤ (CVCost.cvVolumeOpsPrice n L κ c p q : ℝ))
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    (1 - δ ≤
      Pr[r ← ttcCharged atoms φ ε δ cVol cSample;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    (All[r ← ttcCharged atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ K
          * (2 ^ 13 * Cq * (qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3))
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                      + 15 * (Real.log (15 / (2 * δ))
                          + Real.log ((toDNFd (preprocess atoms φ)).length))
                      + 1))]) := by
  have h2le : (2 : ℝ) ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have hlog : (0 : ℝ) ≤ Real.log (1 / p) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2le
    have := Real.log_two_gt_d9
    linarith
  have hvolFac : (0 : ℝ) ≤ qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3) :=
    mul_nonneg hqFac (div_nonneg (mul_nonneg (by positivity) hlog) (by positivity))
  have hCv : (0 : ℝ) ≤ 2 ^ 13 * Cq := by positivity
  have hcVol : (cVol : ℝ)
      ≤ 2 ^ 13 * Cq * (n : ℝ) ^ (kq + 1) * (qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3)) :=
    hcVolCV.trans (cvVolumeOpsPrice_le_poly hn hL hκ0 hκ1 hc1 hc hp0 hp1 hq)
  exact ttc_volume_estimate_poly atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos cVol cSample
    (2 ^ 13 * Cq) (qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3)) rfac R γ K (kq + 1) hkq h4K
    hCv hvolFac hrfac hR1 hγ0 hcVol hcSample

/-- **`K = 4` on the CV route — the form the development is aiming at.**

`Ttc.ttc_volume_estimate_poly_cv` at `K = 4`, i.e. under `hkq3 : kq ≤ 3`: **one draw from
the cooled Gaussian costs `O(n³)` (times `n`-free factors)**.  Then `kv = kq + 1 ≤ 4`, the
sampling side is already `n⁴`, and the whole charged cost is `m·O(n⁴)` — the paper's `n⁵`
is loose by a factor of `n`.

⚠ `hq` is still an assumption here.  Nothing in *this* file bounds `q`, and nothing in it
may be quoted as proving `TTC` runs in `O(m·n⁴)`: `hq`,
`Ttc.HitAndRunTheorem11Input` (via `hcSample`), and Cousins–Vempala's `hphase_mean` /
`hphase_var` (via `hcVolCV`) are all open. -/
theorem ttc_volume_estimate_quartic_cv {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (cVol cSample : ℕ)
    (L κ c p Cq qFac rfac R γ : ℝ) (q kq : ℕ)
    (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hc1 : 1 ≤ c) (hc : c ≤ 1 + 2 / (n : ℝ))
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) (hCq : 0 ≤ Cq) (hqFac : 0 ≤ qFac)
    (hq : (q : ℝ) ≤ Cq * (n : ℝ) ^ kq * qFac)
    (hkq3 : kq ≤ 3)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hcVolCV : (cVol : ℝ) ≤ (CVCost.cvVolumeOpsPrice n L κ c p q : ℝ))
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    (1 - δ ≤
      Pr[r ← ttcCharged atoms φ ε δ cVol cSample;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    (All[r ← ttcCharged atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
          * (2 ^ 13 * Cq * (qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3))
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                      + 15 * (Real.log (15 / (2 * δ))
                          + Real.log ((toDNFd (preprocess atoms φ)).length))
                      + 1))]) :=
  ttc_volume_estimate_poly_cv atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos cVol cSample L κ c p
    Cq qFac rfac R γ q kq 4 hL hκ0 hκ1 hc1 hc hp0 hp1 hCq hqFac hq (by omega) le_rfl hrfac
    hR1 hγ0 hcVolCV hcSample

/-! ## §4 — the `IsBigO` form, with the whole regime kept OUT of the `O(·)`

`Ttc.ttc`'s cost is a random variable and its bound is not a function of `n` alone, so an
asymptotic statement has to say what varies with `n` and what does not.  The choices, and
the reason for each:

* **`m` is bounded by a VISIBLE `mBound`**, never absorbed.  `m` is the DNF cube count,
  exponential in `|φ|` in the worst case (`sections/analysis.tex`'s own `thm:runtime` says
  so); putting it inside the `O(·)` would be the single most misleading thing this file
  could do;
* **`ε`, `δ`, `rfac`, `R`, `γ`, `κ`, `p`, `Cq`, `qFac` and `L` are fixed parameters** with
  named hypotheses.  ⚠ Fixing **`L`** is a real restriction and is stated as one: `L` is
  the log of the total cooling factor, and for Cousins–Vempala it is `≈ log n + 2 log R`,
  i.e. it *grows*.  A statement with `L` growing would carry `(L N)⁴` inside the comparison
  function, as `Ttc.CVCost.isBigO_cvVolumeSamplePrice_linear` does.  Nothing here hides it;
* **`c` and `q` vary with `N`** (`c N ≤ 1 + 2/N` is `N`-dependent by nature, and `q N` is
  the per-sample charge in dimension `N`), each with its own visible hypothesis;
* **the formula family varies with `N`** — `atoms N : Af N → LinAtom N` is an
  `N`-dimensional instance for each `N`, so the statement is about a family of TTC runs.

The implied constant is written out in the proof:
`mBound·(2¹³·Cq·qFac·L⁴·log(1/p)/κ³ + 2⁶²·rfac·(R²/γ²)·log(2R)·Thr(ε,δ,mBound))`. -/

/-- **The runtime is `O(n^K)` almost surely, at fixed regime — with the accuracy guarantee
carried alongside.**

Three claims about the *same* family of runs:

1. every run at dimension `N ≥ 1` meets `Ttc.ttc_volume_estimate`'s accuracy bound;
2. almost every such run is charged at most `Ttc.ttcComplexity …`;
3. `Ttc.ttcComplexity …` is `O(N^K)` with an implied constant free of `N`.

`K` may be taken to be `max(kq + 1, 4)`; at the expected `kq ≤ 3` that is `4`.

⚠ Same conditionality as everywhere in this file: `hq`, `hcVolCV` and `hcSample` are
assumptions, not theorems of this repository. -/
theorem isBigO_ttc_runtime_cv {Af : ℕ → Type*}
    (atoms : ∀ N, Af N → LinAtom N) (φ : ∀ N, BForm (Af N))
    (ε δ : ℝ) (cVol cSample q : ℕ → ℕ) (c : ℕ → ℝ)
    (L κ p Cq qFac rfac R γ : ℝ) (kq K mBound : ℕ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : ∀ N, (φ N).IsPositive)
    (hpos : ∀ N, 0 < volSol (atomSet (atoms N)) (φ N))
    (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hc1 : ∀ N, 1 ≤ c N) (hc : ∀ N : ℕ, c N ≤ 1 + 2 / (N : ℝ))
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) (hCq : 0 ≤ Cq) (hqFac : 0 ≤ qFac)
    (hq : ∀ N : ℕ, (q N : ℝ) ≤ Cq * (N : ℝ) ^ kq * qFac)
    (hkq : kq + 1 ≤ K) (h4K : 4 ≤ K)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hcVolCV : ∀ N : ℕ, (cVol N : ℝ) ≤ (CVCost.cvVolumeOpsPrice N L κ (c N) p (q N) : ℝ))
    (hcSample : ∀ N : ℕ, (cSample N : ℝ)
      ≤ 2 ^ 62 * (N : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R))
    (hm : ∀ N : ℕ, (toDNFd (preprocess (atoms N) (φ N))).length ≤ mBound) :
    (∀ N : ℕ, 1 ≤ N →
      (1 - δ ≤
        Pr[r ← ttcCharged (atoms N) (φ N) ε δ (cVol N) (cSample N);
          r.1 ∈ relErr ε (volSol (atomSet (atoms N)) (φ N))])
      ∧ All[r ← ttcCharged (atoms N) (φ N) ε δ (cVol N) (cSample N);
          (r.2 : ℝ) ≤ ttcComplexity (atoms N) (φ N) ε δ (cVol N) (cSample N)])
    ∧ Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ttcComplexity (atoms N) (φ N) ε δ (cVol N) (cSample N))
        (fun N : ℕ => (N : ℝ) ^ K) := by
  refine ⟨fun N hN => ttc_volume_estimate_parametric (atoms N) (φ N) ε δ hε0 hε1 hδ0 hδ1 hN (hφ N)
    (hpos N) (cVol N) (cSample N), ?_⟩
  have h2le : (2 : ℝ) ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have hlogp : (0 : ℝ) ≤ Real.log (1 / p) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2le
    have := Real.log_two_gt_d9
    linarith
  have hvolFac : (0 : ℝ) ≤ qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3) :=
    mul_nonneg hqFac (div_nonneg (mul_nonneg (by positivity) hlogp) (by positivity))
  have hCv : (0 : ℝ) ≤ 2 ^ 13 * Cq := by positivity
  have hlogR : (0 : ℝ) ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hRg0 : (0 : ℝ) < R ^ 2 / γ ^ 2 := div_pos (pow_pos (by linarith) 2) (pow_pos hγ0 2)
  have hB : (0 : ℝ) ≤ 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hRg0.le) hlogR
  have hCV0 : (0 : ℝ) ≤ 2 ^ 13 * Cq * (qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3)) :=
    mul_nonneg hCv hvolFac
  refine Asymptotics.IsBigO.of_bound
    ((mBound : ℝ) * (2 ^ 13 * Cq * (qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3))
      + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
          * PolyComplexity.threshFactor ε δ mBound)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hcVolN : (cVol N : ℝ)
      ≤ 2 ^ 13 * Cq * (N : ℝ) ^ (kq + 1) * (qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3)) :=
    (hcVolCV N).trans
      (cvVolumeOpsPrice_le_poly hN hL hκ0 hκ1 (hc1 N) (hc N) hp0 hp1 (hq N))
  have hb := PolyComplexity.ttcComplexity_le_poly (atoms N) (φ N) ε δ (cVol N) (cSample N)
    K (kq + 1) hN hkq h4K hCv hvolFac hrfac hR1 hγ0 hε0 hε1 hδ0 hδ1 hcVolN (hcSample N)
  rw [Real.norm_of_nonneg (PolyComplexity.ttcComplexity_nonneg (atoms N) (φ N) ε δ
        (cVol N) (cSample N) hε0 hε1 hδ0 hδ1),
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ K)]
  refine hb.trans ?_
  set CV0 : ℝ := 2 ^ 13 * Cq * (qFac * (L ^ 4 * Real.log (1 / p) / κ ^ 3)) with hCV0def
  set B : ℝ := 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) with hBdef
  set mm : ℕ := (toDNFd (preprocess (atoms N) (φ N))).length with hmm
  have hmle : (mm : ℝ) ≤ (mBound : ℝ) := by exact_mod_cast hm N
  have hTle : PolyComplexity.threshFactor ε δ mm
      ≤ PolyComplexity.threshFactor ε δ mBound :=
    PolyComplexity.threshFactor_mono_m ε δ (hm N)
  have hT1 : 1 ≤ PolyComplexity.threshFactor ε δ mm :=
    PolyComplexity.one_le_threshFactor ε δ mm hε0 hε1 hδ0 hδ1
  have hnK0 : (0 : ℝ) ≤ (N : ℝ) ^ K := by positivity
  have hX0 : (0 : ℝ) ≤ CV0 + B * PolyComplexity.threshFactor ε δ mm :=
    add_nonneg hCV0 (mul_nonneg hB (by linarith))
  have hXle : CV0 + B * PolyComplexity.threshFactor ε δ mm
      ≤ CV0 + B * PolyComplexity.threshFactor ε δ mBound := by
    have := mul_le_mul_of_nonneg_left hTle hB
    linarith
  calc (mm : ℝ) * (N : ℝ) ^ K * (CV0 + B * PolyComplexity.threshFactor ε δ mm)
      ≤ (mBound : ℝ) * (N : ℝ) ^ K * (CV0 + B * PolyComplexity.threshFactor ε δ mm) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmle hnK0) hX0
    _ ≤ (mBound : ℝ) * (N : ℝ) ^ K * (CV0 + B * PolyComplexity.threshFactor ε δ mBound) :=
        mul_le_mul_of_nonneg_left hXle (mul_nonneg (Nat.cast_nonneg _) hnK0)
    _ = (mBound : ℝ) * (CV0 + B * PolyComplexity.threshFactor ε δ mBound)
          * (N : ℝ) ^ K := by ring

/-! ## §5 — the cube count is at least one, unconditionally -/

/-- **`1 ≤ m`, with no hypothesis at all.**

`m = (toDNFd (preprocess atoms φ)).length` is the factor every runtime bound above carries.
It is never zero: `Ttc.preprocess_isPositive` says the preprocessed formula is positive
*whatever* the input was (it is a `Ttc.dnfForm`, which has no `.neg`), and
`Ttc.toDNFd_ne_nil` says a positive formula's deduplicated DNF is nonempty (`Ttc.BForm` has
no `false` constructor).  Neither step needs `hφ` or `hpos`.

Consequence: the runtime bounds of §2–§3 are **strictly positive** whenever their bracket
is, so none of them is the degenerate `cost ≤ 0`.  (`Ttc.PolyComplexity`'s §4 works this
out only at its own `φ = ⊤` witness; it holds in general.) -/
theorem one_le_ttcNumCubes {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) :
    1 ≤ (toDNFd (preprocess atoms φ)).length :=
  List.length_pos_iff.2 (toDNFd_ne_nil (preprocess_isPositive atoms φ))

/-! ## §6 — non-vacuity (`CLAUDE.md` §11)

A `∀` under unsatisfiable hypotheses proves nothing, and a bound of `0` on a quantity that
is `0` proves nothing either.  `Ttc.ttc_volume_estimate_poly_two_cube` exhibits **one**
assignment meeting *every* hypothesis of `Ttc.ttc_volume_estimate_quartic` simultaneously —
the model-side ones *and* the price-side ones — and pins the conclusion where it is not
degenerate.

The data: the **two-cube** instance of `Ttc/Witness/TwoCube.lean` (two disjoint boxes, so
`m ≥ 2` cubes and not the single-box special case), at `ε = δ = 1/2`, with
`cVol = cSample = 1` and `Cv = volFac = rfac = R = γ = 1`, `kv = 4`.  `hφ` is
`Ttc.TwoCube.twoForm_isPositive` and `hpos` is `Ttc.TwoCube.twoVolPos`.

Four things are checked *inside the statement*, not left to the reader:

* the two **price** hypotheses hold at these numbers (`hcSample` because `2⁶²·log 2 ≥ 1`);
* the accuracy conclusion is `1/2 ≤ Pr[…]`, a positive numeral;
* the run measure of the good event is **strictly positive**, so the `All[…]` conjunct is
  not a statement about the zero measure (`ENNReal.toReal ⊤ = 0` cannot be hiding here
  either — a positive `toReal` forces the measure finite and nonzero);
* `1 ≤ m` (`Ttc.one_le_ttcNumCubes`) **and** `0 < ` the runtime right-hand side — the
  latter is conjunct (v) of the statement, machine-checked rather than left to prose, so
  the runtime conjunct is not the degenerate `cost ≤ 0`.

**What it does NOT witness, stated plainly.**  It inhabits the *arithmetic* price bundle,
not the objects that would achieve those prices: it does **not** inhabit
`Ttc.HitAndRunTheorem11Input`, does not discharge Cousins–Vempala's `hphase_mean` /
`hphase_var`, and constructs no oracle at either price.  The witness run is the ordinary
`Ttc.ttc` run, on the ordinary Monte-Carlo / ball-walk bundle, whose *real* prices are
exponential; `cVol = cSample = 1` is a *pricing assumption* here, exactly as everywhere
else in the file. -/

/-- **Every hypothesis of `Ttc.ttc_volume_estimate_quartic` is satisfiable at once, with a
non-degenerate conclusion.**  See §6's docstring for what this does and does not certify. -/
theorem ttc_volume_estimate_poly_two_cube (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1 / 2) (hε1 : (1 / 2 : ℝ) ≤ 1) :
    -- (i) the two PRICE hypotheses hold at `cVol = cSample = 1`, `Cv = volFac = rfac = R = γ = 1`
    ((1 : ℝ) ≤ 1 * (n : ℝ) ^ 4 * 1
      ∧ (1 : ℝ) ≤ 2 ^ 62 * (n : ℝ) ^ 4 * 1 * ((1 : ℝ) ^ 2 / (1 : ℝ) ^ 2) * Real.log (2 * 1))
    -- (ii) the cube count is at least one, so the runtime bound is not `cost ≤ 0`
    ∧ 1 ≤ (toDNFd (preprocess (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1)
              (TwoCube.twoForm n))).length
    -- (iii) the good event has strictly positive, finite measure: `All[…]` is not vacuous
    ∧ (0 < ttcCharged (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1) (TwoCube.twoForm n)
            (1 / 2) (1 / 2) 1 1
          {r | r.1 ∈ relErr (1 / 2)
            (volSol (atomSet (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1))
              (TwoCube.twoForm n))}
      ∧ ttcCharged (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1) (TwoCube.twoForm n)
            (1 / 2) (1 / 2) 1 1
          {r | r.1 ∈ relErr (1 / 2)
            (volSol (atomSet (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1))
              (TwoCube.twoForm n))} ≠ ⊤)
    -- (iv) the capstone's own conclusion at this data, both conjuncts
    ∧ ((1 : ℝ) - 1 / 2 ≤
        Pr[r ← ttcCharged (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1) (TwoCube.twoForm n)
              (1 / 2) (1 / 2) 1 1;
          r.1 ∈ relErr (1 / 2)
            (volSol (atomSet (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1))
              (TwoCube.twoForm n))]
      ∧ All[r ← ttcCharged (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1) (TwoCube.twoForm n)
              (1 / 2) (1 / 2) 1 1;
          (r.2 : ℝ) ≤
            ((toDNFd (preprocess (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1)
                (TwoCube.twoForm n))).length : ℝ) * (n : ℝ) ^ 4
              * (1 * 1
                  + 2 ^ 62 * 1 * ((1 : ℝ) ^ 2 / (1 : ℝ) ^ 2) * Real.log (2 * 1)
                      * (41472 * Real.log (30 / (1 / 2)) / ((1 / 2 : ℝ) ^ 2 * (12 - 1 / 2))
                          + 15 * (Real.log (15 / (2 * (1 / 2)))
                              + Real.log ((toDNFd (preprocess
                                  (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1)
                                  (TwoCube.twoForm n))).length))
                          + 1))])
    -- (v) that runtime bound is STRICTLY POSITIVE, so (iv) is not the degenerate `cost ≤ 0`
    ∧ 0 < ((toDNFd (preprocess (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1)
              (TwoCube.twoForm n))).length : ℝ) * (n : ℝ) ^ 4
            * (1 * 1
                + 2 ^ 62 * 1 * ((1 : ℝ) ^ 2 / (1 : ℝ) ^ 2) * Real.log (2 * 1)
                    * (41472 * Real.log (30 / (1 / 2)) / ((1 / 2 : ℝ) ^ 2 * (12 - 1 / 2))
                        + 15 * (Real.log (15 / (2 * (1 / 2)))
                            + Real.log ((toDNFd (preprocess
                                (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1)
                                (TwoCube.twoForm n))).length))
                        + 1)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hcVol : (1 : ℝ) ≤ 1 * (n : ℝ) ^ 4 * 1 := by nlinarith
  have hcSample : (1 : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * 1 * ((1 : ℝ) ^ 2 / (1 : ℝ) ^ 2) * Real.log (2 * 1) := by
    rw [show (2 : ℝ) * 1 = 2 by norm_num]
    nlinarith
  have hmain := ttc_volume_estimate_quartic
    (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1) (TwoCube.twoForm n) (1 / 2) (1 / 2)
    hε0 hε1 (by norm_num) (by norm_num) hn TwoCube.twoForm_isPositive
    (TwoCube.twoVolPos n hn (1 / 2) (1 / 2) hε0 hε1) 1 1 1 1 1 1 1 4 le_rfl
    zero_le_one zero_le_one le_rfl le_rfl one_pos (by exact_mod_cast hcVol)
    (by exact_mod_cast hcSample)
  have hposR : (0 : ℝ) < ((ttcCharged (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1)
      (TwoCube.twoForm n) (1 / 2) (1 / 2) 1 1)
        {r | r.1 ∈ relErr (1 / 2)
          (volSol (atomSet (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1))
            (TwoCube.twoForm n))}).toReal :=
    lt_of_lt_of_le (by norm_num) hmain.1
  have hm0 : 1 ≤ (toDNFd (preprocess (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1)
      (TwoCube.twoForm n))).length :=
    one_le_ttcNumCubes (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1) (TwoCube.twoForm n)
  refine ⟨⟨hcVol, hcSample⟩, hm0,
    ⟨(ENNReal.toReal_pos_iff.1 hposR).1, (ENNReal.toReal_pos_iff.1 hposR).2.ne⟩, hmain, ?_⟩
  set mm : ℕ := (toDNFd (preprocess (TwoCube.atomsT n hn (1 / 2) (1 / 2) hε0 hε1)
    (TwoCube.twoForm n))).length with hmmdef
  have hm1 : (1 : ℝ) ≤ (mm : ℝ) := by exact_mod_cast hm0
  have hT1 : (1 : ℝ)
      ≤ 41472 * Real.log (30 / (1 / 2)) / ((1 / 2 : ℝ) ^ 2 * (12 - 1 / 2))
          + 15 * (Real.log (15 / (2 * (1 / 2))) + Real.log mm) + 1 :=
    PolyComplexity.one_le_threshFactor (1 / 2) (1 / 2) mm (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * 1) := by
    rw [show (2 : ℝ) * 1 = 2 by norm_num]; linarith
  have hprod : (0 : ℝ) ≤ 2 ^ 62 * 1 * ((1 : ℝ) ^ 2 / (1 : ℝ) ^ 2) * Real.log (2 * 1)
      * (41472 * Real.log (30 / (1 / 2)) / ((1 / 2 : ℝ) ^ 2 * (12 - 1 / 2))
          + 15 * (Real.log (15 / (2 * (1 / 2))) + Real.log mm) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hlog0) (by linarith)
  have hmn : (1 : ℝ) ≤ (mm : ℝ) * (n : ℝ) ^ 4 := by
    have h := mul_le_mul hm1 hn4 zero_le_one (by linarith : (0 : ℝ) ≤ (mm : ℝ))
    linarith
  have h := mul_le_mul hmn (by linarith : (1 : ℝ)
      ≤ 1 * 1 + 2 ^ 62 * 1 * ((1 : ℝ) ^ 2 / (1 : ℝ) ^ 2) * Real.log (2 * 1)
          * (41472 * Real.log (30 / (1 / 2)) / ((1 / 2 : ℝ) ^ 2 * (12 - 1 / 2))
              + 15 * (Real.log (15 / (2 * (1 / 2))) + Real.log mm) + 1))
    zero_le_one (by linarith : (0 : ℝ) ≤ (mm : ℝ) * (n : ℝ) ^ 4)
  linarith

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.cvVolumeOpsPrice_le_poly
#print axioms Ttc.ttc_volume_estimate_poly
#print axioms Ttc.ttc_volume_estimate_quartic
#print axioms Ttc.ttc_volume_estimate_quintic
#print axioms Ttc.ttc_volume_estimate_poly_cv
#print axioms Ttc.ttc_volume_estimate_quartic_cv
#print axioms Ttc.isBigO_ttc_runtime_cv
#print axioms Ttc.one_le_ttcNumCubes
#print axioms Ttc.ttc_volume_estimate_poly_two_cube

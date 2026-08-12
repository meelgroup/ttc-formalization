/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Complexity

/-!
# `Exec/PolyComplexity`: `Ttc.ttcComplexity` is `m · O(n^K)` once the two oracle prices are polynomial

> ## ⚠ NOTHING HERE PROVES THAT `TTC` RUNS IN `O(m·n⁵)` — OR IN ANY TIME AT ALL ⚠
>
> Every theorem in this file is an **implication**.  It takes the two per-call oracle
> prices `cVol`, `cSample` as *given numbers* satisfying *given* polynomial hypotheses, and
> concludes that `Ttc.ttcComplexity` — the **charged** cost of `Ttc.ttcCost`, which counts
> oracle calls and nothing else — is bounded by an explicit polynomial.  It does **not**
> assert that any oracle achieves those prices.  Three separate reasons the antecedent is
> not discharged anywhere in this repository:
>
> * the sampling price `2⁶²·n⁴·rfac·(R²/γ²)·log(2R)` is
>   `Ttc.SamplerCost.samplePrice_le_quartic`, which is meaningful **only given**
>   `Ttc.HitAndRunTheorem11Input` (Lovász–Vempala Theorem 1.1) — a structure that is
>   *assumed* and inhabited nowhere, and whose own proof would rest on `hLS`
>   (Lovász–Simonovits 1993, Corollary 1.5), also unproved here.  Its per-step arithmetic
>   charge `n·rfac` is moreover a **cost-model definition**, not a measurement of any
>   executable (`Ttc/Exec/SamplerCost.lean`, module docstring);
> * a polynomial volume price needs the **Cousins–Vempala** oracle, whose instantiation
>   `Ttc.VolumeAlgorithm.cousinsVempala` still carries the two unproved sampler hypotheses
>   `hphase_mean` and `hphase_var` (`Ttc/Volume/CVInstantiate.lean`).  The volume oracle
>   this repository actually *constructs* is `Ttc.VolumeAlgorithm.monteCarlo`, whose coin
>   count `Ttc.MonteCarlo.nSamp` is **exponential** in `n`
>   (`Ttc/Exec/Complexity.lean`, §4);
> * `Ttc.ttcComplexity` bounds `Ttc.ttcCost`, which charges **one unit per oracle call**.
>   It prices at zero the arithmetic inside a call, the rejection rounds, and `alg:ttc`'s
>   lines 32–42 `while` loops.  A bound on an undercount is not a bound on work.
>
> **`m` is not suppressed anywhere in this file, and must not be.**  `m` is
> `(toDNFd (preprocess atoms φ)).length`, the number of DNF cubes, which is exponential in
> the size of `φ` in the worst case.  Every statement below carries it as an explicit
> factor, and the `IsBigO` corollaries carry a *visible* uniform bound `mBound` on it
> rather than hiding it in the `O(·)`.

## What is actually proved

`Ttc.ttcComplexity atoms φ ε δ cVol cSample = m · (cVol + cSample · Thr(ε, δ, m))` where

```
Thr(ε, δ, m) = 41472·log(30/δ) / (ε²·(12 − ε)) + 15·(log(15/(2δ)) + log m) + 1
```

is `Ttc.PolyComplexity.threshFactor` — and **`Thr` has no `n` in it**.  That is not a
modelling choice made here; it is forced by `Ttc.ttcComplexity`'s definition
(`Ttc/Exec/Complexity.lean:196`), whose body mentions only `ε`, `δ` and `m`.  The
signature `threshFactor (ε δ : ℝ) (m : ℕ) : ℝ` is the formal record of that fact, and
`Ttc.PolyComplexity.ttcComplexity_eq` is the `rfl` that ties it to the real object.  So
**every** `n` in TTC's charged cost enters through `cVol` and `cSample`, exactly as
`Ttc/Exec/Complexity.lean`'s module docstring says ("The dimension `n` does not appear,
and that is not an omission").

Consequently the exponent is `max(kv, 4)` where `kv` is the volume oracle's exponent:

* `Ttc.PolyComplexity.ttcComplexity_le_poly` — the general bound, at any `K` with
  `kv ≤ K` and `4 ≤ K`;
* `Ttc.PolyComplexity.ttcComplexity_le_quartic` — `K = 4`, valid when the volume side is
  `kv ≤ 4`.  **This is the tight one under that hypothesis**;
* `Ttc.PolyComplexity.ttcComplexity_le_quintic` — `K = 5`, valid whenever `kv ≤ 5`.
  **Loose by a factor of `n` whenever `kv ≤ 4`**, since the sampling side is `n⁴`
  (`Ttc.SamplerCost.samplePrice_le_quartic`) and the threshold factor is `n`-free.

`kv` is a **parameter**, deliberately: the volume-side exponent is not settled in this
repository, and hard-coding it would assert something unproved.

`Ttc.PolyComplexity.ttcCost_le_poly` carries the same bound over to `Ttc.ttcCost`, the
**real** charged-cost object, via `Ttc.ttcCost_le_ttcComplexity`
(`Ttc/Exec/Complexity.lean:317`).  It inherits that theorem's `hterm : Ttc.ttcTerminates …`
guard, which is not removable as `alg:ttc` stands.  Everything stated about
`Ttc.ttcComplexity` alone is a statement about an *expression*; `ttcCost_le_poly` is the
one about the run.

## On "an explicit numeral `C`"

There is no single numeral that can multiply the whole right-hand side, because the
volume-side hypothesis carries its own free constant `Cv` (the volume oracle's leading
coefficient) which this file does not — and must not — bound.  What the bounds below do
instead is keep **every numeral explicit** (`2^62` from the sampler side; `41472`, `15`,
`1` inside `threshFactor`) and keep `Cv` a *visible factor* rather than an `O(·)`:

```
ttcComplexity ≤ m · n^K · ( Cv·volFac + 2^62·rfac·(R²/γ²)·log(2R)·Thr(ε,δ,m) )
```

`Ttc.PolyComplexity.ttcComplexity_le_poly_single_constant` is the single-coefficient
variant, `m · (Cv + 2^62) · n^K · (…)`, for readers who want one leading factor; it is
still not a numeral, for the reason just given.

## Model imitated

`Ttc/Exec/SamplerCost.lean` — explicit-constant bound first, `IsBigO` corollary second
with every regime factor a named hypothesis, non-vacuity witness last.

## What this file imports, and why so little

Only `Ttc.Exec.Complexity`.  The sampler-price hypothesis is taken **in the shape**
`Ttc.SamplerCost.samplePrice_le_quartic` concludes, as a hypothesis; the file is
deliberately not linked to `Ttc/Exec/SamplerCost.lean`, so that none of that file's
conditional apparatus (`Ttc.HitAndRunTheorem11Input`) is silently pulled in.  The price
of that decoupling is that composing the two is a one-line `exact` the *caller* writes,
not a theorem here.
-/

namespace Ttc.PolyComplexity

variable {A : Type*} {n : ℕ}

/-! ## §1 — the threshold factor, and the fact that it is `n`-free -/

/-- **The per-sample threshold factor of `Ttc.ttcComplexity`.**

```
41472·log(30/δ) / (ε²·(12 − ε)) + 15·(log(15/(2δ)) + log m) + 1
```

**Its argument list is `(ε, δ, m)` — there is no `n`.**  This is not an abbreviation that
drops a dependence: `Ttc.ttcComplexity`'s body (`Ttc/Exec/Complexity.lean:196`) is
literally this expression, and `Ttc.PolyComplexity.ttcComplexity_eq` proves so by `rfl`.
The whole `n`-dependence of TTC's charged cost therefore sits in `cVol` and `cSample`. -/
noncomputable def threshFactor (ε δ : ℝ) (m : ℕ) : ℝ :=
  41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
    + 15 * (Real.log (15 / (2 * δ)) + Real.log m) + 1

/-- **`Ttc.ttcComplexity` factors through the `n`-free `Ttc.PolyComplexity.threshFactor`,
by `rfl`.**  This is the formal statement that the threshold carries no `n`. -/
theorem ttcComplexity_eq (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (cVol cSample : ℕ) :
    ttcComplexity atoms φ ε δ cVol cSample
      = ((toDNFd (preprocess atoms φ)).length : ℝ)
          * ((cVol : ℝ) + (cSample : ℝ)
              * threshFactor ε δ (toDNFd (preprocess atoms φ)).length) := rfl

/-- **`1 ≤ threshFactor`** on the FPRAS parameter range.  Both `Ttc.ttcThresh` branches
are nonnegative there (`Ttc.ttcThresh_branch_one_nonneg`,
`Ttc.ttcThresh_branch_two_nonneg`) and the `+1` is the `⌈·⌉`-slack `Ttc.ttcComplexity`
already carries. -/
theorem one_le_threshFactor (ε δ : ℝ) (m : ℕ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ threshFactor ε δ m := by
  have h1 := ttcThresh_branch_one_nonneg ε δ hε0 hε1 hδ0 hδ1
  have h2 := ttcThresh_branch_two_nonneg δ hδ0 hδ1 m
  unfold threshFactor
  linarith

/-- **`threshFactor` is monotone in `m`.**  The only occurrence of `m` is `log m`, and
`Real.log 0 = 0 ≤ Real.log M` for every natural `M`, so no `1 ≤ M` guard is needed. -/
theorem threshFactor_mono_m (ε δ : ℝ) {m M : ℕ} (h : m ≤ M) :
    threshFactor ε δ m ≤ threshFactor ε δ M := by
  have hlog : Real.log m ≤ Real.log M := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simpa using Real.log_natCast_nonneg M
    · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)
  unfold threshFactor
  linarith

/-- **`Ttc.ttcComplexity` is nonnegative** on the FPRAS parameter range — needed for the
`IsBigO` corollaries, where `‖·‖` must be discharged. -/
theorem ttcComplexity_nonneg (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (cVol cSample : ℕ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ ttcComplexity atoms φ ε δ cVol cSample := by
  rw [ttcComplexity_eq]
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  have hT := one_le_threshFactor ε δ (toDNFd (preprocess atoms φ)).length hε0 hε1 hδ0 hδ1
  have h1 : (0 : ℝ) ≤ (cVol : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (cSample : ℝ) := Nat.cast_nonneg _
  nlinarith

/-! ## §2 — the explicit polynomial bound

Read the hypothesis list before the exponent.  Nine of the twelve hypotheses below are
*regime* facts about parameters that do **not** shrink with `n` (`rfac` the facet count,
`R/γ` the roundness of the inflated bodies, `ε`, `δ`), and two are the oracle prices
themselves.  None of them is absorbed into the conclusion. -/

section Bound

set_option maxRecDepth 100000

variable {Cv volFac rfac R γ : ℝ}

/-- **THE BOUND.**  Given the two per-call oracle prices as polynomials in `n`,

```
ttcComplexity atoms φ ε δ cVol cSample
  ≤ m · n^K · ( Cv·volFac + 2^62·rfac·(R²/γ²)·log(2R)·Thr(ε,δ,m) )
```

for any `K` with `kv ≤ K` and `4 ≤ K`, where `m = (toDNFd (preprocess atoms φ)).length`
and `Thr = Ttc.PolyComplexity.threshFactor`.

**The two priced hypotheses.**

* `hcSample` is *exactly* the conclusion of `Ttc.SamplerCost.samplePrice_le_quartic`,
  taken here as a hypothesis so that this file does not inherit that file's conditional
  apparatus.  Its `2^62` is that theorem's own numeral;
* `hcVol` carries a free leading constant `Cv`, a free exponent `kv` and a free
  `n`-independent factor `volFac`, because **the volume oracle's polynomial price is not
  settled in this repository** (module docstring).  Nothing here bounds `Cv` or fixes
  `kv`; the theorem composes with whatever the volume side turns out to be, provided
  `kv ≤ K`.

**Where the `n`s are, and are not.**  There is no `n` on the right beyond `n^K`: the
threshold factor is `n`-free by construction (`Ttc.PolyComplexity.ttcComplexity_eq`), so
the *only* inequality spent on the exponent is `n^kv ≤ n^K` and `n^4 ≤ n^K`.  In
particular the bound is **tight in `K`** in the sense that `K = max(kv, 4)` is the least
`K` this argument delivers.

⚠ Conditional — see the module docstring.  This is a bound on the *charged* cost (oracle
calls), under *assumed* prices, and `m` can be exponential in `|φ|`. -/
theorem ttcComplexity_le_poly (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (cVol cSample K kv : ℕ)
    (hn : 1 ≤ n) (hkv : kv ≤ K) (h4K : 4 ≤ K)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ kv * volFac)
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    ttcComplexity atoms φ ε δ cVol cSample
      ≤ ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ K
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * threshFactor ε δ (toDNFd (preprocess atoms φ)).length) := by
  set m : ℕ := (toDNFd (preprocess atoms φ)).length with hm
  set T : ℝ := threshFactor ε δ m with hTdef
  have hT1 : 1 ≤ T := one_le_threshFactor ε δ m hε0 hε1 hδ0 hδ1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hRg0 : (0 : ℝ) < R ^ 2 / γ ^ 2 :=
    div_pos (pow_pos (by linarith) 2) (pow_pos hγ0 2)
  have hnkv : (n : ℝ) ^ kv ≤ (n : ℝ) ^ K := pow_le_pow_right₀ hn1 hkv
  have hn4 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ K := pow_le_pow_right₀ hn1 h4K
  have hCV0 : (0 : ℝ) ≤ Cv * volFac := mul_nonneg hCv hvolFac
  have hB : (0 : ℝ) ≤ 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hRg0.le) hlog0
  -- the volume half
  have h1 : (cVol : ℝ) ≤ (n : ℝ) ^ K * (Cv * volFac) := by
    refine hcVol.trans ?_
    calc Cv * (n : ℝ) ^ kv * volFac = (n : ℝ) ^ kv * (Cv * volFac) := by ring
      _ ≤ (n : ℝ) ^ K * (Cv * volFac) := mul_le_mul_of_nonneg_right hnkv hCV0
  -- the sampling half
  have h2 : (cSample : ℝ) * T
      ≤ (n : ℝ) ^ K * (2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T) := by
    have hstep : (cSample : ℝ) * T
        ≤ (2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) * T :=
      mul_le_mul_of_nonneg_right hcSample (by linarith)
    refine hstep.trans ?_
    have hBT : (0 : ℝ) ≤ 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T :=
      mul_nonneg hB (by linarith)
    calc (2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) * T
        = (n : ℝ) ^ 4 * (2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T) := by ring
      _ ≤ (n : ℝ) ^ K * (2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T) :=
          mul_le_mul_of_nonneg_right hn4 hBT
  rw [ttcComplexity_eq, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [mul_add]
  linarith

/-- **`K = 4` — the tight exponent, when the volume side is `kv ≤ 4`.**

The sampling side is `n⁴` (`Ttc.SamplerCost.samplePrice_le_quartic`) and the threshold
factor is `n`-free, so as soon as the volume oracle is `O(n⁴)` the whole charged cost is
`m·O(n⁴)` — no `n⁵` anywhere.  This is `Ttc.PolyComplexity.ttcComplexity_le_poly` at
`K = 4`; `Ttc.PolyComplexity.ttcComplexity_le_quintic` is the same statement one factor
of `n` weaker. -/
theorem ttcComplexity_le_quartic (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (cVol cSample kv : ℕ)
    (hn : 1 ≤ n) (hkv : kv ≤ 4)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ kv * volFac)
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    ttcComplexity atoms φ ε δ cVol cSample
      ≤ ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * threshFactor ε δ (toDNFd (preprocess atoms φ)).length) :=
  ttcComplexity_le_poly atoms φ ε δ cVol cSample 4 kv hn hkv le_rfl hCv hvolFac hrfac hR1
    hγ0 hε0 hε1 hδ0 hδ1 hcVol hcSample

/-- **`K = 5` — the brief's `m·O(n⁵)`, which is LOOSE whenever `kv ≤ 4`.**

Stated for `kv ≤ 5` so that it composes with whatever the volume side turns out to be.
If the volume side is `kv ≤ 4` then `Ttc.PolyComplexity.ttcComplexity_le_quartic` applies
and *this* bound is a factor of `n` too big — see that theorem's docstring.  Nothing in
this repository establishes a matching `n⁵` **lower** bound; "tight" is never claimed for
this one. -/
theorem ttcComplexity_le_quintic (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (cVol cSample kv : ℕ)
    (hn : 1 ≤ n) (hkv : kv ≤ 5)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ kv * volFac)
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    ttcComplexity atoms φ ε δ cVol cSample
      ≤ ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 5
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * threshFactor ε δ (toDNFd (preprocess atoms φ)).length) :=
  ttcComplexity_le_poly atoms φ ε δ cVol cSample 5 kv hn hkv (by norm_num) hCv hvolFac
    hrfac hR1 hγ0 hε0 hε1 hδ0 hδ1 hcVol hcSample

/-- **The single-leading-coefficient variant** — `m · (Cv + 2^62) · n^K · (…)`.

For readers who want one factor in front.  `Cv + 2^62` is **not** a numeral, and cannot
be made one: `Cv` is the volume oracle's leading constant, which this repository does not
bound (module docstring, "On an explicit numeral `C`").  The remaining regime factors
`volFac`, `rfac`, `R²/γ²`, `log(2R)` and `Thr(ε,δ,m)` stay visible on the right. -/
theorem ttcComplexity_le_poly_single_constant (atoms : A → LinAtom n) (φ : BForm A)
    (ε δ : ℝ) (cVol cSample K kv : ℕ)
    (hn : 1 ≤ n) (hkv : kv ≤ K) (h4K : 4 ≤ K)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ kv * volFac)
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    ttcComplexity atoms φ ε δ cVol cSample
      ≤ ((toDNFd (preprocess atoms φ)).length : ℝ) * (Cv + 2 ^ 62) * (n : ℝ) ^ K
          * (volFac
              + rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * threshFactor ε δ (toDNFd (preprocess atoms φ)).length) := by
  refine (ttcComplexity_le_poly atoms φ ε δ cVol cSample K kv hn hkv h4K hCv hvolFac hrfac
    hR1 hγ0 hε0 hε1 hδ0 hδ1 hcVol hcSample).trans ?_
  set m : ℕ := (toDNFd (preprocess atoms φ)).length with hm
  set T : ℝ := threshFactor ε δ m with hTdef
  have hT1 : 1 ≤ T := one_le_threshFactor ε δ m hε0 hε1 hδ0 hδ1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hRg0 : (0 : ℝ) < R ^ 2 / γ ^ 2 :=
    div_pos (pow_pos (by linarith) 2) (pow_pos hγ0 2)
  have hnK0 : (0 : ℝ) ≤ (n : ℝ) ^ K := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hW : (0 : ℝ) ≤ rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hRg0.le) hlog0) (by linarith)
  have hinner : Cv * volFac + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T
      ≤ (Cv + 2 ^ 62)
          * (volFac + rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T) := by
    have hexp : (Cv + 2 ^ 62)
          * (volFac + rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T)
        = (Cv * volFac + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T)
          + (2 ^ 62 * volFac + Cv * (rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T)) := by
      ring
    have hslack : (0 : ℝ)
        ≤ 2 ^ 62 * volFac + Cv * (rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T) :=
      add_nonneg (mul_nonneg (by norm_num) hvolFac) (mul_nonneg hCv hW)
    linarith
  calc (m : ℝ) * (n : ℝ) ^ K
          * (Cv * volFac + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T)
      ≤ (m : ℝ) * (n : ℝ) ^ K
          * ((Cv + 2 ^ 62)
              * (volFac + rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T)) :=
        mul_le_mul_of_nonneg_left hinner (mul_nonneg hm0 hnK0)
    _ = (m : ℝ) * (Cv + 2 ^ 62) * (n : ℝ) ^ K
          * (volFac + rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * T) := by ring

/-- **The same bound on the REAL charged cost, `Ttc.ttcCost`** — `Ttc.ttcComplexity` is
only an expression; `Ttc.ttcCost` is what the run is charged.

This is `Ttc.ttcCost_le_ttcComplexity` (`Ttc/Exec/Complexity.lean:317`) composed with
`Ttc.PolyComplexity.ttcComplexity_le_poly`, and it carries **every** hypothesis of that
theorem verbatim — in particular `hterm : Ttc.ttcTerminates …`, the absorption loops'
exit, which is *not* removable as `alg:ttc` currently stands (`Ttc/Exec/Complexity.lean`,
"The `Ttc.ttcTerminates` guard is still there").

⚠ `Ttc.ttcCost` charges **one unit per oracle call** and nothing else.  This is therefore
a bound on a charge, at *assumed* per-call prices — not on running time.  See the module
docstring. -/
theorem ttcCost_le_poly (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (c : ℕ → Space n) (t : ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ)
    (hterm : ttcTerminates atoms φ ε δ c t)
    (cVol cSample K kv : ℕ) (hkv : kv ≤ K) (h4K : 4 ≤ K)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ kv * volFac)
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    (ttcCost atoms φ ε δ c t cVol cSample : ℝ)
      ≤ ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ K
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * threshFactor ε δ (toDNFd (preprocess atoms φ)).length) :=
  le_trans
    (ttcCost_le_ttcComplexity atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 c t cVol cSample hterm)
    (ttcComplexity_le_poly atoms φ ε δ cVol cSample K kv hn hkv h4K hCv hvolFac hrfac hR1
      hγ0 hε0 hε1 hδ0 hδ1 hcVol hcSample)

end Bound

/-! ## §3 — the `IsBigO` corollaries, with the regime kept OUT of the `O(·)`

`Ttc.ttcComplexity` is not a function of `n` alone, so an asymptotic statement has to say
what varies with `n` and what does not.  The choice made here, and the reason for each:

* **`rfac`, `R`, `γ`, `ε`, `δ` are fixed** — they are named parameters of the statement
  with named hypotheses, not hidden constants.  In particular the roundness `R/γ` and the
  facet count `rfac` are *not* absorbed;
* **`m` is bounded by a visible `mBound`** rather than being quantified away.  `m` is the
  DNF cube count, exponential in `|φ|` in the worst case (`sections/analysis.tex`'s own
  `thm:runtime` says so); putting it inside the `O(·)` would be the single most
  misleading thing this file could do.  It is a hypothesis, `hm`;
* **the formula family varies with `n`** — `atoms N : Af N → LinAtom N` is an
  `N`-dimensional instance for each `N`, which is what makes the statement about a family
  of TTC runs rather than about one.

The implied constant is
`mBound · (Cv·volFac + 2^62·rfac·(R²/γ²)·log(2R)·Thr(ε,δ,mBound))`, written out in the
proof.  Nothing is in the `O(·)` that is not a hypothesis here. -/

section Asymptotic

set_option maxRecDepth 100000

variable {Cv volFac rfac R γ : ℝ}

/-- **`Ttc.ttcComplexity` is `O(n^K)` in `n`, for `K ≥ max(kv, 4)`**, at fixed regime.

Read the hypothesis list first: `hm` bounds the cube count, `hrfac`/`hR1`/`hγ0` fix the
geometry, `hε0`–`hδ1` fix the FPRAS parameters, and `hcVol`/`hcSample` are the *assumed*
oracle prices.  See the module docstring for why none of that is discharged here. -/
theorem isBigO_ttcComplexity_poly {Af : ℕ → Type*}
    (atoms : ∀ N, Af N → LinAtom N) (φ : ∀ N, BForm (Af N))
    (ε δ : ℝ) (cVol cSample : ℕ → ℕ) (K kv mBound : ℕ)
    (hkv : kv ≤ K) (h4K : 4 ≤ K)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcVol : ∀ N : ℕ, (cVol N : ℝ) ≤ Cv * (N : ℝ) ^ kv * volFac)
    (hcSample : ∀ N : ℕ, (cSample N : ℝ)
      ≤ 2 ^ 62 * (N : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R))
    (hm : ∀ N : ℕ, (toDNFd (preprocess (atoms N) (φ N))).length ≤ mBound) :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ttcComplexity (atoms N) (φ N) ε δ (cVol N) (cSample N))
      (fun N : ℕ => (N : ℝ) ^ K) := by
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hRg0 : (0 : ℝ) < R ^ 2 / γ ^ 2 :=
    div_pos (pow_pos (by linarith) 2) (pow_pos hγ0 2)
  have hB : (0 : ℝ) ≤ 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hRg0.le) hlog0
  have hCV0 : (0 : ℝ) ≤ Cv * volFac := mul_nonneg hCv hvolFac
  refine Asymptotics.IsBigO.of_bound
    ((mBound : ℝ) * (Cv * volFac
      + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
          * threshFactor ε δ mBound)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hb := ttcComplexity_le_poly (atoms N) (φ N) ε δ (cVol N) (cSample N) K kv hN hkv h4K
    hCv hvolFac hrfac hR1 hγ0 hε0 hε1 hδ0 hδ1 (hcVol N) (hcSample N)
  rw [Real.norm_of_nonneg
        (ttcComplexity_nonneg (atoms N) (φ N) ε δ (cVol N) (cSample N) hε0 hε1 hδ0 hδ1),
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ K)]
  refine hb.trans ?_
  set mm : ℕ := (toDNFd (preprocess (atoms N) (φ N))).length with hmm
  have hmle : (mm : ℝ) ≤ (mBound : ℝ) := by exact_mod_cast hm N
  have hTle : threshFactor ε δ mm ≤ threshFactor ε δ mBound :=
    threshFactor_mono_m ε δ (hm N)
  have hT1 : 1 ≤ threshFactor ε δ mm := one_le_threshFactor ε δ mm hε0 hε1 hδ0 hδ1
  have hnK0 : (0 : ℝ) ≤ (N : ℝ) ^ K := by positivity
  have hX0 : (0 : ℝ) ≤ Cv * volFac
      + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * threshFactor ε δ mm :=
    add_nonneg hCV0 (mul_nonneg hB (by linarith))
  have hXle : Cv * volFac
        + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * threshFactor ε δ mm
      ≤ Cv * volFac
        + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * threshFactor ε δ mBound := by
    have := mul_le_mul_of_nonneg_left hTle hB
    linarith
  calc (mm : ℝ) * (N : ℝ) ^ K
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * threshFactor ε δ mm)
      ≤ (mBound : ℝ) * (N : ℝ) ^ K
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * threshFactor ε δ mm) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmle hnK0) hX0
    _ ≤ (mBound : ℝ) * (N : ℝ) ^ K
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * threshFactor ε δ mBound) :=
        mul_le_mul_of_nonneg_left hXle (mul_nonneg (Nat.cast_nonneg _) hnK0)
    _ = (mBound : ℝ) * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * threshFactor ε δ mBound) * (N : ℝ) ^ K := by ring

/-- **`O(n⁴)` — the tight form, when the volume oracle is `O(n^{kv})` with `kv ≤ 4`.** -/
theorem isBigO_ttcComplexity_quartic {Af : ℕ → Type*}
    (atoms : ∀ N, Af N → LinAtom N) (φ : ∀ N, BForm (Af N))
    (ε δ : ℝ) (cVol cSample : ℕ → ℕ) (kv mBound : ℕ) (hkv : kv ≤ 4)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcVol : ∀ N : ℕ, (cVol N : ℝ) ≤ Cv * (N : ℝ) ^ kv * volFac)
    (hcSample : ∀ N : ℕ, (cSample N : ℝ)
      ≤ 2 ^ 62 * (N : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R))
    (hm : ∀ N : ℕ, (toDNFd (preprocess (atoms N) (φ N))).length ≤ mBound) :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ttcComplexity (atoms N) (φ N) ε δ (cVol N) (cSample N))
      (fun N : ℕ => (N : ℝ) ^ 4) :=
  isBigO_ttcComplexity_poly atoms φ ε δ cVol cSample 4 kv mBound hkv le_rfl hCv hvolFac
    hrfac hR1 hγ0 hε0 hε1 hδ0 hδ1 hcVol hcSample hm

/-- **`O(n⁵)` — the brief's target, and a strictly weaker statement than
`Ttc.PolyComplexity.isBigO_ttcComplexity_quartic` whenever `kv ≤ 4`.**

Kept beside the quartic form for the same reason `Ttc.SamplerCost.isBigO_samplePrice_quintic`
is kept beside `Ttc.SamplerCost.isBigO_samplePrice_quartic`: so that the relationship
between the two claims lives in the development and not only in prose. -/
theorem isBigO_ttcComplexity_quintic {Af : ℕ → Type*}
    (atoms : ∀ N, Af N → LinAtom N) (φ : ∀ N, BForm (Af N))
    (ε δ : ℝ) (cVol cSample : ℕ → ℕ) (kv mBound : ℕ) (hkv : kv ≤ 5)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcVol : ∀ N : ℕ, (cVol N : ℝ) ≤ Cv * (N : ℝ) ^ kv * volFac)
    (hcSample : ∀ N : ℕ, (cSample N : ℝ)
      ≤ 2 ^ 62 * (N : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R))
    (hm : ∀ N : ℕ, (toDNFd (preprocess (atoms N) (φ N))).length ≤ mBound) :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ttcComplexity (atoms N) (φ N) ε δ (cVol N) (cSample N))
      (fun N : ℕ => (N : ℝ) ^ 5) :=
  isBigO_ttcComplexity_poly atoms φ ε δ cVol cSample 5 kv mBound hkv (by norm_num) hCv
    hvolFac hrfac hR1 hγ0 hε0 hε1 hδ0 hδ1 hcVol hcSample hm

/-- **`O(n⁴) ⊆ O(n⁵)`, formally** — so that "the `n⁵` bound is loose" is a machine-checked
relation between the two corollaries, not an assertion.  Combined with
`Ttc.PolyComplexity.isBigO_ttcComplexity_quartic` it *derives*
`Ttc.PolyComplexity.isBigO_ttcComplexity_quintic`.

⚠ This says `n⁵` is an upper bound implied by the `n⁴` one.  It does **not** say `n⁵` is
attained: no lower bound on `Ttc.ttcComplexity` is proved anywhere in this repository. -/
theorem isBigO_pow_succ (K : ℕ) :
    Asymptotics.IsBigO Filter.atTop (fun N : ℕ => (N : ℝ) ^ K)
      (fun N : ℕ => (N : ℝ) ^ (K + 1)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ K),
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (K + 1))]
  have : (N : ℝ) ^ K ≤ (N : ℝ) ^ (K + 1) := pow_le_pow_right₀ hN1 (Nat.le_succ K)
  linarith

end Asymptotic

/-! ## §4 — non-vacuity (`CLAUDE.md` §11)

A `∀`-statement over unsatisfiable hypotheses proves nothing, and a bound of `0` on a
quantity that is `0` proves nothing either.  `Ttc.PolyComplexity.exists_nondegenerate_bound`
exhibits **one** assignment satisfying *every* hypothesis of
`Ttc.PolyComplexity.ttcComplexity_le_poly` simultaneously, at which the cube count `m`,
the bounded quantity `Ttc.ttcComplexity`, and the bound itself are all **strictly
positive**.

The formula used is `φ = ⊤` in dimension `1`, whose preprocessing survives intact: the
empty cube is not void, has no vacuous literal, and its region is all of `ℝ¹` — hence
full-dimensional.  The five small lemmas below are that computation; nothing about them
is asymptotic.

**Not covered, and stated so.**  This witness inhabits the hypothesis bundle of
`Ttc.PolyComplexity.ttcComplexity_le_poly` — the *arithmetic* one — and of nothing else.
It does **not** inhabit `Ttc.HitAndRunTheorem11Input` and does not construct an oracle
achieving either price.

**In particular it does NOT witness `Ttc.PolyComplexity.ttcCost_le_poly`**, whose bundle
is strictly larger: it adds `hφ : φ.IsPositive`, `hpos : 0 < volSol (atomSet atoms) φ`,
the run data `c, t`, and `hterm : Ttc.ttcTerminates …`.  And the failure is not an
oversight that a better witness would fix cheaply: `φ = ⊤` **provably** fails `hpos`,
because `Sol(⊤) = ℝⁿ` has infinite Lebesgue measure and `Ttc.volSol` is `(·).toReal`, so
`volSol M ⊤ = 0`.  That is `Ttc.PolyComplexity.volSol_tt_eq_zero` below, machine-checked
rather than asserted.  A witness for `ttcCost_le_poly` would need a *bounded*,
full-dimensional formula **and** a discharge of `hterm`, which is not available as
`alg:ttc` stands (`Ttc/Exec/Complexity.lean`, "The `Ttc.ttcTerminates` guard is still
there").  So `ttcCost_le_poly` is stated here **without** a non-vacuity witness, and this
paragraph is that disclosure. -/

section Witness

/-- The region of the **empty** cube is everything: it constrains nothing. -/
theorem region_nil (M : A → Set (Space n)) : region M ([] : Cube A) = Set.univ := by
  ext x
  simp [region, Cube.holds]

/-- The DNF of `⊤`, deduplicated, is the one-element list containing the empty cube. -/
theorem toDNFd_tt : toDNFd (.tt : BForm A) = [([] : Cube A)] := by
  simp [toDNFd, toDNF, dnfAux]

/-- **Line A2 keeps the empty cube**: its region is `Set.univ`, whose interior is
nonempty (`Space n` has a point). -/
theorem nondegenCubes_singleton_nil (M : A → Set (Space n)) :
    nondegenCubes M [([] : Cube A)] = [([] : Cube A)] := by
  have hne : (interior (region M ([] : Cube A))).Nonempty := by
    rw [region_nil, interior_univ]
    exact Set.univ_nonempty
  rw [nondegenCubes, List.filter_eq_self]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  simp only [decide_eq_true_eq]
  exact hne

/-- **Lines A4–A5 keep the empty cube unchanged**: it holds no zero-normal literal with a
negative bound (it holds no literal at all), so it is not void, and it has no vacuous
literal to delete. -/
theorem cleanDNF_singleton_nil (atoms : A → LinAtom n) :
    cleanDNF atoms [([] : Cube A)] = [([] : Cube A)] := by
  have hv : ¬ VoidCube atoms ([] : Cube A) := by
    rintro ⟨l, hl, -⟩
    exact (List.not_mem_nil (a := l)) hl
  rw [cleanDNF, List.filter_eq_self.2, List.map_singleton, cleanCube, List.filter_nil]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  exact hv

/-- **`⊤` is a fixed point of the preprocessing**, and its DNF has exactly one cube. -/
theorem preprocess_tt (atoms : A → LinAtom n) :
    preprocess atoms (.tt : BForm A) = .tt := by
  rw [preprocess, pruneForm, toDNFd_tt, nondegenCubes_singleton_nil,
    show dnfForm [([] : Cube A)] = (.tt : BForm A) from rfl, cleanForm, toDNFd_tt,
    cleanDNF_singleton_nil]
  rfl

/-- **The witness formula provably fails `Ttc.PolyComplexity.ttcCost_le_poly`'s `hpos`.**

`Sol(⊤) = ℝⁿ`, whose Lebesgue measure is `∞`, and `Ttc.volSol` is `(·).toReal` — so
`volSol M ⊤ = 0` under Mathlib's `(⊤ : ℝ≥0∞).toReal = 0` convention.  Stated at `n = 1`,
the witness's dimension.  This is why §4's disclosure paragraph says `ttcCost_le_poly` has
no non-vacuity witness here rather than merely omitting one. -/
theorem volSol_tt_eq_zero (M : A → Set (Space 1)) : volSol M (.tt : BForm A) = 0 := by
  have hs : sol M (.tt : BForm A) = Set.univ := by
    ext x
    simp [sol, BForm.holds]
  rw [volSol, hs]
  simp

/-- **`m = 1` at the witness formula.** -/
theorem length_toDNFd_preprocess_tt (atoms : A → LinAtom n) :
    (toDNFd (preprocess atoms (.tt : BForm A))).length = 1 := by
  rw [preprocess_tt, toDNFd_tt]
  rfl

set_option maxRecDepth 100000 in
/-- **Every hypothesis of `Ttc.PolyComplexity.ttcComplexity_le_poly` is satisfiable at
once, with `m`, the bounded quantity and the bound all strictly positive.**

The witness: `A = Empty`, `φ = ⊤`, `n = 1`, `K = kv = 4`, `ε = δ = Cv = volFac = rfac =
R = γ = 1`, `cVol = cSample = 1`.  `hcSample` holds there because `2^62·log 2 ≥ 1`. -/
theorem exists_nondegenerate_bound :
    ∃ (A : Type) (n : ℕ) (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
      (cVol cSample K kv : ℕ) (Cv volFac rfac R γ : ℝ),
      1 ≤ n ∧ kv ≤ K ∧ 4 ≤ K ∧ 0 ≤ Cv ∧ 0 ≤ volFac ∧ 1 ≤ rfac ∧ 1 ≤ R ∧ 0 < γ ∧
      0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧
      (cVol : ℝ) ≤ Cv * (n : ℝ) ^ kv * volFac ∧
      (cSample : ℝ) ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) ∧
      0 < (toDNFd (preprocess atoms φ)).length ∧
      0 < ttcComplexity atoms φ ε δ cVol cSample ∧
      0 < ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ K
            * (Cv * volFac
                + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                    * threshFactor ε δ (toDNFd (preprocess atoms φ)).length) := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hsample : (1 : ℝ)
      ≤ 2 ^ 62 * (1 : ℝ) ^ 4 * 1 * ((1 : ℝ) ^ 2 / (1 : ℝ) ^ 2) * Real.log (2 * 1) := by
    rw [show (2 : ℝ) * 1 = 2 by norm_num]
    nlinarith
  refine ⟨Empty, 1, fun a => a.elim, .tt, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1,
    le_refl 1, le_refl 4, le_refl 4, zero_le_one, zero_le_one, le_refl 1, le_refl 1,
    one_pos, one_pos, le_refl 1, one_pos, le_refl 1, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hsample
  · rw [length_toDNFd_preprocess_tt]; norm_num
  · rw [ttcComplexity_eq, length_toDNFd_preprocess_tt]
    have hT := one_le_threshFactor (1 : ℝ) 1 1 one_pos le_rfl one_pos le_rfl
    push_cast
    nlinarith
  · rw [length_toDNFd_preprocess_tt]
    have hT := one_le_threshFactor (1 : ℝ) 1 1 one_pos le_rfl one_pos le_rfl
    push_cast
    nlinarith

end Witness

end Ttc.PolyComplexity

/-! ## Axiom profile -/

#print axioms Ttc.PolyComplexity.threshFactor
#print axioms Ttc.PolyComplexity.ttcComplexity_eq
#print axioms Ttc.PolyComplexity.one_le_threshFactor
#print axioms Ttc.PolyComplexity.threshFactor_mono_m
#print axioms Ttc.PolyComplexity.ttcComplexity_nonneg
#print axioms Ttc.PolyComplexity.ttcComplexity_le_poly
#print axioms Ttc.PolyComplexity.ttcComplexity_le_quartic
#print axioms Ttc.PolyComplexity.ttcComplexity_le_quintic
#print axioms Ttc.PolyComplexity.ttcComplexity_le_poly_single_constant
#print axioms Ttc.PolyComplexity.ttcCost_le_poly
#print axioms Ttc.PolyComplexity.isBigO_ttcComplexity_poly
#print axioms Ttc.PolyComplexity.isBigO_ttcComplexity_quartic
#print axioms Ttc.PolyComplexity.isBigO_ttcComplexity_quintic
#print axioms Ttc.PolyComplexity.isBigO_pow_succ

/-! ### §4 — non-vacuity -/

#print axioms Ttc.PolyComplexity.region_nil
#print axioms Ttc.PolyComplexity.toDNFd_tt
#print axioms Ttc.PolyComplexity.nondegenCubes_singleton_nil
#print axioms Ttc.PolyComplexity.cleanDNF_singleton_nil
#print axioms Ttc.PolyComplexity.preprocess_tt
#print axioms Ttc.PolyComplexity.volSol_tt_eq_zero
#print axioms Ttc.PolyComplexity.length_toDNFd_preprocess_tt
#print axioms Ttc.PolyComplexity.exists_nondegenerate_bound

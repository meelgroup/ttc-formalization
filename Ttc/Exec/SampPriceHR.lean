/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.SamplerCost
import Ttc.Exec.SampleDischarge

/-!
# `Exec/SampPriceHR`: the hit-and-run per-sample price, as a function of the run's own inputs

> ## ⚠ TWO WARNINGS, BOTH LOAD-BEARING ⚠
>
> **1. Nothing charges this price.**  Until 2026-08-19 `Ttc.ttc` was the algorithm at
> *reference* oracles, charged at two fixed per-call numbers, and `Ttc.ttcSampPriceHR` was
> the hit-and-run one — a modelling choice rather than a bound, because the run's own
> sampler was the lazy ball walk and no lemma related the two.  That version of `Ttc.ttc`
> and both fixed charges were deleted.  `Ttc.ttc` (`Model/Theorem`) now *executes* the
> hit-and-run / ball-walk hybrid, and what `Ttc.ttc_volume` bounds is
> `Ttc.TTCSourceSharpOperationalFinal.canonicalCappedSampleQueryEnvelope` — the expected
> query count of the sampler the run actually takes steps in, which is **not** this number.
> `Ttc.ttcSampPriceHR` is now an unconsumed definition: correct arithmetic at the run's own
> geometry, priced against `cor:linf`, charged to nothing.  Do not quote it as the run's
> sampling cost.
>
> What *is* still consumed from this file is the geometry —
> `Ttc.ttcSampInradius`, `Ttc.ttcSampDiamPrice`, `Ttc.ttcSampWarm`, `Ttc.ttcSampTol` — read
> by `Ttc/Exec/TTCSourceSharpOperationalFinal.lean` to instantiate the hybrid sampler at the
> run's own body.  Those are load-bearing; the price built on top of them is not.
>
> **2. Everything here is conditional on an unproved mixing theorem.**  The step count
> inside `Ttc.SamplerCost.samplePrice` is `Ttc.hitAndRunTheorem11Steps`, whose *meaning*
> is Lovász–Vempala Theorem 1.1 — the structure `Ttc.HitAndRunTheorem11Input`, which is
> **assumed and inhabited nowhere in this development**, and which rests on the
> weighted-isoperimetry argument and thence on `hLS` (Lovász–Simonovits 1993, Cor. 1.5),
> unproved here.  As *arithmetic* the definition and every inequality below are
> unconditional; as a *cost* they are conditional.  This is a second, independent reason not
> to quote the number, and it is why `Ttc.ttc_volume`'s sampler envelope goes through
> `Ttc.hybridTransitionBound` — which branches at dimension 1100 into `cor:linf` above and
> the ball walk's own certified bound below — rather than through this file.

## What this file adds

`Ttc.SamplerCost.samplePrice n γ R M ε' rfac` (`Exec/SamplerCost`) prices one hit-and-run
draw as a function of six *free* parameters.  `Ttc.ttc_volume` cannot carry such a
thing *as a named constant*: its statement may only mention constants defined under
`Ttc/Model/`, `Ttc/Probability/` or `Ttc/Geometry/` (`Ttc.Audit.auditSurface`, enforced by
`#modelClosureOfType`).  This file removes the six binders by instantiating each at the
run's **own** data, exactly as `Exec/SamplePrice` does for the ball walk.

(This paragraph used to explain how the headline carried the price: first as free geometry
binders, then as a surface-side copy `Ttc.hrSampPriceAt` charged inside a four-ary
`Ttc.ttc`.  Both arrangements are gone.  The headline carries no price at all now — it
carries the *envelope* of the sampler the run executes, and this file's remaining job is the
geometry that envelope is instantiated at.)

```
ttcSampPriceHR atoms φ ε δ
  = SamplerCost.samplePrice n
      (ttcSampInradius   atoms φ ε δ)   -- γ    = 10^ρ·γ̂ + κ, the inflated inradius
      (ttcSampDiamPrice  atoms φ ε δ)   -- R    = (1 + κ/(10^ρ·γ̂))·diam(10^ρ · Sol)
      (ttcSampWarmPrice  atoms φ ε δ)   -- M    = the uniform warmness
      (algBlock atoms φ ε δ).epsPrime   -- ε'   = ε/12
      (canonRfac (toDNFd (preprocess atoms φ)))   -- rfac = the facet count
```

Every substitution is a quantity the algorithm computes from `(atoms, φ, ε, δ)`; nothing is
invented.  The three geometric ones are the very values `Exec/InflateBound` built for the
ball-walk price, so the two prices are stated at the *same* geometry.

**`R` is a diameter bound where `Ttc.SamplerCost.samplePrice` calls for a circumradius.**
That is conservative in the safe direction (a bounded set's circumradius is at most its
diameter), and it is the largest of the algorithm-derived length scales, so no inequality
below is weakened by it.

## What is *not* here, and why that is honest

`Ttc/Exec/SamplePrice.lean` used to carry `Ttc.ttcSampleSteps_le_ttcSampPrice` — the lemma
that made the *ball-walk* number a price rather than a numeral — and there was no analogue
here, because the run's own chain was the ball walk and nothing in it took a hit-and-run
step.  That file was deleted with the reference oracles on 2026-08-19, and the asymmetry it
recorded is gone with it: there is now no dominance lemma for either number, because
`Ttc.ttc` charges neither.  What dominates the run's sampler work is
`Ttc.TTCSourceSharpOperationalFinal.canonicalCappedSampleQueryEnvelope`, proved about the
hybrid the run executes.  This number remains the price of an oracle the development
*models*, under a theorem the development *assumes*.

The name `ttcSampPriceHR` therefore promises no semantic identity beyond "the arithmetic
`Ttc.SamplerCost.samplePrice` evaluates to at the run's own data", and
`Ttc.ttcSampPriceHR_def` proves exactly that by `rfl`.
-/

namespace Ttc

open MeasureTheory Metric Set
open scoped Pointwise

variable {A : Type*} {n : ℕ}

section AtTheRun

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The hit-and-run per-sample price at the run's own data**, in arithmetic operations.

`Ttc.SamplerCost.samplePrice` at the five algorithm-derived values listed in the module
docstring.  A plain arithmetic `def`: its name claims nothing beyond
`Ttc.ttcSampPriceHR_def`, and in particular it does **not** claim to bound anything
`Ttc.ttc` does — see the module docstring's first warning. -/
noncomputable def ttcSampPriceHR : ℕ :=
  SamplerCost.samplePrice n (ttcSampInradius atoms φ ε δ) (ttcSampDiamPrice atoms φ ε δ)
    (ttcSampWarmPrice atoms φ ε δ) (algBlock atoms φ ε δ).epsPrime
    (canonRfac (toDNFd (preprocess atoms φ)))

theorem ttcSampPriceHR_def :
    ttcSampPriceHR atoms φ ε δ =
      SamplerCost.samplePrice n (ttcSampInradius atoms φ ε δ) (ttcSampDiamPrice atoms φ ε δ)
        (ttcSampWarmPrice atoms φ ε δ) (algBlock atoms φ ε δ).epsPrime
        (canonRfac (toDNFd (preprocess atoms φ))) := rfl

/-- **The price with the `Exec/` names one layer down**, by `rfl`: `Ttc.SamplerCost.samplePrice`
unfolded to its arithmetic — `⌊threshold⌋₊ + 1` transitions plus the two post-processing units
of `Ttc.SamplerCost.drawOpCharge`, each at `⌈n · rfac⌉₊` operations, with the worst-case
tolerance `ε'/(4·(2R)ⁿ)` in place.

This is the intermediate step to `Ttc.ttcSampPriceHR_model`; it is stated separately because
it is the readable one. -/
theorem ttcSampPriceHR_unfold :
    ttcSampPriceHR atoms φ ε δ =
      (⌊2 ^ 56 * (n : ℝ) ^ 2 * ttcSampDiamPrice atoms φ ε δ ^ 2
            / ttcSampInradius atoms φ ε δ ^ 2
          * Real.log (8 * ttcSampWarmPrice atoms φ ε δ
              / ((algBlock atoms φ ε δ).epsPrime
                  / (4 * (2 * ttcSampDiamPrice atoms φ ε δ) ^ n)) ^ 2)⌋₊ + 1 + 2)
        * ⌈(n : ℝ) * canonRfac (toDNFd (preprocess atoms φ))⌉₊ := rfl

/-! ## The hypotheses of `Ttc.SamplerCost.samplePrice_le_quartic`, discharged

Seven of the ten are theorems of the development at the run's own data; three are not, and
are carried as visible binders of `Ttc.ttcSampPriceHR_le_quartic`.  See that theorem's
docstring for the ledger. -/

/-- **The preprocessed DNF has a cube** — `Ttc.toDNFd_ne_nil` at `Ttc.ttcInput_isPositive`.
Three of the discharges below are per-cube facts of `Exec/SampleDischarge` composed with
per-cube upper bounds of `Exec/InflateBound`, and need a cube to compose them at; any cube
does, since neither side of the composition mentions one. -/
theorem exists_mem_toDNFd_ttcInput : ∃ c : Cube A, c ∈ toDNFd (ttcInput atoms φ) :=
  List.exists_mem_of_ne_nil _ (toDNFd_ne_nil (ttcInput_isPositive atoms φ))

/-- **`hγR`, discharged: the inflated inradius is at most the uniform diameter price.**
`Ttc.ttcSampInradius_le_ttcSampDiam` (`Exec/SampleDischarge`) at any cube, then
`Ttc.ttcSampDiam_le` (`Exec/InflateBound`) to drop the cube. -/
theorem ttcSampInradius_le_ttcSampDiamPrice (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcSampInradius atoms φ ε δ ≤ ttcSampDiamPrice atoms φ ε δ := by
  obtain ⟨c, hc⟩ := exists_mem_toDNFd_ttcInput atoms φ
  exact le_trans (ttcSampInradius_le_ttcSampDiam atoms φ ε δ hε0 hε1 hn hφ hpos ⟨c, hc⟩)
    (ttcSampDiam_le atoms φ ε δ hε0 hε1 hn hφ hpos ⟨c, hc⟩)

/-- **`hR1`, discharged: the uniform diameter price is at least `1`.**  In fact at least
`64n`: `Ttc.dim_le_ttcSampStep` (`Exec/SampleDischarge` §5) bounds the ball-walk step below
by `64n`, the step is at most the inflated inradius
(`Ttc.ttcSampStep_le_ttcSampInradius`), and that is at most the diameter price. -/
theorem one_le_ttcSampDiamPrice (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    1 ≤ ttcSampDiamPrice atoms φ ε δ := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h64 := dim_le_ttcSampStep atoms φ ε δ hε0 hε1 hn hφ hpos
  have hstep := ttcSampStep_le_ttcSampInradius atoms φ ε δ
  have hdiam := ttcSampInradius_le_ttcSampDiamPrice atoms φ ε δ hε0 hε1 hn hφ hpos
  linarith

/-- **`hM1`, discharged: the uniform warmness price is at least `1`.**
`Ttc.one_le_ttcSampWarm` (`Exec/SampleDischarge`) at any cube, then `Ttc.ttcSampWarm_le`
(`Exec/InflateBound`) to drop the cube. -/
theorem one_le_ttcSampWarmPrice (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    1 ≤ ttcSampWarmPrice atoms φ ε δ := by
  obtain ⟨c, hc⟩ := exists_mem_toDNFd_ttcInput atoms φ
  exact le_trans (one_le_ttcSampWarm atoms φ ε δ hε0 hε1 hn hφ hpos ⟨c, hc⟩)
    (ttcSampWarm_le atoms φ ε δ hε0 hε1 hn hφ hpos ⟨c, hc⟩)

/-- **`heps1`, discharged: `ε' = ε/12 ≤ 1`.**  Every `Ttc.Params` carries `0 < ε ≤ 1`
(`Ttc.Params.hε0`, `Ttc.Params.hε1`), so this holds on *either* branch of
`Ttc.ttcParamsTotal` and needs no hypothesis on the input at all. -/
theorem algBlock_epsPrime_le_one : (algBlock atoms φ ε δ).epsPrime ≤ 1 := by
  have h0 := (algBlock atoms φ ε δ).hε0
  have h1 := (algBlock atoms φ ε δ).hε1
  show (algBlock atoms φ ε δ).ε / 12 ≤ 1
  linarith

/-! ## The `n⁴` bound at the run's own data -/

/-- **THE BOUND: `2⁶² · n⁴ ·` (three algorithm-derived factors).**

```
ttcSampPriceHR atoms φ ε δ
  ≤ 2⁶² · n⁴ · r · (R²/γ²) · log(2R)
r = canonRfac (toDNFd (preprocess atoms φ))          the facet count
R = ttcSampDiamPrice atoms φ ε δ                     (1 + κ/(10^ρ·γ̂))·diam(10^ρ · Sol)
γ = ttcSampInradius  atoms φ ε δ                     10^ρ·γ̂ + κ
```

`Ttc.SamplerCost.samplePrice_le_quartic` at the run's own five values.  Nothing is hidden in
an `O(·)`: every suppressed factor of `thm:runtime` is printed on the right, and every one of
them is a function of `(atoms, φ, ε, δ)` alone.  Suppressing `r`, `R²/γ²` and `log R` leaves
`O(n⁴)` operations per sample.

### The hypothesis ledger

**Discharged from the algorithm's own invariants** (so *not* binders here):

| `samplePrice_le_quartic` | discharged by |
| --- | --- |
| `hγ0 : 0 < γ` | `Ttc.ttcSampInradius_pos` |
| `hR1 : 1 ≤ R` | `Ttc.one_le_ttcSampDiamPrice` (in fact `64n ≤ R`) |
| `hγR : γ ≤ R` | `Ttc.ttcSampInradius_le_ttcSampDiamPrice` |
| `hM1 : 1 ≤ M` | `Ttc.one_le_ttcSampWarmPrice` |
| `heps0 : 0 < ε'` | `Ttc.algBlock_epsPrime_pos` (`Exec/PriceList`) |
| `heps1 : ε' ≤ 1` | `Ttc.algBlock_epsPrime_le_one` |
| `hn : 1 ≤ n` | a binder of the headline already |

**Carried, because the development does not prove them:**

* `hrfac : 1 ≤ r` — `Ttc.canonRfac` is `Nat.card (FacetIndex D)`, which is `0` for an
  empty facet set; the development carries the identical hypothesis elsewhere
  (`Ttc.Exec.Endgoal`'s `hr : 1 ≤ Nat.card (FacetIndex (toDNF φ))`).  It is very likely
  *provable* at the run's data rather than assumed — `Ttc.toDNFd_ne_nil` gives a cube, and
  a cube with **no** literals has `region = univ` (`Ttc.region` is `{x | c.holds …}` over an
  empty conjunction), which contradicts the boundedness `Ttc.ttcInput_bdd` derives from
  `hφ` and `hpos`; with `Nat.card_pos` that closes it.  Not carried out here, and flagged
  rather than assumed away;
* `hMB : M ≤ (2R)ⁿ` — the warm-start bound.  `Exec/SamplerCost`'s docstring calls the
  warm start "a genuine open hypothesis" and nothing in this repository constructs one;
* `hepsn : 2⁻ⁿ ≤ ε'` — `cor:linf`'s own regime `ε ≥ 2⁻ⁿ`, here `ε ≥ 12·2⁻ⁿ`.  It is a
  condition on the *input pair* `(ε, n)`, not something the algorithm can establish.

⚠ Conditional on `Ttc.HitAndRunTheorem11Input` for its meaning, and about an oracle
`Ttc.ttc` does not call — module docstring. -/
theorem ttcSampPriceHR_le_quartic (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (hrfac : 1 ≤ canonRfac (toDNFd (preprocess atoms φ)))
    (hMB : ttcSampWarmPrice atoms φ ε δ ≤ (2 * ttcSampDiamPrice atoms φ ε δ) ^ n)
    (hepsn : 1 / 2 ^ n ≤ (algBlock atoms φ ε δ).epsPrime) :
    (ttcSampPriceHR atoms φ ε δ : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * canonRfac (toDNFd (preprocess atoms φ))
          * (ttcSampDiamPrice atoms φ ε δ ^ 2 / ttcSampInradius atoms φ ε δ ^ 2)
          * Real.log (2 * ttcSampDiamPrice atoms φ ε δ) :=
  SamplerCost.samplePrice_le_quartic n hn hrfac
    (one_le_ttcSampDiamPrice atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcSampInradius_le_ttcSampDiamPrice atoms φ ε δ hε0 hε1 hn hφ hpos)
    (one_le_ttcSampWarmPrice atoms φ ε δ hε0 hε1 hn hφ hpos)
    hMB (algBlock_epsPrime_pos atoms φ ε δ) (algBlock_epsPrime_le_one atoms φ ε δ) hepsn

set_option maxHeartbeats 4000000 in
/-- **The price, spelled out in `Ttc/Model/` vocabulary**, by `rfl` — the form a headline
statement can carry.

Every `Ttc` constant below is defined under `Ttc/Model/` or `Ttc/Geometry/` — `Ttc.algBlock`,
`Ttc.algPrec`, `Ttc.algGamma`, `Ttc.algScale`, `Ttc.algAtoms`, `Ttc.latticeScale`,
`Ttc.toDNFd`, `Ttc.preprocess`, `Ttc.sol`, `Ttc.atomSet`, `Ttc.volSol`, `Ttc.Space`,
`Ttc.canonRfac` — the only non-`Ttc` names being Mathlib's and `Arlib.KV97.kappaOf`/`cOf`.
That is what would let `Ttc.ttc_volume` carry this expression in its *statement*
without `#modelClosureOfType` (`Audit/ClosureCheck`) going red, exactly as it carries
`Ttc.ttcVolPrice`'s and `Ttc.ttcSampPrice`'s bodies.  Note what is **absent**:
`Ttc.SamplerCost.samplePrice`, `Ttc.hitAndRunTheorem11Steps` and
`Ttc.hitAndRunTheorem11Threshold` all live outside the audit surface, and unfolding them is
the whole point of this lemma.

Reading it: `⌊2⁵⁶ n² R²/γ² · log(8M/ν²)⌋₊ + 1` transitions plus `2` post-processing units, at
`⌈n·r⌉₊` operations each, with `ν = ε'/(4·(2R)ⁿ)` the worst-case TV tolerance. -/
theorem ttcSampPriceHR_model :
    ttcSampPriceHR atoms φ ε δ =
      (⌊2 ^ 56 * (n : ℝ) ^ 2 * ((1 +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))) /
        (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) *
        Metric.diam (latticeScale (algPrec atoms φ ε δ) •
        sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2 /
        (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ)))) ^ 2 *
        Real.log (8 * (((1 +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))) /
        (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) ^ n *
        (latticeScale (algPrec atoms φ ε δ) ^ n *
        (algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ))) /
        (volume (Metric.ball (0 : Space n)
        (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ)))))).toReal) /
        ((algBlock atoms φ ε δ).epsPrime / (4 * (2 * ((1 +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))) /
        (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) *
        Metric.diam (latticeScale (algPrec atoms φ ε δ) •
        sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)))) ^ n)) ^ 2)⌋₊ + 1 + 2) *
        ⌈(n : ℝ) * canonRfac (toDNFd (preprocess atoms φ))⌉₊
      := rfl

/-! ## Non-vacuity (`CLAUDE.md` §11)

A `∀`-statement over unsatisfiable hypotheses proves nothing, and a price that is `0` prices
nothing.  Two facts below, and one gap stated rather than papered over.

**What is proved.**  `Ttc.ttcSampPriceHR_pos`: the price is a genuine positive natural
(indeed at least `3`) whenever `1 ≤ n` and `1 ≤ r`.
`Ttc.ttcSampPriceHR_discharged_hypotheses`: the **seven** hypotheses of
`Ttc.SamplerCost.samplePrice_le_quartic` this file discharges hold *simultaneously* at every
input satisfying the headline's own five conditions — so no contradiction hides among them,
and the only way `Ttc.ttcSampPriceHR_le_quartic` could be vacuous is through its three
remaining binders.

**The gap, stated plainly.**  There is **no witness here exhibiting concrete `atoms`, `φ`,
`ε`, `δ` that satisfy the three carried binders**, so this file does *not* certify
`Ttc.ttcSampPriceHR_le_quartic` non-vacuous.  Two obstacles, both real:

* `hMB : M ≤ (2R)ⁿ` is the warm-start bound, which nothing in this repository proves at any
  data, concrete or otherwise (`Exec/SamplerCost`: "nothing in this repository constructs a
  warm start, so this is a genuine open hypothesis");
* `hrfac` and `hMB` are statements about `toDNFd (preprocess atoms φ)` — the DNF *after*
  `Ttc.pruneForm` and `Ttc.cleanForm` — and `Ttc/Witness/TwoCube.lean`, the development's
  concrete input, is built against `Ttc.toDNF (twoForm n)`, the DNF *before* preprocessing.
  Evaluating the facet count, the diameter and the warmness of the preprocessed pipeline at
  concrete atoms is a separate piece of work.

`Ttc.SamplerCost.exists_nondegenerate_price` (`Exec/SamplerCost`) shows the same hypothesis
bundle is satisfiable by *reals* — `n = 1`, `γ = R = M = rfac = 1`, `ε' = 1/2` — which is
evidence that the bundle is consistent, and is **not** evidence that any TTC input meets it. -/

/-- **The price is positive** — at least `3`, since `Ttc.hitAndRunTheorem11Steps` is a
`Nat.floor` *plus one* and `Ttc.SamplerCost.drawOpCharge` adds two more units, each costing
`⌈n·r⌉₊ ≥ 1` operations.  The mirror of `Ttc.SamplerCost.exists_nondegenerate_price`'s
final conjunct, at the run's own data. -/
theorem ttcSampPriceHR_pos (hn : 1 ≤ n)
    (hrfac : 1 ≤ canonRfac (toDNFd (preprocess atoms φ))) :
    0 < ttcSampPriceHR atoms φ ε δ := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : 0 < (n : ℝ) * canonRfac (toDNFd (preprocess atoms φ)) := by nlinarith
  have hc : 0 < ⌈(n : ℝ) * canonRfac (toDNFd (preprocess atoms φ))⌉₊ := Nat.ceil_pos.2 h
  rw [ttcSampPriceHR_unfold]
  exact Nat.mul_pos (by omega) hc

/-- **The six discharged *inequalities*, simultaneously, at any admissible input** — the
seventh discharge, `hn : 1 ≤ n`, is a binder of this lemma rather than a conjunct.  Each
conjunct is one binder `Ttc.ttcSampPriceHR_le_quartic` does *not* have; together they say the
discharged half of `Ttc.SamplerCost.samplePrice_le_quartic`'s bundle is consistent at every
input the headline already admits. -/
theorem ttcSampPriceHR_discharged_hypotheses (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    0 < ttcSampInradius atoms φ ε δ ∧
      1 ≤ ttcSampDiamPrice atoms φ ε δ ∧
      ttcSampInradius atoms φ ε δ ≤ ttcSampDiamPrice atoms φ ε δ ∧
      1 ≤ ttcSampWarmPrice atoms φ ε δ ∧
      0 < (algBlock atoms φ ε δ).epsPrime ∧
      (algBlock atoms φ ε δ).epsPrime ≤ 1 :=
  ⟨ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos,
    one_le_ttcSampDiamPrice atoms φ ε δ hε0 hε1 hn hφ hpos,
    ttcSampInradius_le_ttcSampDiamPrice atoms φ ε δ hε0 hε1 hn hφ hpos,
    one_le_ttcSampWarmPrice atoms φ ε δ hε0 hε1 hn hφ hpos,
    algBlock_epsPrime_pos atoms φ ε δ, algBlock_epsPrime_le_one atoms φ ε δ⟩

end AtTheRun

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ttcSampPriceHR
#print axioms Ttc.ttcSampPriceHR_def
#print axioms Ttc.ttcSampPriceHR_unfold
#print axioms Ttc.exists_mem_toDNFd_ttcInput
#print axioms Ttc.ttcSampInradius_le_ttcSampDiamPrice
#print axioms Ttc.one_le_ttcSampDiamPrice
#print axioms Ttc.one_le_ttcSampWarmPrice
#print axioms Ttc.algBlock_epsPrime_le_one
#print axioms Ttc.ttcSampPriceHR_le_quartic
#print axioms Ttc.ttcSampPriceHR_model
#print axioms Ttc.ttcSampPriceHR_pos
#print axioms Ttc.ttcSampPriceHR_discharged_hypotheses

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Api

/-!
# `Exec/Complexity`: "(our complexity)", as raw arithmetic in the algorithm's inputs

`ApproxNFA.approxNFA_countNFA` (`nfalean`, `ApproxNFA/Model/Theorem.lean`) writes its
running-time conjunct as **raw arithmetic in the algorithm's inputs**, with no named
auxiliary constant:

```
r.2 ≤ (8 * Real.log (1 / δ) + 1)
        * (49924 * (n * (n + 1) * (Fintype.card Q) ^ 3
            * Real.log (16 * ((n + 1) * Fintype.card Q))) / (ε ^ 2 * (1 - ε)))
      + n * ((n + 1) * Fintype.card Q) ^ 2
```

That is how it keeps every name occurring in the headline `Model/`-defined.  This
module produces the corresponding expression for `TTC`, `Ttc.ttcComplexity`, and
proves the run's charged cost is at most it (`Ttc.ttcCost_le_ttcComplexity`).

## What the expression is

```
ttcComplexity atoms φ ε δ C_vol C_sample
  = m * (C_vol + C_sample * ( 41472 * log(30/δ) / (ε² * (12 − ε))
                            + 15 * (log(15/(2δ)) + log m)
                            + 1 ))
m = (toDNFd (preprocess atoms φ)).length
```

Every name in it is either a Mathlib primitive (`Real.log`, `List.length`) or
`Model/`-defined (`Ttc.toDNFd`, `Ttc.preprocess`).  Nothing from `Exec/` occurs —
in particular neither `Ttc.ttcThresh` nor `Ttc.ttcNumCubes`.

**The dimension `n` does not appear, and that is not an omission.**
`Ttc.Params.thresh` reads only `P.δ`, `P.ε` and `P.m`; it never reads `P.n`, `P.r`,
the inscribed radius `γ̂`, the dilation `q` or the precision `ρ` (`Exec/Api`'s
`Ttc.ttcThresh_eq`).  The dimension enters `TTC`'s cost only through the *per-call*
costs of the volume oracle and of one sample, which `Runtime.lean` deliberately
leaves as the parameters `C_vol`, `C_sample` — the development charges oracle
calls, not the arithmetic inside a call.  So `n` occurs in the bound exactly where
the cost model puts it, inside `cVol` and `cSample`, and inventing an explicit `n`
dependence here would be asserting something unproved.

## The two honest disclosures

### 1. The `max` was eliminated, and what that cost

`Ttc.ttcThresh` is a `max` of two branches (`Exec/Api`, `Ttc.ttcThresh_eq'`):

```
Thresh = max ( 24·log(30/δ) / ((1 − ε/12)·(ε/12)²) ,  15·(log(15/(2δ)) + log m) )
```

`Ttc.ttcThresh_le_sum` replaces it by the **sum** of the two branches, after
rewriting the first branch's denominator — `(1 − ε/12)·(ε/12)² = ε²(12 − ε)/1728`,
so `24 / that = 41472 / (ε²(12 − ε))` — an exact identity, not a bound.

The only inequality spent is `max a b ≤ a + b`, valid because both branches are
nonnegative on the parameter range (`0 < ε ≤ 1`, `0 < δ ≤ 1`), which is proved
here: the first branch has a nonnegative numerator (`30/δ ≥ 30 > 1`) and a positive
denominator (`ε ≤ 1 < 12`), the second is `15·(log(15/(2δ)) + log m)` with
`15/(2δ) ≥ 15/2 > 1` and `Real.log_natCast_nonneg` covering `log m` for every `m`,
including `m = 0` where `Real.log 0 = 0`.

**What is given up:** at most a factor of `2` on the threshold term — the bound is
`a + b ≤ 2·max a b`, so the stated complexity exceeds the true `m·(C_vol +
C_sample·(Thresh + 1))` by less than `m·C_sample·Thresh`.  No branch was picked and
the other silently dropped; both survive, additively.  If the uglier exact shape is
ever wanted, `Ttc.ttcCost_le_thresh_add_one` (`Exec/Api`) is the `max`-carrying
version and this module changes nothing about it.

### 2. The `Ttc.ttcTerminates` guard is still there

`Ttc.ttcCost_le_ttcComplexity` carries `hterm : ttcTerminates … c t` exactly as
`Ttc.ttcCost_le_thresh_add_one` does.  It is **not** removable as the algorithm
currently stands: `Ttc.absorbLevel` is `max j₁ (sInf S)`, and off `Ttc.AbsorbExits`
the set `S` is empty, `sInf ∅ = 0`, so the exit level defaults to `j₁`, at which the
Poisson oracle returns the read-off `Ttc.trajPois` of the sample coins `t` — and `t`
ranges over all of `ℕ → Fin _ → ℕ`, so no deterministic bound holds for every `t`.

**This is the intended seam.**  The guard appears as a *single hypothesis on the
final theorem* and nowhere else in this file: `Ttc.ttcComplexity` is a closed term
with no hypotheses at all, and `Ttc.ttcThresh_le_sum` is unconditional on the run.
When the algorithm is interrupt-truncated (a level budget) so that an unconditional
cost bound becomes provable, discharging `hterm` — or replacing the appeal to
`Ttc.ttcCost_le_thresh_add_one` by its truncated successor — is the only edit
needed here; the complexity expression itself is unaffected.

## §4: the constructed subroutines' own counts — a pricing convention, **not** a
complexity result

`C_vol` and `C_sample` above are free naturals.  The last section of this file
replaces them, per cube, by two numbers the *constructed* subroutines carry:
`Ttc.MonteCarlo.nSamp`, the length of the Monte-Carlo estimator's sum, and
`Ttc.mixSteps`, the iterate count of the ball walk the sampler's law is.  Read the
following four paragraphs before quoting anything from that section.

**There is no cost model in which either number is a running time.**  This
development charges oracle *calls* and nothing else (`Ttc.stepCost`); it has no
operational semantics, no step-counting monad, no notion of a machine operation.
`Ttc.MonteCarlo.est` is a real-valued function of a coin sequence and
`Ttc.ballWalkLaw` is a measure — neither "performs" anything that could be counted.
So no theorem here or anywhere in the development says that `TTC` runs in any amount
of time, and substituting these counts does not create one.  What *is* proved about
them is only this: the estimator reads exactly the first `nSamp` coins
(`Ttc.mcVol_congr_of_agree`), and the sampler's law is the ball walk iterated exactly
`Ttc.e2eBallWalkSteps`-many times (`Ttc.e2eSampD_eq_ballWalk`, by `rfl`).  Charging
one unit per coin and one unit per chain step is then a *convention*, chosen here, not
a consequence.

**The convention undercounts, so the resulting inequality is not an upper bound on
work.**  Three things it prices at zero: the arithmetic inside a ball-walk step and
inside a coin test; the rejection rounds of `Ttc.kv97SampD`, whose number is
unbounded and which nothing in this development bounds; and the `while` loops of
`alg:ttc` lines 32–42, which `Ttc.runCost` never charged either (`Runtime`'s "Two
honest gaps").  A bound on an undercount is not a bound on the count.

**The numbers are exponential in `n`.**  `Ttc.MonteCarlo.nSamp K ε p` is
`⌈(ε²·p·q)⁻¹⌉₊ + 1` with `q = Vol K / Vol(ball 0 (rad K))`, i.e. `Θ(Rⁿ/(ε²p))` for an
enclosing radius `R` — rejection sampling into a ball.  `Ttc.mixSteps` is
`⌈log(√M/eps) / (φ²/2)⌉₊` at a conductance floor `φ` containing both `(γ/(γ+Dm))ⁿ` and
`(1/2)ⁿ`, so `1/φ²` is exponential in `n` as well.  This is **not** Cousins–Vempala's
`O*(n³)`: `Ttc.VolumeAlgorithm.cousinsVempala` still carries two unproved hypotheses
— `hphase_mean` and `hphase_var`, the two that are about the *sampler*
(`Ttc/Volume/CVInstantiate.lean`) — and discharging them needs a Metropolis-filtered
kernel this development does not have.  The constructed volume oracle is
`Ttc.VolumeAlgorithm.monteCarlo`, rejection sampling into a ball, and it is that one
whose count appears below.
`thm:runtime`'s `O(m·n⁴)` remains out of scope, before and after this section.

**No closed form, and no uniform bound over the cubes, is available.**
`Ttc.MonteCarlo.rad` is `Exists.choose` of `∃ R, 0 < R ∧ K ⊆ ball 0 R`: only
`Ttc.MonteCarlo.rad_pos` and `Ttc.MonteCarlo.subset_ball_rad` are provable about it,
and *no upper bound on it is derivable at all*.  Hence `nSamp` has no closed-form
upper bound, per cube or uniformly, and the `cVol` of `Ttc.runCost_le` cannot be
instantiated at any arithmetic expression that dominates it.  That is why the section
below goes through `Ttc.runCostAt` (`Runtime`), the same fold with a **per-cube price
list**, and stops at `∑ᵢ (coinsᵢ + stepsᵢ·⌈Thresh⌉)` — a sum of opaque terms, not an
expression in `n`, `ε`, `δ`, `m`.  `Ttc.ttcComplexity`'s defining property, that it is
raw arithmetic in the algorithm's inputs, is exactly what cannot survive the
substitution.

## Nothing here asserts anything

`Ttc.ttcComplexity` is a `def` whose body is a closed arithmetic term, carrying the
`rfl` lemma `Ttc.ttcComplexity_def` that spells that body out.  It claims no
semantic identity that is not proved: the *only* claim made about it is
`Ttc.ttcCost_le_ttcComplexity`, which is proved.

The same discipline holds in §4.  `Ttc.mcVolCoins` and `Ttc.e2eBallWalkSteps` are
`def`s whose names promise semantic identities — "the coins the volume oracle reads",
"the steps the sampler's chain takes" — and each carries the lemma that proves it
(`Ttc.mcVol_congr_of_agree`, `Ttc.ttcOracleBundle_vol_congr`;
`Ttc.e2eSampD_eq_ballWalk`, `Ttc.ttcRates_eq_e2eSampD`).  `Ttc.ttcCoinAndStepCharge`
promises nothing beyond its name: it is `Ttc.runCostAt` at those two price lists, and
the one claim made about it, `Ttc.ttcCoinAndStepCharge_le_sum`, is proved.
-/

namespace Ttc

open MeasureTheory Set Pointwise

variable {A : Type*} {n : ℕ}

/-! ## The expression

One `def`, closed, with no hypotheses — so it can be read without the FPRAS
parameter range, and so the guard of the bound below is visibly not baked into it. -/

/-- **"(our complexity)"** — the running-time bound of `TTC(F, ε, δ)` as raw
arithmetic in the algorithm's inputs, in the shape
`ApproxNFA.approxNFA_countNFA`'s running-time conjunct uses.

```
m * (C_vol + C_sample * ( 41472·log(30/δ) / (ε²·(12 − ε))
                        + 15·(log(15/(2δ)) + log m)
                        + 1 ))
```

with `m = (toDNFd (preprocess atoms φ)).length` the number of cubes of the
preprocessed formula's DNF.  See the module docstring for why the dimension `n`
does not occur, and for what the `max` of `Ttc.ttcThresh` cost when it was turned
into the `+` between the two `C_sample` terms. -/
noncomputable def ttcComplexity (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (cVol cSample : ℕ) : ℝ :=
  ((toDNFd (preprocess atoms φ)).length : ℝ)
    * ((cVol : ℝ) + (cSample : ℝ)
        * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
            + 15 * (Real.log (15 / (2 * δ))
                + Real.log ((toDNFd (preprocess atoms φ)).length))
            + 1))

/-- **What `Ttc.ttcComplexity` is**, spelled out, by `rfl`. -/
theorem ttcComplexity_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (cVol cSample : ℕ) :
    ttcComplexity atoms φ ε δ cVol cSample
      = ((toDNFd (preprocess atoms φ)).length : ℝ)
          * ((cVol : ℝ) + (cSample : ℝ)
              * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                  + 15 * (Real.log (15 / (2 * δ))
                      + Real.log ((toDNFd (preprocess atoms φ)).length))
                  + 1)) := rfl

/-! ## The two branches of `Thresh`, and their sum

The three lemmas below are what removes the `max`.  The first is an *identity* —
the first branch's denominator cleared — and the other two are the nonnegativity
facts that make `max a b ≤ a + b` available.  All three are statements about real
numbers only; nothing about the algorithm enters them. -/

/-- **The first branch, with its denominator cleared** —
`(1 − ε/12)·(ε/12)² = ε²·(12 − ε)/1728`, so `24 / that = 41472 / (ε²·(12 − ε))`.
An exact identity: nothing is lost here. -/
theorem ttcThresh_branch_one_eq (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (x : ℝ) :
    24 * x / ((1 - ε / 12) * (ε / 12) ^ 2) = 41472 * x / (ε ^ 2 * (12 - ε)) := by
  have h12 : (0 : ℝ) < 12 - ε := by linarith
  have hd1 : ((1 : ℝ) - ε / 12) * (ε / 12) ^ 2 ≠ 0 := by
    have hpos' : (0 : ℝ) < (1 - ε / 12) * (ε / 12) ^ 2 :=
      mul_pos (by linarith) (by positivity)
    exact ne_of_gt hpos'
  have hd2 : ε ^ 2 * (12 - ε) ≠ 0 := by
    have hpos' : (0 : ℝ) < ε ^ 2 * (12 - ε) := by positivity
    exact ne_of_gt hpos'
  rw [div_eq_div_iff hd1 hd2]
  ring

/-- **The first branch is nonnegative.**  `30/δ ≥ 30 > 1` makes the numerator
nonnegative, and `ε ≤ 1 < 12` makes the denominator positive. -/
theorem ttcThresh_branch_one_nonneg (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ 41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε)) := by
  have h12 : (0 : ℝ) < 12 - ε := by linarith
  have hlog : 0 ≤ Real.log (30 / δ) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hδ0]
    linarith
  have hden : (0 : ℝ) < ε ^ 2 * (12 - ε) := by positivity
  positivity

/-- **The second branch is nonnegative.**  `15/(2δ) ≥ 15/2 > 1` since `δ ≤ 1`, and
`Real.log m ≥ 0` for every natural `m` — including `m = 0`, where Mathlib's
`Real.log 0 = 0`. -/
theorem ttcThresh_branch_two_nonneg (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (m : ℕ) :
    0 ≤ 15 * (Real.log (15 / (2 * δ)) + Real.log m) := by
  have h1 : 0 ≤ Real.log (15 / (2 * δ)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * δ)]
    linarith
  have h2 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  linarith

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

include hε0 hε1 hn hφ hpos in
/-- **`Thresh` is at most the sum of its two branches**, with the first branch
rewritten as `41472·log(30/δ) / (ε²·(12 − ε))`.

This is the single inequality that removes the `max` from `Ttc.ttcThresh`.  It is
lossy by at most a factor of `2` on this term (`a + b ≤ 2·max a b` when both are
nonnegative), and it drops *neither* branch.

The five shape binders are `include`d rather than named: after task #33's
proof-binder strip, `Ttc.ttcThresh` is a `def` and takes only `atoms φ ε δ`, but
`Ttc.ttcThresh_eq'` still needs all five, so they must be carried into the
statement's argument list explicitly. -/
theorem ttcThresh_le_sum (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ttcThresh atoms φ ε δ
      ≤ 41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
          + 15 * (Real.log (15 / (2 * δ))
              + Real.log ((toDNFd (preprocess atoms φ)).length)) := by
  rw [ttcThresh_eq' atoms φ ε δ hε0 hε1 hn hφ hpos hδ0, ttcNumCubes_eq,
    ttcThresh_branch_one_eq ε hε0 hε1 (Real.log (30 / δ))]
  have hA := ttcThresh_branch_one_nonneg ε δ hε0 hε1 hδ0 hδ1
  have hB := ttcThresh_branch_two_nonneg δ hδ0 hδ1 (toDNFd (preprocess atoms φ)).length
  exact max_le (by linarith) (by linarith)

/-! ## The bound

One theorem, one guard.  `hterm` is the only hypothesis about the run itself; see
the module docstring, "The `Ttc.ttcTerminates` guard is still there". -/

include hε0 hε1 hn hφ hpos in
/-- **`TTC`'s charged cost is at most `Ttc.ttcComplexity`.**

```
cost(c, t) ≤ m * (C_vol + C_sample * ( 41472·log(30/δ) / (ε²·(12 − ε))
                                     + 15·(log(15/(2δ)) + log m)
                                     + 1 ))
```

with `m = (toDNFd (preprocess atoms φ)).length`.  The right-hand side names nothing
from `Exec/`: it is `Ttc.ttcComplexity`, raw arithmetic in `ε`, `δ`, `m`, `C_vol`,
`C_sample`, in the shape `ApproxNFA.approxNFA_countNFA`'s running-time conjunct
uses.

Only the FPRAS parameter range (`0 < ε ≤ 1`, `0 < δ ≤ 1`) and the input's own shape
hypotheses are required — plus `hterm`, the absorption loops' exit, which is the
**one** run hypothesis and the seam where interrupt-truncation will land.

As with `Ttc.ttcThresh_le_sum`, the five shape binders are `include`d: `ttcIndex`,
`ttcTerminates` and `ttcCost` are `def`s and no longer take them, but
`Ttc.ttcCost_le_thresh_add_one` does. -/
theorem ttcCost_le_ttcComplexity (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ) (cVol cSample : ℕ)
    (hterm : ttcTerminates atoms φ ε δ c t) :
    (ttcCost atoms φ ε δ c t cVol cSample : ℝ)
      ≤ ttcComplexity atoms φ ε δ cVol cSample := by
  refine le_trans
    (ttcCost_le_thresh_add_one atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 c t cVol cSample
      hterm) ?_
  rw [ttcComplexity_def, ttcNumCubes_eq]
  have hthr := ttcThresh_le_sum atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
  gcongr

/-! # §4: the counts the constructed subroutines carry

Everything below prices `Ttc.runCost`'s two free parameters at numbers the
constructed `Vol_ED` and the constructed sampler actually contain.  **Read the module
docstring's §4 first.**  In one line: this is a pricing convention, it undercounts,
the numbers are exponential in `n`, and nothing here bounds a running time.

The section has four parts: the volume oracle's coin count and the theorem that it is
the number of coins read; the sampler's step count and the theorem that it is the
chain's iterate count; both at the run's own data; and the per-cube charge with its
bound. -/

section Counts

/-! ## The volume oracle: how many coins `Ttc.mcVol` reads

`Ttc.mcVol` evaluates `Ttc.MonteCarlo.est` on the cube's normalised region, whose sum
runs over `Finset.range (Ttc.MonteCarlo.nSamp …)`.  `Ttc.mcVolCoins` names that
length, and `Ttc.mcVol_congr_of_agree` proves the name honest: two coin sequences
agreeing below it give the same volume estimate.  That is the *only* sense in which
this development can say a subroutine "does" a number of anything. -/

open scoped Classical in
/-- **The number of coins the constructed `Vol_ED` reads on cube `i`** —
`Ttc.MonteCarlo.nSamp` of the cube's normalised region, and `0` off the DNF, where
`Ttc.mcVol` is `0` and reads nothing.  Noncomputable, and with no closed-form upper
bound: `Ttc.MonteCarlo.rad` is a `Classical.choice` term about which only positivity
and enclosure are provable (module docstring, §4). -/
noncomputable def mcVolCoins (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) (i : Cube A) : ℕ :=
  if hi : i ∈ D then
    MonteCarlo.nSamp (roundBody (cen ⟨i, hi⟩) γ (region M i)) ε' δ'
  else 0

/-- **The estimator depends on the coins only through the first `nSamp` of them.**
Its sum is indexed by `Finset.range (nSamp …)`, so coins from `nSamp` on are never
looked at. -/
theorem monteCarloEst_congr_of_agree (K : Set (Space n)) (ε pf : ℝ) {c c' : ℕ → Space n}
    (h : ∀ k < MonteCarlo.nSamp K ε pf, c k = c' k) :
    MonteCarlo.est K ε pf c = MonteCarlo.est K ε pf c' := by
  unfold MonteCarlo.est
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp only [MonteCarlo.score, h k (Finset.mem_range.1 hk)]

/-- **`Ttc.mcVolCoins` is the number of coins `Ttc.mcVol` reads**: agreement of two
coin sequences below it forces agreement of the volume estimate.  This is what stops
`Ttc.mcVolCoins`' name from standing in for an unproved identification. -/
theorem mcVol_congr_of_agree (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) {c c' : ℕ → Space n}
    (i : Cube A) (h : ∀ k < mcVolCoins M D cen γ ε' δ' i, c k = c' k) :
    mcVol M D cen γ ε' δ' c i = mcVol M D cen γ ε' δ' c' i := by
  unfold mcVol
  by_cases hi : i ∈ D
  · rw [dif_pos hi, dif_pos hi]
    congr 1
    refine monteCarloEst_congr_of_agree _ _ _ ?_
    intro k hk
    exact h k (by simpa [mcVolCoins, dif_pos hi] using hk)
  · rw [dif_neg hi, dif_neg hi]

/-! ## The sampler: how many ball-walk steps its law is

`Ttc.e2eSampD` is `Ttc.kv97SampD` of `Ttc.kv97ContLaw`, and `Ttc.kv97ContLaw` at cube
`i` is `Ttc.ballWalkLaw … (Ttc.mixSteps …)` — an iterate of the lazy ball-walk kernel.
`Ttc.e2eBallWalkSteps` names that iterate count at `Ttc.e2eSampD`'s own arguments and
`Ttc.e2eSampD_eq_ballWalk` checks, by `rfl`, that it is that count.

Two things it is **not**.  It is not a count of anything `Ttc.ttcRun` does: the run's
`GenerateSamples` is the trajectory read-off `Ttc.trajGen`, and `Ttc.mixSteps` does not
occur in `Ttc.ttcRun`'s definitional closure at all — it occurs in `Ttc.ttcRates`, the
*law* the sample coins are drawn from.  And it is not the cost of a sample even under
the convention: `Ttc.kv97SampD` is a rounding-then-rejection law, and the rejection
rounds are not counted here or anywhere. -/

/-- **The number of lazy-ball-walk steps in the law of one sample from cube `i`** —
`Ttc.mixSteps` at the geometry `Ttc.e2eSampD` supplies it: inscribed radius
`10^ρ·γ̂ + κ`, diameter `(1 + κ/(10^ρ·γ̂))·Dm i`, step `10^ρ·γ̂`, warmness the volume
ratio of the inflated body to the enclosing ball, and tolerance `ε'/(4·Vol P'ᵢ)`.

Exponential in `n`: `Ttc.mixSteps`' conductance floor carries `(γ/(γ+Dm))ⁿ` and
`(1/2)ⁿ`, and the step count is inversely proportional to its square. -/
noncomputable def e2eBallWalkSteps {D : DNF A} (ρ : ℤ) (epsPrime rfac : ℝ) {Jt : Type}
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ)
    (Dm : {c : Cube A // c ∈ D} → ℝ) (i : {c : Cube A // c ∈ D}) : ℕ :=
  mixSteps n
    (latticeScale ρ * gammaHat + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
    ((1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac / (latticeScale ρ * gammaHat))
      * Dm i)
    (latticeScale ρ * gammaHat)
    ((volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac) /
      volume (Metric.ball (latticeScale ρ • cen i)
        (latticeScale ρ * gammaHat
          + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal)
    (epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)).toReal))

/-- **The sampler's law is the ball walk iterated `Ttc.e2eBallWalkSteps` times**, by
`rfl` — so the name above is not standing in for an unproved identification.  The
rounding and rejection of `Ttc.kv97SampD` are untouched by this, and uncounted. -/
theorem e2eSampD_eq_ballWalk (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (epsPrime rfac : ℝ) {Jt : Type} (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ) (cen : {c : Cube A // c ∈ D} → Space n)
    (gammaHat : ℝ) (Dm : {c : Cube A // c ∈ D} → ℝ) :
    e2eSampD M D ρ epsPrime rfac Am bv cen gammaHat Dm
      = kv97SampD M D ρ (fun i =>
          ballWalkLaw (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)
            (latticeScale ρ * gammaHat)
            (Arlib.uniformOn volume (Metric.ball (latticeScale ρ • cen i)
              (latticeScale ρ * gammaHat
                + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)))
            (e2eBallWalkSteps ρ epsPrime rfac Am bv cen gammaHat Dm i)) := rfl

/-! ## The two counts at the run's own data -/

section AtTheRun

/-- **The run's per-cube coin count** — `Ttc.mcVolCoins` at the arguments
`Ttc.ttcOracleBundle` gives `Ttc.mcVol`.  `Ttc.ttcOracleBundle_vol_congr` is the check
that these really are those arguments. -/
noncomputable def ttcVolCoins : Cube A → ℕ :=
  mcVolCoins (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
    (ttcCen atoms φ ε δ) (ttcScaledRadius atoms φ ε δ)
    (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime
    (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).deltaPrime

/-- **The run's `Vol_ED` reads exactly `Ttc.ttcVolCoins` coins on cube `i`.**  The
oracle bundle's `vol` field is `Ttc.mcVol` at the run's data, so this is
`Ttc.mcVol_congr_of_agree` — and the fact that it typechecks is what pins
`Ttc.ttcVolCoins`' arguments to the ones the run uses. -/
theorem ttcOracleBundle_vol_congr (c c' : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ) (i : Cube A)
    (h : ∀ k < ttcVolCoins atoms φ ε δ i, c k = c' k) :
    (ttcOracleBundle atoms φ ε δ c t).vol i = (ttcOracleBundle atoms φ ε δ c' t).vol i :=
  mcVol_congr_of_agree _ _ _ _ _ _ i h

open scoped Classical in
/-- **The run's per-cube ball-walk step count** — `Ttc.e2eBallWalkSteps` at the
arguments `Ttc.ttcRates` gives `Ttc.e2eSampD`, and `0` off the DNF.
`Ttc.ttcRates_eq_e2eSampD` is the check that these are those arguments. -/
noncomputable def ttcSampleSteps : Cube A → ℕ := fun i =>
  if hi : i ∈ toDNFd (ttcInput atoms φ) then
    e2eBallWalkSteps (ttcPrec atoms φ ε δ)
      (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime
      (canonRfac (toDNFd (ttcInput atoms φ)))
      (canonAm (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ)))
      (canonBv (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ))
        (latticeScale (ttcPrec atoms φ ε δ)))
      (ttcCen atoms φ ε δ) (ttcScaledRadius atoms φ ε δ)
      (canonDm (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
        (ttcPrec atoms φ ε δ))
      ⟨i, hi⟩
  else 0

/-- **On the DNF, `Ttc.ttcSampleSteps` is `Ttc.e2eBallWalkSteps`** — the `dite` is
only totality. -/
theorem ttcSampleSteps_eq_of_mem {i : Cube A} (hi : i ∈ toDNFd (ttcInput atoms φ)) :
    ttcSampleSteps atoms φ ε δ i
      = e2eBallWalkSteps (ttcPrec atoms φ ε δ)
          (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime
          (canonRfac (toDNFd (ttcInput atoms φ)))
          (canonAm (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ)))
          (canonBv (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ))
            (latticeScale (ttcPrec atoms φ ε δ)))
          (ttcCen atoms φ ε δ) (ttcScaledRadius atoms φ ε δ)
          (canonDm (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
            (ttcPrec atoms φ ε δ))
          ⟨i, hi⟩ := by
  simp only [ttcSampleSteps, dif_pos hi]

/-- **The law the run's sample coins are drawn from is `Ttc.e2eSampD` at exactly the
arguments `Ttc.ttcSampleSteps` uses**, by `rfl`.  Composed with
`Ttc.e2eSampD_eq_ballWalk` this is the proof that `Ttc.ttcSampleSteps` is the iterate
count of the chain in the run's own sampler law — and not merely a name suggesting
so. -/
theorem ttcRates_eq_e2eSampD (c : ℕ → Space n) :
    ttcRates atoms φ ε δ c
      = rates (atomSet (ttcAtoms atoms φ ε δ)) (ttcInput atoms φ)
          (toDNFd (ttcInput atoms φ)) (ttcPrec atoms φ ε δ)
          (e2eSampD (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
            (ttcPrec atoms φ ε δ)
            (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime
            (canonRfac (toDNFd (ttcInput atoms φ)))
            (canonAm (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ)))
            (canonBv (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ))
              (latticeScale (ttcPrec atoms φ ε δ)))
            (ttcCen atoms φ ε δ) (ttcScaledRadius atoms φ ε δ)
            (canonDm (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
              (ttcPrec atoms φ ε δ)))
          (mcVol (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
            (ttcCen atoms φ ε δ) (ttcScaledRadius atoms φ ε δ)
            (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime
            (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).deltaPrime
            c) := rfl

/-! ## The charge, and its bound

`Ttc.ttcCost` at a per-cube price list, priced by the two counts above.  The name says
what is charged — coins and chain steps — because that is all it is: not time, not
operations, not `thm:runtime`'s `O(m·n⁴)`. -/

/-- **`Ttc.runCostAt` at the two constructed counts** — one unit per coin the volume
oracle reads, one unit per ball-walk step in the law of each sample drawn.

**This is a pricing convention and not a running time.**  It undercounts (rejection
rounds, per-step arithmetic, the `while` loops), the counts themselves are exponential
in `n`, and the development contains no theorem relating either to the work an
implementation does.  See the module docstring, §4. -/
noncomputable def ttcCoinAndStepCharge (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ) : ℕ :=
  runCostAt (ttcBlock atoms φ ε δ) (ttcOracleBundle atoms φ ε δ c t)
    (ttcVolCoins atoms φ ε δ) (ttcSampleSteps atoms φ ε δ)
    (ttcPrec atoms φ ε δ) (toDNFd (ttcInput atoms φ))

/-- **The charge is at most `∑ᵢ (coinsᵢ + stepsᵢ·⌈Thresh⌉₊)` over the cubes.**

The right-hand side is a sum of **opaque terms**, not arithmetic in `n`, `ε`, `δ`, `m`:
`Ttc.ttcVolCoins` contains `Ttc.MonteCarlo.rad`, a `Classical.choice` term with no
derivable upper bound, so no uniform closed-form price exists to put in
`Ttc.ttcCost_le_ttcComplexity`'s place.  That is the whole reason this statement is a
sum over cubes rather than `m · (C_vol + C_sample·Thresh)` at concrete constants.

**It is not a running-time bound**, for the four reasons in the module docstring's §4.
`Ttc.ttcComplexity` and `Ttc.ttcCost_le_ttcComplexity` are unaffected by this section
and remain the file's statement about the charged cost.

The `Ttc.ttcTerminates` guard is here for the same reason it is on
`Ttc.ttcCost_le_ttcComplexity`, and is no more removable: off `Ttc.AbsorbExits` the
Poisson read-off is an arbitrary natural. -/
theorem ttcCoinAndStepCharge_le_sum (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ)
    (hterm : ttcTerminates atoms φ ε δ c t) :
    ttcCoinAndStepCharge atoms φ ε δ c t
      ≤ ((toDNFd (ttcInput atoms φ)).map (fun i =>
          ttcVolCoins atoms φ ε δ i
            + ttcSampleSteps atoms φ ε δ i * ⌈ttcThresh atoms φ ε δ⌉₊)).sum :=
  runCostAt_le_sum _ _ _ _ _ _ _ (Nat.le_ceil _) hterm

end AtTheRun

end Counts

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ttcComplexity
#print axioms Ttc.ttcComplexity_def
#print axioms Ttc.ttcThresh_branch_one_eq
#print axioms Ttc.ttcThresh_branch_one_nonneg
#print axioms Ttc.ttcThresh_branch_two_nonneg
#print axioms Ttc.ttcThresh_le_sum
#print axioms Ttc.ttcCost_le_ttcComplexity

/-! ### §4 -/

#print axioms Ttc.mcVolCoins
#print axioms Ttc.monteCarloEst_congr_of_agree
#print axioms Ttc.mcVol_congr_of_agree
#print axioms Ttc.e2eBallWalkSteps
#print axioms Ttc.e2eSampD_eq_ballWalk
#print axioms Ttc.ttcVolCoins
#print axioms Ttc.ttcOracleBundle_vol_congr
#print axioms Ttc.ttcSampleSteps
#print axioms Ttc.ttcSampleSteps_eq_of_mem
#print axioms Ttc.ttcRates_eq_e2eSampD
#print axioms Ttc.ttcCoinAndStepCharge
#print axioms Ttc.ttcCoinAndStepCharge_le_sum

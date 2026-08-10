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

## Nothing here asserts anything

`Ttc.ttcComplexity` is a `def` whose body is a closed arithmetic term, carrying the
`rfl` lemma `Ttc.ttcComplexity_def` that spells that body out.  It claims no
semantic identity that is not proved: the *only* claim made about it is
`Ttc.ttcCost_le_ttcComplexity`, which is proved.
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

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ttcComplexity
#print axioms Ttc.ttcComplexity_def
#print axioms Ttc.ttcThresh_branch_one_eq
#print axioms Ttc.ttcThresh_branch_one_nonneg
#print axioms Ttc.ttcThresh_branch_two_nonneg
#print axioms Ttc.ttcThresh_le_sum
#print axioms Ttc.ttcCost_le_ttcComplexity

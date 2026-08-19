/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Exec.TtcSlowRuntimePerPhase

/-!
# The main theorem of the paper

`Ttc/Model/` describes the paper and nothing else: `Prelude` the preliminaries,
`ProblemSetting` the problem definition, `Pseudocode` the algorithm `alg:ttc` with **no
oracle chosen**, and this file the algorithm at the oracles the paper specifies together
with the one theorem about it — `thm:volumettc` + `thm:runtime` in a single statement.

## The two backends, and only these two

`Ttc.ttc atoms φ ε δ` is the law of one run of `TTC(F, ε, δ)` with

* **volume** — `Ttc.TtcSlowRuntimePerPhase.slowPerPhaseImplementation.algorithm n`, the
  Cousins–Vempala Gaussian-cooling estimator (`sections/analysis.tex`, `cor:vol`), built out
  of the slow canonical construction at the per-phase slack, bound, stream count and
  truncation radius;
* **sampling** — the hit-and-run / ball-walk hybrid carried by
  `Ttc.TTCSourceSharpOperationalFinal.canonicalCappedPolyHybridPlugin`: hit-and-run at
  `21 ≤ n` (`cor:linf`), the lazy ball walk below.  Since `Ttc.ttc_volume` binds `21 ≤ n`,
  the run it describes always takes the hit-and-run branch; the ball walk survives only as
  the off-hypothesis branch that keeps `Ttc.ttc` total.

Until 2026-08-19 this file also carried a second headline about a second `Ttc.ttc`, whose
volume oracle was hit-and-miss Monte Carlo (`Ttc.mcVol`) and whose sampler was the lazy ball
walk, charged at two *fixed* per-call prices it was not proved to pay.  Those reference
oracles and every theorem, price and witness attached to them were deleted, not weakened:
there is one algorithm and one theorem here now.

## Where `Ttc.ttc` is defined, and why it is here rather than in `Pseudocode`

`Ttc/Exec/` imports `Model/Pseudocode` — `Ttc.algIndex`, `Ttc.algAtoms`, `Ttc.algBlock` are
the spec the construction is built against — so `Pseudocode` cannot name the construction
without a cycle.  `Pseudocode` therefore states `alg:ttc` with the oracle bundle as an
*argument* (`Ttc.ttcAlgOutput`), and this file, the only `Model/` file downstream of the
construction, fills it in.  That layering is the reason the four-file surface still means
something for the *specification* even though the *instantiation* names 100+ modules.

## What the theorem says

* **Accuracy.**  `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, at the user's own `Vol(F)`,
  under the eight binders and nothing else — no oracle binder, no certificate binder, no
  implementation binder, no cost-side binder.
* **Expected query cost.**  `∫⁻ r, r.2` — the *expectation* of the run's total membership-
  query count — is at most the constructed volume envelope plus the constructed sampler
  envelope.

The cost half is deliberately an expectation and not an `All[…]`: what the construction
proves is a bound on `∫⁻`, and an almost-sure bound is a different statement.  Getting one
would take Markov's inequality against a failure budget plus the existing
`Ttc.sourceReferenceCutoff`; that work has not been done and is not claimed here.

## ⚠ Three things this is not

1. **Not the paper's exponents.**  The envelope is `Õ(m·n⁴·ρ⁶/ε²)` in *membership-query*
   units, not `O(m·n⁵·ρ²·r_max)`, and the two are not in the same units until the `⌈n·rfac⌉₊`
   charge of `Ttc.TtcSlowRuntimePerPhase.ttc_volume_runtime_perPhase_ops` is applied.  The
   `ρ` exponent is unsettled.  See `lean/PLAN-SHAPE.md` §5 and `lean/PAPER-CLAIMS.md`.
2. **Not a practical bound, though it is now a uniform one.**  Until 2026-08-19 the sampler
   was hit-and-run only at `1100 ≤ n`, and for `21 ≤ n < 1100` the proved transition bound was
   the ball walk's own — `4 ^ n` times a `(radius ratio) ^ (4 n)`.  That hole is closed: the
   spherical-cap estimate `Arlib.MarkovChains.unifSphere_cap_le` now holds from `n ≥ 21`
   (proved by an exact cross-section computation rather than the union bound that forced
   `1100`), so the sampler is hit-and-run at **every dimension this theorem admits** and the
   transition bound is polynomial throughout.  What remains is the size of the constant:
   `2 ^ 66 · n² · R²/r² · log(8 M/ε²)`.  Polynomial is not the same as runnable.
3. **Not inside a four-file audit surface.**  Naming the constructed oracles *is* naming the
   construction: the statement below reaches 637 constants across 108 modules outside
   `Model/`, `Probability/` and `Geometry/`.  `#modelClosureOfType` does not hold of it and is
   not claimed.  What the surface still certifies is the *specification* —
   `Ttc.ttcAlgOutput`, checked in `Ttc/Audit/ClosureCheck.lean`.  The asymmetry is real and
   recorded there rather than papered over by widening the surface until it says nothing.
-/

namespace Ttc

open scoped ENNReal BigOperators Classical
open MeasureTheory Ttc.Monadic
open Ttc.TtcSlowRuntimePerPhase Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem Ttc.CVShaped Ttc.TtcCircumRadius
open Ttc.TTCCVExpectedImplementation

variable {A : Type*}

/-- **The side condition `TTC(F, ε, δ)` is defined under.**

Exactly the binders `Ttc.TTCSourceSharpOperationalFinal.canonicalCappedPolyHybridPlugin`
takes: a usable accuracy target, a nonzero dimension, a positive formula and a solution set
of positive volume.  `δ` is unconstrained — the plugin does not read it — so it does not
appear here even though the theorem below does bound it.

`Ttc.ttc` is *total*: off this condition it is the zero measure, a junk value with no
content, and the theorem discharges the condition from its own hypotheses.  Defining the
algorithm only where it makes sense and reading a junk value elsewhere is what lets the
headline be stated with no definedness side goal (`CLAUDE.md` §11 is about hypotheses that
*nothing* satisfies; these are satisfied — see `Ttc/Witness/`). -/
def TtcInputs {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 ∧ 1 ≤ n ∧ φ.IsPositive ∧ 0 < volSol (atomSet atoms) φ

/-- **`TTC(F, ε, δ)` — the law of one run, at Cousins–Vempala volume and hit-and-run
sampling.**

Four inputs and nothing else: the atoms, the formula, the accuracy target and the failure
budget.  No oracle argument, no interpretation, no parameter block, no precision argument —
the two backends are *chosen here*, not received.

A draw `r : ℝ × ℝ≥0∞` is one complete run: `r.1` is the estimate the run returns and `r.2` is
the number of membership queries it spent getting it.  The two conjuncts of `Ttc.ttc_volume`
are about the two coordinates of the **same** draw, so they describe one execution rather
than two.

The inner failure budget is `4 * δ / 5`: the remaining fifth is what the outer
absorption/estimation stages spend, and the theorem's `1 - δ` is stated at the user's `δ`. -/
noncomputable def ttc {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ) :
    Measure (ℝ × ℝ≥0∞) :=
  if h : TtcInputs atoms φ ε then
    letI : NeZero n := ⟨Nat.ne_of_gt h.2.2.1⟩
    canonicalFullOperationalLaw (slowPerPhaseImplementation.algorithm n)
      (canonicalCappedPolyHybridPlugin atoms φ ε (4 * δ / 5)
        (slowPerPhaseImplementation.algorithm n)
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else 0

/-- **`Ttc.ttc` on its own inputs is the law that executes the two constructed backends.**

By `rfl` after the branch is taken, so the theorem below is about the object the
construction proves things about and not a renamed copy of it. -/
theorem ttc_eq_canonicalFullOperationalLaw {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ) (h : TtcInputs atoms φ ε) :
    letI : NeZero n := ⟨Nat.ne_of_gt h.2.2.1⟩
    ttc atoms φ ε δ
      = canonicalFullOperationalLaw (slowPerPhaseImplementation.algorithm n)
          (canonicalCappedPolyHybridPlugin atoms φ ε (4 * δ / 5)
            (slowPerPhaseImplementation.algorithm n)
            h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) := by
  unfold ttc
  rw [dif_pos h]

/-- **`Ttc.ttc` is a probability measure on its own inputs** — every run returns something,
and the absorption loops halt `Ttc.ttc`-almost surely.  Off the inputs it is `0`. -/
instance instIsProbabilityMeasureTtc {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ) [Fact (TtcInputs atoms φ ε)] :
    IsProbabilityMeasure (ttc atoms φ ε δ) := by
  have h : TtcInputs atoms φ ε := Fact.out
  letI : NeZero n := ⟨Nat.ne_of_gt h.2.2.1⟩
  rw [ttc_eq_canonicalFullOperationalLaw atoms φ ε δ h]
  infer_instance

/-- **`thm:volumettc` + `thm:runtime`, in one statement about one law.**

`TTC(F, ε, δ)` — `Ttc.ttc`, the algorithm of `alg:ttc` run with the Cousins–Vempala
Gaussian-cooling volume estimator and the hit-and-run / ball-walk hybrid sampler — returns an
`ε`-relative estimate of `Vol(F)` with probability at least `1 − δ`, and its **expected**
membership-query count is at most the constructed volume envelope plus the constructed
sampler envelope.

Both conjuncts are about the one law that *executes* those two backends.  There is no oracle
binder, no certificate binder, no implementation binder and no cost-side binder; the axioms
are `[propext, Classical.choice, Quot.sound]`.

Read the module docstring before quoting the cost conjunct: the envelope is in
membership-query units, it is not the paper's exponents, and it is not uniform in `n` below
1100. -/
theorem ttc_volume {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : 21 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- **Accuracy.**  The estimate is within a factor `1 ± ε` of the true volume, except
    -- with probability `δ`.
    (1 - δ ≤ Pr[r ← ttc atoms φ ε δ; r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- **Expected query cost**, on the same run: the Cousins–Vempala volume envelope summed
    -- over the cubes at each cube's own interior circumradius, plus the hybrid sampler's
    -- envelope.
    ((∫⁻ r, r.2 ∂ttc atoms φ ε δ) ≤
      shapedVolumeQueryEnvelopeAt slowPerPhaseImplementation atoms φ ε (4 * δ / 5)
          (fun j ↦ (circumR (interior (callBody atoms φ ε (4 * δ / 5) j))) ^ 2)
        + canonicalCappedSampleQueryEnvelope atoms φ ε (4 * δ / 5)) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hin : TtcInputs atoms φ ε := ⟨hε0, hε1, hn1, hφ, hpos⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
  have hrw := ttc_eq_canonicalFullOperationalLaw atoms φ ε δ hin
  have hcap := ttc_volume_runtime_perPhase atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
  refine ⟨?_, ?_⟩
  · rw [hrw]; exact hcap.1
  · rw [hrw]; exact hcap.2

#print axioms ttc_volume

end Ttc

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Program
import Ttc.Exec.PricedHeadline
import Ttc.Exec.SamplePrice

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

The legacy statement-layer theorem is `Ttc.ttc_volume_estimate`.  The additional theorem
`Ttc.ttc_volume_estimate_accounted` fixes its accounting defect by charging the concrete
hit-and-miss/lazy-ball-walk run at the two prices actually proved for that run.  The
accuracy half comes from
`Ttc.ttc_volume_estimate_parametric` and the running-time half from
`Ttc.PricedHeadline.all_ttc_cost_le_quartic`, both in `Ttc/Exec/PricedHeadline.lean`.

The same-law operational replacement is now exposed at the honestly capped radial-log
interface by
`Ttc.CVCappedRadialLogInterface.ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation`.
It cannot be imported back into this model-layer module without creating the dependency
cycle `Model -> Exec -> Model`.  Its second conjunct integrates the run's actual recorded
volume queries and complete sampling-trajectory query cost as the literal `.2` coordinate.
The volume summand is the finite sum of corrected capped radial-log CV bounds, and the
sampling summand is the concrete capped hybrid-sampler envelope.  Unlike the legacy
theorem, it does not identify those costs with `r.2` of `Ttc.ttc`: it states the bound for
the operational law which actually executes the supplied certified volume oracle and the
capped sampling oracle.  The theorem takes a
`CVCappedRadialLogExpectedImplementation`; the present construction work does not yet
produce a closed inhabitant of that structure.

The concrete construction uses radius-four kernels throughout the cooling schedule,
with the truncation radius expanding with the phase variance and agreeing with the full
body at the terminal phase.  Switching to a full-body kernel immediately after the cold
block is not valid for unrestricted radial inputs: the required local-radius condition
would either fail or force an `R^4`-scale bound.  The expanding-radius bridge in
`CVAdaptiveRadiusFourCrossWarm.lean` avoids that loss.  The construction also separates
the two warmness roles which an honest cost proof needs.  The possibly compounding
actual-path warm budget selects the mixing deadline, while the expected query cost is
evaluated on the exact retained reference law and therefore does not inherit that
multiplicative budget.  `CVHybridOperationalWarmLog.lean` and
`CVWarmBudgetRecurrence.lean` bound the logarithm of the recursive actual warmness;
`CVRecursiveWarmOperational.lean`, `CVGaussianColdHotRecursiveStep.lean`, and
`CVGaussianColdHotRecursiveOperational.lean` package the recursive seed-projected
cold/hot operation; and `CVColdActualWarmReferenceCostArithmetic.lean` bounds its cold
deadlines while pricing the retained reference separately.  The weighted moment and
retained-history reference-TV capstones are in
`CVGaussianHybridWeightedCertificate.lean`.  These components still have to be assembled
into the closed per-input certificate family needed to inhabit the public implementation
structure; no such inhabitant is claimed in this file.

There is also a coefficient-level distinction between the paper's displayed expression
and its `O*` reading.  The concrete hybrid schedule has `J = O(log R)` hot chunks; both
the estimator sample count and hot proposal accounting contain `J`, hence the literal
bound contains an `R^2 log^2 R` contribution.  The current exact
`cvComplexityShapeClipped` omits every `log R` factor, so no universal constant can bound
the concrete schedule by that smaller expression for unrestricted `R`.  A closed
operational theorem must either retain this polylogarithmic radius factor (the honest
`O*` interpretation) or assume a polynomial radius normalization.

That honest interpretation is a checked interface rather than only an audit note.
`Ttc/Exec/CVRadialLogEnvelope.lean` defines
`cvRadialLogComplexityShapeClipped = cvComplexityShapeClipped *
sourceLogFactor (max 1 R2)^2`.  The operational cap on the hot step introduces one
additional clipped dimension factor, so `Ttc/Exec/CVHotRefreshHonestRuntime.lean` defines

    cvCappedRadialLogComplexityShapeClipped
      = cvComplexityShapeClipped * sourceLogFactor (max 1 R2)^2 * max 1 n.

This extra factor is required by the `delta <= 1/(2n)` branch of the executable hot
deadline; omitting it would not be an honest bound for the current kernel.  The expected
query interface is `CVCappedRadialLogExpectedImplementation`, and
`Ttc/Exec/CVCappedRadialLogInterface.lean` transports exactly that bound to the same-law
TTC run.  The adapter assumes the bundled implementation object rather than constructing
it.

The operational Gaussian construction currently applies in dimensions `21 <= n`.
Accordingly the capped TTC theorem states that premise explicitly even though the abstract
expected-query structure itself is indexed for all positive dimensions.  For `n < 21`,
the repository has a semantic exact-volume witness with zero declared query cost, but it
is not an operational membership-query algorithm and is not used to claim an
unconditional executable theorem.  Removing this final range caveat requires either a
checked padding reduction to dimension 21 or a separately costed low-dimensional oracle.

The remaining CV-to-TTC assembly obligation is now explicit rather than an opaque
certificate hypothesis. For every phase `i`, the truncation/transition error `e_i` must
satisfy the scaled moment-budget inequality

`e_i * exp(R^2/(2*sigma_i))^2 * (1+2*T_i)
  <= (T_i-C_i) * (chain(i+1)/chain(i))^2`.

The current global tail selector proves only the unscaled aggregate
`k * sum_i e_i <= 1/40`; it does not yet prove these phasewise inequalities. Closing
this requires the paper's radius choice (equivalently an `R`-aware phasewise selector),
followed by the scalar comparison of the resulting deadline sum with the capped radial
runtime envelope. Until that bridge is supplied, the public capped interface correctly
remains parameterized by a certified implementation object rather than claiming a fully
instantiated TTC oracle.

Compared with `sections/analysis.tex`'s `thm:runtime`, the checked operational theorem is
an expected query-accounting result, not yet a derivation of the paper's
`O(m n^5 rho^2 r_max)` machine-time bound.  With a supplied capped implementation its CV
call term has the honest shape
`cvComplexityShapeClipped * sourceLogFactor(max 1 R2)^2 * max 1 n`, retaining the
single `eps^-2` factor inside `cvComplexityShapeClipped`, plus confidence amplification
and the finite sum over TTC calls.  The unconditional explicit accounting in
`Ttc/Exec/TTCUnconditionalExplicitRuntime.lean` eliminates the former per-call, rate-cap,
endpoint-price, `rho`, `rMax`, and `Threshold` premises.  Its volume summand has the source
`eps^-2` query shape; obtaining the displayed paper term additionally requires the radial
comparison `R2 <= rho^2` and charging one body-membership query by an `O(n*r_i)` facet
scan.  Its sampling summand uses the proved closed rate cap
`(1+epsPrime)*algScale^n*Vol(F)` and the concrete hybrid endpoint-inspection cap.  The
formal preprocessing theory proves the paper threshold is a lower bound on that scaled
volume, not an upper bound, so replacing this honest cap by the paper's
volume-independent `Threshold` is not valid for arbitrarily scaled inputs without a new
normalization hypothesis.  `Ttc.TTCRuntimePaperArithmetic.paperRuntimeEnvelope`
separately machine-checks the deterministic unsuppressed expression from `thm:runtime`.
With a supplied radial-log CV implementation, the newer TTC adapter removes the former
source-certificate condition but deliberately retains the actual finite CV-call sum and
the capped Poisson/hybrid-sampler sum; it does not rewrite either into the paper's
coefficient-free `Threshold` expression.
Exact-real arithmetic, random generation, and preprocessing are outside this query-cost
model.

Both conjuncts speak about **the same run**, drawn from the one measure

    ttc atoms φ ε δ : Measure (ℝ × ℕ)

defined in `Model/Pseudocode` — `TTC`'s own four inputs and nothing else: accuracy about
`r.1`, running time about `r.2`.  This mirrors
`ApproxNFA.countNFAM A n ε δ : PMF (ℝ × ℕ)`.

The two per-call charges do not appear here.  They enter through `Ttc.ttc`'s *definition*,
`Ttc.ttc = Ttc.ttcCharged atoms φ ε δ (cvVolPriceAt …) (hrSampPriceAt …)`, and the equation
is the lemma `Ttc.ttc_def` (by `rfl`).  `Ttc.ttcCharged` is the price-parametric law every
downstream result is proved over.

Eleven explicit binders — `atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos` — thirteen raw, counting
the implicit `{A} {n}`.  Among them there is no
interpretation, no parameter block, no converter, no oracle, no precision, no
inscribed-ball data and no boundedness hypothesis.

`Pr[p ← μ; E p]` is `(μ {p | E p}).toReal` and `All[p ← μ; E p]` is `∀ᵐ p ∂μ`, both from
`Monadic/MeasurePr`.

Audit path: `Model/`'s four files, `Ttc/Probability/`'s four, and `Ttc/Geometry/`.
`#modelClosureOfType Ttc.ttc_volume_estimate` (`Audit/ClosureCheck`) fails the build if any
constant in this theorem's *type* is defined outside them.

## ⚠ The legacy theorem's two prices are not the run's own prices ⚠

`Ttc.ttc` executes neither oracle being priced: its bundle `Ttc.algOracles` is a closed
term over `Ttc.mcVol` — hit-and-miss Monte Carlo — whose sampling law is the lazy ball
walk.  `cVol`/`cSample` are unit multipliers in `Ttc.stepCost`, so substituting *any* pair
of naturals yields a law of this shape; at `0` the charged cost is identically `0`.
Charging `Ttc.cvVolPriceAt` and `Ttc.hrSampPriceAt` inside `Ttc.ttc` is a **modelling
choice, not a costing of this run**.  Use `ttc_volume_estimate_accounted` for the repaired
statement.  The prices the run *can* be shown to pay are `Ttc.ttcVolPrice` (`Exec/PriceList`)
and `Ttc.ttcSampPrice` (`Exec/SamplePrice`), and both are exponential in `n`.  Read the
boxed warning at the head of `Ttc/Exec/PricedHeadline.lean` before quoting the running-time
conjunct, and **note that nothing anywhere proves `TTC` runs in `O(m·n⁴)`**: the
hit-and-run step count is meaningful only under `Ttc.HitAndRunTheorem11Input` (inhabited
nowhere), the per-draw charge rests on `thm:iso`, the charged cost is an undercount, and the
`n⁴` holds only in the temperature-scale regime `R = O(σ)` (`n⁵` at `R ≍ σ√n`, and
`Arlib.MarkovChains.exists_halfspace_max_lt` shows the obvious repair is **false**).

**The price-parametric, unconditional form has not been lost.**  It is
`Ttc.ttc_volume_estimate_parametric`, over `Ttc.ttcCharged` — the old headline, unchanged
except that the measure now goes by its price-parametric name — and it — not this
theorem — is what `Ttc/Exec/TheoremPoly.lean` and `Ttc/Witness/FullTwoCube.lean` consume.
Non-vacuity for *this* theorem is `Ttc.TwoCube.ttc_volume_estimate_two_cube_fixed`
(`Ttc/Witness/FixedPriceTwoCube.lean`).

[`AUDIT.md`](../../AUDIT.md) §1e is written to be read alongside this file, and carries
what is deliberately not restated here: which quantifier the running-time half uses and
why the pointwise form is false; why this is a `Measure` and not a `PMF`; the definitional
closure; the three preprocessing steps the headline certifies `alg:ttc` *plus*; the two
residual hypotheses `hφ` and `hpos`; and that `hbdd` was derived rather than dropped
(§1h).
-/

namespace Ttc

open MeasureTheory Set
open Ttc.Monadic

/-- The existing TTC execution charged at the two uniform prices that are actually proved
for its hit-and-miss volume calls and lazy-ball-walk sample calls.  This does not change
the estimator law; it repairs only the accounting coordinate. -/
noncomputable def ttcAccounted {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ) : Measure (ℝ × ℕ) :=
  ttcCharged atoms φ ε δ (ttcVolPrice atoms φ ε δ) (ttcSampPrice atoms φ ε δ)

/-- Final theorem for the run that this repository actually implements.

Unlike the legacy `ttc_volume_estimate`, the second coordinate is charged using
`ttcVolPrice` and `ttcSampPrice`, the proved uniform bounds for the concrete
hit-and-miss/lazy-ball-walk oracle bundle.  The resulting expression is not claimed to be
polynomial—those two prices are exponential—but accuracy and cost now refer to the same
honestly accounted run. -/
theorem ttc_volume_estimate_accounted {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    (1 - δ ≤
      Pr[r ← ttcAccounted atoms φ ε δ;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    (All[r ← ttcAccounted atoms φ ε δ;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ)
          * (((ttcVolPrice atoms φ ε δ : ℕ) : ℝ) +
            ((ttcSampPrice atoms φ ε δ : ℕ) : ℝ) *
              (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                + 15 * (Real.log (15 / (2 * δ))
                  + Real.log ((toDNFd (preprocess atoms φ)).length)) + 1))]) := by
  simpa only [ttcAccounted] using
    ttc_volume_estimate_parametric atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
      (ttcVolPrice atoms φ ε δ) (ttcSampPrice atoms φ ε δ)

/-- **`thm:volumettc` + `thm:runtime`, at two fixed per-call prices.**  `TTC` is run on
`F = (atoms, φ)` at accuracy `ε` and confidence `δ`; both halves speak about the same run.

* **Accuracy.** `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, at the **user's own**
  `Vol(F)`, **unconditionally** under the nine binders.  The output is
  `Model/Pseudocode`'s `Ttc.ttcRun`, which takes no oracle argument.
* **Running time.** `All[…]` is `∀ᵐ`, with **no termination hypothesis**: the absorption
  loops halt `Ttc.ttc`-almost surely.  At any `(R, γ)` bounding the fixed sampling price
  quartically, `alg:ttc`'s charged cost is at most `m · n⁴ · (2⁴²·volFac + 2⁶²·rfac·(R²/γ²)
  ·log(2R)·(Θ+1))`, written out as explicit arithmetic in `ε`, `δ`, the run's own geometry
  and `m = |toDNFd (preprocess atoms φ)|`.  The guard is discharged at the run's own
  geometry by `Ttc.PricedHeadline.all_ttc_cost_le_quartic_at_run`, which leaves visible the
  two binders nothing in this repository proves — the warm start `M ≤ (2R)ⁿ` and `2⁻ⁿ ≤ ε'`.
  It guards this conjunct only, so the accuracy half stays unconditional.

⚠ **The run does not execute the two oracles being priced.**  Correctness, not efficiency:
nothing here proves `TTC` runs in `O(m·n⁴)`.  See this file's docstring, the boxed warning
in `Ttc/Exec/PricedHeadline.lean`, and `AUDIT.md` §1e. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) the estimate is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[r ← ttc atoms φ ε δ;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) at any `(R, γ)` bounding the fixed sampling price quartically, almost
    -- every run is charged at most `m·n⁴·(2⁴²·volFac + 2⁶²·rfac·(R²/γ²)·log(2R)·(Θ + 1))`
    (∀ R γ : ℝ, 1 ≤ R → 0 < γ →
      ((hrSampPriceAt atoms φ ε δ : ℕ) : ℝ)
          ≤ 2 ^ 62 * (n : ℝ) ^ 4 * canonRfac (toDNFd (preprocess atoms φ))
              * (R ^ 2 / γ ^ 2) * Real.log (2 * R) →
      All[r ← ttc atoms φ ε δ;
        (r.2 : ℝ) ≤
          ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
            * (2 ^ 42
                  * ((canonRfac (toDNFd (preprocess atoms φ)) + 1)
                      * Real.log (8 / (algBlock atoms φ ε δ).epsPrime ^ 2)
                      * ((1 + Real.log (1 + (n : ℝ)
                            * ((algGamma atoms φ ε δ)⁻¹
                                * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                                    (preprocess atoms φ))) ^ 2)) ^ 4
                          * Real.log (1 / (algBlock atoms φ ε δ).deltaPrime)
                          / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10) ^ 3))
                + 2 ^ 62 * canonRfac (toDNFd (preprocess atoms φ)) * (R ^ 2 / γ ^ 2)
                    * Real.log (2 * R)
                    * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                        + 15 * (Real.log (15 / (2 * δ))
                            + Real.log ((toDNFd (preprocess atoms φ)).length))
                        + 1))]) :=
  ⟨(ttc_volume_estimate_parametric atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos _ _).1,
    fun R γ hR1 hγ0 hcS =>
      PricedHeadline.all_ttc_cost_le_quartic atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos _ _
        (2 ^ 42) _ _ R γ (by norm_num)
        (PricedHeadline.zero_le_volFac atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1)
        (PricedHeadline.one_le_canonRfac atoms φ ε hε0 hε1 hn hφ hpos) hR1 hγ0
        (PricedHeadline.cvPrice_le atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1) hcS⟩

#print axioms ttc_volume_estimate
#print axioms ttc_volume_estimate_accounted

end Ttc

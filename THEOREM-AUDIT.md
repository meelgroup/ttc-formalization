# Manuscript theorem audit

`Kr25Ssmxt/Model/` is the statement and program audit surface; proofs live in
`Kr25Ssmxt/Analysis/`. `#krModelClosureOfType` checks that each public statement
unfolds only through `Model/` definitions, and `#krSurplusIn` checks that `Model/`
contains nothing the public statements do not use.

## Current status (2026-11-07)

**Build.** Lean/Mathlib `v4.35.0`, arlib `8d08f89`, arlib-community `db1f401`
(`github.com/uddaloksarkar/arlib-community`). `lake build Kr25Ssmxt` succeeds
with no errors and no `sorry`. Both public theorems depend only on `propext`,
`Classical.choice` and `Quot.sound`.

**Public theorems** (`Model/Theorem.lean`), both about `communityManuscriptTTC`,
the manuscript's Algorithm 1 with the concrete oracles:

| Paper | Lean | Status |
|---|---|---|
| Theorem 1 (`thm:volumettc`, accuracy) | `ttc_theorem1_volume_accuracy` | Proved. No prior-work hypothesis, no regime premise. |
| Theorem 3 (`thm:runtime`, runtime) | `ttc_theorem3_corrected_expected_runtime` | Proved in a corrected form (see below). |
| Theorem 2 (decomposition) | — | Not formalized beyond the volume equality `Decomposition.solution_ae`. |

Shared hypotheses: `n ≥ 21` and a bounded solution set.

**Oracles, discharged to arlib-community public headlines.**
- *Volume:* the program run is arlib-community's `CV18.cv18Program`
  (`CommunityCV18.algorithm` in `Model/Run.lean`) on an exact facet-membership
  query, rescaled and clipped as in the paper. Its guarantee is
  `CV18.cv18TheoremOneOne_program`.
- *Sampling:* arlib-community's `HitAndRun.finiteFacetStep` walk in unit-inball
  coordinates, mapped back and KV97-rounded with rejection
  (`normalizedHitAndRunPointLaw`). Its mixing bound is `HitAndRun.hitAndRun_mixes`.
- A dependency walk confirms the project references neither internal capstone
  (`volumeTheorem_finalScheduled`, `tvLe_iterate_lazy_hitAndRun_uncond`)
  directly; they appear only inside the proofs of those headlines.

**Theorem 1 proof outline.**
1. Strong Markov property of one refreshed component: every refreshed component
   law is refresh-stationary (`manuscriptOriginRefreshedComponentLaw_bind_stationary`,
   `ManuscriptRefreshStationaryStep.lean`, `ManuscriptRefreshStationaryKernel.lean`).
2. With the CV18 outcomes fixed, the ghost fold's point counts at every dyadic
   level are the certified fixed-level Poisson process
   (`ManuscriptOriginGivenVolumesFold.lean`, `ManuscriptOriginStepsCertified.lean`).
3. Ending above the penultimate cutoff costs at most `δ/(6m)` per component,
   i.e. `δ/6` (`ManuscriptOriginCrossing.lean`, `ManuscriptTheoremOneCrossing.lean`);
   the remaining levels cost at most `δ/6` by the dyadic Chernoff sum
   (`ManuscriptTheoremOneGivenOutcomes.lean`).
4. Integrating over the CV18 outcome vector adds the `δ/4` CV18 failure budget,
   and the lattice comparison turns the `ε/2` lattice estimate into an `ε`
   volume estimate (`ManuscriptTheoremOneFinal.lean`).

**Theorem 3 statement.** The charged execution has exactly the output law of
`communityManuscriptTTC`, and its *expected* operation count is at most
`T_preprocessing + m · 30 n⁵ r_max ρ² · S · (cap+1)(parameterFactor+1)` with the
input-only scale `S = 2 + log₁₀⁺ γ + log₁₀⁺(1/minᵢ γᵢ) + log⁺R_max`
(`TTCRuntime.theorem3InputScale`), where `γ = 64mn/(ε/96)·√log(384r/ε)` is the
radius `getprec` requires. The bound no longer mentions the precision `b`:
`getPrecision_le_theorem3PrecisionBound` shows `getprec` returns
`b ≤ 1 + log₁₀⁺ γ + log₁₀⁺(1/minᵢ γᵢ)`.
This corrects the printed claim in two ways: it is an expected (not worst-case)
bound, since the second loop and the rejection sampler have unbounded iteration
counts; and it carries a precision factor, which the printed bound omits (a
two-cube family forces `Ω(b)` first-loop halvings with every quantity in the
printed bound fixed). In particular the bound grows like `log(1/minᵢ γᵢ)`: a
very small component forces a fine lattice, and neither `ρ` nor `maxᵢ Rᵢ`
captures this.

**Fidelity to the manuscript** (`sections/algo.tex`, `sections/analysis.tex`).
- Matches Algorithm 1: `ε' = ε/12`, `δ' = δ/(4m)`, the printed `Threshold`,
  `t = Threshold·10^(bn)·VolED`, overlap deletion, the first loop
  `while p ≥ Threshold/t`, `N ~ Pois(tp)`, the second loop
  `while N + |X| > Threshold` with binomial thinning (realised by labelled fair
  coins), sampling, append, the output `|X|/(p·Threshold·10^(bn))`, and the
  clipping of VolED to `[(1-ε')(2γ/√n)^n, (1+ε')(2R)^n]`. The error budget
  `δ/6 + δ/6 + δ/4` is the paper's.
- Hypotheses not in the printed statements: a bounded solution set (needed for
  finite volume and the clipping radii) and `n ≥ 21` (inherited from the
  formalized Hit-and-Run mixing theorem; the paper cites Lovász–Vempala without
  a dimension restriction).
- `getprec` is concrete (`getPrecision`, `Model/Program.lean`) and is TTC's
  only precision stage: `TTCPreprocessor.choosePrecision` is
  `getprec(·, ε/96)`, returning `⌈log₁₀ maxratio⌉` with
  `maxratio = max(1, maxᵢ γ/γᵢ)`. `PrecisionAdequate` is exactly the printed
  condition `γ ≤ 10ᵇ γᵢ` at `η = ε/96`, proved by `getPrecision_adequate`.
  `PrecisionAdequate.split` derives the two uses in the analysis: the union
  lattice comparison at `ε/8` and the sampler corollary at `ε' = ε/12`
  (`θ = ε'/8 = ε/96`). One difference remains: `γᵢ` is each component's
  certified inball radius, not the maximum inscribed radius the paper names;
  any inball gives a valid, possibly larger, precision.
- Preprocessing returns full-dimensional components whose union agrees with the
  solution set almost everywhere; empty or degenerate DNF cubes (volume zero)
  are dropped.

**Open items.**
- A Lean proof that the six scheduled CV18 logarithmic factors in
  `theorem3ParameterFactor` are polylogarithmic in the public parameters (needed
  only for the paper's `Õ` notation; the exact bound is proved).
- Boolean abstraction and DNF conversion (Theorem 2).
- Manuscript edits: state boundedness; state Theorem 3 in expectation with the
  precision factor and the second-loop and `getprec`/decomposition costs; add
  `minᵢ γᵢ` (the smallest inradius) to the quantities whose polylogarithmic
  factors `Õ` suppresses, since the runtime grows like `log(1/minᵢ γᵢ)`.
- Model surplus: `samplerRadiusRequirement`, `ApproxParams.latticeEta`,
  `TTCRuntime.theorem3PrecisionScale` and `getPrecision_adequate` are defined
  under `Model/` but no longer reached by a public statement (reported by
  `#krSurplusIn`, alongside older entries).

**Removed material.** The older `ttc`/`processComponent(s)` program and
`communityTTC` (Poisson draw before a single thinning loop, output `|X|/p`), its
conditional theorem `ttc_volume_accuracy` with the `Prior`/`StreamingCoreAccuracy`
hypothesis, the unnormalized sampler and older oracle bundle, the older runtime
certificate (`ttc_total_runtime_theorem3`), and the arbitrary-oracle
label-freshness and dyadic-rate lemmas were removed: none is used by either
public theorem (checked by a dependency walk), and that program is not the
manuscript's Algorithm 1.

**Lean 4.35 notes.** `Measure.map` of a non-measurable function is now a Dirac
measure, so bind/map bounds carry explicit measurability hypotheses;
`Measure.prod` unfolds to an `SFinite` case split (use `Measure.prod_eq_bind_map`);
`MathlibCompat.lean` restores `Measure.isProbabilityMeasure_map`.

## History

The notes below record how the formalization developed, oldest first within
each part. They mention definitions and theorems that have since been removed
(see "Removed material" above); the "Current status" section is authoritative.

### Theorem 1 (`sections/analysis.tex`, `thm:volumettc`)

`ttc_volume_accuracy` is a conditional accuracy theorem, not yet the manuscript's
unqualified claim. It assumes `Prior.streamingCoreAccuracy`, dimension at least 21,
a bounded solution set, a certified preprocessor, and either an empty decomposition
or the displayed high-intensity lattice-volume condition. `Prior` is an explicit
hypothesis, not an axiom silently introduced by Lean. The remaining streaming
result must be proved, and the input domain of the manuscript statement must be
made precise: an unbounded solution set can have infinite volume while TTC returns
a finite `NNReal` estimate.
`ManuscriptEmptyAccuracy.lean` proves the empty-decomposition branch for the
current program, and `ManuscriptLatticeAccuracy.lean` proves the deterministic
step from a lattice-count guarantee to volume accuracy for any probability
output law. `ManuscriptProbabilityMeasure.lean` now proves that the full
`communityManuscriptTTC` output law has total mass one without `Prior` or a
streaming hypothesis. `ManuscriptPoissonMarking.lean` records the imported exact
Poisson marking and half-thinning identities, and
`ManuscriptPointIntensity.lean` proves the per-point scaled intensity bounds.
`ManuscriptVolumeGeometry.lean` proves that the manuscript's clipping interval
contains each component's true volume and discharges the concrete clipped CV18
volume contract; the normalized Hit-and-Run batch contract is proved in
`HitAndRunSamplingOracle.lean`.
`ManuscriptUnionLatticeNonempty.lean` proves the finite union has a positive
lattice count when the decomposition is nonempty, and
`ManuscriptDyadicCutoff.lean` proves the cutoff's adjacent-power inequalities.
`ManuscriptLabelFreshness.lean` proves that stored and pending copy labels stay
distinct through the program's state transitions.
`ManuscriptCoinBlockLaw.lean` proves the fair coin stream supplies independent
round streams to distinct labels, each fixed-round survival decision has
probability `2^-rounds`, and the actual stored-plus-pending population at a
fixed round is the count of these independent decisions.
`ManuscriptReachableLabels.lean` proves label freshness holds almost surely
through each complete randomized component transition and the sequential
component fold, for arbitrary oracle laws.
`ManuscriptBernoulliCount.lean` identifies the actual fixed-round
stored-plus-pending population as a binomial law with parameters
`stored copies + pending count` and `2^-rounds`. It also proves that thinning
the program's pending Poisson count yields a Poisson count with the scaled mean,
and that an iid point batch drawn from that fixed-round count has independent
Poisson counts at each lattice point.
`ManuscriptPoissonVectorSum.lean` proves that pointwise addition of two
independent finite Poisson count vectors yields an independent Poisson vector
whose point rates add. This is the union-prefix update needed after deleting
overlap and introducing the next component's batch.
`ManuscriptPoissonVectorRestriction.lean` proves that restricting an independent
Poisson vector to the points outside the incoming component preserves the
product law, which gives the fixed-level deletion step.
`ManuscriptPoissonVectorDeletion.lean` proves the fixed-level update in one
law: zeroing old counts on the incoming component and adding an independent
new Poisson vector produces pointwise independent Poisson counts with the
corresponding updated rates. It composes this with the program's Poisson pending
draw, labelled fixed-round thinning, and iid point batch, giving a complete
fixed-level component count-vector update.
`ManuscriptFixedLevelPrefix.lean` iterates those updates and proves the
independent Poisson point-count invariant for every fixed-level prefix.
`ManuscriptPoissonVectorTotal.lean` proves the prefix's total count is Poisson
with mean equal to the sum of its point rates and obtains an explicit
two-sided Chernoff failure bound. Its imported Poisson event bridge and
scalar tail proof were repaired to build with the current Lean library
without importing the conflicting second Hit-and-Run hierarchy.
The coupling of this fixed-level process to the actual adaptive manuscript
run, and the resulting stopping-level concentration bound, remain open.

### Theorem 3 (`sections/analysis.tex`, `thm:runtime`)

Current progress: `Model/Program.lean` now contains a costed version of the
manuscript TTC control flow, and `Model/Run.lean` instantiates it with charged
CV18 and normalized Hit-and-Run oracles. `CostedMeasureMonad.lean` proves the
writer-law marginal and expected-cost composition inequalities, including an
almost-sure continuation rule for adaptive state bounds;
`ManuscriptCostedOracles.lean` proves the two concrete oracle marginals;
`ManuscriptThinningCosts.lean` proves the first-loop deterministic expected
charge and its logarithmic exit bound. `GeometricRetryExpectation.lean` proves
that a rejection attempt with acceptance probability at least one half has
at most two attempts in expectation, including the independent batch charge.
`FairThinningExpectation.lean` proves the exact expected survivor population
after a fixed number of rounds, its Markov tail, and an expected bound for the
second loop's first-exit counter and charged operation law. The bound is
`2 (stored copies + pending count) / (floor threshold + 1)` rounds.
`PoissonMean.lean` proves the Poisson first moment and integrates the count-loop
charge over the pending count. It yields at most four expected rounds when the
stored population and Poisson mean are each below the guard threshold.
`FairThinningExpectation.lean` also proves almost-sure loop exit and the
stored-population bound after appending the requested batch.
`AcceptanceBudget.lean` and `ScaledVolumeBridge.lean` discharge the concrete
normalized sampler's `1/2` acceptance lower bound from `PrecisionAdequate`,
the integer-lattice comparison, KV97 inflation, and the TV deadline. They
therefore prove the certified charged sample batch's expected retry cost.
`ManuscriptComponentExpectation.lean` now composes these lemmas through each
adaptive component and the whole charged TTC run. The public
`ttc_expected_runtime_explicit` theorem proves an expected-operation bound of
`T_preprocessing + Σᵢ Bᵢ`, with each explicit `Bᵢ` defined in `Model/Run.lean`.
`CV18RoundnessBound.lean` proves the imported CV18 roundness input is at most
`4ρ²+1` and restates the amplified CV18 program's exact cap in terms of its
proved scheduled complexity rate. `RateLogBound.lean` proves that the first-loop logarithmic counter
is bounded by `4bn + clog₂(ceil(clipped-volume-bound)+1)`. The public
`ttc_expected_runtime_linear_precision` theorem replaces that term in the
whole-run expected allowance, exposing linear decimal-precision dependence.
`NormalizedDiameterRuntime.lean` uses the existing precision certificate to
show KV97's inflation width is at most the scaled inradius. Consequently the
normalized Hit-and-Run diameter is at most `4ρ`, its warmness is at most
`(4ρ+1)^n`, and its selected step count is bounded by the imported deadline
with `2^68 n²ρ²` outside the logarithm. The scaled inflated body lies in a
ball of radius `5·10^b R_i+1`, whose logarithm is at most
`b log 10 + log 6 + log⁺ R_max`. The TV-tolerance logarithm is bounded by
`n` times this term plus logarithms of `1+8/epsilonPrime` and the dimension's
unit-ball volume. The public `ttc_expected_runtime_geometric` theorem now
uses the resulting concrete sampler-step envelope. These are proved Lean
inequalities. `CV18RoundnessBound.lean` also specializes the imported query cap
to `45(64C+1)n³ρ²/eps_CV18²` times the exact six-factor scheduled logarithmic
product.
`ClippedVolumeRate.lean` proves `γ_i ≤ R_i`, bounds the manuscript volume clip
by `2(4R_i)^n`, and reduces the first-loop count to
`4bn+2+n·clog₂(ceil(4R_max)+1)`. The public
`ttc_expected_runtime_theorem3_expanded` theorem composes these reductions
into a whole-run expected-operation bound. Its fixed-charge corollary sets
the CV18 non-query allowance to one membership-equivalent unit per call.
The public `ttc_expected_runtime_uniform_budget` theorem further bounds the
whole expected cost by `T_preprocessing + m · B_uniform`, where `B_uniform`
uses the maximum facet count, the imported CV18 query envelope, the imported
Hit-and-Run deadline envelope, the sample cap, and the clipped first-loop
counter. The only axioms in this result are Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. `NormalizedDiameterRuntime.lean` now
also proves the dimension's unit-ball volume is at most `2^n`, hence its
logarithmic contribution is at most `2n`, and derives an explicit selected
sampler-step bound with `2^68 n^4 ρ² (1+b+log⁺R_max)` outside a factor
depending logarithmically on `ρ` and `1/epsilonPrime`.

`ThresholdCapBound.lean` proves the sample cap is at most the ceiling of
`27 log(24/δ)/epsilonPrime² + 15(log(6/δ)+log m)` for nonempty decompositions.
`UniformBudgetAlgebra.lean` proves the whole uniform component allowance is at
most `30 n⁵ r_max ρ² (1+b+log⁺R_max) (cap+1) (parameterFactor+1)`; the
parameter factor is defined in `Model/Run.lean` as the imported CV18 six-log
product divided by the squared internal tolerance plus an explicit
Hit-and-Run mixing logarithm and a constant. The public
`ttc_expected_runtime_theorem3_headline_scale` theorem lifts this bound to
the entire charged run, including `T_preprocessing` and the leading `m`.
Its statement passes model-closure checking and uses only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms. The `ENNReal.ofReal`
right side is proved finite by `ttc_theorem3_headline_budget_finite`, so this is a nonvacuous explicit
expected-operation bound with the requested geometric monomial.

`ManuscriptRateKernelMeasurable.lean` proves joint measurability of both
charged thinning-loop kernels.
`ManuscriptSampleAppendMarginal.lean` proves the charged sampling-and-append
tail has the uncharged state law, proves the needed joint kernel measurability,
and composes the marginal identity through count thinning, a jointly measurable
varying-state Poisson kernel, rate thinning, deletion, the outer CV18
volume bind, and the component sequence. `ManuscriptRunMarginal.lean` proves
that forgetting all operation counts, including after the final estimate,
gives exactly `communityManuscriptTTC`.

`ttc_theorem3_corrected_expected_runtime` combines this output identity and
the explicit expected-cost bound in one public statement. Still required for
the manuscript's tilde-O notation: prove within Lean that the six imported
CV18 scheduled logarithms are polylogarithmic in the public parameters. The
exact headline-scale inequality retains these six factors.
The public `ttc_total_runtime_theorem3` remains a certificate inequality;
`ttc_expected_runtime_theorem3_headline_scale` is the proved concrete
expected-operation bound for the charged run.

`ttc_total_runtime_theorem3` currently proves an accounting inequality for a
caller-supplied preprocessing-operation count plus the concrete geometric
certificate. It does not prove an expected-time bound for the execution of TTC.
It now additionally accepts the measured non-query CV18 arithmetic cost of
each component and a **public hypothesis** that this cost is at most
`C * n * r_i * (Q_i + 1)`, where `Q_i` is the certified CV18 query budget.
The right side includes the sum of these allowances. This hypothesis is not
provided or proved by the imported CV18 development.
The CV18 portion now explicitly charges `n * r_i` for every certified
membership call: `CommunityCV18.membershipArithmeticCostBound` reprices each
imported charged execution, and `TTCMembershipRuntimeCertificate.operations`
sums `n * r_i * volumeQueryCount_i`. This is a membership-work bound; CV18's
non-query arithmetic is outside the imported charged semantics.
`Model/Prelude.lean` also states the operational charges requested for the
costed TTC trace: a facet scan or Hit-and-Run chord step is `n*r_i`,
coordinate rounding is `n`, a rejection membership test is `n*r_i`, and
deletion, a stored-copy coin, Poisson and binomial draws, appending, and scalar
operations each cost one. A deletion pass checks each stored copy and charges
one extra per removed copy. A count-thinning round charges its stored-copy
coins and one binomial draw, independent of the pending count's magnitude.
The primitive charges and their whole-run expected-cost composition are
settled; no additional operation prices are needed. The remaining obligations
are the analytic polylogarithmic classification of the concrete CV18 scheduled
factor and any manuscript claim about bit complexity.
The updated manuscript still says the algorithm "runs in time" without saying
"in expectation," even though its sampler analysis bounds the rejection loop
only in expectation. Its displayed main-loop calculation also does not charge
the second thinning loop or a concrete `getprec`/decomposition cost. Thus that
printed runtime statement is stronger than both the Lean certificate and the
argument currently provided in the manuscript.

Reading the complete `main-arxiv.pdf` reveals that the printed asymptotic
statement also omits a necessary dependence on its *global* precision `b`.
Fix `n ≥ 21`, `m = 2`, `ε`, and `δ`. Let one component be a unit-size cube and
the other a cube of side `2·10^{-B}`. Both have `2n` facets and the same
constant radius ratio `√n`; `R_max` stays constant. Algorithm 2 chooses
`b = B + O(1)` because of the small cube. When Algorithm 1 processes the
unit-size cube, a successful volume estimate gives
`t/Threshold = Θ(10^{bn})`. Its first while loop therefore executes
`Ω(nb) = Ω(B)` rate halvings, even when the stored multiset is empty. The
variables permitted in the printed `\widetilde O(m n^5 ρ² r_max)` bound stay
fixed, so this family contradicts that bound even *in expectation*. The
proposed explicit factor `1+b+log⁺R_max` repairs this scale mismatch.

The second while loop and rejection sampler make a deterministic worst-case
runtime bound impossible under the manuscript pseudocode: either can take
arbitrarily many random iterations. For the corrected expected-time claim,
the omitted second-loop accounting has a short argument. At its entry,
`|X| ≤ Threshold` and the first loop ensures the fresh Poisson mean is below
`Threshold`. After `k` fair thinning rounds, the expected retained-plus-pending
count is below `2·Threshold/2^k`. Markov gives a geometric tail for additional
rounds and at most four rounds in expectation under the formalized guard. The appendix separately
derives at most `3/2` rejection attempts in expectation. Thus these omissions
need Lean proofs but do not invalidate the corrected expected arithmetic bound
under the agreed unit charges and CV18 non-query hypothesis.
The `communityManuscriptTTC` law records only an estimate, not an execution cost. The
certificate fixes the imported CV18 query budget and the normalized Hit-and-Run walk deadline,
but the finite-supremum overheads have no proved polynomial/polylogarithmic
envelope.

The costed run now has a proved output marginal equal to
`communityManuscriptTTC` and an explicit finite expected-cost bound.
Theorem 1's high-probability
control of a small rate does not alone bound the expected number of rounds on
the exceptional event.

`PaperRuntime.runtime_tail_le_of_expected_cost` now proves the Markov transfer:
if a costed law has expected cost at most `budget`, then the probability of cost
at least `budget / failure` is at most `failure`. The cutoff has a degree-one
dependence on `1 / failure`. This is an auxiliary high-probability theorem,
not yet a TTC runtime result, because it has not been specialized using the
proved expected-cost bound.
`PaperRuntime.community_ttc_runtime_tail_of_expected_cost` instantiates the
cutoff with preprocessing, the concrete geometric certificate, and an explicit
extra-work budget. Its hypotheses still expose the marginal equality and
final envelope, but the former is now proved separately.
Its marginal-equality hypothesis now names `communityManuscriptTTC` rather
than the older `communityTTC` law. `ManuscriptThinningCosts.lean` constructs
costed laws for both manuscript thinning loops and proves that forgetting
their charges recovers exactly the corresponding uncharged loop laws. It also
proves that an explicit dyadic exit level bounds the deterministic first-loop
charge. The component costs have been composed into one costed TTC law. Its
global expected-cost bound and marginal equality are proved.

### Program fidelity to `sections/algo.tex`

The diff from the last commit touching `lean/` (`eeea231`, 2026-09-11) to
`HEAD` changes Algorithm 1 in several material ways. The current manuscript
calls `getprec` with `ε/96`; scales each volume by
`Threshold * 10^(b*n)` before the Poisson draw; clips CV18 volume estimates;
performs a rate-controlled thinning loop **before** that draw; binomially thins
the pending count in the second loop; and divides the output by
`p * Threshold * 10^(b*n)`.

`Model/Program.lean` now defines `manuscriptTTC` with those two loops, the
scaled Poisson intensity, and the output normalization. `Model/Run.lean`
defines `communityManuscriptTTC` and applies the paper's radius-based clipping
to concrete CV18 outcomes. Multiplicity is retained through labelled copies.
The old `ttc` and `communityTTC` definitions remain because the current
probability proof chain unfolds them. In particular, the public
`ttc_volume_accuracy` theorem **still concerns the old program**, and no
accuracy theorem has yet been proved for `communityManuscriptTTC`.

The older `ttc` core in `Model/Program.lean` is **not** the manuscript's TTC probability
program. In the manuscript, line 24 sets
`t = Threshold * 10^(b*n) * VolED(P)`, line 32 performs a deterministic
rate-based halving loop before drawing `N ~ Poisson(t*p)`, and line 46 returns
`|X| / (p * Threshold * 10^(b*n))`. The current `processComponent` draws
`Poisson(volumeOutcome * state.rate)` before a single count-based thinning
loop, while `TTCState.initial` sets `rate = 1` and `TTCState.estimate` returns
`|X| / rate`. These laws differ: with positive probability the realized
Poisson count is below `Threshold` even when the manuscript's first loop
requires a halving. The manuscript's described clipping of `VolED` to the
inner/outer-radius volume interval is absent from `communityCV18VolumeLaw`.
`TTCPreprocessor.choosePrecision` is an abstract adequate choice, not the
manuscript's `getprec` implementation.

`Model/Run.lean` does import and connect CV18 and finite-step Hit-and-Run/KV97,
but `communityTTC` is merely `ttc` with those oracles. The new
`communityManuscriptTTC` uses the corrected core and clipped volume law. The
current accuracy theorem, its `Prior`
hypothesis, and the probability/measurability chain are all about the current
`processComponent` law. A faithful replacement requires new proofs of that
chain and of the theorem's stochastic core; changing the two model files alone
would leave the existing headline unsupported. The manuscript accuracy claim
also remains conditional on `Prior` in this repository independently of the
program mismatch.

The model still has an abstract `choosePrecision` witness rather than the
printed `getprec` computation at `ε/96`; its adequacy predicate currently uses
`ε/8` for the lattice comparison. The manuscript sampler now runs its finite-facet
walk in unit-inball coordinates and maps the result back before KV97 rounding.
`NormalizedHitAndRunGeometry.lean` proves the map sends uniform measure on the
normalized body to uniform measure on the inflated scaled body, proves the TV
contract, and bounds the normalized diameter by the outer/inner radius ratio
times the small inflation factor. The model now also has a one-point retry
trace: it draws a geometric number of failed proposals and charges each attempt
for its finite walk, coordinate rounding and membership test. Forgetting this
charge provably recovers the conditional accepted-point law. The corresponding
independent batch sums these charges and has the manuscript batch law as its
first marginal. The main `communityManuscriptTTC` consumes the uncharged
marginal; the costed whole-run law is now proved to forget to that same law,
and its expected-cost bound is proved. The revised appendix
specifies tolerance `ε/(16W)` with `W=(2R)^n` and an actual rejection loop with
expected at most `3/2` attempts. The Lean retry lemma gives the weaker bound
two; `ScaledVolumeBridge.lean` now proves its acceptance premise for the
certified concrete sampler.

The manuscript's revised Theorem 1 proof uses a Poisson multiset invariant
after the scaled intensity, a no-undue-halving argument that separates the
first and second while loops, and union bounds for the volume and sampling
events. The current `Prior.streamingCoreAccuracy` applies to the older core,
so it does not discharge those new obligations. Theorem 2's decomposition
statement and proof changed only editorially in this diff; the existing
`Decomposition.solution_ae` expresses the volume-relevant equality but does
not implement Boolean abstraction or DNF conversion. The corrected
expected-cost inequality and whole-run output marginal are proved for the
charged manuscript run; the formal polylogarithmic simplification remains
unproved.

`ManuscriptMarkingMeasure.lean` now proves the measure-level Poisson marking
identity for an iid batch supported on a finite subset of the countable
lattice space. It identifies the count-vector law with a product of Poisson
measures, derives each point's Poisson marginal, and instantiates the identity
for the normalized Hit-and-Run batch used by the manuscript run. It also
proves that summing the marked point counts recovers the original Poisson draw,
and proves measure-level Poisson thinning through a binomial kernel. These lemmas
have only Lean's standard axioms. `ManuscriptNoUndueFirstHalving.lean` also
combines successful component volume estimation, the certified lattice
comparison, the component-to-union count bound and the dyadic cutoff to show
that the first while-loop makes no further halving at the last admissible
level. The adaptive second thinning loop still needs a coupling to fixed
dyadic levels, although crossing a fixed level is now proved to imply an
oversized population at that level. The full nonempty-prefix invariant, its concentration and the
final failure-probability bound are not yet proved.

The fixed-level analysis now proves the Poisson law for every
delete-and-append prefix: distinct copy labels give independent thinning,
Poisson marking gives independent point counts, and deleting overlap before
adding a new batch updates their rates coordinatewise. The total prefix count
is Poisson with mean equal to the sum of point rates. The rate-envelope lemma
gives a two-sided Chernoff bound for the manuscript's count window. At the
penultimate dyadic cutoff, the upper envelope and the union's lattice count
give a total mean below two thirds of the threshold, yielding the explicit
`exp(-Threshold/15)` upper-tail bound. These results concern an analysis
process with prescribed component rates. Its coupling to the adaptive
`communityManuscriptTTC` execution, including the stopping level and
conditioning on successful oracle outcomes, remains open. Thus the public
Theorem 1 declaration still concerns the older core and requires `Prior`.
The live program is also proved to retain a dyadic rate almost surely at
every component prefix. Consecutive first- and second-loop coin blocks compose
to one absolute-level thinning operation on stored copies. Under a successful
volume estimate, the first loop cannot jump past the dyadic cutoff even when
it makes several halvings; a second-loop jump past that cutoff implies that
the fixed-level stored-plus-pending population exceeds the threshold.
The manuscript threshold inequalities now give the explicit cutoff budget
`δ/(6m)` per component and the geometric two-sided concentration budget
`δ/6`. The count envelope is proved to imply an `ε/2` relative estimate of
the scaled lattice count at a positive rate. The empty-decomposition case and
the deterministic conversion from an `ε/2` scaled-lattice estimate to an `ε`
volume estimate are proved for `communityManuscriptTTC`. The latter is an
internal conditional assembly lemma; its stochastic lattice-estimate premise
has not yet been discharged for the adaptive run.

The current Theorem 1 work also projects the actual labelled `TTCState` onto
point-count vectors. Removal and append agree exactly with coordinate deletion
and addition; actual IID batches with a Poisson count satisfy the product
Poisson marking law under this projection. The certified fixed-level process
now uses the concrete component geometry and normalized sampler point law. Its
full component list covers the finite coded union, and every component has the
proved two-sided point-rate envelope. For each admissible dyadic level, its
total count has the manuscript's Chernoff bound; the geometric sum is at most
`δ/6`. At the penultimate cutoff, every certified component prefix has the
upper-tail budget `δ/(6m)`. The actual first- and second-loop thinning of
stored points and pending count are represented jointly as a function of
independent decisions indexed by copy label. The
concrete certified sampler is now proved to implement the labelled-state
Poisson marking law, both after overlap deletion and after a fixed number of
pending-count thinning rounds. These are fixed-level laws. The
independent product of the actual CV18 component outcome laws is proved
to have all volume estimates tagged good and relatively accurate with probability at least
`1 - δ/4`. The complete charged manuscript component trace records each CV18
outcome and has both the independent product CV18 law and the charged component
fold as its exact marginals. The per-component CV18 success budget is proved on
that same trace. The remaining central step is a common coupling across the adaptive halving and
component loops, followed by the good-oracle event and stopping-level union
bound. The public Theorem 1 statement is still the older conditional theorem.
The fixed-level concentration and cutoff-prefix budgets are now instantiated
with the exact normalized Hit-and-Run/KV97 point laws of the concrete TTC
sampler for every successful CV18 outcome vector. A new IID point-tape lemma
shows that selecting precisely the pending labels surviving any thinning
stopping round yields the same batch law as the concrete sampler. The entire
second thinning loop followed by sample append has an equivalent law driven
by one coin stream and this independent point tape. At a fixed successful
CV18 outcome, the complete concrete component has an equal-law representation
that pre-draws its pending Poisson population before first-loop halving; the
pre-draw mean agrees with the incoming-rate mean on every actual first-loop
outcome. A Poisson population drawn at dyadic level zero can also be thinned to any fixed
absolute dyadic level, and shifting the fair-coin array to any absolute
starting level preserves its law. The shared absolute-level coin and Poisson
coupling across all components remains to be proved.
For one component, an explicit probability law now packages a level-zero
Poisson count, an infinite fair-coin array, and permanent IID point marks.
The same source can be evaluated at every fixed dyadic level; its point-count
vector has exactly the independent Poisson law used by the fixed-level
analysis. The measurable evaluation and the source's probability normalization
are proved. Identifying the adaptive multi-component run with a stopping
projection of one product of these sources remains open.
The independent component source product is now proved to fold, at each fixed
dyadic level, into exactly the certified delete-and-append prefix law, including
the actual component order and the concrete normalized sampler. This result
uses one component-indexed source law for all levels. It does not establish
that the adaptive algorithm is a stopping projection of this law; that
pathwise and measure-preserving coupling is still the missing Theorem 1 step.
The concrete total-count law and the levelwise Chernoff error estimate have
also been transferred to that shared source. The finite stopped-level union
bound is proved for real probabilities. Combining them for the executable
adaptive run still depends on the missing coupling.
For a single component, a deterministic state lemma also identifies the
stored point count after both thinning loops and append as the count from a
cumulative coin block plus the appended batch count. It assumes only the
already-proved fresh-label invariant.
The two thinning coin streams have now been proved to splice into one fair
coin stream at the deterministic first-loop exit round. For each incoming
state and component intensity, the first-loop Poisson draw is proved
independent of the first-loop coins, and the complete pair of thinning loops
with that Poisson draw has an exact single-coin-stream law. A probability
measure product-swap theorem supplies the needed order change. The remaining
coupling must reindex the pre-drawn Poisson survivors and their point marks
onto the fresh contiguous labels used by the executable state, consistently
across later adaptive rounds and components.
The relabeling step is now proved for arbitrary injective copy-label maps:
future fair coins and IID point marks retain their joint product law, even
when a pre-thinning history chooses the survivor count and both label maps.
Independent first-round coin arrays for stored and newly drawn copies also
merge into one fair array at the fresh-label boundary. The merge is proved
pathwise on stored samples and on the pending count. These lemmas supply the
local ingredients for the still-open whole-run source coupling.
At any dyadic incoming rate, the actual two-loop and Poisson kernel is now
proved equal to a kernel that draws one level-zero Poisson population, thins
it through the absolute incoming and first-loop levels, and then runs one
active fair-coin stream. This is an exact measure equality for the executable
thinning part of a component; attaching the sampler point marks and carrying
the source through all later components remain open.
The full one-component kernel is now also represented with the absolute
level-zero Poisson pre-draw and an IID tape of normalized sampler point marks.
The local thinning loop can use separate independent coin arrays for stored
and newly drawn copies: its first exit round, result, and probability law are
proved equal to the executable single-array loop. These results still do not
identify the adaptive multicomponent run with the fixed-level source product.
The complete one-component kernel is now also represented with separate
independent active coin streams for stored and newly drawn copies, while
retaining the absolute Poisson pre-draw and concrete IID sampler tape.
The second thinning loop is now proved to depend on the fresh coin array only
at the finite labels allocated to its pending copies. Restricting a fair
array to those labels, including after the deterministic rate-loop shift,
has the expected independent product law. The split-loop result has an exact
finite-label representation, ready for survivor-origin relabeling.
The full one-component law has now been lifted to that finite fresh-coin
representation. The two thinning stages' surviving copy indices have a
proved injective map back to their original Poisson labels. Conditional on
the thinning history, the concrete sampler's IID batch can be drawn from
those original-label locations of a point tape. The remaining coupling must
place that point tape and the old-copy coin histories into one shared source
through all components and adaptive levels.
The one-component kernel is now proved equal to a source-driven kernel that
draws the new copies' future fair coins and point marks at their original
Poisson labels. A deterministic bijection identifies the labels surviving
both thinning stages with the labels surviving one spliced absolute coin
stream. Consequently the appended batch point-count vector equals the marked
Poisson source's point-count vector at the absolute level reached by the
adaptive count loop. Ghost origin invariants now track retained old copies
through deletion, both thinning loops, and append. They identify the
concrete state's point counts with source marked-point counts and prove the
exact deterministic delete-and-append recurrence through a finite component
fold. The fold's point counts are now identified with `fixedLevelFold` from
the empty initial state. The incoming marked Poisson count vector has its
fixed-level product law even when the first and second fresh coin streams
are spliced at an arbitrary deterministic round. A ghost configuration now
proves that one complete source-driven manuscript component transition
preserves fresh labels, unique origins, marks, surviving coins, valid tags,
and reverse coverage. For any finite sequence of such transitions, the
executable final state's point-count vector equals the source-driven
`fixedLevelFold` at its final adaptive level. The fair-coin filtration now
has a fixed-prefix/future product law. For the actual first-exit thinning
loop, the future stream after the stopping round is independent of the round
count; the `sInf ∅ = 0` nontermination branch is removed using its null-event
proof. The split old/new coin loop inherits a merged stopped-tail law.
Component and original-copy coordinates are encoded in one global fair
stream, with a product law for every fixed-level future source family and
for the future family after either stopping-loop representation. The
future coins remain fair on the allocated executable labels even when the
observed prefix adaptively determines the origin map and label count;
this is proved as an almost-everywhere bind law for measurable continuations.
Stored-copy thinning is proved insensitive to every coin outside the
allocated label range, and the finite allocated-label restriction of a fair
stream has the expected product law. The source-labelled one-component
sampler kernel is now also proved insensitive to old-copy coins outside that
range, including the dependent survivor-label batch. The full one-component
future-source kernel has the corresponding restricted-coin representation.
The one-component source law is now proved equal to a product of two finite
independent fair-coin blocks, for allocated old labels and surviving new
labels, with the same source-labelled sampler kernel. This finite-block law
has been propagated through the Poisson draw and first-loop stream: the
actual `communityManuscriptComponentGivenVolume` output law equals the new
finite-coin source kernel whenever the incoming state has its proved dyadic
rate and label-freshness invariants.
The allocated-label source product law is also lifted to an arbitrary
measure-valued adaptive continuation, under the almost-sure origin-history
invariant. This permits the source law to be substituted inside a fold while
retaining later randomized component work. The same bind-level result is
proved directly for old-copy coins read from the persistent global fair
stream after a prefix chosen at a fixed absolute level; the required
measurability of the finite-block family follows from the joint source map
and the almost-sure history invariant.
The actual first-exit stopping round now has a stronger stopped-prefix law:
its unused fair tail is independent of every coin observed before the stop,
not only the stopping-round count. This is lifted to the global
component/original-label source and to a measure-valued adaptive origin-map
continuation. The merged old/new thinning loop has the same stopped-prefix
global-source law.
The source substitution is now factored as a general joint-product adaptive
bind lemma and instantiated for the merged old/new stopping loop. Its
continuation may depend on the entire stopped prefix and return a randomized
output measure, so the adaptive origin assignment can be carried into a
component-fold coupling.
The source-labelled sampler kernel now has an explicit deterministic tape
result, and the ghost configuration's `advance` state is proved equal to that
result for every fixed random input. The corresponding point-tape map law
identifies the ghost state's conditional output measure with the executable
source-labelled kernel.
The executable uncharged component fold is now proved equal to the product
law of all clipped CV18 volume outcomes bound to a fixed-volume executable
fold. That fixed-volume fold is proved jointly measurable and probability
preserving. This removes the need to track CV18 draws inside the coin-source
coupling: the concentration proof may condition on the complete independent
volume outcome vector, with its good-outcome event already bounded separately.
The same conditioning equality is now proved for the public
`communityManuscriptTTC` output measure in the nonempty branch.
For the coin coupling, a ghost source-tail refresh replaces every unobserved
future coin while preserving the current executable state, absolute level,
origin history, marks, survival, and reverse-completeness invariants. The
refreshed source's old-copy coins have the exact independent fair product law
on the state's allocated labels. This gives a lawful transition from a
history-bearing ghost state to fresh coins for the next component.
`ManuscriptSourceRefresh.lean` now proves the complete one-component state
law: after an independent refresh of future old-copy coins, the ghost advance
has the same state marginal as the executable component, first with a fixed
CV18 outcome and then including the CV18 draw. It also proves refresh leaves
every fixed-level source count at or before the current level unchanged.
`ManuscriptOriginMeasurable.lean` gives the source and ghost configurations
their product measurable structures and proves refresh and fixed-coin
point-tape advances measurable. Refresh is also proved jointly measurable in
the incoming ghost configuration and the independent future source, and forms
a Markov kernel whose state projection is the unchanged executable state and
whose previously reached fixed-level count projections are unchanged. The
entire observed source prefix at the adaptive current level is measurable,
fixed by refresh, and independent of the newly drawn future source even for
a random incoming ghost configuration. The source point-count functions are
proved measurable. It constructs a normalized ghost tape law,
proves that law has total mass one, and identifies its state marginal with
the executable source-labelled sampler kernel.
`ManuscriptOriginMarginalKernel.lean` now proves the state-level induction
equation for an arbitrary incoming ghost law: the source-driven component
state marginal is the executable component law applied to the incoming state
marginal. `ManuscriptOriginSourceStepMeasurable.lean` proves the source update
is jointly measurable in the incoming ghost source and appended point tape,
including the valid-label filter, marks, and coin splice. It permits random
label and round parameters and proves the source projection of the actual ghost
advance jointly measurable in the incoming configuration and sampler tape.
`ManuscriptOriginAppendMeasurable.lean` proves joint measurability of the
origin-label append operation for random old origins, label parameters, and
survivor indices.
`ManuscriptSurvivorIndexMeasurable.lean` builds total measurable selectors for
both thinning stages and proves their agreement with the finite survivor-label
map on valid indices. `ManuscriptOriginOldCoinsMeasurable.lean` proves that the
old-copy coin stream read from a random ghost configuration is measurable,
along with the component's integer controls and extended pending-copy coin
array. `ManuscriptOriginActiveRoundsMeasurable.lean` proves the actual
second-loop exit round and ghost level jointly measurable.
`ManuscriptOriginAdvanceOriginMeasurable.lean` and
`ManuscriptOriginAdvanceStateMeasurable.lean` prove the origin and executable
state projections jointly measurable, including the varying survivor count
and sampler tape. Thus the full deterministic ghost `advance` is jointly
measurable in its incoming configuration and sampler tape.
`ManuscriptOriginTapeKernelMeasurable.lean` lifts this to a Markov kernel for
the independent Hit-and-Run point tape after the count and coin choices are
fixed. `ManuscriptOriginCountTapeKernel.lean` also integrates the Poisson
pending-copy count into a Markov kernel with the coin arrays fixed. The
random-coin work now proves the pending-copy extension, pending count, merged
coin stream, and actual second-loop exit round jointly measurable in the
incoming ghost configuration and both coin arrays.
`ManuscriptOriginSourceCoinPairMeasurable.lean` proves the full source update
jointly measurable with both coin arrays random. The origin and state
projections are also proved jointly measurable in
`ManuscriptOriginAdvanceCoinPairMeasurable.lean` and
`ManuscriptOriginAdvanceStateCoinPairMeasurable.lean`. Thus the complete ghost
advance is jointly measurable in the incoming configuration, both coin arrays,
and point tape. `ManuscriptOriginRandomCoinKernel.lean` integrates the fair
coin arrays, point tape, and Poisson count into a Markov kernel for fixed
intensity. `ManuscriptOriginRefreshedKernel.lean` composes it with the source
refresh kernel.
`ManuscriptIndependentBindSwap.lean` and
`ManuscriptOriginRefreshedStateMarginal.lean` reorder these independent draws
to the same order as the executable component. The fixed-CV18-outcome state
marginal is now proved exactly in `ManuscriptOriginOrderedMarginal.lean`:
the refreshed ghost kernel projects to
`communityManuscriptComponentGivenVolume`.
`ManuscriptOriginIntensityMeasurable.lean` proves the entire deterministic
ghost `advance` jointly measurable in the incoming configuration, varying
intensity, both coin arrays, and the point tape. This includes the first-loop
controls, pending count, second-loop exit, survivor count and labels, origin
map, source update, executable state, and resulting level.
`ManuscriptOriginVaryingIntensityKernel.lean` lifts this result through the
independent point tape, both fair coin arrays, and the Poisson count, with
the intensity varying jointly with the incoming configuration.
`ManuscriptOriginVaryingRefreshKernel.lean` proves joint measurability of the
source-refreshed component law at varying intensity by rewriting the refresh
map as a bind over the fixed independent source measure.
`ManuscriptOriginVolumeKernel.lean` integrates an arbitrary probability law
of CV18 outcomes into a measurable ghost component transition, proves it has
total mass one, and proves that its executable-state marginal is exactly the
current `manuscriptProcessComponent` for the concrete clipped CV18 law.
`ManuscriptOriginVolumeFold.lean` iterates the ghost transition through any
finite list of components equipped with the geometric route and normalized
CV18 volume law. Its output remains a probability measure and its state
marginal is exactly the executable `manuscriptProcessComponents` law.
`ManuscriptOriginCertifiedRun.lean` supplies the geometric routes and clipped
CV18 probability laws for the preprocessor's actual component list and proves
that the resulting ghost run projects to the manuscript's executable
multicomponent state law from its initial state. The remaining probabilistic
step is to identify the ghost run's fixed-level source-count law, conditional
on the clipped CV18 outcomes, with the independent Poisson product law already
proved for prescribed component sources. Then the finite dyadic union bound
can transfer fixed-level concentration to the adaptively selected final level.
`ManuscriptAdaptiveSplicedSourceLaw.lean` proves that a fresh component's
Poisson count, two spliced fair-coin streams, and iid point tape have exactly
the canonical Poisson-tape law, even when the splice round is chosen from the
incoming history. It also proves the new source is independent of that history
at a fixed intensity, and gives the conditional-law identity for varying
intensity. Its fixed-level corollary proves that the new component's Poisson
point-count vector is independent of an arbitrary incoming history even when
the splice round and label offset depend on that history. The remaining
coupling must account for the old source's refreshed future tails across the
entire adaptive fold.
`ManuscriptAdaptiveFixedLevelUpdate.lean` applies this to the ghost source
state: for any incoming ghost law, adding one independent spliced source has
the fixed-level delete-and-add Poisson kernel on its point-count vector.
This isolates the old-source refresh as the remaining one-step distribution
identity.
`ManuscriptOriginSourceCountKernel.lean` proves that the actual randomized
ghost component, before refreshing old source tails, has precisely this
fixed-level delete-and-add Poisson count law. The coin splice has disappeared
from the resulting law. `ManuscriptOriginRefreshedCountKernel.lean` proves the
corresponding statement for the actual refreshed ghost component: the old
count vector is first drawn from the refreshed old source, then the independent
Poisson vector is added after deleting the current component. These files
compile and are imported by the root module. What remains is the whole-run
invariant identifying refreshed old source counts at a fixed future level
with the required independent product source law across adaptive stopping
levels. The existing past-count preservation lemma applies only when the
observed level is at most the current level.
The new `manuscriptOriginRefreshedComponentLaw_pastLevel_sourceCounts`
specializes the refreshed kernel to that observed-level case, eliminating the
refresh term completely. The future-level case still needs a conditional
source-tail law; it cannot follow from past-count preservation alone.
`ManuscriptSourceRefresh.lean` now gives a pathwise formula for every future
level: an old source tag survives exactly when it survives the observed prefix
and a fresh fair tail of the remaining length. It also identifies the
future-level point-count vector. `ManuscriptOriginMeasurable.lean` lifts that
identity through `refreshLaw` to an explicit pushforward of the global fair
source. The remaining measure step is to calculate that finite fresh-tail
count law jointly with the incoming observed-prefix distribution, then
establish its preservation through the adaptive component fold.
`ManuscriptFutureTagLaw.lean` calculates this conditional law for a fixed
incoming ghost configuration: distinct valid component/copy tags receive
independent Bernoulli survival decisions for the remaining rounds, and the
future-level point-count vector is exactly the finite marked count of those
decisions. `ManuscriptOriginRefreshedCountKernel.lean` combines it with the
new component's independent Poisson point vector, giving the full one-step
future-level count kernel. The still open step is to integrate these
conditional kernels against the adaptively generated prefix law and show the
result is the certified fixed-level Poisson process at every component prefix.
`ManuscriptSourceRefreshIdempotent.lean` proves that the source-tail refresh
kernel is idempotent, both on a fixed incoming configuration and on an
arbitrary ghost law. This makes refresh a measure-level projection. To turn
that into the whole-run invariant, the component kernel must be shown to
preserve the projected laws (or equivalently to commute with a final refresh
on the observations needed by the fixed-level proof). That preservation is
not yet proved.
`ManuscriptStationaryFixedLevelKernel.lean` proves the exact one-component
fixed-level Poisson delete-and-add law for any incoming ghost measure fixed by
the refresh kernel. It removes the leading refresh by stationarity and uses
the actual unrefreshed component's Poisson count law. To iterate this result,
the missing preservation theorem must show that a refreshed component sends a
refresh-stationary incoming law to another refresh-stationary law.
`ManuscriptSourceFreshCriterion.lean` now gives an equivalent concrete
independence formulation. A ghost configuration is reconstructed from its
observed-prefix representative and unused relative-time source tail; the
reconstruction is pathwise exact and measurable. Refreshing any ghost law
produces a product of the observed representative law and the global fair
tail law. Conversely, that product identity implies refresh stationarity.
The component preservation proof can therefore target the joint stopped-prefix
and fresh-tail law supplied by the existing strong Markov lemmas, rather than
an abstract equality of full ghost kernels.
The same file also proves the unconditional product representation of the
refreshed law: draw the observed representative from the incoming ghost law,
draw an independent global fair tail, and reconstruct the full configuration.
This representation is the input measure for the remaining stopped-prefix
calculation at one component.
`ManuscriptStoppedPrefixSource.lean` now states the second thinning loop's
strong Markov result directly for its complete stopped merged coin prefix
and complete shifted merged fair stream. `ManuscriptStoppedPrefixContinuation.lean`
lifts the equality through any measurable continuation, allowing the eventual
component-source proof to carry its point tape, origin labels, and output
configuration alongside the independent post-stop coin stream. The remaining
work is to identify the ghost output's relative-time unused source tail with
the appropriate coordinates of that post-stop stream, including old
component tags not read by the executable loop.
`ManuscriptOriginUnusedTailStep.lean` now calculates that output tail
pathwise. At the appended component it is the fresh component stream shifted
by the number of post-preprocessing thinning rounds; at every other
component it is the global refreshed old source shifted by the full number
of rounds elapsed since the incoming level. The full output source-tail
function is proved equal to the corresponding if-then-else combination.
The remaining probabilistic step is to show this combined shifted family is
jointly independent of the output observed representative under the actual
Poisson/coin/tape draws.
`ManuscriptCombinedTailLaw.lean` proves that for any fixed pair of shifts,
the if-then-else combination of an independent global old fair source and
one new component fair stream has exactly the global fair source law. The
index map used in this proof is injective across every component, including
the replaced one. The adaptive-shift version still requires applying the
stopped-prefix continuation law to the actual component transition.
The same file now integrates that fixed-shift identity over an arbitrary
observed-prefix law whose prefix selects the component and both shifts. When
the two source streams are conditionally independent given that prefix, the
combined tail is jointly independent of the prefix and globally fair. This
reduces the adaptive-shift step to establishing the required conditional
product law for the actual second thinning stop.
The public accuracy theorem still retains `Prior` and covers the older
`communityTTC` until that step is proved.
`ManuscriptGenericStoppedPrefix.lean` proves the stopped-prefix product law
for any measurable stopping round whose fibers are almost surely determined
by the corresponding coin prefix. It also proves independence of the entire
reindexed global component future source from that stopped prefix. The
remaining application must encode the actual second-loop stop as such a
prefix-adapted stop on the joint old-component and newly drawn coin source,
then relate the resulting observed prefix to the output ghost configuration.
`ManuscriptJointSourceEncoding.lean` now constructs that joint old/new source
from a single fair array using a time-preserving injective index map. It
proves the pushforward law is the product of the global old-component source
and an independent fresh-copy stream, and proves fixed-time prefix/shift
identities for both projections. The remaining stopped-time argument must
establish prefix adaptation of the actual second-loop exit event under this
encoding and map the observed stopped prefix to the output configuration.
The joint-source encoding now also proves, under the ghost origin-history
injectivity invariant, that merging old allocated labels with fresh new
labels is itself a fair stream. Its first-exit event is prefix-adapted on the
single joint source; consequently the stopped joint-source prefix is
independent of the complete shifted old-component and fresh-copy sources.
This is proved in `manuscriptJointMergedRead_stoppedPrefix_jointTail_law`.
The executable second loop first restricts fresh labels to survivors of the
deterministic rate-thinning loop, so the next bridge must identify that
restricted stop and its output representative with this joint-source law.
`ManuscriptSurvivorRelabel.lean` now extends the actual finite survivor list
to an injective relabeling of every fresh coin coordinate. It proves that
the resulting merged old/new stream is fair, that the executable second-loop
stopping round is pathwise equal to first exit on that merged stream, and
that its stopped prefix is independent of both complete unused source
families. Combining those tails yields a full fair global source independent
of that prefix. `ManuscriptOriginJointSourceBridge.lean` connects the old
source read after refresh and a deterministic shift to the indexed source
used in this coupling. The remaining work is to include the deterministic
first-loop prefix and point tape, prove the observed ghost output depends
only on those prefixes plus the second-loop stopped prefix and round, and
then transport the product law through the actual component kernel.
`ManuscriptStoppedRoundPrefix.lean` strengthens the stopping theorem by
retaining the stopping round together with the observed source prefix. It
also reconstructs the measurable second-loop result from that pair.
`ManuscriptSurvivorRelabel.lean` proves the executable finite second-loop
result equals this reconstruction for the survivor-filtered input.
`ManuscriptStoppedSurvivorIndex.lean` proves that canonical surviving-copy
indices and their original Poisson labels depend only on the stopped
prefix. `ManuscriptGlobalSourcePrefix.lean` proves that the old global fair
source splits at the deterministic first-loop round into its observed
prefix and an independent fair future source. The remaining whole-step
argument must combine these two splits with the point tape and the source
append to prove refresh stationarity for the actual output configuration.
`ManuscriptSurvivorPairTail.lean` transports the survivor-filtered stopped
law from the single encoded fair array to the actual product of old global
source and fresh-copy source. Conditional on a fixed pre-thinning coin tape,
the pair consisting of the second-loop stopping round and the prefix of the
stream actually read by that loop is independent of both complete remaining
source families. This is an exact measure identity, with no `Prior` premise.
`ManuscriptTwoStageSourceProduct.lean` composes the deterministic first-loop
prefix split with this adaptive second-loop stopped law. It proves that the
joint first-loop prefix and second-loop stopped observation are independent
of the complete remaining old/new source pair. `ManuscriptFirstLoopObservation.lean`
shows the rate-thinning result depends only on its fixed-round coin prefix.
`ManuscriptObservedRepresentativeExt.lean` reduces equality of observed ghost
outputs to equality of their executable states, source data, origin, level,
and source-coin prefix below the reached level. The remaining pathwise step
must reconstruct these output fields from the two-loop observation and point
tape. It must then transport the joint product law through the actual
component kernel and iterate the fixed-level Poisson prefix invariant.
`ManuscriptOutputSourcePrefix.lean` proves the appended source's observed
prefix is fixed by the old source prefix and the new component's finite
future-coin prefix. The ghost source retains all coordinates below the
reached level, including coordinates the loop never read.
`ManuscriptSurvivorFullPrefixTail.lean` therefore strengthens the joint
product theorem: the first-loop prefix and both complete source prefixes
through the adaptive second-loop stop are independent of the complete
remaining old/new source pair. It also proves equal complete stopped
observations give equal second-loop states and pending counts.
`ManuscriptAdvanceObserved.lean` connects the refreshed global source's
first-loop prefix to the actual rate-thinning result. The next step must
combine these pathwise lemmas for the actual `advance` output's observed
representative, carry the point tape, and transport the product law through
the component kernel.
The stopped-prefix file also proves that equal new-source prefixes give
equal coin prefixes after survivor renumbering, which is the input needed
to identify the original Poisson labels selected for the appended batch.

#### Avoidable scaling cost in the older sampler implementation

The older `communityTTC` sampler walks directly on the decimal-scaled body:
`hitAndRunDiameter P b eta` is the diameter of `hitAndRunBody P b eta`, whose
facet offsets include `10^b * P.presentation.offset`. The imported deadline is
`2^64 * n^2 * D^2 * log(8M/eps^2)`, and `hitAndRunSteps` is its ceiling. For a
fixed nondegenerate polytope, the diameter grows on the order of `10^b`, so the
step budget grows at least on the order of `10^(2b)` for large `b`. The abstract
`TTCPreprocessor.choosePrecision` may choose any adequate precision, including
arbitrarily large ones. This is a bound on the walk length selected by the
older Lean implementation, not an inherent cost of sampling from the scaled
polytope or a refutation of the manuscript's intended arithmetic bound.
`communityManuscriptTTC` now uses the normalized walk and the runtime
certificate charges its normalized deadline.
Both radii scale by `10^b`, so their ratio is unchanged. A similarity-normalized
walk can use that ratio in the mixing deadline; its tighter TV tolerance affects
only a logarithm. The deterministic first halving loop also takes only
`O(n(1+b+log⁺ R_max))` rounds under the clipping bound.

A proof of the proposed shape for the concrete Lean run uses the normalized
sampler now in `communityManuscriptTTC`: Hit-and-Run runs on a
similarity-normalized body with unit inradius and maps samples back before
KV97 rounding. The walk deadline can depend on the radius ratio instead of the
absolute decimal-scaled diameter. The imported CV18 result bounds membership
queries by its scheduled rate, and the imported Hit-and-Run result bounds
mixing steps by its explicit deadline. The costed TTC execution and its
whole-run expected-cost proof now exist. The costed sampling law separately
records rejection attempts and proves their expected charge. The explicit
budget is now factored into `m n⁵ ρ² r_max (1+b+log⁺R_max)` times an explicit
sample cap and parameter factor. The exact scheduled CV18 logarithmic
product still needs a formal polylogarithmic classification. The whole-run
charge-forgetting marginal is proved.

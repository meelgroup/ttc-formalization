# Manuscript theorem audit

`Kr25Ssmxt/Model/` is the statement and program audit surface. Proofs belong in
`Kr25Ssmxt/Analysis/`. `#krModelClosureOfType` checks that both public theorem
statements unfold only through `Model/` definitions.

`Model/Theorem.lean` now declares exactly two theorems: the older conditional
accuracy theorem and the corrected expected-runtime theorem. The intermediate
runtime inequalities are in `Analysis/ManuscriptRuntimeBounds.lean`. The
accuracy declaration still concerns the older TTC core; it must be replaced
after proving the current manuscript program's stochastic lattice-count lemma.

## Theorem 1 (`sections/analysis.tex`, `thm:volumettc`)

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
output law. The nonempty adaptive Poisson invariant and concentration bound
remain open.

## Theorem 3 (`sections/analysis.tex`, `thm:runtime`)

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

## Program fidelity to `sections/algo.tex`

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

### Avoidable scaling cost in the older sampler implementation

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

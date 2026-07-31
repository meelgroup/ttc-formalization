# How to audit this formalisation

`lake build` being green and `#print axioms` returning
`[propext, Classical.choice, Quot.sound]` proves that the development has **no
holes**. Neither proves that it states the **right theorem about the right
object**. That check is human-only, and this file is designed to let you make it
in a few minutes without reading a single hard proof.

Everything you need is in [`Ttc/Model/`](Ttc/Model/) — four files, no proofs
worth the name. Nothing in `Model/` refers to a definition outside `Model/`
except Mathlib, so you never have to follow a name into `Analysis/` to find out
what it means.

---

## 1. Is the capstone about the real object?

Read only the **type** of one declaration — everything before the `:=`.

**[`Ttc.TtcProb.volume_estimate`](Ttc/Model/Theorem.lean#L40)** — `thm:volumettc`:

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) :
    1 - T.δ ≤
      (T.μ {ω | ttcOutput T.P T.O T.fuel T.ρ T.D ω ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

*With probability at least `1 − δ`*, the algorithm's output lies in
`(1 ± ε)·Vol(F)`. Four things make that a claim rather than a shape:

* **The measured thing is the algorithm.**
  [`ttcOutput`](Ttc/Model/Pseudocode.lean#L138) is
  [`Ttc.run`](Ttc/Model/Pseudocode.lean#L132) — the line-by-line transcription of
  `alg:ttc` — with the oracles drawn at `ω`. Read `Model/Pseudocode` against
  `sections/algo.tex`; it is the whole algorithm, and there is no second model it
  is quietly swapped for.
* **The target is `Vol(F)`, not a surrogate.**
  [`Ttc.volSol M φ = (volume (sol M φ)).toReal`](Ttc/Model/Prelude.lean#L173) —
  Mathlib's Lebesgue measure of the set of real points satisfying the formula. No
  discretisation, no rational grid.
* **That set is what the algorithm enumerates.**
  [`Ttc.TtcProb.sol_eq_union`](Ttc/Analysis/Capstone.lean#L112) says
  `⋃ c ∈ T.D, region T.M c = sol T.M T.φ` — `thm:decomposition`, *proved* from the
  `isDNF` field via
  [`Ttc.sol_eq_iUnion_region`](Ttc/Analysis/Decomposition.lean#L112).
* **The interval is the paper's.**
  [`relErr ε b = Set.Icc ((1−ε)b) ((1+ε)b)`](Ttc/Model/Prelude.lean#L181), and
  `T.μ` is a probability measure (field `isProb`).

---

## 2. What is assumed? Read the fields of `TtcProb`

Every global hypothesis is a field of
[`Ttc.TtcProb`](Ttc/Model/ProblemSetting.lean#L38). There are no others: the
theorem quantifies over the structure and adds nothing — no side hypothesis, no
`variable`, no instance argument carrying content.

**Only one lemma of the paper is assumed** (`lem:numlattice`). `lem:lattice` used
to be two more fields; it is now *proved*
([`Ttc.TtcProb.lattice_lo`](Ttc/Analysis/LatticeAssembled.lean#L173),
[`lattice_hi`](Ttc/Analysis/LatticeAssembled.lean#L178)) from the geometric
fields below, which are hypotheses about the **input**, not about the analysis.

| Field | Line | What it asserts | Status |
| --- | --- | --- | --- |
| `ε`, `δ`, `hε0`, `hε1` | [40](Ttc/Model/ProblemSetting.lean#L40), [44](Ttc/Model/ProblemSetting.lean#L44) | `ε ∈ (0,1]`, and the failure probability | the theorem's own parameters |
| `atoms`, `M`, `M_eq` | [48](Ttc/Model/ProblemSetting.lean#L48)–[53](Ttc/Model/ProblemSetting.lean#L53) | each atom is a linear constraint `A x ≤ b`, and `M` interprets it as that half-space | **assumed of the input** — this is what "SMT(LRA)" means |
| `φ`, `D` | [55](Ttc/Model/ProblemSetting.lean#L55), [57](Ttc/Model/ProblemSetting.lean#L57) | the formula and its DNF | inputs |
| `isDNF` | [59](Ttc/Model/ProblemSetting.lean#L59) | `D` and `φ` agree on every Boolean assignment | **assumed** of the external `ToDNF`/AllSAT tool. `thm:decomposition` is *proved* from it |
| `isPositive` | [62](Ttc/Model/ProblemSetting.lean#L62) | no literal of `D` is negated | **assumed of the input** — see §4 and README finding 5 |
| `Ω`, `mΩ`, `μ`, `isProb` | [64](Ttc/Model/ProblemSetting.lean#L64)–[70](Ttc/Model/ProblemSetting.lean#L70) | a probability space for the algorithm's randomness | structure, not an assumption |
| `P`, `eps_eq`, `dim_eq` | [72](Ttc/Model/ProblemSetting.lean#L72)–[76](Ttc/Model/ProblemSetting.lean#L76) | the parameter block, run at the theorem's own `ε` and in the ambient dimension | inputs + two ties that used to be missing |
| `cubes_le`, `facets_le` | [78](Ttc/Model/ProblemSetting.lean#L78), [80](Ttc/Model/ProblemSetting.lean#L80) | `m` bounds the number of cubes, `r` the number of facets | **assumed of the input**; the paper's `m`, `r` |
| `normal_ne_zero` | [82](Ttc/Model/ProblemSetting.lean#L82) | every facet's normal vector is nonzero | **assumed of the input**; a zero normal is not a facet |
| `O`, `fuel` | [84](Ttc/Model/ProblemSetting.lean#L84), [86](Ttc/Model/ProblemSetting.lean#L86) | the `ω`-indexed oracle bundle, the loop budget | inputs; see §4 on `O` and on `fuel` |
| `cen`, `gammaHat`, `hgammaHat`, `ball_subset` | [88](Ttc/Model/ProblemSetting.lean#L88)–[96](Ttc/Model/ProblemSetting.lean#L96) | each `P(cᵢ)` contains an `ℓ₂`-ball of radius `γ̂ > 0` about its own centre | **assumed of the input** — `lem:nonconv`'s own hypothesis, in the paper's words. The LP of `alg:prec` that computes `γ̂` is **not modelled** |
| `volume_ne_top` | [98](Ttc/Model/ProblemSetting.lean#L98) | each `P(cᵢ)` has finite volume | **assumed of the input** — the paper leaves it implicit |
| `ρ`, `rho_eq` | [101](Ttc/Model/ProblemSetting.lean#L101), [103](Ttc/Model/ProblemSetting.lean#L103) | the precision is `GetPrecision`'s output, `ρ = ⌈log₁₀(γ/γ̂)⌉` | `alg:prec` line 91, transcribed — and now **load-bearing**, see §4 |
| `L`, `L_eq` | [105](Ttc/Model/ProblemSetting.lean#L105), [107](Ttc/Model/ProblemSetting.lean#L107) | `L` **is** `\|Sol(F) ∩ 𝕃ⁿ\|/10^(ρn)` ([`normalisedCount`](Ttc/Model/Prelude.lean#L166)) | definition, not an assumption |
| `numlattice` | [110](Ttc/Model/ProblemSetting.lean#L110) | **`lem:numlattice`**: `Pr[ output ∈ (1±ε/3)·L ] ≥ 1 − δ` | **assumed** — the one remaining field of its kind. Every *estimate* it rests on is now proved, `lem:chernoff` included (`Analysis/Chernoff`, `Analysis/Sketch`, `Analysis/Poisson`); what is still assumed is the probabilistic model of the loop — see §4 |

The README's [What is assumed](README.md#what-is-assumed) says the same at
length, with the exact list of what *is* proved about each.

**Where the `δ` comes from.** It is not hand-waved. `numlattice` gives
`Pr[ output ∈ (1±ε/3)·L ] ≥ 1 − δ`; the deterministic chain shows that event is
*contained in* the `(1±ε)·Vol(F)` event; measure monotonicity does the rest. So
the `δ` is earned — given `lem:numlattice`, which is assumed.

Nothing anywhere here is about running time (`thm:runtime` is out of scope).

---

## 3. Is the theorem non-vacuous?

A `∀ (T : TtcProb A n), …` proves nothing if `TtcProb` is uninhabited.

[`Ttc.nonempty_ttcProb`](Ttc/Analysis/Capstone.lean#L242), witnessed by
[`Ttc.trivialProb`](Ttc/Analysis/Capstone.lean#L181): the empty DNF over an
unsatisfiable formula, on the one-point sample space with the Dirac measure —
`Vol(F) = 0`, `L = 0`, output `0`, so `lem:numlattice`'s event has probability
`1` and the witness holds even at `δ = 0`. It needs `1 ≤ n`, because `Ttc.Params`
requires a positive dimension and `dim_eq` ties it to the ambient one.

`TtcProb` is the only hypothesis-bundling structure the capstone quantifies over.
(`Ttc.TtcAnalysis` in [`Analysis/Capstone`](Ttc/Analysis/Capstone.lean#L44) is an
internal device for the arithmetic, not part of the statement.)

**Read that witness before trusting it.** It is degenerate — every geometric
field is vacuous because there are no polytopes — and §4 says why that matters.

---

## 4. Where a name stands in for a proof

`#print axioms` cannot see a definition whose *name* claims more than its body
proves. These are the residual assumptions of that kind. None is hidden — each is
stated in the file that introduces it — but they are collected here because they
are exactly what a green build does not certify.

**`lem:numlattice` is assumed, and it is now the only assumed lemma.** The
`numlattice` field asserts precisely the conclusion the paper spends its
streaming analysis deriving. So the theorem is *conditional*: what it proves is
that a `(1±ε/3)` guarantee about `L` upgrades to a `(1±ε)` guarantee about
`Vol(F)`, with the `δ` carried across intact. That upgrade is now proved end to
end — `lem:lattice`, `lem:nonconv` and `claim:cl` included.

**What is still missing is bookkeeping, not mathematics.** Every *estimate*
`lem:numlattice`'s proof invokes is now a theorem here, including the one the
paper imports from Soos et al.: `lem:chernoff` is proved from the Poisson moment
generating function upwards
([`Analysis/Chernoff`](Ttc/Analysis/Chernoff.lean)), as are both of its
applications, `lem:process`, the epoch series, and the `Vol_ED` failure budget
the paper omits. What is *not* done is composing them into a statement about
`Ttc.run`, and an auditor should know exactly why:

* ~~`Ttc.Oracles` cannot express independence.~~ **Fixed** — calls are now
  clock-indexed (see the note above), so independence is statable.
* ~~`lem:process` is only a pmf identity.~~ **Fixed** —
  [`Ttc.countLaw_eq_pi`](Ttc/Analysis/PoissonLaws.lean#L91) gives it as an
  identity of measures, with independence, thinning and superposition as
  corollaries.
* **The invariant is still not carried along the fold, and the halvings between
  two cubes form a *stopping time*.** The paper's `𝒳^(i)_j` is "the state when
  `p` is `2^(−j)`" — conditioning on a random event. Preserving a Poisson
  invariant across that conditioning is the deep remaining step.
* **Fuel adequacy is required and not assumed.** Both loops return the current
  state when the budget runs out; at small `fuel` the output is not close to `L`
  and `numlattice` would be false. Any discharge of the field needs this
  hypothesis.

So `numlattice` remains a genuine assumption; it is just no longer an assumption
about any unproved *estimate*.

**The geometric fields are hypotheses about the input, and they are real.**
`ball_subset`, `volume_ne_top`, `normal_ne_zero`, `isPositive`, `cubes_le`,
`facets_le` are not consequences of anything here; they are what the paper
assumes of the decomposition (`ball_subset` verbatim, the rest implicitly).
Two are worth staring at:
* `isPositive` **excludes negated atoms**, which the paper's algorithm does not.
  A negated atom denotes an *open* half-space, and on a facet hyperplane the
  lattice count of a set and of its closure differ — so this is not a technicality
  volume arguments wash out. See README finding 5. Concretely: `lem:lattice` is
  proved here for positive DNFs only.
* `volume_ne_top` is implied by `ball_subset` plus boundedness, which the paper
  never states. It is assumed rather than derived.

**`L` is now the lattice count, not a bare real.** The `L_eq` field pins it to
[`Ttc.normalisedCount`](Ttc/Model/Prelude.lean#L166) `= |Sol(F) ∩ 𝕃ⁿ|/10^(ρn)`,
and `lem:lattice` is proved about *that*. (Previously `L` was a free real related
to `Vol(F)` only by assumption; that gap is closed.)

**The non-vacuity witness is degenerate.** `trivialProb` has no cubes at all, so
`Vol(F) = 0`, `L = 0`, the output is `0`, and every geometric field holds
vacuously. It shows the fields are mutually consistent — it does *not* exhibit a
non-trivial formula on which the algorithm provably works. Do not read it as
evidence that the assumptions are satisfiable in an interesting case.

**The oracle bundle constrains almost nothing.**
[`Ttc.Oracles`](Ttc/Model/Pseudocode.lean#L72) has four external calls as fields.
Only two carry any hypothesis — `halve_card_le` (thinning does not grow `X`) and
`gen_card` (`GenerateSamples` returns exactly `N` points, for every precision
`ρ`). Nothing states that `vol` is an `(1±ε')`-accurate volume estimate, that
`pois c λ` is Poisson-distributed, or that `halve c` keeps each element
independently with probability ½. That is deliberate — those *are* the
distributional content of `lem:numlattice`, which is assumed — but it means the
invariants in `Analysis/Invariants` are structural facts about the modelled
execution, not statements about the real algorithm's behaviour.

**The `clock` is not in the pseudocode.** `Ttc.SketchState` carries a counter of
oracle draws, and `halve`/`pois`/`gen` take it as their first argument. An
auditor comparing against `algo.tex` will not find it there. It is present
because an *unindexed* oracle cannot model fresh randomness: `halve` applied
twice to the same multiset would return the same answer, so a thinning that
happened to be a no-op would freeze `𝒳` forever. Read it as naming the draw, not
as algorithm state — `X` and `p` are the paper's state, `clock` is bookkeeping.

**`GetPrecision` is a formula, not an algorithm — but it is no longer inert.**
`γ̂` is still an input: the LP of `alg:prec` that computes the largest inscribed
ball, and the loop taking the max over polytopes, are **not modelled**. What *is*
now proved is that the precision it returns is exactly what the accuracy proof
needs: [`Ttc.gamma_le_latticeScale_mul`](Ttc/Analysis/LatticeAssembled.lean#L68)
shows `ρ = ⌈log₁₀(γ/γ̂)⌉` makes `10^ρ·γ̂ ≥ γ`, which is what gives the *dilated*
polytopes the inscribed radius `lem:nonconv` requires. So `rho_eq` is
load-bearing: delete it and `lem:lattice` no longer goes through.

**The parameter block is a transcription, checkable only by eye.** The constants
in [`Ttc.Params`](Ttc/Model/Prelude.lean#L191) — `η`, `ε'`, `Thresh`, `κ`, `γ`,
`ρ` — assert by their definitions that they are what `alg:ttc` (lines 17–20) and
`alg:prec` (line 86) compute. Read them beside `sections/algo.tex`. Unlike
before, the *results about* them are now reached by the headline: `κ` and `γ`
enter `lem:lattice` through [`Ttc.Params.shell_factor_bound`](Ttc/Analysis/Parameters.lean#L102)
and [`shell_factor_bound_deflated`](Ttc/Analysis/Parameters.lean#L144), so
"the constants are verified" and "the main theorem holds" now meet — for `η`, `κ`,
`γ`, `ρ`. They still do not meet for `ε'` and `Thresh`, which enter only through
`lem:numlattice`.

**Fuel, not termination.** Both `while` loops in `Model/Pseudocode` take an
explicit iteration budget and return the current state when it runs out. No
termination theorem is claimed, and claiming one would be false: the second loop
terminates only with high probability.

---

## 5. Re-checking the machine-checkable part

```bash
lake exe cache get && lake build     # zero "declaration uses 'sorry'" warnings
```

```lean
import Ttc
#print axioms Ttc.TtcProb.volume_estimate
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.TtcProb.lattice_lo
-- [propext, Classical.choice, Quot.sound]
```

```bash
# nothing (the `grep -v` drops the phrase "`sorry`-free" from two docstrings)
grep -rn "sorry\|admit\|native_decide\|sorryAx\|^axiom " Ttc.lean Ttc/ | grep -v '`sorry`'
```

See the README's [Verifying the claim](README.md#verifying-the-claim) for the
full-development axiom sweep.

**Checking §4's "which results does the headline actually reach" claim.** Paste
this into a file and `lake env lean` it; it walks the headline's transitive
constant set and reports membership.

```lean
import Ttc
open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut seen : Lean.NameSet := {}
  let mut todo := [`Ttc.TtcProb.volume_estimate]
  while !todo.isEmpty do
    let n := todo.head!; todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet do todo := c :: todo
  for t in [`Ttc.Params.shell_factor_bound, `Ttc.Params.shell_factor_bound_deflated,
            `Ttc.Params.kappa_div_gamma_le, `Ttc.gamma_le_latticeScale_mul,
            `Ttc.prodKernel_claim_cl_b, `Ttc.Params.epsPrime_window] do
    Lean.logInfo m!"{t} reached: {seen.contains t}"
```

Everything listed comes back `true` except `epsPrime_window`, which is `false` —
`ε'` and `Thresh` reach the headline only through the assumed `lem:numlattice`.

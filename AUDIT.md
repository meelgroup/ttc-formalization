# How to audit this formalisation

`lake build` being green and `#print axioms` returning
`[propext, Classical.choice, Quot.sound]` proves that the development has **no
holes**. Neither proves that it states the **right theorem about the right
object**. That check is human-only, and this file is designed to let you make it
in a few minutes without reading a single hard proof.

Everything you need is in [`Ttc/Model/`](Ttc/Model/) — four files, 434 lines, no
proofs worth the name. Nothing in `Model/` refers to a definition outside
`Model/` except Mathlib, so you never have to follow a name into `Analysis/` to
find out what it means.

---

## 1. Is the capstone about the real object?

Read only the **type** of one declaration — everything before the `:=`.

**[`Ttc.TtcProb.volume_estimate`](Ttc/Model/Theorem.lean#L40)** — `thm:volumettc`:

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) :
    1 - T.δ ≤
      (T.μ {ω | ttcOutput T.P T.O T.fuel T.D ω ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

*With probability at least `1 − δ`*, the algorithm's output lies in
`(1 ± ε)·Vol(F)`. Four things make that a claim rather than a shape:

* **The measured thing is the algorithm.**
  [`ttcOutput`](Ttc/Model/Pseudocode.lean#L107) is
  [`Ttc.run`](Ttc/Model/Pseudocode.lean#L101) — the line-by-line transcription of
  `alg:ttc` — with the oracles drawn at `ω`. Read `Model/Pseudocode` against
  `sections/algo.tex`; it is the whole algorithm, and there is no second model it
  is quietly swapped for.
* **The target is `Vol(F)`, not a surrogate.**
  [`Ttc.volSol M φ = (volume (sol M φ)).toReal`](Ttc/Model/Prelude.lean#L120) —
  Mathlib's Lebesgue measure of the set of real points satisfying the formula. No
  discretisation, no rational grid.
* **That set is what the algorithm enumerates.**
  [`Ttc.TtcProb.sol_eq_union`](Ttc/Analysis/Capstone.lean#L111) says
  `⋃ c ∈ T.D, region T.M c = sol T.M T.φ` — `thm:decomposition`, *proved* from the
  `isDNF` field via
  [`Ttc.sol_eq_iUnion_region`](Ttc/Analysis/Decomposition.lean#L112).
* **The interval is the paper's.**
  [`relErr ε b = Set.Icc ((1−ε)b) ((1+ε)b)`](Ttc/Model/Prelude.lean#L128), and
  `T.μ` is a probability measure (field `isProb`).

---

## 2. What is assumed? Read the fields of `TtcProb`

Every global hypothesis is a field of
[`Ttc.TtcProb`](Ttc/Model/ProblemSetting.lean#L31). There are no others: the theorem
quantifies over the structure and adds nothing — no side hypothesis, no
`variable`, no instance argument carrying content.

| Field | Line | What it asserts | Status |
| --- | --- | --- | --- |
| `ε`, `δ`, `hε0`, `hε1` | [33](Ttc/Model/ProblemSetting.lean#L33), [35](Ttc/Model/ProblemSetting.lean#L35) | `ε ∈ (0,1]`, and the failure probability | the theorem's own parameters |
| `M`, `φ`, `D` | [41](Ttc/Model/ProblemSetting.lean#L41), [45](Ttc/Model/ProblemSetting.lean#L45) | the formula, its interpretation, its DNF | inputs |
| `isDNF` | [47](Ttc/Model/ProblemSetting.lean#L47) | `D` and `φ` agree on every Boolean assignment | **assumed** of the external `ToDNF`/AllSAT tool. `thm:decomposition` is *proved* from it |
| `L`, `hL` | [49](Ttc/Model/ProblemSetting.lean#L49), [51](Ttc/Model/ProblemSetting.lean#L51) | a nonnegative real, *intended* as `\|Q ∩ 𝕃ⁿ\|/10^(ρn)` | see §4 — nothing ties `L` to a lattice count |
| `lattice_lo`, `lattice_hi` | [53](Ttc/Model/ProblemSetting.lean#L53), [55](Ttc/Model/ProblemSetting.lean#L55) | **`lem:lattice`** at `η = ε/8`: `L` approximates `Vol(F)` two-sidedly | **assumed**. Its derivation from `lem:nonconv` is proved (`Analysis/Lattice`, `Analysis/Nonconv`, `Analysis/Recentred`, `Analysis/Repair`); the residual gap is the measure-theoretic reduction inside `claim:cl` |
| `Ω`, `mΩ`, `μ`, `isProb` | [57](Ttc/Model/ProblemSetting.lean#L57)–[63](Ttc/Model/ProblemSetting.lean#L63) | a probability space for the algorithm's randomness | structure, not an assumption |
| `P`, `O`, `fuel` | [65](Ttc/Model/ProblemSetting.lean#L65)–[69](Ttc/Model/ProblemSetting.lean#L69) | the parameter block, the `ω`-indexed oracle bundle, the loop budget | inputs; see §4 on `O` and on `fuel` |
| `gammaHat` | [72](Ttc/Model/ProblemSetting.lean#L72) | `γ̂`, the smallest inscribed-ball radius over the polytopes | input — the LP of `alg:prec` that computes it is **not modelled** |
| `ρ`, `rho_eq` | [75](Ttc/Model/ProblemSetting.lean#L75), [77](Ttc/Model/ProblemSetting.lean#L77) | the precision is `GetPrecision`'s output, `ρ = ⌈log₁₀(γ/γ̂)⌉` | `alg:prec` line 91, transcribed; `ρ` is passed to every `GenerateSamples` call |
| `numlattice` | [80](Ttc/Model/ProblemSetting.lean#L80) | **`lem:numlattice`**: `Pr[ output ∈ (1±ε/3)·L ] ≥ 1 − δ` | **assumed**. The epoch union-bound skeleton is proved (`Analysis/Sketch`, `Analysis/Poisson`); the residual gap is the Poisson–Chernoff estimate `lem:chernoff` |

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

[`Ttc.nonempty_ttcProb`](Ttc/Analysis/Capstone.lean#L220), witnessed by
[`Ttc.trivialProb`](Ttc/Analysis/Capstone.lean#L175): the one-point sample space
with the Dirac measure, the degenerate oracle bundle, and the everywhere-false
interpretation — `Vol(F) = 0`, `L = 0`, output `0`, so `lem:numlattice`'s event
has probability `1` and the witness holds even at `δ = 0`.

`TtcProb` is the only hypothesis-bundling structure the capstone quantifies over.
(`Ttc.TtcAnalysis` in [`Analysis/Capstone`](Ttc/Analysis/Capstone.lean#L43) is an
internal device for the arithmetic, not part of the statement.)

**Read that witness before trusting it.** It is degenerate, and §4 says why that
matters.

---

## 4. Where a name stands in for a proof

`#print axioms` cannot see a definition whose *name* claims more than its body
proves. These are the residual assumptions of that kind. None is hidden — each is
stated in the file that introduces it — but they are collected here because they
are exactly what a green build does not certify.

**`lem:numlattice` is assumed, and it is the load-bearing one.** The `numlattice`
field asserts precisely the conclusion the paper spends its analysis deriving. The
development proves the surrounding arithmetic and a good deal of the machinery
(`Analysis/Sketch`, `Analysis/Poisson`), but not the Poisson–Chernoff estimate
that closes it. So the theorem is *conditional* in the strongest sense: what it
proves is that a `(1±ε/3)` guarantee about `L` upgrades to a `(1±ε)` guarantee
about `Vol(F)`, with the `δ` carried across intact. That upgrade is the real
content.

**`L` is unconnected to any lattice.** It is a bare real described in prose as
`|Q ∩ 𝕃ⁿ|/10^(ρn)`, with no lattice count in sight. `lattice_lo`/`lattice_hi`
relate it to `Vol(F)` by assumption.

**The non-vacuity witness is degenerate.** `trivialProb` sets `Vol(F) = 0` and
`L = 0` and outputs `0`. It shows the fields are mutually consistent — it does
*not* exhibit a non-trivial formula on which the algorithm provably works. Do not
read it as evidence that the assumptions are satisfiable in an interesting case.

**The oracle bundle constrains almost nothing.**
[`Ttc.Oracles`](Ttc/Model/Pseudocode.lean#L51) has four external calls as fields.
Only two carry any hypothesis — `halve_card_le`
([59](Ttc/Model/Pseudocode.lean#L59), thinning does not grow `X`) and `gen_card`
([66](Ttc/Model/Pseudocode.lean#L66), `GenerateSamples` returns exactly `N`
points — for every precision `ρ`). Nothing states that `vol` is an `(1±ε')`-accurate volume estimate, that
`pois λ` is Poisson-distributed, or that `halve` keeps each element independently
with probability ½. That is deliberate — those *are* the distributional content
of `lem:numlattice`, which is assumed — but it means the invariants in
`Analysis/Invariants` are structural facts about the modelled execution, not
statements about the real algorithm's behaviour.

**`GetPrecision` is a formula, not an algorithm.** `ρ` is threaded properly — the
`rho_eq` field pins it to `⌈log₁₀(γ/γ̂)⌉` and
[`gen`](Ttc/Model/Pseudocode.lean#L64) receives it at every call — but `γ̂` itself
is an input. The LP of `alg:prec` that computes the largest inscribed ball, and
the loop taking the max over polytopes, are **not modelled**. What *is* proved is
the mathematics around it: that dilation scales inscribed radii
([`ball_radius_scales`](Ttc/Analysis/Lattice.lean#L84)), and that the two repairs
cost at most one decimal digit
([`precision_increase_le_one`](Ttc/Analysis/Repair.lean#L154)) and `O(log m)`
digits ([`gamma_scale_cost`](Ttc/Analysis/Recentred.lean#L306)) respectively.

**The parameter block is a transcription, checkable only by eye.** The constants
in [`Ttc.Params`](Ttc/Model/Prelude.lean#L138) — `η`, `ε'`, `Thresh`, `κ`, `γ`,
`ρ` — assert by their definitions that they are what `alg:ttc` (lines 17–20) and
`alg:prec` (line 86) compute. Read them beside `sections/algo.tex`. What *is*
proved is that each satisfies the inequality it was chosen for
([`Analysis/Parameters`](Ttc/Analysis/Parameters.lean)) — **but those theorems are
not reached by the headline.** `Ttc.Params` itself is: `thresh` through `Ttc.run`'s
loop guard, and `gamma`/`precision` through the `rho_eq` field. The *results about*
them — `kappa_div_gamma_le`, `shell_factor_bound`, `epsPrime_window` — are not. So
"the constants are verified" and "the main theorem holds" remain two separate
results that do not meet.

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
```

```bash
# nothing (the `grep -v` drops the phrase "`sorry`-free" from two docstrings)
grep -rn "sorry\|admit\|native_decide\|sorryAx\|^axiom " Ttc.lean Ttc/ | grep -v '`sorry`'
```

See the README's [Verifying the claim](README.md#verifying-the-claim) for the
full-development axiom sweep.

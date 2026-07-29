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

**[`Ttc.TtcAnalysis.volume_estimate`](Ttc/Model/Theorem.lean#L64)**

```lean
theorem Ttc.TtcAnalysis.volume_estimate (T : TtcAnalysis A n) :
    T.est ∈ Set.Icc ((1 - T.ε) * volSol T.M T.φ) ((1 + T.ε) * volSol T.M T.φ)
```

Two things to check:

* **`volSol` is `Vol(F)`, not a surrogate.**
  [`Ttc.volSol M φ = (volume (sol M φ)).toReal`](Ttc/Model/Prelude.lean#L261)
  — Mathlib's Lebesgue measure of `Ttc.sol M φ`, the set of real points
  satisfying the formula (`Model/Prelude`). No discretisation, no rational grid.
* **That set is what the algorithm enumerates.**
  [`Ttc.TtcAnalysis.sol_eq_union`](Ttc/Model/Theorem.lean#L56) says
  `⋃ c ∈ T.D, region T.M c = sol T.M T.φ` — the paper's `thm:decomposition`,
  proved (not assumed) from the `isDNF` field via
  [`Ttc.sol_eq_iUnion_region`](Ttc/Model/ProblemSetting.lean#L52).

**`T.est`, though, is a free real** — nothing in the type above says it is what
the algorithm outputs. [`Ttc.TtcAnalysis.run_volume_estimate`](Ttc/Model/Theorem.lean#L75)
is the version stated about [`Ttc.run`](Ttc/Model/Pseudocode.lean#L127) itself,
under the explicit bridge hypothesis of §4. Read both; the second is the one that
says something about the algorithm.

---

## 2. What is assumed? Read the interface fields

Every global hypothesis of the result is a field of
[`Ttc.TtcAnalysis`](Ttc/Model/Prelude.lean#L309). There are no others: the
capstone quantifies over the structure and adds nothing.

| Field | Line | What it asserts | Where it comes from |
| --- | --- | --- | --- |
| `ε`, `hε0`, `hε1` | [311](Ttc/Model/Prelude.lean#L311), [313](Ttc/Model/Prelude.lean#L313), [315](Ttc/Model/Prelude.lean#L315) | `ε ∈ (0,1]` | the theorem's own hypothesis |
| `M`, `φ`, `D` | [317](Ttc/Model/Prelude.lean#L317), [319](Ttc/Model/Prelude.lean#L319), [321](Ttc/Model/Prelude.lean#L321) | the formula, its interpretation, its DNF | inputs |
| `isDNF` | [323](Ttc/Model/Prelude.lean#L323) | `D` and `φ` agree on every Boolean assignment | **assumed** of the external `ToDNF`/AllSAT tool. `thm:decomposition` is *proved* from it |
| `L`, `hL` | [325](Ttc/Model/Prelude.lean#L325), [327](Ttc/Model/Prelude.lean#L327) | a nonnegative real, *intended* as `\|Q ∩ 𝕃ⁿ\|/10^(ρn)` | see §4 — nothing ties `L` to a lattice count |
| `est` | [329](Ttc/Model/Prelude.lean#L329) | a real, *intended* as the algorithm's output `\|X\|/p` | see §4 — nothing ties `est` to `Ttc.run` |
| `lattice_lo`, `lattice_hi` | [331](Ttc/Model/Prelude.lean#L331), [333](Ttc/Model/Prelude.lean#L333) | `lem:lattice` at `η = ε/8`: `L` approximates `Vol(F)` two-sidedly | **assumed**. Its derivation from `lem:nonconv` is proved (`Analysis/Lattice`, `Analysis/Nonconv`, `Analysis/Recentred`, `Analysis/Repair`); the residual gap is the measure-theoretic reduction inside `claim:cl` |
| `sketch_lo`, `sketch_hi` | [335](Ttc/Model/Prelude.lean#L335), [337](Ttc/Model/Prelude.lean#L337) | `lem:numlattice`: `est` approximates `L` to within `ε/3` | **assumed**. The epoch union-bound skeleton is proved (`Analysis/Sketch`, `Analysis/Poisson`); the residual gap is the Poisson–Chernoff estimate `lem:chernoff` |

The README's [What is assumed](README.md#what-is-assumed) says the same thing at
length, with the exact list of what *is* proved about each.

**The `δ` is carried, not re-derived.** `sketch_lo`/`sketch_hi` are asserted
*deterministically*, for one fixed run. So the theorem reads: *on the event that
`lem:numlattice`'s guarantee holds, the output is a relative `ε`-approximation of
the true volume.* Combining that event with `Pr ≥ 1 − δ` is `lem:numlattice`'s
own content. Nothing here is about running time.

---

## 3. Is the theorem non-vacuous?

A `∀ (T : TtcAnalysis A n), …` proves nothing if `TtcAnalysis` is uninhabited.

* [`Ttc.nonempty_ttcAnalysis`](Ttc/Model/Theorem.lean#L85) — `Nonempty (TtcAnalysis A n)`.
* [`Ttc.TtcAnalysis.ideal`](Ttc/Analysis/Capstone.lean#L77) — stronger, and the
  one to read: it builds an instance for **any** formula, **any** DNF
  representation of it and **any** `ε ∈ (0,1]`, by setting `L = est = Vol(F)`
  (every error term zero). So the quantification ranges over a large family, not
  a contrived point.

`TtcAnalysis` is the only hypothesis-bundling structure the capstone quantifies
over.

---

## 4. Where a name stands in for a proof

`#print axioms` cannot see a definition whose *name* claims more than its body
proves. These are the residual assumptions of that kind. None is hidden — each is
also stated in the file that introduces it — but they are collected here because
they are exactly what a green build does not certify.

**The big one — the faithfulness bridge is assumed, not proved.**
[`Ttc.run`](Ttc/Model/Pseudocode.lean#L127) transcribes `alg:ttc` lines 22–46,
and `est` is a bare real. The link between them is
[`Ttc.TtcAnalysis.IsOutputOf`](Ttc/Model/Pseudocode.lean#L152) — `T.est = run P O fuel T.D`
— written as an **explicit hypothesis** rather than left to the field's name.
Under it, [`Ttc.TtcAnalysis.run_volume_estimate`](Ttc/Model/Theorem.lean#L75)
gives the two-sided bound for `Ttc.run` itself, so the guarantee is about the
transcribed algorithm and not a free variable. The hypothesis is satisfiable
([`Ttc.exists_isOutputOf`](Ttc/Analysis/Capstone.lean#L136)), so that theorem is
not vacuous.

But **satisfiable is not proved**: nothing shows the bridge holds of the real
algorithm, because that *is* `lem:numlattice`. Read the witness before trusting
the shape of it — it is the degenerate run (`fuel = 0`, everywhere-false
interpretation, both sides `0`).

This is the one structural difference from a completed formalisation. The
pattern to aim at has *two* models of the algorithm — a paper-faithful
transcription and the operational one the analysis reasons about — joined by a
**proved** bridge, which is what puts the operational model outside the trusted
base. Here there is only the transcription, and the bridge is a hypothesis.
Closing it is the main remaining work.

**`L` is unconnected to any lattice.** It is a bare real described in prose as
`|Q ∩ 𝕃ⁿ|/10^(ρn)`, with no lattice count in sight. It has no analogue of
`IsOutputOf`.

**The oracle bundle constrains almost nothing.**
[`Ttc.Oracles`](Ttc/Model/Pseudocode.lean#L79) has four external calls as fields.
Only two carry any hypothesis — `halve_card_le` ([87](Ttc/Model/Pseudocode.lean#L87),
thinning does not grow `X`) and `gen_card` ([93](Ttc/Model/Pseudocode.lean#L93),
`GenerateSamples` returns exactly `N` points). Nothing states that `vol` is an
`(1±ε')`-accurate volume estimate, that `pois λ` is Poisson-distributed, or that
`halve` keeps each element independently with probability ½. That is deliberate —
those *are* the distributional content of `lem:numlattice` — but it means the
invariants in `Analysis/Invariants` are structural facts about the modelled
execution, not statements about the real algorithm's behaviour.

**The parameter block is a transcription, checkable only by eye.** The five
constants in [`Ttc.Params`](Ttc/Model/Prelude.lean#L197) — `η`, `ε'`, `Thresh`,
`κ`, `γ`, `ρ` — assert by their definitions that they are what `alg:ttc`
(lines 17–20) and `alg:prec` (line 86) compute. Read them beside
`sections/algo.tex`. What *is* proved is that each satisfies the inequality it
was chosen for ([`Analysis/Parameters`](Ttc/Analysis/Parameters.lean)), so if a
constant in the paper changes, exactly one definition changes here and the
corresponding theorem either still compiles or does not.

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
#print axioms Ttc.TtcAnalysis.volume_estimate
-- [propext, Classical.choice, Quot.sound]
```

```bash
# nothing (the `grep -v` drops the phrase "`sorry`-free" from two docstrings)
grep -rn "sorry\|admit\|native_decide\|sorryAx\|^axiom " Ttc.lean Ttc/ | grep -v '`sorry`'
```

See the README's [Verifying the claim](README.md#verifying-the-claim) for the
full-development axiom sweep.

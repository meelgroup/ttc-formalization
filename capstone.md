# Capstone: making the fp Poisson-sampler proof *manually verifiable*

Green is not done. `lake build` + `#print axioms` prove that `theo:main`
(`main_concrete_full`) follows from *our* definitions; they say **nothing** about
whether those definitions are the paper's — that the object we bound really is the
floating-point Poisson sampler, and that `poi λ` really is the Poisson law. That
gap is closed *socially*: a referee reads a handful of statement-only files and
checks, by eye, that we formalized the right thing.

This file is a **sequence of prompts** that build that audit surface for this
repo. Run them in order. Each is self-contained and names the concrete objects in
*this* development (`main_concrete_full`, `TRSampler`, `condOn`, `poi`, `FPSystem`,
`candLaw`, the ledger `Prop`s). The goal of the whole sequence: a referee can read
`Model/` top-to-bottom, never open a proof, and come away convinced.

The methodology behind these prompts is in [`CLAUDE.md`](CLAUDE.md) (interface →
instance → capstone); this file is the *last mile*.

---

## The audit target for this paper

The headline is `theo:main` (`technical-proofs.tex:6-20`), formalized as
`ApproxPoisson.main_concrete_full` in [`Main/MainTheorem.lean`](ApproxPoisson/Main/MainTheorem.lean).
Informally:

> the floating-point sampler `\sampler` — Knuth's `\lopoif` for `λ < 10`, the
> transformed-rejection `\hipoif` for `λ ≥ 10` — produces a distribution within
> total-variation `≤ ε·(λ + κ_exp + ½) + o(ε)` (low range) / the conditional
> `condOn`-bound + `2e⁻¹⁸` (high range) of the true Poisson `poi λ`.

**Its definitional closure** (unfold every identifier in the statement,
transitively) is what a referee must trust:

- `Arlib.tvDist` — the distance being bounded;
- `poi λ` — the ideal target (`= Arlib.poissonPMF λ`);
- the sampler's output law — `(lowRangeAnalysis_concrete_fp_final …).dist` for
  `λ < 10`, and `Arlib.condOn S.K S.accProb` over the concrete `TRSampler S` for
  `λ ≥ 10`;
- `FPSystem` — the floating-point model (a relative-error bound `ε`);
- the ledger `Prop`s of [`Basics/Assumptions.lean`](ApproxPoisson/Basics/Assumptions.lean).

Everything reachable from those is *trusted*; everything else is *proof content*.
The prompts below shrink and validate that closure.

---

## Prompt 1 — build the `Model/` audit surface (three statement-only files)

> Create a directory `ApproxPoisson/Model/` containing exactly three files, each
> **statement-only** (definitions + theorems whose bodies are one-line applications
> of the real proofs, which live elsewhere). No new mathematics — only re-exports
> and readable restatements.
>
> 1. `Model/IdealTarget.lean` — *what the sampler should produce.* The ideal
>    Poisson law `poi λ`, the total-variation distance `Arlib.tvDist`, and nothing
>    else a referee must trust about "closeness." Add the header sentence: "the
>    quantity guaranteed is `tvDist (sampler output) (poi λ)`."
> 2. `Model/Sampler.lean` — *what the algorithm IS,* transcribed from the paper's
>    `\Cref{alg:knuthpoisson}` (low) and `\Cref{alg:btrapprox}` (high). State the
>    two output laws as the repo already models them: the fp Knuth pmf `fpProb`
>    and the transformed-rejection output `condOn K accProb`. Transcribe the
>    paper's *displayed* operations, not an optimized encoding (see Prompt 3).
> 3. `Model/MainTheorem.lean` — *what is guaranteed.* A single theorem combining
>    both regimes, whose body is `:= main_concrete_full …` (or the end-to-end
>    variant, Prompt 7). This is the one theorem a referee reads.
>
> Everything in `Model/` must be reachable from these three by unfolding. Put the
> **definitional-closure sentence** (Prompt 2) in the `Model/MainTheorem.lean`
> header.

---

## Prompt 2 — write the definitional closure, explicitly and falsifiably

> In the `Model/MainTheorem.lean` header, write one sentence naming the full
> definitional closure of the headline statement:
>
> > "the closure of `main_concrete_full` is `Model/IdealTarget` (`poi`, `tvDist`)
> > + `Model/Sampler` (`fpProb`, `condOn K accProb`) + `FPSystem` + the run's
> > `candLaw` construction + the ledger `Prop`s {`expEnvelope`, `logFactAverage`,
> > `logAtomicBound`, `factAtomicBound`, `domination`} + the inline `hAform`."
>
> Then *verify it by hand*: unfold every identifier in the theorem statement,
> transitively, and confirm you reach exactly that set. **If the closure surprises
> you, that is a finding — fix the statement, not the sentence.** (E.g. if an
> internal sharpening like `maxnum` leaks into the RHS, expand it — Prompt 5.)

---

## Prompt 3 — transcribe the sampler faithfully, and invert the bridges

> The headline must be stated over the object a referee can compare to the paper's
> pseudocode, with every modeling convenience *consumed inside the proof*, not left
> for the reader to trust.
>
> 1. **The loop is a conditional law.** The paper's unbounded `while` (accept/reject)
>    is modeled as `condOn K accProb` — the accepted candidate's conditional
>    distribution — *not* an operational loop (see `CLAUDE.md §13`). In
>    `Model/Sampler.lean`, state this modeling as the definition and add a one-line
>    docstring: "the rejection loop's output law is `X | accept`; this is exact, not
>    an approximation of the loop." A referee should not have to reconstruct why a
>    static `condOn` equals a `while`.
> 2. **Displayed operations, not optimizations.** Where the concrete instance uses an
>    efficient form (the candidate law as a pushforward-through-floor CDF `candLaw`),
>    the transcription should show the paper's own operation and the equivalence
>    should be a *lemma* (`candLaw = pushforward`), proved off to the side. Transcribe
>    `⌊H⁻¹(u)⌋`, not the CDF-difference shortcut.
> 3. **Flip every faithfulness bridge** so the *transcription* is the statement's
>    object and the bridge is consumed in the proof. Do this for **both** ranges and
>    **every** quantity the theorem mentions (output law, acceptance probability,
>    normalizer `W`), not just the output.

---

## Prompt 4 — validate `poi λ` against an external Poisson definition

> `Model/IdealTarget.lean` defines the target in *our* vocabulary (`Arlib.poissonPMF`).
> A referee must check by hand that it is *the* Poisson law — and off-by-one /
> normalization bugs hide exactly here.
>
> - State (and prove, off to the side) a bridge `poi_eq_mathlib : poi λ k =`
>   Mathlib's Poisson pmf `λ^k e^{-λ} / k!`, or — if Mathlib has no counterpart —
>   to the naive closed form written out. Pin the things that hide bugs *in the
>   statement*: the `k!`, the `e^{-λ}` normalizer, support `k ≥ 0`.
> - Do the same for the low-range comparison object: `\Cref{lem:knuthpoisson}`
>   (`knuthProb_eq_poi`) already says the *exact* Knuth sampler equals `poi`;
>   surface that lemma in `Model/` so the reader sees the ideal low-range sampler
>   is validated, not assumed.

---

## Prompt 5 — expand the closure until the bound is elementary

> Read `Model/MainTheorem.lean` as a stranger. Every identifier a referee must look
> up is a defect. Expand the guarantee's RHS so it mentions **only the algorithm's
> own inputs** (`ε`, `λ`) and universal constants — no project definition on the
> right-hand side except the thing being bounded (`tvDist`).
>
> - Replace interface-field accessors (`A.kexp`, `A.rem`, `S.C_rej`, `S.C2_dhat`, …)
>   with their concrete values or an explicit bound in the direction the statement
>   needs (you may lose a little tightness; keep the sharp version as a named
>   companion).
> - Expand `maxnum`, `η`, `γ₁`, `γ₂` to numeric bounds where they appear in the
>   guarantee, so the `λ ≥ 10` bound reads as an elementary function of `ε, λ`.
> - Target: the low-range guarantee is visibly `≤ ε·(λ + κ_exp + ½) + o(ε)`, and the
>   high-range guarantee is a printed polynomial in `λ, ε` plus `2e⁻¹⁸`.

---

## Prompt 6 — identify the concrete objects field by field

> `Model/` says what the theorem is *about*; the referee still wants each field of
> the concrete object pinned to the algorithm.
>
> - For `TRSampler`: one `rfl`-style identification per field (`K`, `accProb`, `gK`,
>   `gKi`, `W_K`, `hdom`, …), plus a **completeness claim with a count**: "`TRSampler`
>   has exactly N fields and there are exactly N identifications; drop one and a
>   field goes unidentified." Note which are *not* `rfl` and why (the ones that hold
>   only via a proved bridge, e.g. `hdom = Assumptions.domination`).
> - For `FPSystem`: state the one modeling assumption plainly — a rounding oracle
>   with `|rnd x − x| ≤ ε|x|`, monotone/idempotent/`rnd 1 = 1` — and say what real
>   IEEE arithmetic detail is *out of scope* (subnormals, rounding mode).

---

## Prompt 7 — state the residual risk yourself

> Every artifact has gaps that are real but not `sorry`s. Put them in the
> `Model/MainTheorem.lean` header so a referee never discovers one unaided. For this
> repo they are:
>
> 1. **The ledger assumptions** (`Basics/Assumptions.lean`): the group-C hardware
>    constants (`κ_log`/`κ_fact`/`κ_exp`) and Hörmann's `domination` — cited, not
>    proved (the paper cites them too). The low range is reduced to `κ_exp` alone.
> 2. **The inline `hAform`.** The concrete *candidate-deviation* bound is still an
>    un-discharged hypothesis of the high-range capstone (the abstract `lem:dhatdist`
>    is proved; the concrete sub-probability connection is in progress in
>    `HighRange/ConcreteHatFp.lean`). Name it — do not let "axiom-clean" imply it's
>    closed.
> 3. **Oracle semantics.** The statement reads coins from a probability space; the
>    i.i.d.-uniform-ness of those coins lives in `arlib`, not surfaced in `Model/`.
>    Surface or name it.
> 4. **Modeling choices:** `o(ε)` is an explicit nonnegative remainder slot (not
>    Lean's little-o); distributions are `ℕ → ℝ` summing to 1 via `tsum` (not
>    measure objects); the loop is a conditional law. All deliberate — say so.
>
> Prefer the **end-to-end** high-range theorem
> `FinalAssembly.main_high_concrete_end_to_end` for the audit when you want `lrbound`
> and the group-C leaves *load-bearing* (no compound deviation assumed); note it is
> `λ ≥ 10` only and still carries `hAform`.

---

## Prompt 8 — the gate

> ```bash
> lake build                                   # zero errors, zero `uses 'sorry'`
> ```
> ```lean
> -- scratch file, deleted afterward:
> import ApproxPoisson.Model.MainTheorem
> #print axioms ApproxPoisson.main_concrete_full
> -- expect: [propext, Classical.choice, Quot.sound]
> ```
>
> Run `#print axioms` on the **`Model/` theorems specifically** — those are what's
> being audited — from a throwaway scratch file (don't leave a `Check.lean` in the
> tree). Then re-read `Model/` top to bottom in the audit order you claim,
> pretending you've never seen the repo. Anything you have to look up is a defect in
> Prompt 5.

---

## Keep the cross-references honest (line numbers drift)

Three artifacts go stale on every statement edit — re-derive at end of session, not
from memory:

- [`README.md`](README.md) — the headline code block + the module map.
- [`PAPER-TO-LEAN.md`](PAPER-TO-LEAN.md) — one `paper-label → decl (file#Lline)`
  row per numbered paper statement.
- the paper's own `\Cref{…}` targets in Lean docstrings.

```bash
grep -n "theorem main_concrete_full" ApproxPoisson/Main/MainTheorem.lean
```

A stale `file:line` costs more credibility than the second it saves.

---

## Project-specific gotchas

- **One Mathlib checkout via symlink.** `.lake/packages` symlinks into `arlib`'s
  package dir; a second Mathlib clone is ~5 GB and fails on a full disk. Restart the
  Lean server if `lake setup-file` starts erroring on space.
- **The rejection loop is a `condOn`, never an operational model** — the single
  biggest modeling win; `dtv(p, p|_A) = p(Aᶜ)` replaces a coupling argument.
- **Pushforward-through-floor is a discretized CDF** (`candLaw g M W k = (g(k+1)−g(k))/W`);
  a distribution proof is a telescoping sum, not measure theory. The measure-model
  bridge (`ConcreteHatFp.cdfPmf_gFp`) connects it back to the `muBand` pushforward.
- **`#print axioms` can still hide an assumption:** a `def` whose docstring claims a
  semantic identity its body doesn't prove is invisible. Re-audit every `def` whose
  name promises one (this bit us on `hdensDerivAbs`); the fix is an explicit
  hypothesis or a mechanized proof.
- **The multiplicative error-DAG needs sign-definiteness** — it applies only where
  every node keeps a fixed sign (`hinv`'s cancellation does *not* fit); forcing it
  smuggles in a false step, and it was a bug-oracle hit against the paper.
- **`rw` under a `tvDist`/`∑'` binder** can fail with "motive is not type correct";
  transport with `congrArg` / `le_of_le_of_eq` instead.
- **New files need explicit `git add`** — a green `lake build` won't remind you.

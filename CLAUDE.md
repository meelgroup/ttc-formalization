# End-to-End Formal Verification Playbook

A reusable methodology for taking a paper (or algorithm) all the way to a
**machine-checked, `sorry`-free, axiom-clean** proof in Lean 4 + Mathlib, using
AI agents for scale. Distilled from a completed project (an FPRAS correctness
proof + an algorithm-equivalence result). Nothing here is project-specific; copy
this file into a new repo and follow it.

---

## 0. The one-paragraph summary

Prove the hard math **once, abstractly**, over a structure of hypotheses; then
build **one concrete instance** that discharges every hypothesis. Find the single
**crux lemma** that is the mathematical heart and prove it first — the rest turns
into bookkeeping. Land **one named lemma at a time**, rebuilding green after each.
Treat `#print axioms` as the only authoritative definition of "done." Use the
formalization as an **oracle** to find bugs in the original paper. Parallelize
with agents on **disjoint files**, keep a **tight leash** (verify every green
yourself), and **never trust an agent's "it builds" on faith**.

---

## 1. Architecture: interface → instance → capstone

The single most important structural decision. Split the work into three layers:

1. **Abstract interface** — a `structure` bundling the algorithm's modeling
   content as *fields* (hypotheses: equalities, bounds, independence facts,
   measurability/admissibility guards). Example shape:
   ```lean
   structure Analysis (V : Type) where
     P    : ProbSpace
     R    : V → ℝ
     key_bound : ∀ v, ...        -- the facts the proof consumes
     ...
   ```
2. **Abstract theorem** — prove the headline result over *any* `Analysis`. This
   is where the deep probability / combinatorics lives. It should come out
   **axiom-clean on its own**, independent of any concrete model.
3. **Concrete discharge** — build one `instance : Analysis` from the real objects
   and prove every field. Then the capstone is `theorem := abstract_theorem
   concreteInstance`.

**Why this wins:** the hard math is quarantined from the fiddly modeling. You can
prove (2) while (3) still has `sorry`s, and vice versa. Agents can work on
different fields of (3) in parallel because fields are independent. When (3) goes
green, the capstone lights up automatically.

**Corollary — "honest final theorem":** make sure the capstone is about the
*real* object, not a convenient surrogate. If the interface models an idealized
process (a clamped/"spirited" variant, an independent-runs product space, …), add
the **coupling lemma** that connects it back to the real algorithm, and state the
final theorem over the real thing.

---

## 2. Crux-first: find the heart, prove it, de-risk everything

Before grinding, identify the **one lemma** that carries the mathematical
difficulty — the second-moment expansion, the key independence factorization, the
locality fact an optimization relies on. Prove *that* first.

Once the crux is green, the surrounding theorem usually collapses into
**bookkeeping** (filter/image manipulation, induction, unfolding). In this
project, proving "the lazy test = the eager test" turned a scary
distributional-equivalence goal into a routine `Finset.filter_congr`.

Heuristic: if a proof feels huge, you haven't found the crux yet. Look for the
lemma that, once assumed, makes everything else routine — and attack it in
isolation.

---

## 3. Land one lemma at a time (never write 150-line monoliths)

The failure mode that burns the most time: attempting a single enormous proof.
Instead:

- Decompose into **named helper lemmas**, each independently statable.
- Prove and **`lake build` green after each one** before moving on.
- If a proof exceeds ~40 lines, that's a signal to factor out a sub-lemma.
- Keep a stub with `sorry` for the not-yet-done pieces so the file stays
  buildable and you can `#print axioms` the finished parts.

This also makes delegation possible: a named lemma with a clear signature is a
self-contained task an agent can own.

---

## 4. Verification discipline: what "done" actually means

**`#print axioms` is authoritative — grep is not.** `sorry` elaborates to the
`sorryAx` axiom, and `#print axioms Foo` walks the *entire transitive dependency
tree*. So the definition of done is:

```lean
#print axioms MyTheorem
-- 'MyTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those three are Mathlib's standard foundational axioms. **Anything else**
(`sorryAx`, a custom `axiom`, `Classical.choice`-adjacent surprises) means you're
not done. Three complementary checks, in order of strength:

1. `#print axioms <capstone>` — transitive, authoritative. The gold standard.
2. `lake build` emitting **zero** `declaration uses 'sorry'` warnings — catches
   sorries even in *dead/unused* declarations that (1) wouldn't reach.
3. `grep -rn "sorry\|admit\|native_decide\|sorryAx"` over your source — a cheap
   sanity sweep. Necessary-not-sufficient; it's fooled by comments and blind to
   transitive use.

Do all three. Ship only when all agree. (grep alone is the classic false
"it's proven.")

**But green is not correct — and your job is not done at green.** These three
checks establish the proof has no holes; they do **not** establish it proves the
*right statement* over the *real* object. That gap is human-only: a complete,
axiom-clean proof of a surrogate, or of a vacuous `∀` over an uninhabited
structure, passes all three checks above. You must therefore also produce the
**human-audit surface** of §11 — the artifact that lets a human run the four
checks the machine cannot. Do not report the project as done until it exists.

---

## 5. The formalization as a bug-oracle for the paper

A completed formalization is the strongest possible referee. **Wherever Lean
forced a hypothesis the paper doesn't state, that's a signal of a gap.**

When reviewing the source paper's proofs, cross-check each step against the
machine-checked version and classify every discrepancy:

- **Genuine error** — a statement that is false as written (e.g. a lemma whose
  case-split is under-guarded; a corollary quantified over a boundary case where
  it fails). Give a concrete counterexample.
- **Boundary/degenerate imprecision** — true generically, false at a degenerate
  point (empty max, a sink/leaf, a weight-0 or weight-1 edge, division by a
  quantity that can vanish). Usually WLOG-fixable but unstated.
- **Fine, implicit** — the step is correct but relies on a positivity /
  well-definedness fact the paper never states (`R(v) > 0`, `w(σ) > 0`).

Report with `file:line`, the claim, and *why* — and say plainly that the main
result still stands (or doesn't). This turns "we formalized it" into "we
formalized it **and** found the four things a referee should have caught."

---

## 6. Modeling decisions: pick the model that makes the theorem provable

Faithfulness and tractability trade off. Choose deliberately and **document the
choice in the file's docstring**.

- **Pointwise equality on a shared space ≫ measure-theoretic coupling.** If two
  processes can be expressed as functions of the *same* underlying randomness,
  prove them **equal as functions** (`funext`). Equal random variables are a
  *strictly stronger* result than "same distribution," and you skip all the
  measure theory. Reach for a genuine coupling only when the processes genuinely
  can't share coordinates.
- **Represent implementation artifacts by their mathematical content.** Pointers,
  caches, and lazy data structures matter for *runtime*, not *distribution*.
  Model a "pointer" by the object it points to; model a "cache flag" by the
  predicate it computes. Prove the decision logic equivalent; skip the plumbing.
- **Reuse proven-equal quantities instead of re-deriving them.** If a lazy
  algorithm computes the same numbers as the eager one (because cardinalities
  match), let the lazy model *reference* the eager estimates rather than
  re-running the whole estimate recursion. Note in the docstring that they are
  provably identical.
- **Scope caveat, stated honestly.** Formalizing "the algorithm computes the
  right thing" is not the same as formalizing "it runs in time T." If you prove
  the former, say so, and say the latter is out of scope. Don't let a README
  imply more than you proved.

---

## 7. Multi-agent orchestration (scaling without chaos)

Agents let you parallelize, but only with discipline.

**Partition by file.** One agent per file (or per disjoint file-group). Never let
two agents edit the same file — merge conflicts and clobbering. New work goes in
new files.

**Brief precisely.** A good agent task states: the exact theorem to prove
(verbatim, "do not weaken it"), the file to edit and how to build it, the
**exact lemma names** it can use (with signatures), the **proof strategy**
step-by-step, and an incremental instruction ("get the base cases green first,
then the main case"). Vague briefs produce flailing.

**Keep a tight leash.**
- Verify every claimed "it builds green" **yourself** — rebuild and re-check
  axioms. Agents report false greens; trust nothing unverified.
- Distinguish **dead** from **idle**: compare the agent's output-file mtime and
  the edited `.lean` mtime, and check for a live build process. A stale output
  with a fresh file usually means it died mid-edit — **resume from transcript**
  (edits persist on disk across API drops), don't restart from scratch.
- Background agents notify on completion; don't poll. For long waits, a single
  long-interval heartbeat as a fallback is enough.

**Serialize what must be serial.** The lazy/lock (e.g. `lake` build lock) already
serializes builds. But *logical* dependencies (define the model before proving
things about it) you must sequence yourself — do the linchpin definitions,
confirm they typecheck, *then* fan out the proofs.

**Adversarially verify findings.** For review/audit tasks, have independent
agents each try to *refute* a finding from a distinct angle; keep only what
survives. Redundant identical checks catch less than diverse ones.

---

## 8. When to ask the user vs. proceed

Ask only when the answer **changes what you build** and you can't derive it:

- A fork that changes effort by an **order of magnitude** (a distilled result vs.
  a full faithful model; preserve git history vs. fresh; which license and
  copyright holder). Present a **recommendation** as the first option.
- An **outward-facing or hard-to-reverse** action (creating a public repo,
  restructuring a shared repo, force-pushing). Confirm the plan first.

Otherwise pick the sensible default, state it, and keep moving. Don't ask about
things you can verify in the code or that have an obvious convention.

---

## 9. Mathlib / Lean gotchas that cost real time

- **`x / 0 = 0`** (and `1 / 0 = 0`) is the convention. Don't fight it. Lean on
  strict-positivity invariants (`0 < wt`, `0 < R`, `denominator ≠ 0`) and cancel
  with `div_mul_cancel₀` / `field_simp`, discharging the `≠ 0` side goal from
  those invariants. A "cancellation" proof that ignores the zero case gets stuck
  on a false-looking identity — that's the tell you need a positivity hypothesis.
- **Add positivity/well-definedness invariants to your model up front.** If the
  math divides by `w(σ)` or `R(v)`, bake `w(σ) > 0` / `R(v) > 0` into the
  structure (e.g. a `reaches_t` field, an edge-weight-in-`(0,1)` field). It's far
  cheaper than case-splitting on zero everywhere.
- **Real parameters, not rational discretization**, when the algorithm is real —
  a `K`-grid surrogate is often *not* simpler and isn't the real theorem.
- **`filter`/`image` swaps are unconditional:**
  `(s.image f).filter p = (s.filter (p ∘ f)).image f` — no injectivity needed.
  `Finset.filter_biUnion`, `Finset.filter_filter` merge/distribute cleanly.
- **Well-founded recursion + strong induction:** mirror the definition's
  `termination_by`/`decreasing_by` in proofs via
  `suffices ∀ n, ∀ x, measure x = n → P x` + `Nat.strong_induction_on`, so the IH
  covers all smaller elements. Grep the codebase for an existing induction pattern
  and copy it rather than reinventing.
- **Measurability/integrability guards** propagate: if your abstract theorem needs
  bounded-measurable ("admissible") integrands, thread that as a typeclass/field
  and discharge it once with reusable closure lemmas.
- **`Σ` (capital sigma) and other unicode** are reserved tokens — don't use them
  inside identifiers.
- **Multiline `exact`** must keep continuations indented under the tactic; a
  dedented next line parses as a new command ("unexpected token").

---

## 10. Git & release hygiene

- **`.gitignore` the build dir** (`/.lake/`, `/build/`, `*.olean`) — it's
  gigabytes (Mathlib cache + oleans) and must never enter a public repo. This is
  the #1 release hazard.
- **Root module re-exports everything.** Make the library root import the capstone
  so `import <Lib>` and a bare `lake build` compile *and expose* the headline
  theorem. Verify with a content-change probe (touch alone won't trigger a
  content-hash rebuild).
- **Extracting to a public repo:** for a clean public history, `git archive
  HEAD:<subdir> | tar -x` into a fresh dir, `git init`, one "Initial public
  release" commit, push. (Or `git subtree split` to preserve history.)
- **Submodule with a live build cache:** to convert a tracked subdir into a
  submodule without losing the multi-GB `.lake` cache, move `.lake` aside on the
  **same filesystem** (instant rename), `git rm -r --cached`, `git submodule
  add`, then move `.lake` back. `.gitignore` keeps it out of the submodule.
- **Rebase, don't merge, for orthogonal divergence.** If your change and the
  remote's touch disjoint files, `git rebase` keeps history linear. If a
  submodule checkout blocks a rebase's base checkout, `git submodule deinit -f`
  first, rebase, then `git submodule update --init`.
- **Provide `lake exe cache get` in the build instructions** so users don't
  compile Mathlib from source. Pin Lean and Mathlib to matching versions.
- **Scrub internal scaffolding before publishing:** delete handoff/roadmap/agent-
  log docs and dev-only demo files; remove phase codenames and cross-repo paths
  from user-facing docstrings; fix stale docstrings that describe an old state.

---

## 11. Communication & honesty

- Report **outcomes faithfully**: what's proven, what's assumed, what's out of
  scope. If a lemma is non-load-bearing or a corollary is dead, say so.
- When you delete or "prove" something, check it isn't actually **false** — a
  `sorry` standing in for a false statement should be *surfaced and removed*, not
  papered over.
- A README should claim exactly what's formalized. "Accuracy guarantee" ≠ "FPRAS
  including runtime." Scope the claim precisely.
- State the axiom profile in the README and show the reader how to re-check it.

**Produce the human-audit surface (what the machine can't check).** §4's three
checks prove the proof has no holes; a human must still verify it proves the
*right* statement, and the failure modes below all survive a green, axiom-clean
build. So emit a short `AUDIT.md` (or a "How to audit this" README section)
that makes the following four things **findable in minutes** by a human who will
*not* read the hard proofs. For each, give the `file:line` and the one thing to
check:
- **Capstone statement — is it about the REAL object?** Point to the single named
  final theorem. The human reads only its *type* (before the `:=`). If the
  interface models an idealized process, ensure the **coupling lemma** back to the
  real algorithm exists and the final theorem is stated over the real thing (§1
  corollary), and link it. A green build over a surrogate certifies nothing —
  never present one as the result.
- **Interface fields — are any secretly false or too strong?** List the
  `structure`'s fields (the global assumptions of the whole result), each with the
  `file:line` where the concrete instance discharges it, so the human reads the
  assumptions without reconstructing them.
- **Non-vacuity witness.** A capstone `∀ (S : Structure), P S` is worthless if
  `Structure` is uninhabited (vacuously true). Provide and point to a
  `Nonempty`/`Inhabited` witness — the exact/ideal instance with every error
  coefficient `0` — for *every* hypothesis-bundling structure the capstone
  quantifies over. If any is missing, the theorem may be vacuous; flag it loudly.
- **Semantic `def`s — does a name stand in for a proof?** `#print axioms` does
  **not** see a `def foo := <closed form>` whose name/docstring *claims* it equals
  some other quantity without proving it (e.g. `hdensDerivAbs` asserted-in-prose
  to equal `|hcont'|`). List every `def` whose name promises a semantic identity;
  each must carry a proving lemma or an explicit "UNPROVEN: assumed equal to …"
  flag, never the name alone. Surface the residual assumptions in `AUDIT.md`.

---

## 12. The reusable checklist

**Setup**
- [ ] Pin `lean-toolchain` + Mathlib to matching versions; `lake exe cache get`.
- [ ] `.gitignore`: `/.lake/`, `/build/`, `*.olean`, `.DS_Store`.

**Design**
- [ ] Abstract `structure` of hypotheses; abstract theorem over any instance.
- [ ] Positivity / well-definedness invariants baked into the structure.
- [ ] Identify the crux lemma(s); plan the concrete discharge field-by-field.

**Prove**
- [ ] Crux first, in isolation, green.
- [ ] One named lemma at a time; `lake build` green after each.
- [ ] Parallelize independent lemmas/fields across agents on disjoint files.
- [ ] Verify every agent's green yourself; resume dead agents from transcript.

**Verify done**
- [ ] `#print axioms <capstone>` = `[propext, Classical.choice, Quot.sound]`.
- [ ] Zero `declaration uses 'sorry'` in your files.
- [ ] grep sweep: no `sorry`/`admit`/`sorryAx`/custom `axiom` in source.
- [ ] Capstone is about the **real** object (coupling lemma in place).
- [ ] Emit the **human-audit surface** (§11) — `AUDIT.md` or a README section
      giving `file:line` for the capstone, structure fields + their discharge,
      non-vacuity witness(es), and the semantic-`def` list with residual
      assumptions — so a human runs the four human-only checks without reading the
      proofs. Do not report done until this exists.

**Bonus value**
- [ ] Cross-check the source paper against the formalization; report real bugs
      with `file:line` + counterexamples, classified by severity.

**Release**
- [ ] Root re-exports the capstone; bare `lake build` compiles everything.
- [ ] Scrub internal scaffolding + docstrings.
- [ ] README scoped honestly, with the axiom-check recipe.
- [ ] **Keep the README current — refresh it at least every ~30 min of active
      work** (and after every landed lemma or agent that changes the
      proved-vs-assumed picture): the module table, the "what is proved" and
      "what remains" sections, and the axiom-check example must always match the
      code on disk. A stale README is the fastest way to overstate what's done.
- [ ] Public repo / submodule wired; build cache preserved; both remotes pushed.

---

## 13. Patterns and gotchas from the floating-point Poisson-sampler project

Concrete lessons this project added to the methodology above.

**Share one Mathlib checkout via a symlink.** When a sibling project depends on a
local library (here `arlib`), don't let it clone its own Mathlib — a second
checkout is ~5 GB and on a full disk it simply fails mid-`lake`. Point the
project's `.lake/packages` at the library's package dir (`ln -s`), copy the
library's `lake-manifest.json`, and add the library as a path dependency. One
Mathlib, both projects. Watch for a stale IDE language server re-triggering the
clone and exhausting disk anyway — restart the Lean server if `lake setup-file`
starts erroring on space.

**Non-vacuity is part of "honest final theorem."** A capstone `∀ (S : Structure), …`
is worthless if `Structure` is uninhabited. Exhibit a witness — the *exact/ideal*
instance with every error coefficient set to `0` — and prove `Nonempty Structure`.
Do this for *every* hypothesis-bundling structure, including the concrete
(`RealSampler`) one, not just the abstract interface.

**"Axiom-clean" can still hide an assumption.** `#print axioms` sees `sorry` and
custom axioms — it does **not** see a *definition whose docstring claims more than
its body proves*. A `def hdensDerivAbs := <closed form>` asserted-in-prose to equal
`|hcont'|` is an invisible assumption. Put such identifications in an **explicit
hypothesis** of the consuming theorem, or mechanize them; never let a naming
convention stand in for a proof. Re-audit every `def` whose name promises a
semantic identity.

**Extract generic lemmas to the shared library mid-project, and define
specializations from the general.** The moment a lemma has no project-specific
content (TV distance, conditioning, rejection-sampling correctness, the error-DAG),
move it to the library — but define the special case *from* the general one
(`condEvent p A := condOn p 1_A`) with a one-line bridge lemma, rather than letting
the library carry two unrelated notions of the same thing.

**Bug-oracle extends to the paper's *computed* artifacts.** Cross-checking isn't
only for proofs: the paper's max-λ table didn't reproduce from its own bound
because the evaluation script applied an undocumented damping factor. Re-derive
every headline number from the stated bound, not from the script that produced it.

**A long-silent agent is not necessarily dead.** The "stale output + fresh source
file ⟹ died mid-edit" heuristic misfires for an agent running a single 90-minute
proof that hasn't flushed output. Before touching a possibly-live agent's file
(which violates one-agent-per-file), `SendMessage` it and wait — a ping is cheap,
a concurrent-edit clobber is not.

---

*Keep this file. It compounds: each project adds a gotcha or a pattern. The
methodology — abstract-then-instantiate, crux-first, one-lemma-at-a-time,
axioms-are-truth, formalization-as-oracle, tight-leash agents — transfers to any
theorem you want to take end-to-end.*

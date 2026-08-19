/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Lean
import ImportGraph.Lean.Environment

/-!
# The audit *commands* — machinery only, no invocations

Split out of `Ttc/Audit/ClosureCheck.lean` so that a file wanting to *run* an audit does not
have to import the file that *states* the audits.

`Ttc/Exec/VolPriceCVAlg.lean` uses `#closureReport`, and importing `Ttc.Audit.ClosureCheck`
for it dragged in `Ttc.Model.Theorem` — putting `Ttc.Model.Theorem` in the import closure of
every downstream capstone, and so making it impossible to state a runtime theorem about the
constructed oracle *inside* `Ttc/Model/Theorem.lean` without a cycle.

The commands live here; `Ttc.Audit.ClosureCheck` keeps the surface argument and the
invocations.  Nothing about what the audit *means* is decided in this file.
-/

open Lean Elab Command

namespace Ttc.Audit

/-- This development's own probability-space constructions, **by declaration name**. A
statement whose closure hits any of these is stated *in terms of* a probability space we built,
rather than merely being proved with one.

* `Ttc.TtcProb` — the 59-field hypothesis bundle (`Ttc/TtcProb.lean`);
* `Ttc.Oracles` — the four external calls as a structure (`Model/Pseudocode`);
* `Ttc.trajLaw`, `Ttc.trajOracles`, `Ttc.totalRate` — the coupled Poisson family, its law, and
  the bundle that reads a trajectory (`Coupling/Family`);
* `Ttc.MonteCarlo` — the constructed volume oracle and its coin space `Ttc.MonteCarlo.coins`
  (`Volume/MonteCarlo`);
* `Ttc.TtcAnalysis` — the analysis-side bundle (`Capstone`);
* `Ttc.run` — the modelled execution itself (`Model/Pseudocode`).

Matching is by **`Name` prefix**, not substring. nfalean can use substring matching because its
namespaces track its directories; here everything is under one `Ttc` namespace, so substring
matching produces false positives — `"Ttc.run"` would catch `Ttc.runScale`, `Ttc.runPrec` and
`Ttc.runCount`, which are steps of `alg:ttc` living in `Model/Pseudocode` and are not
probability constructions at all. `Name` prefix gets `Ttc.MonteCarlo.coins` from
`Ttc.MonteCarlo` and `Ttc.Oracles.vol` from `Ttc.Oracles` while leaving `Ttc.runScale` alone. -/
def forbidden : List Name :=
  [`Ttc.TtcProb, `Ttc.Oracles, `Ttc.trajLaw, `Ttc.trajOracles, `Ttc.totalRate,
   `Ttc.MonteCarlo, `Ttc.TtcAnalysis, `Ttc.run]

/-- Directories whose contents are probability-space content wholesale, checked against the
**defining module** rather than the name. `Ttc.Coupling` is the coupled level family and
`Ttc.Process` the Poisson/thinning level process; neither uses a matching namespace (its
declarations are bare `Ttc.trajLaw`, `Ttc.half`, …), so a name test cannot see them. -/
def forbiddenModules : List Name :=
  [`Ttc.Coupling, `Ttc.Process]

/-- The transitive definitional closure, accumulating only the `Ttc` constants.

Walks the type *and* — where there is one — the value of every constant reached. See the
module docstring for what that means for theorems (`ConstantInfo.value? = none`), which is the
notion of "what the statement means" this audit is after. -/
partial def closureAux (env : Environment) :
    NameSet → List Name → NameSet → NameSet
  | _, [], acc => acc
  | seen, c :: rest, acc =>
    if seen.contains c then closureAux env seen rest acc
    else
      let seen := seen.insert c
      let acc := if (`Ttc).isPrefixOf c then acc.insert c else acc
      match env.find? c with
      | none => closureAux env seen rest acc
      | some ci =>
        let next := ci.type.getUsedConstants.toList
          ++ (match ci.value? with | some v => v.getUsedConstants.toList | none => [])
        closureAux env seen (next ++ rest) acc

/-- The members of `cls` that are one of `forbidden`, or are defined in a module under one of
`forbiddenModules`. -/
def forbiddenIn (env : Environment) (cls : NameSet) : List Name :=
  cls.toList.filter fun c =>
    forbidden.any (fun f => f.isPrefixOf c) ||
      (match env.getModuleFor? c with
       | some mod => forbiddenModules.any fun f => f.isPrefixOf mod
       | none => false)

end Ttc.Audit

open Ttc.Audit in
/-- Report the `Ttc` constants a declaration transitively unfolds to, and fail if any of them
is one of our probability-space constructions. Seeds with the constant itself, so its own body
is unfolded too. -/
elab "#closure " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  let some _ := env.find? n | throwError "not found"
  let cls := (closureAux env {} [n] {}).erase n
  let bad := forbiddenIn env cls
  if bad.isEmpty then
    logInfo m!"OK — closure of {n} is free of our probability spaces \
      ({cls.toList.length} Ttc constants)"
  else
    throwError m!"FORBIDDEN in closure of {n}: {bad}"

open Ttc.Audit in
/-- The same audit for a **theorem**: seed from its *type*, so the statement — not the proof —
is what gets unfolded. (The proof is allowed to construct a probability space; that is what
`Exec/Canonical` is for.) -/
elab "#closureOfType " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  let some ci := env.find? n | throwError "not found"
  let cls := closureAux env {} ci.type.getUsedConstants.toList {}
  let bad := forbiddenIn env cls
  if bad.isEmpty then
    logInfo m!"OK — the STATEMENT of {n} is free of our probability spaces \
      ({cls.toList.length} Ttc constants)"
  else
    throwError m!"FORBIDDEN in the statement of {n}: {bad}"

/-! ## The audit surface: `Ttc/Model/` **and** `Ttc/Probability/`

### Why it is two directories and not one

`Ttc.ttc_volume` is a statement about `Ttc.ttc`, and `Ttc.ttc` is a
`MeasureTheory.Measure (ℝ × ℕ)` — a *law*, not a number. So the ambient probability
vocabulary is unavoidably part of what the headline's **type** unfolds to: the volume
oracle's coin space, the ½-thinning kernel and the trajectory law it generates, and the
sampler's two laws are named by the statement whether or not they are named by the paper's
pseudocode. A one-directory surface therefore forces a false choice — either
`Model/Pseudocode.lean` stops being pseudocode, or the vocabulary is filed with the
pseudocode it is not a step of.

`Ttc/Probability/` is that vocabulary, and the check below admits it **deliberately**, not
by accident: `Ttc.Audit.auditSurface` names both directories and every message the four
commands print says both. A check that silently widens its own allowed set is worthless;
this one widens it with the reason written down, and the widening is bounded by the rule
in the next paragraph.

### What keeps this honest rather than a dodge

`Ttc/Probability/` contains **vocabulary, and two contracts about it** — as of this
writing sixteen `def`s (`Ttc.MonteCarlo.coinLaw`, `Ttc.MonteCarlo.coins`; `Ttc.half`,
`Ttc.thinKernel`, `Ttc.chainKernel`, `Ttc.trajLaw`, `Ttc.toMultiset`, `Ttc.trajThin`,
`Ttc.trajPois`, `Ttc.trajGen`, `Ttc.padRow`; `Ttc.mixSteps`, `Ttc.ballWalkLaw`;
`Ttc.kv97SampD`, `Ttc.kv97ContLaw`, `Ttc.e2eSampD`) and two `instance`s
(`Ttc.isMarkovKernel_thinKernel`, `Ttc.isMarkovKernel_chainKernel`, which are the Markov
arguments Ionescu–Tulcea's `Kernel.trajMeasure` takes). **No hypothesis bundle, no
`@[simp]` lemma, nothing assumed, and nothing that asserts anything about `TTC`.**

The one qualification, and it is deliberate: `Probability/Trajectory` also carries the
two `Prop`s `Ttc.trajThin_le` and `Ttc.card_trajGen` — the sub-multiset and cardinality
contracts `Ttc.Oracles` demands of the read-offs defined beside them. They are not
vocabulary, and they are here for a structural reason rather than a topical one: a
theorem cannot be stated upstream of the definition it mentions, and the run's oracle
bundle (`Ttc.ttcOracleBundle`, `Exec/Api`) consumes both at elaboration time, so they cannot
go downstream either. Neither is visible to the walk below (a theorem is entered only through its
type, and both are reached as `_proof_` fields), so admitting them changed no closure
count. That bound — *`Prop`s only where a definition in this directory forces one, and
only where the walk cannot see them* — is what keeps this from being an open door.

Every property of these objects — that the kernels are Markov, that the walk mixes, that
the estimator is unbiased, that the loops terminate almost surely — is proved *outside*
the surface (`Process/Thinning`, `Process/Truncation`, `Coupling/Family`,
`Sampler/Construct`, `Volume/MonteCarlo`), and none of it is needed to read the statement.
`Ttc/Probability.lean`'s docstring restates that rule for anyone adding a file there.

An auditor's reading list is therefore six files rather than four: `Model/Prelude`,
`Model/ProblemSetting`, `Model/Pseudocode`, `Model/Theorem`, `Ttc/Probability/` (four
short files, two of which import Mathlib and `Arlib` alone, and which between them state
exactly two `Prop`s — the two oracle contracts named above), and `Ttc/Geometry/`.

**3. `Ttc/Geometry/` is the third directory, and it is definitions only.** The
convex-geometry data the sampler is applied at — `Ttc.facetOf`, `Ttc.canonAm`,
`Ttc.canonBv`, `Ttc.canonDm`, `Ttc.canonRfac` — is *not* probability. ⚠ This paragraph used
to add that it is "not vocabulary the statement is written in either", on the ground that
`Ttc.ttc_volume` mentioned none of the five; **that stopped being true on 2026-08-12**,
when the headline's two prices were fixed, and it is moot now that the headline is stated
outside the surface entirely.  They stay in `Ttc/Geometry/CanonPolytope.lean` — moved there
from `Model/Prelude` — because `Ttc.ttcAlgOutput`'s closure still reaches them and
`#modelClosure Ttc.ttcAlgOutput`, the one live check, would fail outright otherwise.  That is
why `auditSurface` names three directories instead of two.

The bound on what may go there is tighter than for `Ttc/Probability/`: **definitions only,
no `Prop`s at all, and nothing that is not convex geometry determined by the formula.**
`Ttc/Probability/` earns its two `Prop`s from a structural argument (a theorem cannot be
stated upstream of the definition it mentions, and the run's oracle bundle consumes both at
elaboration time); no such argument applies here, and there is nothing in the directory
that would need one. Every property of these five objects is proved outside the surface,
as before.

**A note on two prices that used to live inside the surface.**  Until 2026-08-19
`Model/Pseudocode` carried `Ttc.cvVolPriceAt` and `Ttc.hrSampPriceAt` — copies of two
`Ttc/Exec/` prices — because `Ttc.ttc` was then defined as the algorithm *charged at* them,
and `#modelClosure Ttc.ttc` walks definition bodies.  Copies are the case `CLAUDE.md` §13 is
about, so two `rfl` bridges in `Exec/VolPriceCVAlg` proved each copy equalled the price it
was named after, making drift a build error.

Both copies, both bridges and the charged `Ttc.ttc` are gone.  `Ttc.ttc` executes the two
oracles now rather than paying a fixed number for calling them, and what bounds its cost is
an envelope proved about the execution (`Model/Theorem`).  Nothing in the surface names a
price, so the §13 hazard this paragraph existed to manage no longer arises here.
-/

namespace Ttc.Audit

/-- **The audit surface, as directories.** A constant is inside it when the module that
defines it lies under one of these. See the section docstring above for why there are three
and what `Ttc/Probability/` and `Ttc/Geometry/` are allowed to contain; extending this list
is a change to what the reader-facing promise *means* and must be argued for there, not
here. -/
def auditSurface : List Name := [`Ttc.Model, `Ttc.Probability, `Ttc.Geometry]

/-- Constants in `cls` that are **not** defined in a file under one of
`Ttc.Audit.auditSurface`, paired with the module that does define them. -/
def outsideSurface (env : Environment) (cls : NameSet) : List (Name × Name) :=
  cls.toList.filterMap fun c =>
    match env.getModuleFor? c with
    | some mod => if auditSurface.any (fun d => d.isPrefixOf mod) then none else some (c, mod)
    | none => some (c, `«unknown»)

end Ttc.Audit

open Ttc.Audit in
/-- **The reader-facing audit check.** Every `Ttc` constant in the definitional closure of
`id` is defined under `Ttc/Model/` or `Ttc/Probability/`. Fails the build otherwise, naming
the stray constants and the modules they escaped to. -/
elab "#modelClosure " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  let some _ := env.find? n | throwError "not found"
  let cls := (closureAux env {} [n] {}).erase n
  match outsideSurface env cls with
  | [] => logInfo m!"OK — closure of {n} is defined entirely under Ttc/Model/, \
      Ttc/Probability/ or Ttc/Geometry/ ({cls.toList.length} Ttc constants)"
  | bad => throwError m!"OUTSIDE Model/, Probability/ and Geometry/ in closure of {n}: {bad}"

open Ttc.Audit in
/-- The same, seeded from a **theorem's** type, so the statement — not the proof — is what
gets unfolded. -/
elab "#modelClosureOfType " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  let some ci := env.find? n | throwError "not found"
  let cls := closureAux env {} ci.type.getUsedConstants.toList {}
  match outsideSurface env cls with
  | [] => logInfo m!"OK — the STATEMENT of {n} is defined entirely under Ttc/Model/, \
      Ttc/Probability/ or Ttc/Geometry/ ({cls.toList.length} Ttc constants)"
  | bad => throwError m!"OUTSIDE Model/, Probability/ and Geometry/ in the statement of {n}: {bad}"

/-! ## Reporting variants that do not fail the build

The four commands above are the audit proper: they *throw*, so a regression stops `lake
build`. Until the gap below is closed, the same information is available from these, which
only `logInfo`. They are what the measurements in the next section were taken with. -/

namespace Ttc.Audit

/-- A one-line size report for a declaration's closure: how many `Ttc` constants, how many of
them are outside the audit surface, and which forbidden ones it hits. Never fails. -/
def reportOn (env : Environment) (n : Name) (fromTypeOnly : Bool) : MessageData :=
  match env.find? n with
  | none => m!"{n}: not found"
  | some ci =>
    let cls :=
      if fromTypeOnly then closureAux env {} ci.type.getUsedConstants.toList {}
      else (closureAux env {} [n] {}).erase n
    let outside := outsideSurface env cls
    m!"{n}{if fromTypeOnly then " (statement)" else ""}: \
      {cls.toList.length} Ttc constants, {outside.length} outside Model/ and Probability/, \
      forbidden hits: {forbiddenIn env cls}"

end Ttc.Audit

open Ttc.Audit in
/-- Non-failing size report on a declaration's whole closure. -/
elab "#closureReport " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  logInfo (reportOn env n false)

open Ttc.Audit in
/-- Non-failing size report on a declaration's *statement*. -/
elab "#closureReportOfType " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  logInfo (reportOn env n true)

/-! ## The measurement, as of the port

All four audits **fail** here today. The invocations are kept, commented out, so the target is
written down next to the tool that checks it; uncommenting any of them breaks `lake build`,
which is exactly the behaviour wanted once the gap is closed. Reproduce with `lake env lean`
on a scratch file that `import Ttc.Audit.ClosureCheck` and runs the four commands, or use the
non-failing `#closureReport` / `#closureReportOfType` above.

### `Ttc.ttcAlgOutput` — the algorithm (`Model/Pseudocode`)

Full closure (a `def`, so the body is walked): **109** `Ttc` constants, of which **0** are
defined outside the audit surface — and, as it happens, none of them is a probability
constant at all: all 109 are under `Ttc/Model/`.  `#modelClosure Ttc.ttcAlgOutput`
**passes**, and is enabled below, so it fails the build the moment a definition the
algorithm depends on drifts out of it.  It reached that state by moving one `def` —
`Ttc.conj`, formerly `Ttc/Dnf.lean` — into `Model/Prelude`.

`#closure Ttc.ttcAlgOutput` still fails, on seven constants: `Ttc.Oracles`, its six
projections, and `Ttc.run`.  **All seven are defined in `Model/Pseudocode` itself**, so this
is not a filing problem — it is the monadic-versus-oracle gap.  nfalean's `countNFAM` is a
`PMF` built from `PMF.pure`/`bind`/`bernoulli` and takes no oracle argument; ours folds
`Ttc.run` over an `Oracles` bundle.  Closing it means making `alg:ttc` monadic, which
`Ttc/Monadic/` is the beginning of.

`#closure Ttc.ttcAlgOutput` reports **7** forbidden constants, and *all seven are defined in
`Model/Pseudocode` itself*: `Ttc.Oracles` with its six projections (`vol`, `covered`, `thin`,
`pois`, `gen`, and the structure), plus `Ttc.run`. This is the one real structural difference
from nfalean, and it is not incidental: `countNFAM` is a `PMF (ℝ × ℕ)` built from `PMF.pure`,
`PMF.bind` and `PMF.bernoulli`, so it takes *no* oracle argument; `Ttc.ttcAlgOutput` is a fold
of `Ttc.run` over an assumed `Ttc.Oracles` bundle. Closing check 1 for the algorithm means
making `alg:ttc` monadic, not moving a file.

### The three measurements that used to be here, and why they are gone

Three further sections measured `Ttc.ttc_volume`'s statement (206 constants, 0 outside),
`Ttc.ttcRun` (157) and `Ttc.ttc` (207) — the algorithm with its oracle argument filled in,
and the law of the pair `(estimate, cost)` — and recorded that `#modelClosure` passed on all
three while `#closure` failed on the monadic-versus-oracle gap.

All three measured objects were deleted on 2026-08-19.  `Ttc.ttcRun` and the fixed-price
`Ttc.ttcCharged` are gone outright; `Ttc.ttc` still exists but is a **different object** — the
law of a run at the constructed Cousins–Vempala volume estimator and the hit-and-run /
ball-walk hybrid sampler (`Model/Theorem`), where before it was the algorithm at *reference*
oracles charged at two fixed per-call numbers.  Naming the constructed pair is naming the
construction: the new `Ttc.ttc` and the new `Ttc.ttc_volume` reach 637 constants across 108
modules outside the surface, so neither can be checked, and neither is.

Quoting the old numbers at the new objects would be exactly the substitution
`CLAUDE.md` §13 warns about — a name standing in for an analysis that was done of something
else — so the numbers were removed rather than adjusted.  What survives is the measurement of
`Ttc.ttcAlgOutput` above: 109 constants, 0 outside, `#modelClosure` enabled in
`Ttc/Audit/ClosureCheck.lean` and failing the build on drift.  That check is about the
*specification*, and the specification is what still lives inside `Model/`.

`Ttc/Audit/ClosureCheck.lean` states the resulting asymmetry — the algorithm is auditable in
four files, the runtime claim is not — and argues why widening the surface to 108 modules
would be worse than admitting it.

-/


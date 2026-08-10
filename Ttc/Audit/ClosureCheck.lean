import Ttc.Model.Pseudocode
import Ttc.Model.Theorem

/-!
# Audit: what the `TTC` statement is actually made of

Two machine checks, ported verbatim in structure and naming from
`nfalean/ApproxNFA/Monadic/ClosureCheck.lean`, so that the two developments read alike and an
auditor who has seen one has seen the other.

**1. No probability space of ours** (`#closure`, `#closureOfType`). The definitional closure of
the declaration mentions none of *this* development's probability-space constructions: no
`Ttc.TtcProb` (the 59-field hypothesis bundle), no `Ttc.Oracles` (the oracle bundle the
pseudocode runs over), no `Ttc.trajLaw` / `Ttc.trajOracles` / `Ttc.totalRate` (the coupled
Poisson family of `Coupling/Family`), no `Ttc.MonteCarlo.coins` (the volume oracle's coin
space), and nothing from `Ttc.Coupling` or `Ttc.Process`.

(Mathlib's `MeasureTheory` API is of course a probability-space development; that is Mathlib's
business. The point of the check is whether *this* development has to construct a probability
space of its own in order to *state* its theorem.)

**2. `Model/` and `Probability/` are the whole audit surface** (`#modelClosure`,
`#modelClosureOfType`). Every `Ttc` constant the declaration transitively unfolds to is
*defined in a file under `Ttc/Model/` or under `Ttc/Probability/`*. This is the check that
backs the reader-facing promise made in `Ttc.lean`: open those two directories — four files
of model plus four short definition-only files of probability vocabulary — and every constant
the headline mentions is defined in front of you. It is strictly stronger than check 1, and
it fails the build the moment a definition the statement depends on drifts out of them, which
is exactly the regression worth catching.

The surface was one directory until the probability vocabulary was moved out of
`Model/Prelude` into `Ttc/Probability/`. **Why it is two, and what bounds the second one,
is argued at "The audit surface" below — read that before quoting this check**; the short
version is that `Ttc.ttc` is a `Measure`, so the ambient randomness is part of what the
headline's type unfolds to no matter where it is filed, and `Ttc/Probability/` is held to
definitions-only in exchange for being admitted.

## What "closure" means here, precisely

`closureAux` walks **both** the type and the value (`ci.value?`) of each constant it reaches.
In this Lean version `ConstantInfo.value?` returns `none` for theorems, so the walk has an
asymmetry that is worth stating because it is exactly the notion we want:

* **definitions** are unfolded through their *bodies* — what a `def` is built from is in scope;
* **theorems** are entered only through their *types* — a proof term's internals are not.

That is the right notion for an audit of a *statement*: we care about what the headline
*means*, not about which lemmas its proof happens to chain together. A proof is free to use
the measure-theoretic product space; a statement that mentions it has a different meaning.

Note that `Ttc.Params` bundles five *proof* fields, so some proof terms are genuinely part of
what the algorithm is (see `Model/Pseudocode`'s docstring); those are reached through the
types they inhabit, as they should be.

## Status in this repo

`#modelClosure` **passes** on the three algorithm-side declarations — `Ttc.ttcAlgOutput`,
`Ttc.ttcRun` and `Ttc.ttc` — and `#modelClosureOfType` on the headline's statement; all four
invocations are enabled at the bottom of this file, so a definition drifting out of
`Ttc/Model/` **or** `Ttc/Probability/` fails `lake build`. `#closure` still fails on the
three algorithm-side ones, on the monadic-versus-oracle gap and on the probability
vocabulary; **every constant it names is defined inside the surface**, so the two checks
disagree by construction rather than by filing (see the measurement section below). The two
`Ttc.ttc_volume_estimate` `#closure` invocations remain commented out.

`Ttc.Audit.forbidden` and `Ttc.Audit.forbiddenModules` were **not** touched by the move to
`Ttc/Probability/`, deliberately: the eleven definitions kept their existing full names, so
`` `Ttc.trajLaw `` and `` `Ttc.MonteCarlo `` still match exactly what they matched before,
and check 1 measures exactly what it used to. Renaming them into a `Ttc.Probability.*`
namespace would have made those two entries silently dead, which is the sort of quiet
weakening this file exists to prevent.
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

`Ttc.ttc_volume_estimate` is a statement about `Ttc.ttc`, and `Ttc.ttc` is a
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

`Ttc/Probability/` contains **vocabulary only** — as of this writing eleven `def`s
(`Ttc.MonteCarlo.coinLaw`, `Ttc.MonteCarlo.coins`; `Ttc.half`, `Ttc.thinKernel`,
`Ttc.chainKernel`, `Ttc.trajLaw`; `Ttc.mixSteps`, `Ttc.ballWalkLaw`; `Ttc.kv97SampD`,
`Ttc.kv97ContLaw`, `Ttc.e2eSampD`) and two `instance`s
(`Ttc.isMarkovKernel_thinKernel`, `Ttc.isMarkovKernel_chainKernel`, which are the Markov
arguments Ionescu–Tulcea's `Kernel.trajMeasure` takes). **No `Prop`, no hypothesis bundle,
no `@[simp]` lemma, nothing assumed, and nothing that asserts anything about `TTC`.**
Every property of these objects — that the kernels are Markov, that the walk mixes, that
the estimator is unbiased, that the loops terminate almost surely — is proved *outside*
the surface (`Process/Thinning`, `Process/Truncation`, `Coupling/Family`,
`Sampler/Construct`, `Volume/MonteCarlo`), and none of it is needed to read the statement.
`Ttc/Probability.lean`'s docstring restates that rule for anyone adding a file there.

An auditor's reading list is therefore five files rather than four: `Model/Prelude`,
`Model/ProblemSetting`, `Model/Pseudocode`, `Model/Theorem`, and `Ttc/Probability/` (four
short definition-only files, three of which import Mathlib and `Arlib` alone). The
convex-geometry data the sampler is applied at — `Ttc.facetOf`, `Ttc.canonAm`,
`Ttc.canonBv`, `Ttc.canonDm`, `Ttc.canonRfac` — is *not* probability and stays in
`Model/Prelude`.
-/

namespace Ttc.Audit

/-- **The audit surface, as directories.** A constant is inside it when the module that
defines it lies under one of these. See the section docstring above for why there are two
and what `Ttc/Probability/` is allowed to contain; extending this list is a change to what
the reader-facing promise *means* and must be argued for there, not here. -/
def auditSurface : List Name := [`Ttc.Model, `Ttc.Probability]

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
  | [] => logInfo m!"OK — closure of {n} is defined entirely under Ttc/Model/ or \
      Ttc/Probability/ ({cls.toList.length} Ttc constants)"
  | bad => throwError m!"OUTSIDE Model/ and Probability/ in closure of {n}: {bad}"

open Ttc.Audit in
/-- The same, seeded from a **theorem's** type, so the statement — not the proof — is what
gets unfolded. -/
elab "#modelClosureOfType " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  let some ci := env.find? n | throwError "not found"
  let cls := closureAux env {} ci.type.getUsedConstants.toList {}
  match outsideSurface env cls with
  | [] => logInfo m!"OK — the STATEMENT of {n} is defined entirely under Ttc/Model/ or \
      Ttc/Probability/ ({cls.toList.length} Ttc constants)"
  | bad => throwError m!"OUTSIDE Model/ and Probability/ in the statement of {n}: {bad}"

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

Full closure (a `def`, so the body is walked): **108** `Ttc` constants, of which **0** are
defined outside `Ttc/Model/`.  `#modelClosure Ttc.ttcAlgOutput` **passes**, and is enabled
below, so it fails the build the moment a definition the algorithm depends on drifts out of
`Model/`.  It reached that state by moving one `def` — `Ttc.conj`, formerly `Ttc/Dnf.lean` —
into `Model/Prelude`.

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

### `Ttc.ttc_volume_estimate` — the headline (`Model/Theorem`)

Statement closure (a theorem, so only its *type* is entered): **201** `Ttc` constants, of
which **0** are defined outside `Ttc/Model/`, and 25 are matched by `forbidden` — all of
them, now, *inside* `Model/`.  This is checked, not asserted: `#modelClosureOfType
Ttc.ttc_volume_estimate` is enabled at the foot of this file and fails the build on drift.

The table below is the historical record of the four groups that *used* to be outside, kept
because it documents what had to move and why.  It no longer describes the current state:

| group (module) | count | why the *statement* names it |
| --- | --- | --- |
| `Volume/MonteCarlo` | 12 | the accuracy conjunct's outer `∫⁻ … ∂(MonteCarlo.coins n)` *is* this coin space, and `Ttc.ttcOracleBundle` supplies `Ttc.mcVol` as the `vol` field |
| `Coupling/Family` | 12 | `Ttc.trajLaw` is the inner measure integrated against; `Ttc.trajOracles` is what the bundle unfolds to; `chainKernel`/`thinKernel`/`padPoint`/`toMultiset` are what those two are built from |
| `Model/Pseudocode` | 8 | `Ttc.Oracles` + six projections + `Ttc.run` — inherited from `Ttc.ttcAlgOutput`, and *inside* the audit surface, so `#modelClosure` is content with them |
| `Process/Thinning` | 3 | `Ttc.half` and its proof obligations, reached through `thinKernel` |

**`Ttc.TtcProb` is *not* in the closure.** The 59-field hypothesis bundle does not appear in
the statement at all — that part of the nfalean discipline already holds, and it is what
`Model/Theorem`'s docstring claims.

The 86 constants outside `Model/`, by module and by what they are:

| module | n | what |
| --- | --- | --- |
| `Exec/Api` | 18 | the run's abbreviations and parameter block (`ttcInput`, `ttcAtoms`, `ttcCen`, `ttcRadius`, `ttcScaledRadius`, `ttcBlock`, `ttcPrec`, `ttcIndex`, `ttcOracleBundle`, `ttcRates`, `ttcThresh`, `ttcTerminates`, `ttcCost`, `ttcNumCubes`) plus four proof terms |
| `Volume/MonteCarlo` | 12 | probability space + constructed volume oracle |
| `Coupling/Family` | 12 | probability space (the coupled Poisson family) |
| `Sampler/Construct` | 11 | constructed sampler (`ballWalkLaw`, `kv97ContLaw`, `kv97SampD`, `mixSteps`) |
| `Exec/CanonPolytope` | 6 | geometry data (`canonAm`, `canonBv`, `canonDm`, `canonRfac`, `facetOf`) |
| `Exec/Endgoal` | 5 | constructed oracles and the lattice enumeration |
| `Sampler/Rates` | 3 | parameter block: the Poisson rate vector (`rates`, `cubeAt`, `cubeOf`) |
| `Runtime` | 3 | cost model for the running-time conjunct (`runCost`, `stepCost`, `Terminates`) |
| `Process/Thinning` | 3 | probability: the ½-thinning law |
| `Exec/EndToEnd` | 3 | sampler: `e2eSampD` |
| `Invariants` | 2 | the loop invariant `AbsorbExits`, via `ttcTerminates` |
| `Exec/VolDischarge` | 2 | constructed volume oracle `Ttc.mcVol` |
| `Exec/Inputs` | 2 | `runOracles`, `runRates` |
| `Exec/Coverage` | 2 | covering data (`coverOfRegion`, `memPtOfRegion`) |
| `Volume/Oracle` | 1 | `roundBody` |


So the gap is concentrated: **half** of it (`Exec/Api` 18 + `Sampler/Rates` 3 + `Exec/Inputs`
2 + `Runtime` 3 = 26) is naming and cost-model vocabulary that could plausibly move into
`Model/`; the other half (`Volume/MonteCarlo` 12 + `Coupling/Family` 12 + `Sampler/Construct`
11 + `Process/Thinning` 3 + `Exec/VolDischarge` 2 + `Exec/EndToEnd` 3 = 43) is the two
*constructed* oracles and the probability spaces they run on, which the statement names only
because the theorem is stated at the constructed bundle rather than monadically.

Contrast nfalean, where `#closure countNFAM` and `#modelClosure countNFAM` both pass.

### `Ttc.ttcRun` — the algorithm with its oracle argument filled in

`Ttc.ttcRun` (`Model/Pseudocode`) is `Ttc.ttcAlgOutput` at the bundle the run `(c, t)`
itself supplies, and it is what the headline's accuracy conjunct is now stated over.
Full closure: **156** `Ttc` constants, of which **0** are outside `Ttc/Model/`, so
`#modelClosure Ttc.ttcRun` **passes** and is enabled below.  That is the machine-checked
form of "the headline's accuracy conjunct names only `Model/` things": it fails the build
the moment any part of the *constructed oracle bundle* drifts out of `Model/`, which is a
much larger surface than `Ttc.ttcAlgOutput`'s.

**The count is not comparable across `private`.**  It was 155 until
`Ttc.exists_latticeEnum` (`Model/Pseudocode`) stopped being `private`, and that is a
reporting change, not a drift: a private declaration's real name begins `_private`, not
`Ttc`, so `closureAux`'s `(`Ttc).isPrefixOf` test skipped it even though `Ttc.latticeEnum`
is `Classical.choose`n from it and it was always *in* the closure.  156 is the honest
number.  Read the count as an alarm bell for the "outside `Ttc/Model/`" tally beside it,
never as a size the file should be judged by.

Getting there moved three groups of declarations into `Model/Pseudocode`, each keeping its
name and its proof: the count-vector dictionary and the two oracle contracts
(`Ttc.count_toMultiset`, `Ttc.toMultiset_le_of_count_le`, `Ttc.trajThin_le`,
`Ttc.card_trajGen`, formerly `Coupling/Family`) — of which the dictionary has since gone
on to `Ttc/ModelSupport.lean`, restated at the sum `Ttc.toMultiset` unfolds to, which
changes none of these counts because no theorem outside a `def`'s body is in a closure;
the coverage test
(`Ttc.coverOfRegion`, `Ttc.memPtOfRegion`, formerly `Exec/Coverage`); and the lattice
enumeration (`Ttc.HasLatticeEnum`, `Ttc.exists_latticeEnum`, `Ttc.latticeEnum` and its
unconditional injectivity, formerly `Exec/Endgoal`).  Only what the bundle is *built
from* moved: the enumeration's two guarded properties `Ttc.latticeEnum_mem` and
`Ttc.latticeEnum_onto` are back in `Exec/Endgoal`, and `Ttc.card_toMultiset` in
`Coupling/Family`, because no field of the bundle needs either.
`#closure Ttc.ttcRun` still fails, on the same monadic-versus-oracle gap
as `Ttc.ttcAlgOutput` plus `Ttc.MonteCarlo`'s estimator — all of them defined in
`Model/Pseudocode` itself.

`Ttc.ttcRun`'s count went 156 → **157** when the oracle bundle its body used to spell
out inline was named `Ttc.algOracles` (`Model/Pseudocode`), so that `Ttc.algCost` could
be charged on the same bundle.  A naming change, not drift.

### `Ttc.ttc` — the whole algorithm as one law (`Model/Pseudocode`)

`Ttc.ttc atoms φ ε δ cVol cSample : Measure (ℝ × ℕ)` is the `Measure` analogue of
nfalean's `ApproxNFA.countNFAM : PMF (ℝ × ℕ)`: draw the volume coins, draw the sample
trajectory at the rates they produced, return `(estimate, cost)`.  Full closure:
**194** `Ttc` constants, of which **0** are outside `Ttc/Model/`, so
`#modelClosure Ttc.ttc` **passes** and is enabled below.  It is the machine-checked
form of "the headline names only `Model/` things" for *both* conjuncts at once —
strictly larger than `Ttc.ttcRun`'s surface, because it also covers the rate vector,
the two coin spaces and the charging model.

Getting there moved definitions upstream, keeping every name and statement, split by
role between the two `Model/` files that already existed:

* into `Model/Prelude` (the vocabulary — the ambient random objects, not steps of
  `alg:ttc`): `Ttc.MonteCarlo.coinLaw`/`coins` (formerly `Volume/MonteCarlo`),
  `Ttc.half` (`Process/Thinning`), `Ttc.thinKernel`/`chainKernel`/`trajLaw` with the
  two Markov-kernel instances Ionescu–Tulcea takes as instance arguments
  (`Coupling/Family`), `Ttc.mixSteps`/`ballWalkLaw`/`kv97SampD`/`kv97ContLaw`
  (`Sampler/Construct`), `Ttc.e2eSampD` (`Exec/EndToEnd`), and the canonical linear
  description `Ttc.facetOf`/`canonAm`/`canonBv`/`canonDm`/`canonRfac`
  (`Exec/CanonPolytope`) together with `Ttc.instFiniteCubeMem`/`instFiniteFacetIndex`,
  which `Ttc.facetOf` needs and which used to sit in `Model/Pseudocode`;
* into `Model/Pseudocode` (steps of `alg:ttc`): the charging model
  `Ttc.stepCost`/`runCost` (`Runtime`), and line 20's rate vocabulary
  `Ttc.cubeOf`/`cubeAt`/`rates` with the private choice principle `Ttc.exists_cubeOf`
  and the specification `Ttc.cubeOf_spec` that travel with `Ttc.cubeOf`
  (`Sampler/Rates`).

Nothing was duplicated: `Ttc.algRates` and `Ttc.algCost` (`Model/Pseudocode`) are the
run's own `Ttc.ttcRates` and `Ttc.ttcCost` spelled in `Model/` vocabulary, and
`Ttc.algRates_eq_ttcRates`, `Ttc.algCost_eq_ttcCost` (`Exec/Api`) hold by `rfl`.  The
honesty bridge is `Ttc.ttc_eq_ttcPairLaw` (`Monadic/Program`), which identifies
`Ttc.ttc` with the composition–product form `Ttc.ttcPairLaw` the rest of the
development reasons about; it is *not* `rfl`, because `Ttc.ttc` is stated with
`MeasureTheory.Measure.bind`/`map` — deliberately, so that no measurability proof has
to enter `Model/` — and the three-line proof is where `⊗ₘ` is unfolded.

`#closure Ttc.ttc` fails on 25 constants: `Ttc.Oracles` and its projections,
`Ttc.run`, `Ttc.MonteCarlo`'s estimator and coin space, `Ttc.trajLaw`,
`Ttc.trajOracles` and `Ttc.padPoint`.  **All 25 are defined under `Model/`.**  That is
the residual, and it is structural: `forbidden` was written to catch a *statement*
that names this development's probability spaces, and `Ttc.ttc` is by construction a
measure, so it names them.  What the list no longer detects is a filing problem —
`#modelClosure` is the check that does.

### Knock-on: `Ttc.ttc_volume_estimate`'s statement

Unchanged as a statement, but its closure improved as a side effect of the moves:
**201** `Ttc` constants, of which **0** are outside `Ttc/Model/`, and the 25 that
`forbidden` still matches by name are every one of them *defined inside* `Model/`.
(The trajectory was 212/86 → 219/71 → 229/30 → 201/0; earlier revisions of this
paragraph quoted the intermediate figures and were left stale by later moves.  It
is measured, so re-run rather than trust the prose.)

That is why `#modelClosureOfType Ttc.ttc_volume_estimate` is **enabled** below: the
headline's *type* — not merely the algorithm — now names nothing defined outside
the four `Model/` files, and the build fails if that ever stops being true.

`#closureOfType` stays disabled, and by construction rather than by filing: it
forbids a statement naming this development's probability spaces, and
`Ttc.ttc` **is** a measure, so the statement names them.  Every constant it flags
is under `Model/`.
-/

section Invocations

-- #closure Ttc.ttcAlgOutput
#modelClosure Ttc.ttcAlgOutput
#modelClosure Ttc.ttcRun
#modelClosure Ttc.ttc
-- #closureOfType Ttc.ttc_volume_estimate
#modelClosureOfType Ttc.ttc_volume_estimate

end Invocations

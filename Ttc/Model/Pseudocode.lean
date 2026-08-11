/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.ModelSupport
import Ttc.Probability

/-!
# `Model/Pseudocode`: `alg:ttc`, **and the preprocessing that precedes it**

A line-by-line transcription of Algorithm 1, followed by a line-by-line
transcription of the **four preprocessing steps** the verified algorithm applies
before it, ending in `Ttc.ttcAlgOutput` — `TTC(F, ε, δ)`'s output as one term, over
an oracle bundle — and in `Ttc.ttcRun`, the same term with that bundle filled in
from the run itself, which is what the headline is stated over and which takes **no
oracle argument**. The structural invariants of the modelled execution are in
`Invariants`, and every theorem about the preprocessing vocabulary stays in
`Exec/` (`Exec/Scale`, `Exec/ScaleFactor`, `Exec/Inscribed`, `Exec/Cleanup`,
`Exec/Prune`).

## What proof content is here, and why

This file **is not proof-free**, and it used to claim it was. What it now carries is
the smallest set of proofs that leaves it able to elaborate at all: **four
theorems**, one of them `private`, and no instances. Every one of them is a fact
about something *this file defines*, without which some *other* definition of this
file cannot be written down. Two groups:

1. **What the run's own oracle bundle cannot be built without** (1).
   `Ttc.algOracles` constructs an `Ttc.Oracles` and that structure has two *proof*
   fields; `Ttc.trajThin_le` and `Ttc.card_trajGen` now sit in
   `Probability/Trajectory` beside the read-offs they are about, but
   `Ttc.latticeEnum_injective`, which `thin_le` is applied at, mentions
   `Ttc.latticeEnum` and so has to stay here with it.
2. **What a `Classical.choose` cannot be taken without** (3). `Ttc.latticeEnum` is
   `choose`n from `Ttc.exists_latticeEnum`, and `Ttc.cubeOf` from the `private`
   `Ttc.exists_cubeOf`; `Ttc.cubeOf_spec` is that choice's `choose_spec`, and stays
   only because exporting the `private` theorem it reads would put a *new* name in
   the audit surface to remove an old one — and, unlike every other theorem here,
   a name that `#modelClosure` would then *see*, since `Ttc.cubeOf` unfolds to a
   `Classical.choose` of it.  That is measured, not estimated: it is +1 on
   `#modelClosure Ttc.ttc` (199 → 200) and on the statement closure (206 → 207).

`Ttc.exists_latticeEnum` is the one theorem here that `#modelClosure` already sees,
for the same reason: `Ttc.latticeEnum` is `Classical.choose` of it, and a `def`'s
body *is* walked. It cannot leave the audit surface at all.

**Everything that could leave has left.** Of the four, none but
`Ttc.exists_latticeEnum` is reachable by `Ttc/Audit/ClosureCheck.lean`'s
`closureAux` — it does not walk a theorem's value, and `Ttc.algOracles`' two proof
fields are lifted into anonymous `Ttc.algOracles._proof_1/_2`, which are themselves
theorems — so the rest are invisible in `#modelClosure Ttc.ttc`; they are here
because the file does not *elaborate* without them, and that failure is the check.
What kept them here is not the audit but their **statements**: each of the three
mentions a definition of this file (`Ttc.latticeEnum`, `Ttc.cubeOf`,
`Ttc.HasLatticeEnum`), and those definitions are in the measured closure, so they
cannot move out of the audit surface either.

What was here and is not any more:

* `Probability/Trajectory` — the five trajectory read-offs `Ttc.toMultiset`,
  `Ttc.trajThin`, `Ttc.trajPois`, `Ttc.trajGen`, `Ttc.padRow` together with the two
  oracle contracts about them, `Ttc.trajThin_le` and `Ttc.card_trajGen`.  Read-offs
  of a trajectory belong beside the trajectory law, and the two contracts had to
  travel with them: a theorem cannot be stated upstream of the definition it
  mentions.  `Ttc.algOracles` below still reads all seven, by import; the move
  changed no closure count, since the five are inside the audit surface either way
  and the two are invisible to the walk;
* `ModelSupport` — the four facts whose statements mention nothing of this file, so
  that nothing kept them: the count-vector dictionary `Ttc.count_toMultiset`,
  `Ttc.count_toMultiset_of_notMem`, `Ttc.toMultiset_le_of_count_le` (stated there at
  the sum `Ttc.toMultiset` *is*, generic in the carrier type, so every use is
  by unfolding a definition), and `Ttc.exists_finEnum_of_finite`, which is what
  `Ttc.hasLatticeEnum_of_finite` was once `Ttc.HasLatticeEnum` is not mentioned.
  `Ttc/ModelSupport.lean` is the one file outside `Model/` and `Ttc/Probability/`
  that this file imports, and its docstring states what that costs.

and, evicted downstream earlier, with names, statements and proofs unchanged:

* `Exec/Params` — the five side conditions a `Ttc.Params` needs (`hm`, `hr`) and
  what they rest on: `Ttc.one_le_card_cubes`, `Ttc.one_le_card_facets`,
  `Ttc.region_nil`, `Ttc.not_isBounded_univ_space`, `Ttc.exists_lit_of_isBounded`,
  `Ttc.one_le_card_cubes_of_ne_nil`, `Ttc.one_le_card_facets_of_isBounded`, plus
  the totalisation's two agreement lemmas `Ttc.ttcParamsTotal_eq` and
  `Ttc.ttcParamsTotal_eq_junk`;
* `Exec/Dedup` — the four basic properties of this file's converter
  (`Ttc.mem_toDNFd`, `Ttc.toDNFd_isDNFOf`, `Ttc.exists_mem_toDNF`,
  `Ttc.toDNFd_ne_nil`), the three positivity lemmas (`Ttc.cubeForm_isPositive`,
  `Ttc.dnfForm_isPositive`, `Ttc.preprocess_isPositive`), and the proof-carrying
  block `Ttc.inputParams` with its agreement lemma
  `Ttc.inputParamsTotal_eq_inputParams`.

The run does not read `Ttc.inputParams`: it reads the *total* block
`Ttc.inputParamsTotal`, which is a function of `(atoms, φ, ε, δ)` alone and needs no
lemma at all. That is what let the whole group go.

What is also **not** here, because nothing defined here needs it: the enumeration's
two guarded membership properties (`Exec/Endgoal`) and `Ttc.card_toMultiset`
(`Coupling/Family`).

There is no geometry, no measure theory and no probability, and nothing about what
the algorithm *achieves* — the two tables below say where each of those lives.

## The algorithm carries no proof binder

The reference for this layout is
`nfalean/ApproxNFA/Model/`, whose theorem is stated about `countNFAExec A n ε δ` —
the algorithm applied to its **inputs alone**. This file now does the same:
`Ttc.ttcAlgOutput atoms φ ε δ O` and `Ttc.ttcRun atoms φ ε δ c t` take no proof,
and neither do `Ttc.runScale`, `Ttc.runPrec`, or the nine read-offs
`Ttc.algBlock … Ttc.algMem` of the run section.

`Ttc.Params` still bundles five proof fields alongside its five data fields, so
`Ttc.ttcParams` still cannot be *applied* without proofs. What removes them from
the algorithm is not an unbundling but a totalisation: all five side conditions
(`0 < ε`, `ε ≤ 1`, `1 ≤ n`, `1 ≤ m`, `1 ≤ r`) are propositions about the *data*, so
`Ttc.ttcParamsTotal` and `Ttc.inputParamsTotal` **decide** them classically and fall
back on `Ttc.junkParams` when they fail. The run reads the total block, and
`Ttc.ttcParamsTotal_eq` (`Exec/Params`) /
`Ttc.inputParamsTotal_eq_inputParams` (`Exec/Dedup`) say that wherever the
headline's hypotheses hold it *is* the block `Ttc.inputParams` (`Exec/Dedup`)
builds — so every theorem stated about the latter transfers verbatim, by proof
irrelevance, and nothing about the junk branch is claimed. Those three, and the
side conditions they consume, are *downstream*: the total block needs none of
them.

The visible gain is that `Ttc.ttc_volume_estimate`'s type names no proof term:
`Ttc.preprocess_bdd` (`Exec/Api`) used to appear in it and no longer does. The
boundedness fact is still *proved*, and still spent — inside proofs, such as
`Ttc.ttcBlock_eq` (`Exec/Api`) and `Ttc.inputParamsTotal_preprocess`
(`Exec/BddPrep`) — but the statement no longer mentions it.

**This file imports one file, `Model/ProblemSetting`, and nothing else of ours.**
`Ttc.toDNFd`, the deduplicated line-16 converter that `Ttc.pruneForm` and
`Ttc.cleanForm` are defined over, used to live in `Exec/Dedup`; it is defined
*here* now (line A1 below), a two-line wrapper on `Ttc.toDNF` of `Model/Prelude`.
**Every** theorem about it — `Ttc.mem_toDNFd`, `Ttc.toDNFd_isDNFOf`,
`Ttc.toDNFd_nodup`, `Ttc.toDNFd_ne_nil`, `Ttc.length_toDNFd_le_card`, … — is in
`Exec/Dedup`, which imports this file: the edge runs `Model/ → Exec/`, never back.

The imports `Ttc.Dnf` and `Ttc.Lattice.Decomposition` were here for
`Ttc.toDNF_isDNFOf` and `Ttc.region_subset_sol`, which only the *evicted* proofs
used; with those gone the audit surface's import closure is `Model/ProblemSetting →
Model/Prelude → Mathlib` and nothing else.

```
line 22        p ← 1 ;  X ← ∅
lines 23–45    for i = 1 to m:
line 24          t ← Vol_ED(P(cᵢ), ε', δ')
lines 26–30      for s ∈ X: if s ∈ P(cᵢ) then remove s from X
lines 32–35      while p ≥ Thresh/t: remove each element of X w.p. ½ ; p ← p/2
line 38          Nᵢ ← Pois(t·p)
lines 39–42      while Nᵢ + |X| > Thresh:
                     remove each element of X w.p. ½ ; Nᵢ ← Pois(t·p/2) ; p ← p/2
line 43          S ← GenerateSamples(P(cᵢ), Nᵢ, ρ)
line 44          X ← X ⊎ S
line 46        output |X| / p
```

Throughout, the state after a cube is `Ttc.SketchState`: the multiset `𝒳` and the
**level** `j`, with `p = 2^(−j)`. The level is carried instead of `p` so that the
rate is an index rather than a real number — every randomised call is a read-off
at a level, and the paper's `Nois(j)` and `Err(j)` are events about that index.

| line | Lean |
| --- | --- |
| 22 (`p ← 1`) | level `0`: the second component of the initial `⟨0, 0⟩` |
| 22 (`X ← ∅`) | the first component of `⟨0, 0⟩` |
| 23–45 (`for i`) | `List.foldl` of `Ttc.step` over the cube list |
| 24 (`Vol_ED`) | `Ttc.Oracles.vol` |
| 26–30 (removal) | `Ttc.dropCovered`, a filter on `Ttc.Oracles.covered` |
| 32–35 (`while`) | `Ttc.haltLevel` — the least level at which the guard fails |
| 38 (`Pois(t·p)`) | `Ttc.Oracles.pois i j (t·2^(−j))` at the exit level |
| 39–42 (`while`) | `Ttc.absorbLevel` — the least level at which the guard fails |
| 39–42 (thinning) | `Ttc.Oracles.thin j₀ j'`, the survivors at level `j'` |
| 43 (`GenerateSamples`) | `Ttc.Oracles.gen` |
| 44 (`X ⊎ S`) | the `+` in `Ttc.step` |
| 46 (output) | `Ttc.run`; `Ttc.ttcOutput` (`Ttc/TtcProb.lean`) is it as a random variable |

**The four external calls are fields of `Ttc.Oracles`**, so the state evolution is
deterministic given their answers — all the randomness sits at that boundary,
which is where `lem:numlattice` lives.

**Four deviations from `algo.tex`** — the exit-level modelling of the two `while`
loops, its degenerate behaviour when the loop never exits, the thinning as a
read-off rather than a repeated coin, and the extra `(i, j)` arguments to `pois`
and `gen` — are recorded in `AUDIT.md` §1h-i, with the reason for each.

# The preprocessing: what `Model/Theorem` certifies `alg:ttc` **plus**

`Ttc.ttc_volume_estimate` does not measure a run of `alg:ttc` on the user's `F`.
It measures a run of `alg:ttc` on an input that four steps have already rewritten,
with the returned estimate divided by `qⁿ`. Those four steps are transcribed here,
in the same style as `alg:ttc` above, because the audit path is `Model/` and
nothing outside `Model/` may carry a step of the algorithm.

```
line A1        D  ← ToDNFd(F_bool)                        -- line 16, deduplicated
line A2        D  ← [ c ∈ D | interior(P(c)) ≠ ∅ ]        -- STEP 1: prune
line A3        F  ← DnfForm(D)                            -- read D back as a formula
line A4        D  ← [ c ∈ ToDNFd(F) | ¬ Void(c) ]         -- STEP 2a: drop void cubes
line A5        D  ← [ [ l ∈ c | ¬ Vacuous(l) ] | c ∈ D ]  -- STEP 2b: delete vacuous literals
line A6        F  ← DnfForm(D)                            -- read D back as a formula
line A7        for c ∈ ToDNFd(F):
line A8            (cen c, γ c) ← SomeInscribedBall(P(c)) -- STEP 3: the ball
line A9        γ̂  ← min over c of (γ c)
line A10       q  ← max 1 ( Thresh / (Vₙ · γ̂ ⁿ) )         -- STEP 4: the dilation factor
line A11       for a an atom of F:  a ← ⟨a.coeff, q · a.bound⟩
line A12       run alg:ttc (lines 22–46) on the dilated F, at radius q·γ̂
line A13       output (that run's output) / qⁿ
```

| line | Lean | where |
| --- | --- | --- |
| A1 (`ToDNFd`) | `Ttc.toDNFd` | here |
| (the reading `M`) | `Ttc.atomSet` | here |
| A2 (prune) | `Ttc.nondegenCubes` | here |
| A3, A6 (`DnfForm`) | `Ttc.dnfForm`, over `Ttc.cubeForm` | here |
| A2–A3 together | `Ttc.pruneForm` | here |
| A4 (`Void`) | `Ttc.VoidCube`, filtered by `Ttc.cleanDNF` | here |
| A5 (`Vacuous`) | `Ttc.VacuousLit`, filtered by `Ttc.cleanCube` | here |
| A4–A6 together | `Ttc.cleanForm` | here |
| A2–A6 together | `Ttc.preprocess` | here |
| A8 (`SomeInscribedBall`) | `Ttc.ballData`, `Ttc.autoCen` | here |
| A8 (centres) | `Ttc.cenOf` | here |
| A9 (`γ̂`) | `Ttc.gammaOf`, `Ttc.autoGamma` | here |
| A10 (`Vₙ`) | `Ttc.unitBallVol` | here |
| A10 (`q`) | `Ttc.scaleFactor`, `Ttc.runScale` | here |
| A11 (dilate) | `Ttc.scaleAtoms`, `Ttc.algAtoms` | here |
| (line 17, `ρ`) | `Ttc.runPrec`, `Ttc.algPrec` | here |
| (the coins' index) | `Ttc.algIndex` | here |
| A12 (the run) | `Ttc.run`, above | here |
| A13 (`/qⁿ`) | the division in `Ttc.ttcAlgOutput` | here |
| A12–A13 as one term | `Ttc.ttcAlgOutput` | here |

Every line of that table is a definition of *this* file, with no exception, and
three `rfl` lemmas in `Exec/Api` (`Ttc.ttcRun_eq_ttcAlgOutput`,
`Ttc.ttcRun_eq_ttcEstimate`, `Ttc.ttcInput_eq_preprocess`) machine-check that the
headline measures them. **Which of the four steps are in the paper** — steps 1, 3
and 4 are not, and step 1 changes `Sol` by a null set — is `AUDIT.md` §1h-ii, and
what completeness of the transcription does and does not buy is §1h-iii. Read those
before quoting this file as "the paper's algorithm".
-/

namespace Ttc

open Multiset

variable {n : ℕ} {ι : Type*}

/-- The loop state: the sample multiset `X` and the **level** `j`, with `p = 2^(−j)`.
`X` is the paper's `𝒳`; the level is the paper's `p`, carried as its exponent so
that the rate is an index the randomised oracles can be told (see the module
docstring). -/
structure SketchState (n : ℕ) where
  /-- The multiset `𝒳` of retained lattice points. -/
  X : Multiset (Space n)
  /-- The **level**: `p = 2^(−level)`. Incremented by every halving. -/
  level : ℕ

namespace SketchState

/-- The paper's sampling rate `p = 2^(−level)`. A definition, not a field: `p` is
only ever `1` halved some number of times, so the level determines it. -/
noncomputable def p (st : SketchState n) : ℝ := (1 / 2 : ℝ) ^ st.level

end SketchState

/-- The four external calls, as fields. Their *distributions* are what
`lem:numlattice` is about, and that is assumed. -/
structure Oracles (n : ℕ) (ι : Type*) where
  /-- `Vol_ED(P(cᵢ), ε', δ')` (line 24). -/
  vol : ι → ℝ
  /-- Membership test `s ∈ P(cᵢ)` (line 27). -/
  covered : Space n → ι → Bool
  /-- "Remove every element of `X` with probability ½", iterated (lines 33, 40):
  `thin j₀ j' X` is what survives of `X` at level `j'`, entering at level `j₀`.
  See deviation (c). -/
  thin : ℕ → ℕ → Multiset (Space n) → Multiset (Space n)
  /-- Thinning **removes** elements: the result is a sub-multiset. Stronger than
  "the cardinality does not grow", and it is what the pseudocode says — the loop
  deletes elements of `X`, it never invents them. -/
  thin_le : ∀ j₀ j' X, thin j₀ j' X ≤ X
  /-- A draw from `Pois(λ)` (lines 38, 41), for cube `i` at level `j`. -/
  pois : ι → ℕ → ℝ → ℕ
  /-- `GenerateSamples(P(cᵢ), N, ρ)` (line 43), for cube `i` at level `j`: `N`
  points of `P(cᵢ) ∩ 𝕃ⁿ`, where the lattice `𝕃ⁿ = 10^(-ρ)·ℤⁿ` is fixed by `ρ`. -/
  gen : ι → ℕ → ℕ → ℤ → Multiset (Space n)
  /-- `GenerateSamples` returns exactly `N` points. -/
  gen_card : ∀ i j N ρ, card (gen i j N ρ) = N

variable (P : Params) (O : Oracles n ι)

/-- **Lines 26–30.** Drop from `X` every point already covered by `P(cᵢ)`. -/
def dropCovered (i : ι) (X : Multiset (Space n)) : Multiset (Space n) :=
  X.filter fun s => O.covered s i = false

/-- **Lines 32–35.** `while p ≥ Thresh/t do (X ← halve X ; p ← p/2)`, as its exit
level: the least level at or above `j` whose rate `2^(−j')` is below `Thresh/t`.
Deterministic — no randomness enters this loop, only the rate. -/
noncomputable def haltLevel (t : ℝ) (j : ℕ) : ℕ :=
  max j (sInf {j' | ¬ P.thresh / t ≤ (1 / 2 : ℝ) ^ j'})

/-- **Lines 39–42.** `while Nᵢ + |X| > Thresh do (X ← halve X ; Nᵢ ← Pois(t·p/2) ; p ← p/2)`,
as its exit level: the least level `j'` at or above `j₁` at which the surviving
sketch and the level-`j'` Poisson draw together fit under `Thresh`. `j₀` is the
level the step was entered at, which is what `thin` measures survival from. -/
noncomputable def absorbLevel (i : ι) (t : ℝ) (X : Multiset (Space n)) (j₀ j₁ : ℕ) : ℕ :=
  max j₁ (sInf {j' | j₁ ≤ j' ∧ ¬ P.thresh <
    (O.pois i j' (t * (1 / 2 : ℝ) ^ j') : ℝ) + (card (O.thin j₀ j' X) : ℝ)})

/-- **Lines 24–42.** The state after both `while` loops of iteration `i`, paired
with the surviving Poisson draw `Nᵢ`. Split out of `Ttc.step` so that the
`GenerateSamples` append can be stated on its own (`Ttc.card_step`). -/
noncomputable def stepPre (st : SketchState n) (i : ι) : SketchState n × ℕ :=
  let t := O.vol i
  let X₀ := dropCovered O i st.X
  let j := absorbLevel P O i t X₀ st.level (haltLevel P t st.level)
  (⟨O.thin st.level j X₀, j⟩, O.pois i j (t * (1 / 2 : ℝ) ^ j))

/-- **Lines 24–44.** One iteration of the main loop; `ρ` is the precision fixed at
line 17. -/
noncomputable def step (ρ : ℤ) (st : SketchState n) (i : ι) : SketchState n :=
  let res := stepPre P O st i
  ⟨res.1.X + O.gen i res.1.level res.2 ρ, res.1.level⟩

/-- **Lines 22–46.** Fold `step` over the cubes from `X = ∅` at level `0`, output
`|X|/p`. `ρ` is `GetPrecision`'s output (line 17), fixed before the loop and passed
to every `GenerateSamples` call. -/
noncomputable def run (ρ : ℤ) (cubes : List ι) : ℝ :=
  let final := cubes.foldl (step P O ρ) ⟨0, 0⟩
  (card final.X : ℝ) / final.p

/-! ## The charging model, `thm:runtime`

What the running-time half of the headline counts.  It is part of the audit surface
because the theorem *bounds* it: `Ttc.ttc` returns a cost, so a referee must be able to
read what that number is.  Everything proved about it — that it is bounded by the
closed form `Ttc.ttcComplexity` — is in `Exec/Complexity` and `Runtime`. -/

/-- **The cost of one iteration**, as `thm:runtime` accounts it: one `Vol_ED` call
(`alg:ttc` line 24) plus one `GenerateSamples` draw per point returned (line 43).
`N` is the surviving Poisson count `Nᵢ`. -/
def stepCost (cVol cSample N : ℕ) : ℕ := cVol + cSample * N

/-- **The cost of the whole run**: the per-iteration cost summed along the fold
that `Ttc.run` performs, so the state — and hence each `Nᵢ` — is the one the
algorithm actually reaches. -/
noncomputable def runCost (cVol cSample : ℕ) (ρ : ℤ) (cubes : List ι) : ℕ :=
  (cubes.foldl
    (fun (acc : ℕ × SketchState n) i =>
      (acc.1 + stepCost cVol cSample (stepPre P O acc.2 i).2, step P O ρ acc.2 i))
    (0, ⟨0, 0⟩)).1

/-! # The preprocessing, lines A1–A13

Definitions only, exactly as above: what each step *is*. Everything proved about
them stays in `Exec/` — `Ttc.sol_cleanForm` and `Ttc.volSol_pruneForm` (that the
body is preserved), `Ttc.volSol_scaleAtoms` (that the dilation is exact),
`Ttc.ball_subset_cenOf` and `Ttc.gammaOf_pos` (that the constructed ball is one),
`Ttc.thresh_le_scaled_ball_volume` (that `q` is large enough).

See the module docstring for the `alg:ttc` line each of these implements, and for
the three `rfl` bridges (`Ttc.ttcRun_eq_ttcAlgOutput`, `Ttc.ttcRun_eq_ttcEstimate`,
`Ttc.ttcInput_eq_preprocess`, all `Exec/Api`) that pin the headline's measured
quantity to them. -/

section Preprocess

variable {A : Type*}

/-! ## The interpretation: what an atom denotes

Every step below is stated over the *set* an atom denotes, not over the atom
itself. `Ttc.atomSet` is that reading — the map `M` the headline used to take as a
binder together with an equation defining it. -/

/-- **The interpretation `M`.** The theorem used to take `M` as a binder together
with `M_eq : M = fun a => (atoms a).halfspace`; this is that right-hand side, named,
so that the binder and its defining equation are both discharged by `rfl`. -/
def atomSet (atoms : A → LinAtom n) : A → Set (Space n) := fun a => (atoms a).halfspace

/-! ## Line A1: the converter, deduplicated -/

/-- **Line A1.** `Ttc.toDNF` — `alg:ttc` line 16, the circuit-AllSAT call — run
through a deduplication pass. Noncomputable only because `Ttc.Cube A` carries no
`DecidableEq` for an abstract atom type `A`; the instance is supplied by
`Classical.decEq`, written explicitly in the body.

Deduplication is needed because `Ttc.ttc_volume_final`'s side condition
`((toDNF φ).length : ℝ) ≤ P.m` with `P.m = Nat.card {c // c ∈ toDNF φ}` is a
`Nodup` condition in disguise, and the raw converter provably fails it
(`Ttc.toDNF_length_gt_card_cubes`, on `a ∨ a`). Everything proved about `toDNFd`
— that it has the same members as `toDNF φ` (`Ttc.mem_toDNFd`), is duplicate-free
(`Ttc.toDNFd_nodup`), is still a correct positive DNF (`Ttc.toDNFd_isDNFOf`,
`Ttc.toDNFd_isPositive`), and discharges the side condition
(`Ttc.length_toDNFd_le_card`) — is in `Exec/Dedup`, which imports this file. -/
noncomputable def toDNFd (φ : BForm A) : DNF A :=
  @List.dedup _ (Classical.decEq (Cube A)) (toDNF φ)

/-! ## Step 2, lines A4–A6: cleaning the zero-normal atoms

A literal whose atom has a zero normal is not a constraint: with a nonnegative
bound it denotes `Set.univ`, with a negative bound `∅`. Line A5 deletes the first
kind; line A4 deletes the cubes containing the second. `Ttc.Cube A` is a `List` and
`A` carries no `DecidableEq`, so both filters decide their predicate classically —
the idiom of `Ttc.toDNFd`. -/

/-- A literal is **vacuous** when its atom's normal is `0` and its bound is `≥ 0`:
positively, it constrains nothing. The `Vacuous` of line A5. -/
def VacuousLit (atoms : A → LinAtom n) (l : Lit A) : Prop :=
  (atoms l.atom).coeff = 0 ∧ 0 ≤ (atoms l.atom).bound

/-- A cube is **void** when it contains a literal whose atom's normal is `0` and
whose bound is `< 0`: positively, it is unsatisfiable. The `Void` of line A4. -/
def VoidCube (atoms : A → LinAtom n) (c : Cube A) : Prop :=
  ∃ l ∈ c, (atoms l.atom).coeff = 0 ∧ (atoms l.atom).bound < 0

/-- **Line A5.** The cube with its vacuous literals deleted. -/
noncomputable def cleanCube (atoms : A → LinAtom n) (c : Cube A) : Cube A :=
  c.filter fun l => !(@decide (VacuousLit atoms l) (Classical.propDecidable _))

/-- **Lines A4–A5.** The cleaned DNF: void cubes dropped, vacuous literals deleted
from the rest. -/
noncomputable def cleanDNF (atoms : A → LinAtom n) (D : DNF A) : DNF A :=
  (D.filter fun c => !(@decide (VoidCube atoms c) (Classical.propDecidable _))).map
    (cleanCube atoms)

/-! ## Lines A3 and A6: reading a cube list back as a formula

Both rewriting steps rebuild the *formula* from the surviving cubes rather than
editing the DNF in place. They have to: `Ttc.IsDNFOf D φ` quantifies over **all**
Boolean assignments, and neither rewrite is justified at an arbitrary assignment —
`Ttc.not_isDNFOf_cleanDNF` and `Ttc.not_isDNFOf_nondegenCubes_degForm` are the
machine-checked refutations. A positive DNF is the `Ttc.toDNF` of its own
disjunction of conjunctions (`Ttc.toDNF_dnfForm`), so the rebuilt formula is a
genuine `Ttc.IsDNFOf` of the surviving cubes. -/

/-- The formula of a cube: the conjunction of its atoms, via `Ttc.conj`. -/
def cubeForm (c : Cube A) : BForm A := conj (c.map Lit.atom)

/-- **Lines A3 and A6.** The formula of a DNF: the disjunction of its cubes'
formulas. `[]` has no positive formula denoting `∅` (`Ttc.BForm` has no `false`
constructor and `IsPositive (.neg _)` is `False`), so it is sent to the junk value
`BForm.tt`; every theorem about `dnfForm` therefore assumes `D ≠ []`. -/
def dnfForm : DNF A → BForm A
  | [] => .tt
  | [c] => cubeForm c
  | c :: D => .or (cubeForm c) (dnfForm D)

/-! ## Step 1, lines A2–A3: pruning the degenerate cubes

A cube whose region has empty interior is either unsatisfiable or
lower-dimensional; either way its region is convex and Lebesgue-null. Line A2
deletes those cubes and line A3 reads the survivors back as a formula. Having
nonempty interior is not decidable, so the filter decides classically — hence the
`noncomputable`. -/

/-- **Line A2.** The sublist of cubes whose region has nonempty interior: the
full-dimensional cubes of the decomposition. -/
noncomputable def nondegenCubes (M : A → Set (Space n)) (D : DNF A) : DNF A :=
  D.filter fun c => @decide _ (Classical.propDecidable (interior (region M c)).Nonempty)

/-- **Lines A2–A3 as one step: `φ` with its degenerate (lower-dimensional or empty)
cubes pruned away.**

`Ttc.nondegenCubes` keeps exactly the cubes whose region has nonempty interior, and
`Ttc.dnfForm` reads the surviving list back as a formula, so that `Ttc.IsDNFOf`
survives (it would not, for the pruned list against the original `φ`:
`Ttc.not_isDNFOf_nondegenCubes_degForm`). `Ttc.volSol_pruneForm` says the deletion
is invisible to the measure; `Ttc.sol_pruneForm_subset` says it is *not* invisible
to the set. -/
noncomputable def pruneForm (atoms : A → LinAtom n) (φ : BForm A) : BForm A :=
  dnfForm (nondegenCubes (atomSet atoms) (toDNFd φ))

/-- **Lines A4–A6 as one step.** The cleaned input formula: `Ttc.toDNFd φ`, cleaned,
read back as a formula. `Ttc.sol_cleanForm` says this denotes literally the same
subset of `Ttc.Space n` as `φ` does. -/
noncomputable def cleanForm (atoms : A → LinAtom n) (φ : BForm A) : BForm A :=
  dnfForm (cleanDNF atoms (toDNFd φ))

/-- The input the amended algorithm actually runs on: degenerate cubes pruned,
then zero-normal atoms constant-folded. -/
noncomputable def preprocess (atoms : A → LinAtom n) (φ : BForm A) : BForm A :=
  cleanForm atoms (pruneForm atoms φ)

/-! ## Step 3, lines A7–A9: the inscribed ball

`alg:prec` line 86 obtains `γ̂` from an LP, `γ̂ ← MaxInscribedBall(Pⁱ)`. What is
transcribed here is weaker and total: *some* inscribed ball per cube, chosen
classically, and the least of the resulting radii. Non-maximality costs nothing in
soundness — the radius enters only through `ρ = ⌈log₁₀(γ/γ̂)⌉`, and a smaller `γ̂`
only makes the lattice finer. -/

open Classical in
/-- **Line A8.** Some inscribed ball of the region of `i`, if one exists; `(0, 0)`
otherwise. The pair is `(centre, radius)`. The choice is classical and carries
**no** optimality claim: it is *an* inscribed ball, not the largest one.

The `open Classical in` supplies the `Decidable` instance for the (undecidable)
existential; the definition is `noncomputable` regardless. -/
noncomputable def ballData (M : A → Set (Space n)) (i : Cube A) : Space n × ℝ :=
  if h : ∃ p : Space n × ℝ, 0 < p.2 ∧ Metric.ball p.1 p.2 ⊆ region M i then h.choose else (0, 0)

/-- **Line A8.** The centre map: each cube gets its own inscribed-ball centre. -/
noncomputable def cenOf (M : A → Set (Space n)) (D : DNF A) :
    {c : Cube A // c ∈ D} → Space n := fun i => (ballData M i.val).1

/-- **Line A9.** The shared inscribed radius `γ̂`: the least of the per-cube radii.

Total by construction — on an empty DNF the infimum of the empty family of reals is
`0`, which is exactly the degenerate value `Ttc.ball_subset_cenOf` tolerates. -/
noncomputable def gammaOf (M : A → Set (Space n)) (D : DNF A) : ℝ :=
  ⨅ i : {c : Cube A // c ∈ D}, (ballData M i.val).2

/-! ## Step 4, lines A10–A11: the dilation

Volume is homogeneous of degree `n`, so dilating the input by `q ≥ 1` multiplies
`Vol(Sol F)` by exactly `qⁿ` — as large as needed to clear `Thresh`, which is what
`alg:ttc`'s Poisson sketch requires and what the printed algorithm does not
guarantee. Line A13's division by `qⁿ` undoes it; relative error is invariant. -/

/-- **`Vₙ`, the volume of the unit ball of `Ttc.Space n`, as a real.** Deliberately
opaque: the Gamma-function formula `π^{n/2}/Γ(n/2+1)` is never needed, only
`Ttc.unitBallVol_pos` and `Ttc.volume_ball_eq`. -/
noncomputable def unitBallVol (n : ℕ) : ℝ :=
  (MeasureTheory.volume (Metric.ball (0 : Space n) 1)).toReal

/-- **Line A10.** The dilation factor `q`: enough to push `Vol(Sol F)` past `Thresh`.
Computed from the inscribed radius `γ̂` and the dimension, with **no knowledge of
`Vol`** — that is what makes this preprocessing rather than a hypothesis.

`max 1 (…)` overshoots the exact factor `(Thresh/(Vₙ γ̂ⁿ))^{1/n}`; that is
deliberate. It avoids an `n`-th root — `1 ≤ q` gives `q ≤ qⁿ`, which is all
`Ttc.thresh_le_scaled_ball_volume` needs — at the price of a larger dilation, and
the price is zero because line A13 divides by `qⁿ`. -/
noncomputable def scaleFactor (n : ℕ) (P : Params) (gammaHat : ℝ) : ℝ :=
  max 1 (P.thresh / (unitBallVol n * gammaHat ^ n))

/-- **Line A11.** The input formula's atoms, dilated by `c`: same normals, bounds
scaled. Scaling the bound and not the normal is what dilates rather than rotates —
the half-space `{x | ⟪a, x⟫ ≤ b}` becomes `{x | ⟪a, x⟫ ≤ c·b} = c · {x | ⟪a, x⟫ ≤ b}`
(`Ttc.halfspace_scaleAtoms`). -/
def scaleAtoms (c : ℝ) (atoms : A → LinAtom n) : A → LinAtom n :=
  fun a => ⟨(atoms a).coeff, c * (atoms a).bound⟩

end Preprocess

/-! # The parameter block

`alg:ttc` lines 17–20 *compute* `η, ε', δ', Thresh, κ, γ, ρ` from `(F, ε, δ)`.  All
seven are already `def`s on `Ttc.Params` (`Model/Prelude`), so what is left is the
block itself: `Ttc.ttcParams`, which reads `m` and `r` off the decomposition, and
`Ttc.ttcParamsTotal` / `Ttc.inputParamsTotal`, which are what the run reads.

**There are no proofs here.**  `Ttc.Params` bundles five *proof* fields
(`hε0 hε1 hn hm hr`), so `Ttc.ttcParams` cannot be *applied* without them — but it
is applied only inside `Ttc.ttcParamsTotal`, on the branch where a `Decidable`
instance has already produced them, and `Ttc.junkParams` discharges its own five by
`le_refl` and `one_pos`.  So nothing in this section needs a lemma, and every lemma
that used to be here is now downstream:

* `Exec/Params` — what supplies `hm` and `hr` when a *caller* builds the block
  (`Ttc.one_le_card_cubes`, `Ttc.one_le_card_facets`, `Ttc.region_nil`,
  `Ttc.not_isBounded_univ_space`, `Ttc.exists_lit_of_isBounded`,
  `Ttc.one_le_card_cubes_of_ne_nil`, `Ttc.one_le_card_facets_of_isBounded`), the
  two agreement lemmas `Ttc.ttcParamsTotal_eq` and `Ttc.ttcParamsTotal_eq_junk`,
  and the tie-back lemmas `Ttc.ttcParams_eps`, … that were always there;
* `Exec/Dedup` — everything about this file's converter (`Ttc.mem_toDNFd`,
  `Ttc.toDNFd_isDNFOf`, `Ttc.exists_mem_toDNF`, `Ttc.toDNFd_ne_nil`,
  `Ttc.toDNFd_nodup`, `Ttc.toDNFd_isPositive`, `Ttc.toDNFd_ne_nil_of`,
  `Ttc.natCard_mem_list`, `Ttc.natCard_mem_list_of_nodup`, `Ttc.card_toDNFd`,
  `Ttc.length_toDNFd_le_card`), the three positivity lemmas
  (`Ttc.cubeForm_isPositive`, `Ttc.dnfForm_isPositive`,
  `Ttc.preprocess_isPositive`), and the proof-carrying block `Ttc.inputParams`
  together with `Ttc.inputParamsTotal_eq_inputParams`;
* `Exec/CubeBounds` — the positivity route to a nonempty raw DNF
  (`Ttc.exists_mem_dnfAux_true`, `Ttc.toDNF_ne_nil`, …), which was never here.
-/

section ParamBlock

variable {A : Type*}

/-! ## The block itself -/

/-- **The parameter block `TTC(F, ε, δ)` computes**, from the DNF its AllSAT call
returned, the ambient dimension, and the requested accuracy and confidence.

`m` and `r` are the *exact* counts, not bounds: `alg:ttc` reads them off the
decomposition.  Taking them exactly is what makes `Ttc.ttcParams_cubes_le` and
`Ttc.ttcParams_facets_le` (`Exec/Params`) `le_refl` rather than assumptions.

Everything downstream — `η = ε/8`, `ε' = ε/12`, `δ' = δ/(4m)`, `Thresh`, `κ`, `γ`,
`ρ = ⌈log₁₀(γ/γ̂)⌉` — is already a `def` on `Params` (`Model/Prelude.lean`), so no
further computation is needed here. -/
noncomputable def ttcParams (D : DNF A) (n : ℕ) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ D})
    (hr : 1 ≤ Nat.card (FacetIndex D)) : Params where
  ε := ε
  δ := δ
  n := n
  m := Nat.card {c : Cube A // c ∈ D}
  r := (Nat.card (FacetIndex D) : ℝ)
  hε0 := hε0
  hε1 := hε1
  hn := hn
  hm := hm
  hr := by exact_mod_cast hr

/-! ## The block as a **total** function of the data

`Ttc.Params` bundles five *proof* fields (`hε0 hε1 hn hm hr`), so `Ttc.ttcParams`
cannot be *applied* without proofs — and that, and nothing else, is what forced
proof binders onto `Ttc.ttcAlgOutput` and `Ttc.ttcRun`.  All five side conditions
are propositions about the *data* alone, so they can be **decided** classically
rather than supplied, giving the block as a function of `(atoms, φ, ε, δ)` only.
That is what the run below uses, and it is why the run carries no proof binder —
and why this section needs no lemma of its own.

The junk branch is inhabited because `Params`' proof fields constrain only its own
stored scalars (`0 < ε`, `ε ≤ 1`, `1 ≤ n`, `1 ≤ m`, `1 ≤ r`), never the formula:
`⟨1,1,1,1,1⟩` is a `Params`.  Nothing is claimed about it — `Ttc.ttcParamsTotal_eq`
(`Exec/Params`) says the branch is not taken wherever the headline's hypotheses
hold, and every theorem stated about `Ttc.ttcParams` transfers verbatim through it
(proof irrelevance makes its right-hand side independent of *which* proofs are
supplied).
-/

/-- **A `Ttc.Params` at constant data** — the value `Ttc.ttcParamsTotal` falls back
on when the side conditions fail.

Every field is a stored scalar and every proof field is `le_refl` or `one_pos`, so
this is unconditionally a `Params`.  It asserts nothing: no lemma relates any of
its fields to a formula. -/
noncomputable def junkParams : Params where
  ε := 1
  δ := 1
  n := 1
  m := 1
  r := 1
  hε0 := one_pos
  hε1 := le_refl 1
  hn := le_refl 1
  hm := le_refl 1
  hr := le_refl 1

open scoped Classical in
/-- **The parameter block of `alg:ttc` lines 17–20, as a total function of the
data.**  On the branch where the five side conditions hold this is literally
`Ttc.ttcParams` (`Ttc.ttcParamsTotal_eq`, `Exec/Params`); on the other branch it is
`Ttc.junkParams`, about which nothing is claimed. -/
noncomputable def ttcParamsTotal (D : DNF A) (n : ℕ) (ε δ : ℝ) : Params :=
  if h : 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ n ∧ 1 ≤ Nat.card {c : Cube A // c ∈ D} ∧
      1 ≤ Nat.card (FacetIndex D) then
    ttcParams D n ε δ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  else junkParams

/-- **The block the run actually reads** — `Ttc.ttcParamsTotal` at the algorithm's
own inputs, `(toDNFd φ, n, ε, 4δ/5)`.

Its *data* never mentions `atoms`; the `atoms` binder is kept so that this is a
drop-in replacement for the proof-carrying `Ttc.inputParams` (`Exec/Dedup`) at the
call sites, and `Ttc.inputParamsTotal_eq_inputParams` (`Exec/Dedup`) is where the
two are identified. -/
noncomputable def inputParamsTotal {n : ℕ} (_atoms : A → LinAtom n) (φ : BForm A)
    (ε δ : ℝ) : Params :=
  ttcParamsTotal (toDNFd φ) n ε (4 * δ / 5)

end ParamBlock

/-! # The algorithm's output, lines A7–A13 completed

What is left of `alg:ttc` after the parameter block is the *rest of the
preprocessing* — the inscribed ball of lines A7–A9, the dilation factor of line
A10, the dilated atoms of line A11 — and then line A12's run and line A13's
division.  All of it is here, so that `Ttc.ttcAlgOutput` below is
`TTC(F, ε, δ)`'s output written in one term, at the algorithm's own inputs.

The four wrappers `Ttc.autoCen`, `Ttc.autoGamma`, `Ttc.runScale`, `Ttc.runPrec`
were in `Exec/Rescaled` and `Exec/Inputs`; they are definitions with no proof
content and they name no theorem, so they belong with the pseudocode they
transcribe.  Their two companions there, `Ttc.scaledAtoms` and `Ttc.runCount`,
stayed behind: they quantify over a free `(φ, γ̂)` that the algorithm does not
have, and the algorithm's own instances of them are `Ttc.algAtoms` and
`Ttc.algIndex` in the run section below. -/

section Algorithm

variable {A : Type*}

/-! ## Lines A7–A9: the ball `GetPrecision` computes -/

/-- **Lines A7–A8.**  The centre map `GetPrecision` produces: `Ttc.cenOf` over the
input's own cube list. -/
noncomputable def autoCen {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) :
    {c : Cube A // c ∈ toDNFd φ} → Space n :=
  cenOf (atomSet atoms) (toDNFd φ)

/-- **Line A9.**  The inscribed radius `γ̂` `GetPrecision` produces — the least of
the per-cube radii. -/
noncomputable def autoGamma {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) : ℝ :=
  gammaOf (atomSet atoms) (toDNFd φ)

section Wrappers

variable {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **Line A10.**  The dilation `q` the algorithm applies to its input, at the
parameter block the inputs determine.  `≥ 1` always (`Ttc.runScale_pos`,
`Exec/Rescaled`), and computable from `γ̂` and `n` alone — **no knowledge of
`Vol(F)`**. -/
noncomputable def runScale (gammaHat : ℝ) : ℝ :=
  scaleFactor n (inputParamsTotal atoms φ ε δ) gammaHat

/-- **`GetPrecision`'s output** (`alg:ttc` line 17): `ρ ← ⌈log₁₀(γ/γ̂)⌉`, computed
from the parameter block and the inscribed radius. -/
noncomputable def runPrec (gammaHat : ℝ) : ℤ :=
  (inputParamsTotal atoms φ ε δ).precision gammaHat

end Wrappers

/-! ## Lines A12–A13: the run, and the estimate brought back to scale -/

/-- **`TTC(F, ε, δ)`'s output**, as `alg:ttc` computes it: the fold of lines 22–46
(`Ttc.run`) over the preprocessed formula's cubes `Ttc.toDNFd (Ttc.preprocess atoms φ)`,
at the computed parameter block `Ttc.inputParamsTotal` (lines 17–20) and the computed
precision `Ttc.runPrec` (line 17, at the *dilated* radius `q·γ̂`), with the estimate
divided by `qⁿ` to bring it back to the original scale (line A13).

`O` is the **oracle bundle**: `alg:ttc` line 24's `Vol_ED` and line 43's
`GenerateSamples` are calls into it, exactly as the paper prints them.  Nothing
about `O` is assumed here — it is an argument.  `Ttc.ttcOracleBundle` (`Exec/Api`)
is the bundle the verified run reads, built from the Monte-Carlo volume estimator
and the constructed sampler, and `Ttc.ttcAlgOutput_eq_ttcEstimate` (`Exec/Api`,
by `rfl`) identifies this term at that bundle with the quantity the headline
bounds.

**No proof binder.**  The block is `Ttc.inputParamsTotal`, a function of
`(atoms, φ, ε, δ)` alone, so this term is a closed function of the algorithm's
*data* — nothing here is a proof and nothing here is assumed.  Wherever the
headline's hypotheses hold the block is the one `Ttc.inputParams` (`Exec/Dedup`)
builds (`Ttc.inputParamsTotal_eq_inputParams`, `Exec/Dedup`), so every theorem
about the latter transfers. -/
noncomputable def ttcAlgOutput {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (O : Oracles n (Cube A)) : ℝ :=
  run (inputParamsTotal atoms (preprocess atoms φ) ε δ) O
      (runPrec atoms (preprocess atoms φ) ε δ
        (runScale atoms (preprocess atoms φ) ε δ (autoGamma atoms (preprocess atoms φ))
          * autoGamma atoms (preprocess atoms φ)))
      (toDNFd (preprocess atoms φ))
    / (runScale atoms (preprocess atoms φ) ε δ (autoGamma atoms (preprocess atoms φ))) ^ n

end Algorithm

end Ttc

/-! # What `Vol_ED` **computes**, with no probability space of ours

This section holds the *data* half of the constructed volume oracle: the definitions
`Ttc.mcVol` unfolds to, and nothing else.  Every theorem about them — measurability,
unbiasedness, the Bernoulli variance, Chebyshev — stays in `Ttc/Volume/MonteCarlo.lean`,
which imports this file.

## Why the split exists

`Ttc.mcVol` is the number `alg:ttc` line 24 reads.  For `Ttc.run` to *call* it rather than
receive it as an oracle field, the definitions below must be reachable from
`Ttc/Model/Pseudocode.lean`, which is the audit surface.  They are, because they are
*here*: `Ttc/Audit/ClosureCheck.lean` requires the algorithm's output to be defined
entirely under `Ttc/Model/` or `Ttc/Probability/`, and the estimator is not
probability vocabulary, so the data half of it lives in `Model/` rather than in
`Volume/`.

## Data versus law: what had to move, and what did not

The obstruction was `Ttc.MonteCarlo.nSamp`, the sample count.  It is `⌈(ε²·p·q)⁻¹⌉ + 1`
where `q` is the hitting probability, and `q` used to be *defined* as
`(Ttc.MonteCarlo.coinLaw n (target K)).toReal` — a measure this development constructs
(`Arlib.uniformOn` on the unit ball).  Defining the sample count that way would have put
our own probability space inside the algorithm's definitional closure.

It does not have to be.  The hitting probability has a closed form in Lebesgue volume
alone — `Ttc.MonteCarlo.hitData` below — and the two agree exactly whenever `K` really is
enclosed by `Metric.ball 0 (rad K)`, which is `Ttc.MonteCarlo.hit_eq_hitData`
(`Volume/MonteCarlo.lean`), the hypothesis `Ttc.MonteCarlo.correct` establishes for itself.
So `nSamp` is defined from `hitData`, the coin law appears only in the *theorems*, and the
definitional closure of `Ttc.mcVol` contains **no measure constructed by this development**.

**What could not be separated, and is not claimed to be.**  `MeasureTheory.volume` — that
is, Mathlib's Lebesgue measure on `ℝⁿ` — stays in the closure, in three places, and each is
genuinely needed at definition time:

* `Ttc.MonteCarlo.scale`, the constant the returned estimate is multiplied by, is the volume
  of the enclosing ball;
* `Ttc.MonteCarlo.target` tests the coins against `MeasureTheory.toMeasurable volume K`
  rather than `K`, which is what makes `est_meas` hold for *every* `K`
  (see `Volume/MonteCarlo.lean`'s docstring);
* `Ttc.MonteCarlo.hitData` is a ratio of two Lebesgue volumes.

A volume estimator whose output does not mention volume would be a different object.  What
the split buys is precisely that the measure in the closure is *Mathlib's*, not one of ours
— which is the distinction `Ttc/Audit/ClosureCheck.lean` draws.

## Contents

`Ttc.roundBody`, and then, in `Ttc.MonteCarlo`: `rad`, `target`, `hitData`, `scale`,
`nSamp`, `ind`, `score`, `est`; finally `Ttc.mcVol`. -/

namespace Ttc

open MeasureTheory Pointwise

/-- **The normalisation `Vol_ED` is called on.** `K` moved so that its inscribed
ball becomes the unit ball at the origin: the image of `K` under
`y ↦ γ⁻¹ · (y − c)`.

Cousins–Vempala Theorem 1.1 (`Ttc.VolumeAlgorithm`, `Volume/Oracle`) speaks only about
bodies containing the unit ball, whereas `Ttc.TtcProb.ball_subset` supplies a ball
of radius `γ̂` about a centre that is not the origin. This is the change of
variable that closes the gap; that it does is *proved* in `Ttc/Volume/Bridge.lean`
(`Ttc.VolumeAlgorithm.of_ball`), not assumed.

Lives here rather than in `Model/Prelude` because it is this oracle's
normalisation, not vocabulary of the paper's problem — and here rather than in
`Volume/Oracle` because `Ttc.mcVol` is built from it and this file is the audit
surface. -/
noncomputable def roundBody {n : ℕ} (c : Space n) (γ : ℝ) (K : Set (Space n)) :
    Set (Space n) := γ⁻¹ • ((-c) +ᵥ K)

end Ttc

namespace Ttc.MonteCarlo

open MeasureTheory

variable {n : ℕ}

/-! ## The enclosing radius

`Ttc.MonteCarlo.correct` hands over exactly three facts about `K` — convex, contains the
unit ball, finite volume — and `Arlib.Convexity.exists_closedBall_superset_of_convex` turns
them into a radius (`Ttc.MonteCarlo.exists_ball_superset`).  `rad` takes the *least* such
radius, plus one, totally: it is defined (as `1`) even when no radius exists, so that `est`
is a total function and `est_meas` needs no hypothesis. -/

open scoped Classical in
/-- **The least enclosing radius, plus one**; `1` if no radius exists.

`sInf` rather than `Exists.choose`: the infimum of the valid radii is a *canonical* choice,
so an **upper** bound is derivable — `Ttc.MonteCarlo.rad_le_of_subset_closedBall` in
`Ttc/Volume/RadBound.lean` turns any explicit enclosing closed ball into a bound on `rad`,
which is what makes the sample count's closed form unconditional.  With `Exists.choose` no
such inequality is provable: `Exists.choose_spec` gives only `0 < ·` and `K ⊆ ball 0 ·`,
both lower-bound facts, and the satisfying set is upward closed.

The `+ 1` is load-bearing.  `sInf` of the valid radii need not itself be valid — take `K` a
closed ball, whose infimum of *open*-ball radii is its own radius — so the `+ 1` reopens the
ball and keeps `Ttc.MonteCarlo.subset_ball_rad`.  The definition stays total: it is `1` when
no radius exists, so `est` is a total function and `est_meas` needs no hypothesis. -/
noncomputable def rad (K : Set (Space n)) : ℝ :=
  if ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R
  then sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} + 1 else 1

/-! ## The target set

`target K` is the set the *coins* are tested against: the measurable hull of `K`, pulled
back along `x ↦ rad K • x`.  It is measurable for **every** `K`
(`Ttc.MonteCarlo.measurableSet_target`), which is what makes
`Ttc.VolumeAlgorithm.est_meas` — quantified over all `K`, measurable or not — provable. -/

/-- The measurable hull of `K`, in unit-ball coordinates. -/
noncomputable def target (K : Set (Space n)) : Set (Space n) :=
  (fun x : Space n => rad K • x) ⁻¹' toMeasurable volume K

/-! ## The estimator -/

/-- **The hitting probability, as arithmetic**: `Vol K / Vol(ball 0 (rad K))`, written out
in Lebesgue volume alone.

This is the *data* form of the chance that one rescaled coin lands in `K`.  The *law* form
is `Ttc.MonteCarlo.hit`, `(coinLaw n (target K)).toReal`, and the two are equal exactly
when `K ⊆ Metric.ball 0 (rad K)` — `Ttc.MonteCarlo.hit_eq_hitData`, proved in
`Volume/MonteCarlo.lean`, where the enclosure hypothesis is available.

Only this form is used to *define* the sample count, so that the coin law stays out of the
algorithm's definitional closure; see this section's docstring. -/
noncomputable def hitData (K : Set (Space n)) : ℝ :=
  (rad K ^ n)⁻¹ * (volume K).toReal / (volume (Metric.ball (0 : Space n) 1)).toReal

/-- The volume of the enclosing ball, `Vol(ball 0 (rad K)) = (rad K)ⁿ · Vol(ball 0 1)`. -/
noncomputable def scale (K : Set (Space n)) : ℝ :=
  rad K ^ n * (volume (Metric.ball (0 : Space n) 1)).toReal

/-- The number of samples: `⌈(ε²·p·q)⁻¹⌉ + 1`, where `q = Ttc.MonteCarlo.hitData K` is the
hitting probability in its arithmetic form.  Noncomputable, and `Θ(Rⁿ/(ε²p))` — exponential
in `n`.  See the module docstring of `Ttc/Volume/MonteCarlo.lean`. -/
noncomputable def nSamp (K : Set (Space n)) (ε pf : ℝ) : ℕ :=
  ⌈(ε ^ 2 * pf * hitData K)⁻¹⌉₊ + 1

/-- The indicator of `target K`, as a function of one coin. -/
noncomputable def ind (K : Set (Space n)) : Space n → ℝ :=
  Set.indicator (target K) (1 : Space n → ℝ)

/-- The `i`-th sample's score: `1` if the `i`-th rescaled coin lands in `K`, else `0`. -/
noncomputable def score (K : Set (Space n)) (i : ℕ) : (ℕ → Space n) → ℝ :=
  fun ω => ind K (ω i)

/-- **The estimate.** `Vol(ball 0 (rad K)) · (#hits / N)`. -/
noncomputable def est (K : Set (Space n)) (ε pf : ℝ) (ω : ℕ → Space n) : ℝ :=
  scale K / (nSamp K ε pf : ℝ) * ∑ i ∈ Finset.range (nSamp K ε pf), score K i ω

end Ttc.MonteCarlo

namespace Ttc

open scoped Classical in
/-- **`Vol_ED`'s output, as a function of the volume oracle's coins.**

`Ttc.ttc_volume` carries `vol : Cube A → ℝ` together with a binder `volED_eq`
pinning it to `volAlg.est`.  With `volAlg` fixed to the *constructed* oracle
`Ttc.VolumeAlgorithm.monteCarlo`, `vol` is no longer a free function: it is this
term, and `volED_eq` becomes the theorem `Ttc.mcVol_eq` (`Exec/VolDischarge`).

Off the DNF the value is `0`; the algorithm never reads it (only `i ∈ D` is ever
queried), and totality is what lets the definition avoid a proof argument.

Defined here rather than in `Exec/VolDischarge` so that it lies inside the audit
surface `Ttc/Audit/ClosureCheck.lean` checks. -/
noncomputable def mcVol {A : Type*} {n : ℕ} (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ)
    (c : ℕ → Space n) (i : Cube A) : ℝ :=
  if hi : i ∈ D then
    γ ^ n * MonteCarlo.est (roundBody (cen ⟨i, hi⟩) γ (region M i)) ε' δ' c
  else 0

end Ttc

/-! # `TTC(F, ε, δ)` on one run, with no oracle argument

`Ttc.ttcAlgOutput` above takes the oracle bundle `O : Ttc.Oracles n (Cube A)` as an
argument, because `alg:ttc` line 24's `Vol_ED` and line 43's `GenerateSamples` are
printed as external calls.  `Ttc.ttcRun` below is the same algorithm with that
argument **filled in** by the data the run itself supplies: the volume coins `c` and
the sample trajectory `t`.  It takes no oracle, so the headline
(`Model/Theorem`) does not have to name one.

`Ttc.ttcRun_eq_ttcAlgOutput` (`Exec/Api`) is the proof — by `rfl` — that this is the
same number as `Ttc.ttcAlgOutput … (Ttc.ttcOracleBundle … c t)`.  Without that lemma
this definition would be a rename; with it, it is the *same term*, and the bundle is
a fact about the proof rather than a name in the statement.

## What had to come here for that to be possible

Everything the bundle is built from, since the whole point is that
`Ttc/Audit/ClosureCheck.lean`'s `#modelClosure Ttc.ttcRun` passes — every `Ttc`
constant `Ttc.ttcRun` unfolds to is defined under `Ttc/Model/` or
`Ttc/Probability/`.  Three groups moved into this file for that reason, each keeping
its name and its proof:

* the five trajectory read-offs and the two oracle **contracts** about them
  (`Ttc.trajThin_le`, `Ttc.card_trajGen`), formerly `Coupling/Family` — the bundle's
  `thin_le` and `gen_card` fields are exactly those two.  All seven have since gone
  on to `Probability/Trajectory`, beside the trajectory law they read off, which is
  inside the audit surface just as this file is; the count-vector dictionary they
  are proved from went to `ModelSupport`, where it is stated without mentioning
  `Ttc.toMultiset`;
* the **coverage test** (`Ttc.coverOfRegion`, `Ttc.memPtOfRegion`), formerly
  `Exec/Coverage` — `alg:ttc` line 27's membership query, classically;
* the **lattice enumeration** (`Ttc.HasLatticeEnum`, `Ttc.exists_latticeEnum`,
  `Ttc.latticeEnum` and its unconditional injectivity), formerly `Exec/Endgoal` —
  line 43's `GenerateSamples` draws from `Sol(F) ∩ 𝕃ⁿ`, so the enumeration of that
  set is part of the algorithm, not of its analysis, and `Ttc.latticeEnum` is
  `choose`n from `Ttc.exists_latticeEnum`, which is why that theorem had to come too
  — and, being reached through a `def`'s body, is the one theorem here that
  `#modelClosure` actually sees.  Its two *guarded* properties
  (`Ttc.latticeEnum_mem`, `Ttc.latticeEnum_onto`) did not: nothing here needs them,
  and they are back in `Exec/Endgoal` with the *geometric* input — that boundedness
  of `Sol(F)` makes the intersection finite — which `Exec/Geometry` supplies and
  which is not needed to *define* the enumeration.

Nothing here asserts anything about the bundle: `Ttc.ttcRun`'s body is a closed term
and every proof it contains is discharged in this file. -/

namespace Ttc

open MeasureTheory Set

/-! ## Line 27: the coverage test

`alg:ttc` line 27 asks `s ∈ P(cᵢ)`.  These are that query as a `Bool`, classically,
and its reindexing along an enumeration of the lattice points.  Noncomputable — a
*specification* of the test, not an implementation; `Ttc.coverOfRegion_eq_true`
(`Exec/Coverage`) is the only thing the development ever asks of it. -/

/-- **The coverage test, classically.**  `alg:ttc` line 27's membership query
`s ∈ P(cᵢ)`, as a `Bool`, via `Classical.propDecidable`. -/
noncomputable def coverOfRegion {A X : Type*} (M : A → Set X) (x : X) (c : Cube A) : Bool :=
  @decide (x ∈ region M c) (Classical.propDecidable _)

/-- **The per-lattice-point form of the coverage test** — the test indexed by the
enumeration rather than by the point, by definition, so
`Ttc.coverOfRegion_memPtOfRegion` (`Exec/Coverage`) is `rfl`. -/
noncomputable def memPtOfRegion {A : Type*} {n L : ℕ} (M : A → Set (Space n))
    (ptE : Fin L → Space n) (c : Cube A) (s : Fin L) : Bool :=
  coverOfRegion M (ptE s) c

/-! ## Line 43: the enumeration of `Sol(F) ∩ 𝕃ⁿ`

`GenerateSamples` draws lattice points of a cube, so the algorithm needs an
enumeration of `Sol(F) ∩ 𝕃ⁿ` indexed by `Fin |Sol(F) ∩ 𝕃ⁿ|` — the paper's `Fin N`.
`Ttc.latticeEnum` is that enumeration as a **total function of `(M, φ, ρ)` alone**:
no proof argument, so the algorithm's output does not mention a boundedness proof
through it.

It is **unconditionally injective**, which is what the `thin` contract needs, and that
is all of it this file proves.  The two substantive properties (every enumerated point
is a solution lattice point, and every solution lattice point is enumerated) are
guarded by `Ttc.HasLatticeEnum` and are read off `Ttc.exists_latticeEnum`'s
`choose_spec` in `Exec/Endgoal` (`Ttc.latticeEnum_mem`, `Ttc.latticeEnum_onto`), where
`Ttc.hasLatticeEnum_of_isBounded` also supplies the guard from boundedness of `Sol(F)`.
When no enumeration exists the intersection is infinite, `Set.ncard` of an infinite set
is `0`, and `Fin 0` is empty — which is why injectivity is free.

That the guard follows from *finiteness* is `Ttc.exists_finEnum_of_finite`
(`ModelSupport`): pure `Nat.card` bookkeeping, mentioning neither
`Ttc.HasLatticeEnum` nor `Ttc.latticeCount`, since the latter is by definition the
`Set.ncard` the enumeration is indexed by.  The *geometric* fact that boundedness of
`Sol(F)` gives finiteness is `Ttc.exists_lattice_enum_of_isBounded`
(`Exec/Geometry`) and is not needed here. -/

variable {A : Type*} {n : ℕ}

/-- What an enumeration of `Sol(F) ∩ 𝕃ⁿ` is: a bijective listing by `Fin N`, at the
paper's own `N = |Sol(F) ∩ 𝕃ⁿ|` (`Ttc.latticeCount`). -/
def HasLatticeEnum (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) : Prop :=
  ∃ ptE : Fin (latticeCount M φ ρ) → Space n, Function.Injective ptE ∧
    (∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)) ∧
    (∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x)

/-- The total version: an enumeration exists *unconditionally*, injective always, and
with the two membership properties whenever `Ttc.HasLatticeEnum` holds.  This is what
`Ttc.latticeEnum` is `choose`n from, so it is part of the algorithm; the two membership
properties read off its `choose_spec` (`Ttc.latticeEnum_mem`, `Ttc.latticeEnum_onto`)
are not, and live in `Exec/Endgoal`. -/
theorem exists_latticeEnum (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) :
    ∃ ptE : Fin (latticeCount M φ ρ) → Space n, Function.Injective ptE ∧
      (HasLatticeEnum M φ ρ →
        (∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)) ∧
        (∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x)) := by
  by_cases h : HasLatticeEnum M φ ρ
  · obtain ⟨ptE, hinj, hmem, honto⟩ := h
    exact ⟨ptE, hinj, fun _ => ⟨hmem, honto⟩⟩
  · have hinf : (sol M φ ∩ fineLattice n (latticeScale ρ)).Infinite := by
      intro hfin
      exact h (exists_finEnum_of_finite hfin)
    have hzero : latticeCount M φ ρ = 0 := hinf.ncard
    haveI hempty : IsEmpty (Fin (latticeCount M φ ρ)) := by
      rw [hzero]; infer_instance
    refine ⟨fun s => isEmptyElim s, ?_, fun h' => absurd h' h⟩
    intro a _ _
    exact isEmptyElim a

/-- **The enumeration of `Sol(F) ∩ 𝕃ⁿ`, as a function of the inputs alone.**
Its index type is `Fin (latticeCount M φ ρ)`, i.e. the paper's `Fin N`. -/
noncomputable def latticeEnum (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) :
    Fin (latticeCount M φ ρ) → Space n :=
  (exists_latticeEnum M φ ρ).choose

/-- `ptE_inj`, unconditionally. -/
theorem latticeEnum_injective (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) :
    Function.Injective (latticeEnum M φ ρ) :=
  (exists_latticeEnum M φ ρ).choose_spec.1

/-! ## Line 20: the level-`0` rates `θ`

`alg:ttc` line 20 sets, for each enumerated lattice point `s`, the rate
`θ(s) = sampD(c, s) · Vol_ED(P(c))` where `c` is the cube `s` is assigned to.  The
assignment is `Ttc.cubeAt`: a *total* function of `s`, so the rates are a closed term.
`Ttc.cubeOf_spec` (`Sampler/Rates`) — the only thing ever asked of it — says it is a
cube of the decomposition containing the point, whenever one exists. -/

/-- The choice principle behind `Ttc.cubeOf`: a *total* function of `x` that lands
in the decomposition and covers `x` whenever anything in the decomposition does. -/
private theorem exists_cubeOf (M : A → Set (Space n)) (D : DNF A) (x : Space n) :
    ∃ c : Cube A, (∃ c' : Cube A, c' ∈ D ∧ x ∈ region M c') → (c ∈ D ∧ x ∈ region M c) := by
  by_cases h : ∃ c' : Cube A, c' ∈ D ∧ x ∈ region M c'
  · exact ⟨h.choose, fun _ => h.choose_spec⟩
  · exact ⟨[], fun h' => absurd h' h⟩

/-- **A cube of `D` containing `x`.**  Total in `x` — no proof argument — so that
the rates built from it are a closed term; `Ttc.cubeOf_spec` is the only thing ever
asked of it. -/
noncomputable def cubeOf (M : A → Set (Space n)) (D : DNF A) (x : Space n) : Cube A :=
  (exists_cubeOf M D x).choose

/-- `Ttc.cubeOf` is a cube of `D` containing `x`, whenever there is one. -/
theorem cubeOf_spec {M : A → Set (Space n)} {D : DNF A} {x : Space n}
    (h : ∃ c' : Cube A, c' ∈ D ∧ x ∈ region M c') :
    cubeOf M D x ∈ D ∧ x ∈ region M (cubeOf M D x) :=
  (exists_cubeOf M D x).choose_spec h

/-- **The cube the enumerated point `s` is assigned to.** -/
noncomputable def cubeAt (M : A → Set (Space n)) (φ : BForm A) (D : DNF A) (ρ : ℤ)
    (s : Fin (latticeCount M φ ρ)) : Cube A :=
  cubeOf M D (latticeEnum M φ ρ s)

/-- **The level-`0` rates of `alg:ttc` line 20.**  The sampler's mass at the
enumerated point, in the cube it was assigned to, times that cube's volume
estimate. -/
noncomputable def rates (M : A → Set (Space n)) (φ : BForm A) (D : DNF A) (ρ : ℤ)
    (sampD : Cube A → Space n → ℝ) (vol : Cube A → ℝ) :
    Fin (latticeCount M φ ρ) → ℝ :=
  fun s => sampD (cubeAt M φ D ρ s) (latticeEnum M φ ρ s) * vol (cubeAt M φ D ρ s)

/-! ## The run's own data, and `TTC(F, ε, δ)` on one run

Nine abbreviations, each a plain function of the algorithm's inputs, spelling out
what lines A10–A13 and lines 17–20 compute; then `Ttc.ttcRun`, which is
`Ttc.ttcAlgOutput` at the bundle those nine determine.

Nothing here is a proof binder: the parameter block is `Ttc.inputParamsTotal`, a
total function of the data, so all nine — and `Ttc.ttcRun` itself — are closed
functions of `(atoms, φ, ε, δ)` and the two coin sequences.

The dilated atoms carry no second boundedness proof: `Ttc.inputParams_scaleAtoms`
(`Exec/Rescaled`) holds by `rfl`, so the parameter block — and therefore the
precision — may be read at the *original* atoms. -/

section Run

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The parameter block** `alg:ttc` lines 17–20 computes, at the preprocessed
formula: `Ttc.inputParamsTotal` at `Ttc.preprocess atoms φ`. -/
noncomputable def algBlock : Params :=
  inputParamsTotal atoms (preprocess atoms φ) ε δ

/-- **Line A10.**  The dilation `q` the algorithm applies to its input. -/
noncomputable def algScale : ℝ :=
  runScale atoms (preprocess atoms φ) ε δ (autoGamma atoms (preprocess atoms φ))

/-- **Line A11.**  The dilated atoms: same normals, bounds scaled by `Ttc.algScale`. -/
noncomputable def algAtoms : A → LinAtom n :=
  scaleAtoms (algScale atoms φ ε δ) atoms

/-- **Lines A9 + A11.**  The inscribed radius after the dilation, `q · γ̂`. -/
noncomputable def algGamma : ℝ :=
  algScale atoms φ ε δ * autoGamma atoms (preprocess atoms φ)

/-- **`GetPrecision`'s output `ρ`** (line 17), at the dilated radius. -/
noncomputable def algPrec : ℤ :=
  runPrec atoms (preprocess atoms φ) ε δ (algGamma atoms φ ε δ)

/-- **`N = |Sol(F) ∩ 𝕃ⁿ|`** at that precision, for the dilated input — the index the
run's sample coins range over. -/
noncomputable def algIndex : ℕ :=
  latticeCount (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
    (algPrec atoms φ ε δ)

/-- **The enumeration `GenerateSamples` draws from** — `Ttc.latticeEnum` at the
dilated input and the computed precision. -/
noncomputable def algEnum : Fin (algIndex atoms φ ε δ) → Space n :=
  latticeEnum (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
    (algPrec atoms φ ε δ)

/-- **Lines A7–A8 + A11.**  The inscribed-ball centres, moved by the dilation. -/
noncomputable def algCen : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Space n :=
  fun i => algScale atoms φ ε δ • autoCen atoms (preprocess atoms φ) i

/-- **Line 27's membership table**: the coverage test at each enumerated point. -/
noncomputable def algMem : Cube A → Fin (algIndex atoms φ ε δ) → Bool :=
  memPtOfRegion (atomSet (algAtoms atoms φ ε δ)) (algEnum atoms φ ε δ)

/-- **`TTC(F, ε, δ)`'s output on one run `(c, t)`, with no oracle argument.**

`Ttc.ttcAlgOutput` at the bundle the run itself supplies: `Vol_ED` (line 24) is the
Monte-Carlo estimator `Ttc.mcVol` at the volume coins `c`, and lines 33/38/40/41/43's
`thin`, `Pois` and `GenerateSamples` are the read-offs `Ttc.trajThin`,
`Ttc.trajPois`, `Ttc.trajGen` of the sample trajectory `t`, padded by
`Ttc.padRow` — all five in `Probability/Trajectory`.  The bundle's two proof fields
are `Ttc.trajThin_le` at `Ttc.latticeEnum_injective` and `Ttc.card_trajGen`; the two
contracts are proved beside the read-offs they are about, and
`Ttc.latticeEnum_injective` above.

Nothing is assumed, and nothing is a proof: this is a closed term in
`(atoms, φ, ε, δ, c, t)`.  `Ttc.ttcRun_eq_ttcAlgOutput` (`Exec/Api`) proves that it
is `Ttc.ttcAlgOutput … (Ttc.ttcOracleBundle … c t)`, so this is not a second
description of the algorithm but the same term with its oracle argument filled
in. -/
noncomputable def algOracles (c : ℕ → Space n)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) : Oracles n (Cube A) where
  vol := mcVol (atomSet (algAtoms atoms φ ε δ))
    (toDNFd (preprocess atoms φ)) (algCen atoms φ ε δ)
    (algGamma atoms φ ε δ)
    (algBlock atoms φ ε δ).epsPrime
    (algBlock atoms φ ε δ).deltaPrime c
  covered := coverOfRegion (atomSet (algAtoms atoms φ ε δ))
  thin := fun _j₀ j' X => trajThin (algEnum atoms φ ε δ) (t j') X
  thin_le := fun _j₀ j' X => trajThin_le (latticeEnum_injective _ _ _) (t j') X
  pois := fun i j _lam => trajPois (algMem atoms φ ε δ i) (t j)
  gen := fun i j N _ρ =>
    trajGen (algEnum atoms φ ε δ) (algMem atoms φ ε δ i) (t j) N
      (padRow (algEnum atoms φ ε δ) (algMem atoms φ ε δ i))
  gen_card := fun i j N _ρ =>
    card_trajGen (algEnum atoms φ ε δ) (algMem atoms φ ε δ i) (t j) N
      (padRow (algEnum atoms φ ε δ) (algMem atoms φ ε δ i))

/-- **`TTC(F, ε, δ)`'s output on one run `(c, t)`, with no oracle argument.** -/
noncomputable def ttcRun (c : ℕ → Space n)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) : ℝ :=
  ttcAlgOutput atoms φ ε δ (algOracles atoms φ ε δ c t)

/-- **Line 20's rate vector `θ`, on the volume coins `c`** — the sampler's mass at
each enumerated lattice point (`Ttc.e2eSampD` at the run's own geometry) times that
point's cube's volume estimate (`Ttc.mcVol` at `c`).  `Ttc.trajLaw` of this is the
law the sample coins `t` are drawn from. -/
noncomputable def algRates (c : ℕ → Space n) : Fin (algIndex atoms φ ε δ) → ℝ :=
  rates (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
    (toDNFd (preprocess atoms φ)) (algPrec atoms φ ε δ)
    (e2eSampD (atomSet (algAtoms atoms φ ε δ)) (toDNFd (preprocess atoms φ))
      (algPrec atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (canonRfac (toDNFd (preprocess atoms φ)))
      (Jt := Fin (Nat.card (FacetIndex (toDNFd (preprocess atoms φ)))))
      (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)))
      (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
        (latticeScale (algPrec atoms φ ε δ)))
      (algCen atoms φ ε δ) (algGamma atoms φ ε δ)
      (canonDm (atomSet (algAtoms atoms φ ε δ)) (toDNFd (preprocess atoms φ))
        (algPrec atoms φ ε δ)))
    (mcVol (atomSet (algAtoms atoms φ ε δ)) (toDNFd (preprocess atoms φ))
      (algCen atoms φ ε δ) (algGamma atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (algBlock atoms φ ε δ).deltaPrime c)

/-- **The charged cost of the run `(c, t)`** — `Ttc.runCost` folded over the
preprocessed formula's cube list, at the per-call charges `cVol` (one `Vol_ED` call)
and `cSample` (one generated sample). -/
noncomputable def algCost (c : ℕ → Space n)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) (cVol cSample : ℕ) : ℕ :=
  runCost (algBlock atoms φ ε δ) (algOracles atoms φ ε δ c t) cVol cSample
    (algPrec atoms φ ε δ) (toDNFd (preprocess atoms φ))

/-! ## `TTC(F, ε, δ)` as one program: the law of `(estimate, cost)`

`Ttc.ttc` is the whole algorithm, as a single measure on the pair
`(estimate, cost)` — the `Measure` analogue of nfalean's
`ApproxNFA.countNFAM : PMF (ℝ × ℕ)`.  It is a two-line monadic program:

```
c ← MonteCarlo.coins n                      -- the volume oracle's coins
t ← trajLaw (algRates … c)                  -- the sample trajectory at those rates
return (ttcRun … c t, algCost … c t)        -- the estimate and what it cost
```

written with `MeasureTheory.Measure.bind` and `MeasureTheory.Measure.map`, neither of
which carries a measurability obligation: the definition is total and proof-free, and
every measurability fact it needs to *behave* like the display above is proved
downstream (`Ttc.ttc_eq_ttcPairLaw`, `Monadic/Program`).

Returning the pair is what makes both halves of `Ttc.ttc_volume_estimate` — accuracy
and running time — statements about *the same run*. -/
noncomputable def ttc (cVol cSample : ℕ) : MeasureTheory.Measure (ℝ × ℕ) :=
  (MonteCarlo.coins n).bind fun c =>
    (trajLaw (algRates atoms φ ε δ c)).map fun t =>
      (ttcRun atoms φ ε δ c t, algCost atoms φ ε δ c t cVol cSample)

end Run

end Ttc

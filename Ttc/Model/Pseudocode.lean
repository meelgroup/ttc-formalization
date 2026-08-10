/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Dnf
import Ttc.Lattice.Decomposition
import Ttc.Model.ProblemSetting

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

This file **is not proof-free**, and it used to claim it was. It carries about a
dozen tactic proofs, and they are of exactly two kinds — no others:

1. **What a `Ttc.Params` cannot be built without.** `Ttc.Params` bundles five
   *proof* fields (`hε0 hε1 hn hm hr`), so the parameter block of lines 17–20
   cannot be *written down* without proofs that the decomposition has a cube
   (`hm`) and a facet (`hr`). The algorithm's own preprocessing supplies both, so
   the lemmas that supply them have to live where the block is built — here:
   `Ttc.instFiniteCubeMem`, `Ttc.instFiniteFacetIndex`, `Ttc.one_le_card_cubes`,
   `Ttc.one_le_card_facets`, `Ttc.region_nil`, `Ttc.not_isBounded_univ_space`,
   `Ttc.exists_lit_of_isBounded`, `Ttc.one_le_card_cubes_of_ne_nil`,
   `Ttc.one_le_card_facets_of_isBounded`. Likewise `Ttc.dnfForm_isPositive` and
   `Ttc.preprocess_isPositive`, which supply `Ttc.inputParams`' `hφ` for the
   formula the algorithm is handed, together with `Ttc.junkParams`,
   `Ttc.ttcParamsTotal` and `Ttc.inputParamsTotal`, which are what let the *run*
   read that block while carrying none of those proofs.
2. **The basic properties of this file's own converter** `Ttc.toDNFd` (line A1),
   which `Ttc.inputParams` instantiates the two facts above *at*:
   `Ttc.mem_toDNFd`, `Ttc.exists_mem_toDNF`, `Ttc.toDNFd_isDNFOf`,
   `Ttc.toDNFd_ne_nil`. They cannot sit in `Exec/Dedup`, which imports this file.

Nothing else. No geometry, no measure theory, no probability, and nothing about
what the algorithm *achieves* — the two tables below say where each of those
lives. A referee reading `Model/` for the *statement* may skip every proof here;
none of them is load-bearing for what the theorem says, only for what can be
written down.

## The algorithm carries no proof binder

The reference for this layout is
`nfalean/ApproxNFA/Model/`, whose theorem is stated about `countNFAExec A n ε δ` —
the algorithm applied to its **inputs alone**. This file now does the same:
`Ttc.ttcAlgOutput atoms φ ε δ O` and `Ttc.ttcRun atoms φ ε δ c t` take no proof,
and neither do `Ttc.runScale`, `Ttc.runPrec`, `Ttc.runCount`, or the nine
read-offs `Ttc.algBlock … Ttc.algMem` of the run section.

`Ttc.Params` still bundles five proof fields alongside its five data fields, so
`Ttc.ttcParams` and `Ttc.inputParams` still cannot be *written down* without
proofs. What removes them from the algorithm is not an unbundling but a
totalisation: all five side conditions (`0 < ε`, `ε ≤ 1`, `1 ≤ n`, `1 ≤ m`,
`1 ≤ r`) are propositions about the *data*, so `Ttc.ttcParamsTotal` and
`Ttc.inputParamsTotal` **decide** them classically and fall back on
`Ttc.junkParams` when they fail. The run reads the total block, and
`Ttc.ttcParamsTotal_eq` / `Ttc.inputParamsTotal_eq_inputParams` say that wherever
the headline's hypotheses hold it *is* the block `Ttc.inputParams` builds — so
every theorem stated about the latter transfers verbatim, by proof irrelevance,
and nothing about the junk branch is claimed.

The visible gain is that `Ttc.ttc_volume_estimate`'s type names no proof term:
`Ttc.preprocess_bdd` (`Exec/Api`) used to appear in it and no longer does. The
boundedness fact is still *proved*, and still spent — inside proofs, such as
`Ttc.ttcBlock_eq` (`Exec/Api`) and `Ttc.inputParamsTotal_preprocess`
(`Exec/BddPrep`) — but the statement no longer mentions it.

**This file imports no `Exec/` file.** `Ttc.toDNFd`, the deduplicated line-16
converter that `Ttc.pruneForm` and `Ttc.cleanForm` are defined over, used to live
in `Exec/Dedup`; it is defined *here* now (line A1 below), a two-line wrapper on
`Ttc.toDNF` of `Model/Prelude`. Its theorems (`Ttc.mem_toDNFd`,
`Ttc.toDNFd_nodup`, `Ttc.toDNFd_isDNFOf`, `Ttc.length_toDNFd_le_card`, …) stay in
`Exec/Dedup`, which now imports this file — the edge runs `Model/ → Exec/`, never
back. The two imports here are `Ttc.Dnf` (for `Ttc.conj`, which `Ttc.cubeForm`
folds, and `Ttc.toDNF_isDNFOf`) and `Ttc.Lattice.Decomposition` (for
`Ttc.region_subset_sol`, which the parameter block's `hr` needs); `Ttc.Dnf` and
`Ttc.Lattice.Decomposition` both depend on nothing but Mathlib and
`Model/Prelude`.

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
| 46 (output) | `Ttc.run`, and `Ttc.ttcOutput` as a random variable |

**The four external calls are fields of `Ttc.Oracles`**, so the state evolution is
deterministic given their answers — all the randomness sits at that boundary,
which is where `lem:numlattice` lives.

## Four deviations from `algo.tex`

These are the places where the Lean development does not say quite what the paper
says. They are recorded here, because this is the file a reader consults to check
the modelling.

**(a) The `while` loops are exit levels, not iterations.** Neither loop is written
as a recursion. `Ttc.haltLevel` and `Ttc.absorbLevel` are the **least level at or
above the current one at which the loop's guard fails**, an `sInf` over `ℕ`, and
the step jumps straight there. This is what the loops compute when they terminate,
and it needs no termination proof — which matters, because the second loop has
none to give: it exits when repeated thinning brings `Nᵢ + |𝒳|` under `Thresh`,
which happens only with high probability. A fuelled recursion would have been the
alternative, and it forces an iteration budget into the statement of the main
theorem; this does not.

**(b) An empty exit set exits immediately.** When no level satisfies the exit
condition — the run where the algorithm loops forever — the set that
`Ttc.absorbLevel` takes an `sInf` over is empty, `Nat.sInf` returns `0` by
convention, and the `max` with the entry level degenerates to "stay put". Nothing
depends on this corner: every consequence drawn from an exit level is of the form
"every level strictly below it had the guard true" (`Ttc.lt_haltLevel`,
`Ttc.lt_absorbLevel`), which is vacuously true when the loop does not move.

**(c) The thinning is a read-off at a level, not a repeated coin.**
`Ttc.Oracles.thin j₀ j' X` is the sub-multiset of `X` that survives down to level
`j'`, having entered the step at level `j₀` — one call, not `j' − j₀` of them. This
is what lets the loops be exit levels: the guard at a candidate level `j'` can be
evaluated without running the loop to get there. The only law assumed of it is
`Ttc.Oracles.thin_le`: thinning **removes** copies, never invents them. Note that
`thin j₀ j₀` is a no-op on the states the run reaches, but is not assumed to be the
identity outright — the concrete family in `Coupling/Family` realises it as a cap
against the level-`j₀` counts, which is the identity exactly there.

**(d) The randomised calls are told the cube and the level.** `pois` takes `(i, j)`
and `gen` takes `(i, j)`, where `algo.tex:38,41,43` pass neither. The index is what
names the draw: two calls with different `(i, j)` are different draws, which is
what a distributional hypothesis needs in order to speak of independence. The level
in particular is needed because `lem:numlattice`'s `Err(j)` must be an event about a
level-`j` process coupled to the run, and a level-blind sampler cannot realise that
coupling — see README finding 15 and `AUDIT.md`.

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
| A11 (dilate) | `Ttc.scaleAtoms`, `Ttc.scaledAtoms` | here |
| (line 17, `ρ`) | `Ttc.runPrec` | here |
| (the coins' index) | `Ttc.runCount` | here |
| A12 (the run) | `Ttc.run` / `Ttc.ttcOutput`, above | here |
| A13 (`/qⁿ`) | the division in `Ttc.ttcAlgOutput` | here |
| A12–A13 as one term | `Ttc.ttcAlgOutput` | here |

## Which of the four are in the paper

**Steps 1, 3 and 4 are not in the paper's `alg:ttc`.** Step 2 is not printed there
either, but unlike the other three it is not a change to the algorithm: it rewrites
the input syntax and leaves the body alone.

* **Step 1, the pruning (A2–A3), is not in `alg:ttc`.** It changes `Sol(F)` — by a
  **null set only**: the deleted cubes have convex regions with empty interior, so
  `Ttc.sol_pruneForm_subset` is a genuine `⊆` and may in general be *strict* (an
  isolated lower-dimensional piece sitting beside the surviving union is dropped),
  while the **measure** is preserved exactly (`Ttc.volSol_pruneForm`). The soundness
  of the substitution rests on that volume equality, not on any claim about the set,
  and it is legitimate solely because the headline's conclusion merely **measures**
  `Ttc.sol`. (`Ttc.degForm` is *not* an example of the strictness — its `thinCube`
  region is the point `0` inside `fatCube`'s `[−1,1]`, so pruning leaves `Sol`
  unchanged there. It is the witness for something else: that pruning destroys
  `Ttc.IsDNFOf`, `Ttc.not_isDNFOf_nondegenCubes_degForm`, because `IsDNFOf` is a
  statement about Boolean valuations rather than about the solution set.)
* **Step 2, the cleaning (A4–A6), does not change what the algorithm does.**
  `Ttc.sol_cleanForm` is an **exact set equality**: a literal `0·x ≤ b` with
  `0 ≤ b` denotes `Set.univ` and a cube containing one with `b < 0` denotes `∅`, so
  deleting them is constant folding. Not printed in `alg:ttc`, but nothing is lost
  or gained.
* **Step 3, the ball construction (A7–A9), is not `alg:ttc`.** `alg:prec` line 86
  computes the *maximum* inscribed ball by an LP; `Ttc.ballData` picks *some*
  inscribed ball, classically. Non-maximality only inflates the precision
  `ρ = ⌈log₁₀(γ/γ̂)⌉`, so the guarantee is untouched and only the run gets more
  expensive.
* **Step 4, the dilation (A10–A13), is not in `alg:ttc` and changes what the
  algorithm does.** `alg:ttc` sets `p ← 1` and only ever halves it, so its sketch is
  `Poisson(Λ)` with `Λ ≤ Vol(Sol F)`; on a body of volume `10⁻⁶` it draws
  `Pois(10⁻⁶)` points and returns `0`. **The printed algorithm is wrong there**
  (`Ttc.Box.big_not_derivable`, README finding 20). So the input is dilated by
  `q = Ttc.scaleFactor` and the estimate divided by `qⁿ` — exact, because volume is
  homogeneous of degree `n` (`Ttc.volSol_scaleAtoms`).

## The transcription is complete, and two `rfl`s say so

Every line of the table above is now a definition of *this* file, with no
exception — `Ttc.toDNFd`, the line-16 converter, included. In particular
`Ttc.atomSet`, `Ttc.nondegenCubes` and `Ttc.pruneForm` — which used to sit in
`Exec/Inputs`, `Exec/Degenerate` and `Exec/Prune` — are here, and so is their
composite with the cleaning pass, `Ttc.preprocess`. Every *theorem* about them
stays in `Exec/`; only the definitions moved.

That the headline really measures these definitions is machine-checked. Its
accuracy conjunct is stated about `Ttc.ttcRun` *directly*, so no bridge is needed to
see what is measured; three `rfl` lemmas in `Exec/Api` connect that term to the
run's own vocabulary:

* `Ttc.ttcRun_eq_ttcAlgOutput` — `Ttc.ttcRun` **is** `Ttc.ttcAlgOutput` at the
  constructed oracle bundle `Ttc.ttcOracleBundle`. This is the lemma that makes
  `Ttc.ttcRun` the algorithm rather than a rename of it.
* `Ttc.ttcRun_eq_ttcEstimate` — and it **is** the run's estimate. That is lines
  A12–A13 at the bundle the development builds.
* `Ttc.ttcInput_eq_preprocess` — the formula that run is on is this file's
  `Ttc.preprocess atoms φ`. That is lines A2–A6.

So a reader who reads `Model/Prelude`, `Model/ProblemSetting`, this file and
`Model/Theorem`, and stops, has read the algorithm that is certified *and* the
input it is certified on. Nothing in the algorithm's statement is left in `Exec/`.

**What this does not make true.** The transcription being complete is a claim about
*where the definitions live*, not a claim that the transcribed algorithm is the
paper's. The four honesty notes above stand unchanged: steps 1, 3 and 4 are not in
the paper's `alg:ttc`; step 1 changes `Sol` by a null set (`⊆`, not `=`); step 2 is
an exact set equality and so changes nothing; and step 3 constructs *some* inscribed
ball, not `alg:prec`'s maximal one.
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

@[simp] theorem p_mk (X : Multiset (Space n)) (j : ℕ) :
    (⟨X, j⟩ : SketchState n).p = (1 / 2 : ℝ) ^ j := rfl

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

/-- **`TTC(F, ε, δ)`'s output, as a random variable over the input formula.**

The algorithm's **input is the formula**: there is no DNF argument. The cube list
the main loop folds over is `toDNF φ`, produced here by the line-16 converter from
`φ`, `F`'s Boolean abstraction (line 15). `P` is the parameter block of lines
17–20, `ρ` is `GetPrecision`'s output (line 17), and `O ω` are the oracles drawn at
the sample point `ω`.

`toDNF` is a *parameter* rather than the fixed `Ttc.toDNF` of `Model/Prelude`
because `TTC` runs an optimised circuit AllSAT, and `thm:runtime` is stated in
terms of `m`, **that** procedure's cube count — pinning the converter would prove
the guarantee for a different, generally exponentially larger `m`. Correctness
holds for any converter meeting `Ttc.IsDNFOf`, and `Ttc.toDNF_isDNFOf` shows at
least one does, so the parameter is not an empty hypothesis.

This is the quantity `thm:volumettc` bounds; `Ttc.runCost` is what `thm:runtime`
bounds, over the same run. -/
noncomputable def ttcOutput {A : Type*} {Ω : Type} (P : Params)
    (O : Ω → Oracles n (Cube A)) (toDNF : BForm A → DNF A) (ρ : ℤ)
    (φ : BForm A) (ω : Ω) : ℝ :=
  run P (O ω) ρ (toDNF φ)

/-! # The preprocessing, lines A1–A13

Definitions only, exactly as above: what each step *is*. Everything proved about
them stays in `Exec/` — `Ttc.sol_cleanForm` and `Ttc.volSol_pruneForm` (that the
body is preserved), `Ttc.volSol_scaleAtoms` (that the dilation is exact),
`Ttc.ball_subset_cenOf` and `Ttc.gammaOf_pos` (that the constructed ball is one),
`Ttc.thresh_le_scaled_ball_volume` (that `q` is large enough).

See the module docstring for the `alg:ttc` line each of these implements, and for
the two `rfl` bridges (`Ttc.ttcEstimate_eq_ttcOutput`, `Ttc.ttcInput_eq_preprocess`)
that pin the headline's measured quantity to them. -/

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

/-! # The parameter block, and the six facts a `Ttc.Params` needs to exist

`alg:ttc` lines 17–20 *compute* `η, ε', δ', Thresh, κ, γ, ρ` from `(F, ε, δ)`.  All
seven are already `def`s on `Ttc.Params` (`Model/Prelude`), so what is left is the
block itself: `Ttc.ttcParams`, which reads `m` and `r` off the decomposition, and
`Ttc.inputParams`, which is `ttcParams` at the algorithm's own inputs.

**Why there are proofs in this file.**  `Ttc.Params` bundles five *proof* fields
(`hε0 hε1 hn hm hr`), so a parameter block cannot be built without them; `hm`
(at least one cube) and `hr` (at least one facet) are not free.  The algorithm's
own preprocessing supplies both, so the lemmas that supply them have to be
available where the block is built — here.  They are, exhaustively:

| lemma | says | was in |
| --- | --- | --- |
| `Ttc.instFiniteCubeMem`, `Ttc.instFiniteFacetIndex` | both index types are finite, so `Nat.card` is not the junk value `0` | `Exec/Params` |
| `Ttc.one_le_card_cubes`, `Ttc.one_le_card_facets` | one member ⟹ `1 ≤ Nat.card` | `Exec/Params` |
| `Ttc.region_nil` | a literal-free cube denotes `Set.univ` | `Exec/CubeBounds` |
| `Ttc.not_isBounded_univ_space` | `ℝⁿ` is unbounded for `1 ≤ n` | `Exec/CubeBounds` |
| `Ttc.exists_lit_of_isBounded` | bounded `Sol` ⟹ every cube carries a literal | `Exec/CubeBounds` |
| `Ttc.one_le_card_cubes_of_ne_nil`, `Ttc.one_le_card_facets_of_isBounded` | the two packaged conclusions | `Exec/CubeBounds` |

Four more come up for a different reason: they are the **basic properties of this
file's own converter**, `Ttc.toDNFd` (line A1), and `Ttc.inputParams` instantiates
the two facts above *at* `toDNFd φ`.  They were in `Exec/Dedup`, which imports this
file for the definition, so leaving them there was a genuine import cycle
(`Model/Pseudocode → Exec/Dedup → Model/Pseudocode`).  They are:

| lemma | says | was in |
| --- | --- | --- |
| `Ttc.mem_toDNFd` | deduplication preserves the cubes | `Exec/Dedup` |
| `Ttc.exists_mem_toDNF` | a positive formula's DNF has a cube | `Exec/Dedup` |
| `Ttc.toDNFd_isDNFOf` | `toDNFd φ` is still a correct DNF of `φ` | `Exec/Dedup` |
| `Ttc.toDNFd_ne_nil` | `toDNFd` of a positive formula is nonempty | `Exec/Dedup` |

**That is the whole of the proof content `Model/` carries, together with the three
positivity lemmas of the next section** (`Ttc.cubeForm_isPositive`,
`Ttc.dnfForm_isPositive`, `Ttc.preprocess_isPositive`, which supply
`Ttc.inputParams`' `hφ` for the preprocessed formula), **and it is not an
accident.**  It is exactly: the facts without which a `Ttc.Params` cannot be
constructed, plus the four properties of the converter this file defines.  Nothing
else moved.  The tie-back lemmas about `ttcParams` (`Ttc.ttcParams_eps`, …) stay in
`Exec/Params`; the positivity route to a nonempty raw DNF
(`Ttc.exists_mem_dnfAux_true`, `Ttc.toDNF_ne_nil`, …) stays in `Exec/CubeBounds`;
and the counting lemmas (`Ttc.natCard_mem_list`, `Ttc.natCard_mem_list_of_nodup`,
`Ttc.card_toDNFd`, `Ttc.length_toDNFd_le_card`) together with `Ttc.toDNFd_nodup`,
`Ttc.toDNFd_isPositive` and `Ttc.toDNFd_ne_nil_of` stay in `Exec/Dedup`.

This file's one new import is `Ttc.Lattice.Decomposition`, for
`Ttc.region_subset_sol`; that module imports only Mathlib and `Model/Prelude`, so
the edge still runs `Model/ → Exec/` and never back.
-/

section ParamBlock

variable {A : Type*}

/-! ## Finiteness of the two index types

Both are subtypes cut out by membership in a `List`, hence finite; `Nat.card` of an
infinite type is `0`, so the positivity lemmas below would be *false* without this.
-/

instance instFiniteCubeMem (D : DNF A) : Finite {c : Cube A // c ∈ D} :=
  List.finite_toSet D |>.to_subtype

instance instFiniteFacetIndex (D : DNF A) : Finite (FacetIndex D) := by
  unfold FacetIndex
  have : ∀ c : {c : Cube A // c ∈ D}, Finite {l : Lit A // l ∈ c.val} := fun c =>
    (List.finite_toSet c.val).to_subtype
  infer_instance

/-- **The DNF has a cube ⟹ `1 ≤ m`.**  Reduces `Params`' `hm` to a statement about
the input formula's decomposition. -/
theorem one_le_card_cubes {D : DNF A} {c : Cube A} (hc : c ∈ D) :
    1 ≤ Nat.card {c : Cube A // c ∈ D} :=
  Nat.one_le_iff_ne_zero.mpr <| Nat.card_ne_zero.mpr ⟨⟨⟨c, hc⟩⟩, inferInstance⟩

/-- **Some cube has a literal ⟹ `1 ≤ r`.**  Reduces `Params`' `hr` likewise.  A cube
with no literals is the empty conjunction, whose region is all of `Space n`; the
facet count is then genuinely `0` and `Params` genuinely does not apply. -/
theorem one_le_card_facets {D : DNF A} {c : Cube A} (hc : c ∈ D) {l : Lit A}
    (hl : l ∈ c) : 1 ≤ Nat.card (FacetIndex D) :=
  Nat.one_le_iff_ne_zero.mpr <| Nat.card_ne_zero.mpr ⟨⟨⟨⟨c, hc⟩, ⟨l, hl⟩⟩⟩, inferInstance⟩

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

/-! ## `hm` and `hr`, derived rather than assumed

`hm` comes from the DNF being nonempty; `hr` from the solution set being bounded.
Neither is derivable from nothing — an unsatisfiable `φ` has an empty DNF, and
`φ = tt` has the single literal-free cube `[]` — so each is derived from a
hypothesis the top-level statement already carries.
-/

/-- A cube with no literals denotes all of the ambient space: `Cube.holds` is a
bounded universal quantifier over the cube's literals, hence vacuously true. -/
theorem region_nil {X : Type*} {M : A → Set X} : region M ([] : Cube A) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ h => absurd h (List.not_mem_nil)

/-- `ℝⁿ` is unbounded as soon as `1 ≤ n`.  Used to contradict `hbdd` in
`Ttc.exists_lit_of_isBounded`. -/
theorem not_isBounded_univ_space {n : ℕ} (hn : 1 ≤ n) :
    ¬ Bornology.IsBounded (Set.univ : Set (Space n)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Space n) := inferInstance
  exact NormedSpace.unbounded_univ ℝ (Space n)

/-- **Every cube of a DNF of a formula with bounded solution set has a literal.**

If some cube `c` were literal-free then `region M c = Set.univ`, and soundness of
the decomposition (`Ttc.region_subset_sol`) would give `Set.univ ⊆ sol M φ`,
making `sol M φ` unbounded — contradicting `hbdd`.  This is what discharges
`Ttc.ttcParams`' `hr` without assuming it. -/
theorem exists_lit_of_isBounded {n : ℕ} (hn : 1 ≤ n)
    {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hbdd : Bornology.IsBounded (sol M φ))
    {c : Cube A} (hc : c ∈ D) : ∃ l : Lit A, l ∈ c := by
  by_contra hno
  have hcnil : c = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun l hl => hno ⟨l, hl⟩
  subst hcnil
  have huniv : (Set.univ : Set (Space n)) ⊆ sol M φ := by
    rw [← region_nil (M := M) (A := A)]
    exact region_subset_sol hD hc
  exact not_isBounded_univ_space hn (hbdd.subset huniv)

/-- **A nonempty DNF has at least one cube**, in the `Nat.card` form
`Ttc.ttcParams` wants for its `hm`. -/
theorem one_le_card_cubes_of_ne_nil {D : DNF A} (hne : D ≠ []) :
    1 ≤ Nat.card {c : Cube A // c ∈ D} := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil D hne
  exact one_le_card_cubes hc

/-- **`hr`, from boundedness of the solution set.**  Combines
`Ttc.exists_lit_of_isBounded` with `Ttc.one_le_card_facets`.  Stated for an
arbitrary DNF `D` of `φ`, so that it applies to deduplicated variants of
`Ttc.toDNF φ` as well. -/
theorem one_le_card_facets_of_isBounded {n : ℕ} (hn : 1 ≤ n)
    {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hbdd : Bornology.IsBounded (sol M φ)) (hne : D ≠ []) :
    1 ≤ Nat.card (FacetIndex D) := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil D hne
  obtain ⟨l, hl⟩ := exists_lit_of_isBounded hn hD hbdd hc
  exact one_le_card_facets hc hl

/-! ## The four properties of `Ttc.toDNFd` that `Ttc.inputParams` instantiates at

`Ttc.inputParams` applies the two lemmas above to `D := toDNFd φ`, so it needs
`IsDNFOf (toDNFd φ) φ` and `toDNFd φ ≠ []`.  Both are properties of the converter
*defined in this file* (line A1), which is why they are here and not in
`Exec/Dedup`: that module imports this one.  Everything else proved about `toDNFd`
— duplicate-freeness, positivity, and the counting route to `hlen` — stays in
`Exec/Dedup`.
-/

/-- **Deduplication preserves the cubes.**  Everything the development asks of a DNF
is a statement about its members, so this single lemma is what makes `toDNFd` a
drop-in replacement for `toDNF`.

`Ttc.Cube A` has no `DecidableEq` to synthesize, so `List.mem_dedup`'s instance
argument is handed over by hand, matching `Ttc.toDNFd`'s own `Classical.decEq`. -/
theorem mem_toDNFd {φ : BForm A} {c : Cube A} : c ∈ toDNFd φ ↔ c ∈ toDNF φ :=
  @List.mem_dedup _ (Classical.decEq (Cube A)) c (toDNF φ)

/-- **`toDNFd` is still a correct DNF of `φ`.**  `DNF.holds v D = ∃ c ∈ D, c.holds v`
depends on `D` only through its members, and `Ttc.mem_toDNFd` says those are
unchanged; `Ttc.toDNF_isDNFOf` does the rest. -/
theorem toDNFd_isDNFOf (φ : BForm A) : IsDNFOf (toDNFd φ) φ := by
  intro v
  rw [← toDNF_isDNFOf φ v]
  constructor
  · rintro ⟨c, hc, hcv⟩
    exact ⟨c, mem_toDNFd.1 hc, hcv⟩
  · rintro ⟨c, hc, hcv⟩
    exact ⟨c, mem_toDNFd.2 hc, hcv⟩

/-- **A positive formula has at least one cube.**  Structural induction: `BForm` has
no `false` constructor, `neg` is excluded by positivity, `or` appends and `and`
crosses, and both operations preserve "has a member". -/
theorem exists_mem_toDNF : ∀ (φ : BForm A), φ.IsPositive → ∃ c, c ∈ toDNF φ := by
  intro φ
  induction φ with
  | tt => intro _; exact ⟨[], List.mem_singleton_self _⟩
  | atom a => intro _; exact ⟨[⟨a, true⟩], List.mem_singleton_self _⟩
  | neg φ _ => intro h; exact absurd h id
  | and φ ψ ihφ ihψ =>
      rintro ⟨hφ, hψ⟩
      obtain ⟨c, hc⟩ := ihφ hφ
      obtain ⟨d, hd⟩ := ihψ hψ
      refine ⟨c ++ d, ?_⟩
      show c ++ d ∈ (toDNF φ).cross (toDNF ψ)
      rw [DNF.cross, List.mem_flatMap]
      exact ⟨c, hc, List.mem_map_of_mem hd⟩
  | or φ ψ ihφ ihψ =>
      rintro ⟨hφ, _⟩
      obtain ⟨c, hc⟩ := ihφ hφ
      exact ⟨c, List.mem_append_left _ hc⟩

/-- **A positive formula has a non-empty deduplicated DNF.**  Together with
`Ttc.one_le_card_cubes_of_ne_nil` this discharges `hm` for `toDNFd`. -/
theorem toDNFd_ne_nil {φ : BForm A} (h : φ.IsPositive) : toDNFd φ ≠ [] := by
  obtain ⟨c, hc⟩ := exists_mem_toDNF φ h
  exact List.ne_nil_of_mem (mem_toDNFd.2 hc)

/-! ## The block at the algorithm's own inputs -/

/-- **The parameter block `TTC` computes** (`alg:ttc` lines 17–20), with `hm` and
`hr` supplied by `Ttc.one_le_card_cubes_of_ne_nil` and
`Ttc.one_le_card_facets_of_isBounded` rather than assumed.  The headline used to
carry `P` as a binder with `hP : P = ttcParams …`; this is that right-hand side,
named, so that both are discharged by `rfl`.

The internal failure parameter is `δ₀ = 4δ/5`, so that the conclusion is a clean
`1 − δ` — see `Exec/Final.lean` for what that reprices. -/
noncomputable def inputParams {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)) : Params :=
  ttcParams (toDNFd φ) n ε (4 * δ / 5) hε0 hε1 hn
    (one_le_card_cubes_of_ne_nil (toDNFd_ne_nil hφ))
    (one_le_card_facets_of_isBounded hn (toDNFd_isDNFOf φ) hbdd (toDNFd_ne_nil hφ))

/-! ## The block as a **total** function of the data

`Ttc.Params` bundles five *proof* fields (`hε0 hε1 hn hm hr`), so `Ttc.ttcParams`
and `Ttc.inputParams` cannot be *written down* without proofs — and that, and
nothing else, is what forced proof binders onto `Ttc.ttcAlgOutput` and
`Ttc.ttcRun`.  All five side conditions are propositions about the *data* alone,
so they can be **decided** classically rather than supplied, giving the block as a
function of `(atoms, φ, ε, δ)` only.  That is what the run below uses, and it is
why the run carries no proof binder.

The junk branch is inhabited because `Params`' proof fields constrain only its own
stored scalars (`0 < ε`, `ε ≤ 1`, `1 ≤ n`, `1 ≤ m`, `1 ≤ r`), never the formula:
`⟨1,1,1,1,1⟩` is a `Params`.  Nothing is claimed about it — `Ttc.ttcParamsTotal_eq`
says the branch is not taken wherever the headline's hypotheses hold, and every
theorem stated about `Ttc.ttcParams` transfers verbatim through it (proof
irrelevance makes its right-hand side independent of *which* proofs are supplied).
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
`Ttc.ttcParams` (`Ttc.ttcParamsTotal_eq`); on the other branch it is
`Ttc.junkParams`, about which nothing is claimed. -/
noncomputable def ttcParamsTotal (D : DNF A) (n : ℕ) (ε δ : ℝ) : Params :=
  if h : 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ n ∧ 1 ≤ Nat.card {c : Cube A // c ∈ D} ∧
      1 ≤ Nat.card (FacetIndex D) then
    ttcParams D n ε δ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  else junkParams

/-- **The agreement lemma — the whole point.**  Where the five side conditions hold,
the total block *is* `Ttc.ttcParams` at the very same arguments.  The proofs
`hε0 … hr` occur on the right and not on the left, and by proof irrelevance the
right-hand side does not depend on which proofs they are; so every theorem stated
about `Ttc.ttcParams` transfers verbatim. -/
theorem ttcParamsTotal_eq (D : DNF A) (n : ℕ) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ D}) (hr : 1 ≤ Nat.card (FacetIndex D)) :
    ttcParamsTotal D n ε δ = ttcParams D n ε δ hε0 hε1 hn hm hr := by
  rw [ttcParamsTotal, dif_pos ⟨hε0, hε1, hn, hm, hr⟩]

/-- **The junk branch, named.**  Stated so that the fallback is visible as a
statement rather than only as a branch of the `dite`: if any side condition fails
the block is the default value, and in particular nothing about the formula can be
read off it. -/
theorem ttcParamsTotal_eq_junk (D : DNF A) (n : ℕ) (ε δ : ℝ)
    (h : ¬ (0 < ε ∧ ε ≤ 1 ∧ 1 ≤ n ∧ 1 ≤ Nat.card {c : Cube A // c ∈ D} ∧
      1 ≤ Nat.card (FacetIndex D))) :
    ttcParamsTotal D n ε δ = junkParams := by
  rw [ttcParamsTotal, dif_neg h]

/-- **`Ttc.inputParams` as a total function of the data** — the block the run
actually reads.

`Ttc.inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd` is `Ttc.ttcParams (toDNFd φ) n ε
(4δ/5)` with `hm` and `hr` derived from `hφ` and `hbdd`; its *data* never mentions
`atoms`, which enters only through those two derivations.  The `atoms` binder is
kept so that this is a drop-in replacement at the call sites. -/
noncomputable def inputParamsTotal {n : ℕ} (_atoms : A → LinAtom n) (φ : BForm A)
    (ε δ : ℝ) : Params :=
  ttcParamsTotal (toDNFd φ) n ε (4 * δ / 5)

/-- **The agreement lemma at the algorithm's inputs.**  Under the four hypotheses
the headline already carries — three plain inequalities and boundedness — the total
block is `Ttc.inputParams`. -/
theorem inputParamsTotal_eq_inputParams {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)) :
    inputParamsTotal atoms φ ε δ = inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd :=
  ttcParamsTotal_eq _ _ _ _ hε0 hε1 hn _ _

end ParamBlock

/-! # The algorithm's output, lines A7–A13 completed

What is left of `alg:ttc` after the parameter block is the *rest of the
preprocessing* — the inscribed ball of lines A7–A9, the dilation factor of line
A10, the dilated atoms of line A11 — and then line A12's run and line A13's
division.  All of it is here, so that `Ttc.ttcAlgOutput` below is
`TTC(F, ε, δ)`'s output written in one term, at the algorithm's own inputs.

The six wrappers `Ttc.autoCen`, `Ttc.autoGamma`, `Ttc.runScale`,
`Ttc.scaledAtoms`, `Ttc.runPrec`, `Ttc.runCount` were in `Exec/Rescaled` and
`Exec/Inputs`; they are definitions with no proof content and they name no
theorem, so they belong with the pseudocode they transcribe. -/

section Algorithm

variable {A : Type*}

/-! ## The preprocessed formula is positive

`Ttc.inputParams` needs `φ.IsPositive`, and the formula the algorithm is handed is
`Ttc.preprocess atoms φ`, which is a `Ttc.dnfForm` — built from `.and`, `.or`,
`.atom` and `.tt` only, hence positive with no hypothesis at all.  This is the
one fact `Ttc.ttcAlgOutput` needs and gets for free.

(`Exec/Cleanup` proves the same thing under the name `Ttc.isPositive_dnfForm`;
that module imports this one, so the two-line induction is repeated here rather
than imported.  Neither is an assumption — both are proofs.) -/

/-- A cube's formula is positive: it is a `Ttc.conj` of atoms. -/
theorem cubeForm_isPositive (c : Cube A) : (cubeForm c).IsPositive := isPositive_conj _

/-- **`Ttc.dnfForm` is always positive** — it is built from `.or`, `.and`, `.atom`
and `.tt` only, and `Ttc.BForm.IsPositive` is exactly "no `.neg`". -/
theorem dnfForm_isPositive : ∀ D : DNF A, (dnfForm D).IsPositive := by
  intro D
  induction D with
  | nil => exact trivial
  | cons c D ih =>
      cases D with
      | nil => exact cubeForm_isPositive c
      | cons c' D' => exact ⟨cubeForm_isPositive c, ih⟩

/-- **The formula the algorithm is handed is positive**, unconditionally: lines
A3 and A6 both rebuild it with `Ttc.dnfForm`. -/
theorem preprocess_isPositive {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) :
    (preprocess atoms φ).IsPositive := dnfForm_isPositive _

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

/-- **Line A11.**  The dilated input: same normals, bounds scaled by
`Ttc.runScale`. -/
noncomputable def scaledAtoms (gammaHat : ℝ) : A → LinAtom n :=
  scaleAtoms (runScale atoms φ ε δ gammaHat) atoms

/-- **`GetPrecision`'s output** (`alg:ttc` line 17): `ρ ← ⌈log₁₀(γ/γ̂)⌉`, computed
from the parameter block and the inscribed radius. -/
noncomputable def runPrec (gammaHat : ℝ) : ℤ :=
  (inputParamsTotal atoms φ ε δ).precision gammaHat

/-- **`|Sol(F) ∩ 𝕃ⁿ|`** at that precision — the index the run's sample coins range
over. -/
noncomputable def runCount (gammaHat : ℝ) : ℕ :=
  latticeCount (atomSet atoms) φ (runPrec atoms φ ε δ gammaHat)

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
headline's hypotheses hold the block is the one `Ttc.inputParams` builds
(`Ttc.inputParamsTotal_eq_inputParams`), so every theorem about the latter
transfers. -/
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

/-! # The trajectory read-offs

`Ttc.trajOracles` (`Coupling/Family`) is an `Ttc.Oracles` bundle whose four random
fields are *read off* a trajectory `ω : ℕ → Fin L → ℕ` of the coupled level family.
Two of its six fields — `thin_le` and `gen_card` — are **contracts**: proof
obligations, discharged in `Coupling/Family` by `Ttc.toMultiset_le_of_count_le` and
`Multiset.card_replicate`. The other four are **values**: plain arithmetic on `ω`.

This section holds the values, and nothing else. It is deliberately positioned
*upstream* of `Ttc.Oracles`: it needs nothing beyond `Model/Prelude` (for
`Ttc.Space`), and a `Ttc.run` that reads the trajectory directly needs no oracle
bundle and hence no contract.

Nothing here is a `Prop`, and nothing here is assumed: every declaration is a
definition whose body is the arithmetic the paper's pseudocode performs. The facts
*about* these definitions — that `Ttc.trajThin` produces a sub-multiset, that
`Ttc.trajGen` produces exactly `N` points — stay with the theorems that prove them,
in `Coupling/Family`, and are what `Ttc.trajOracles`' two contract fields are built
from.

## Why the read-offs take a *row*, not a table

`trajPois` takes the membership row `mem i : Fin L → Bool` and the level slice
`ω j : Fin L → ℕ`, not the table `mem` and the trajectory `ω` with indices `i`, `j`.
That is the honest granularity: the value depends on the table only at the cube
being processed and on the trajectory only at the level being read, which is
precisely what `Ttc.trajOracles_pois_congr` and `Ttc.trajOracles_gen_congr`
(`Monadic/EventMeasurable`) and the congruence lemmas of `Exec/Coverage` say. Taking
rows makes those facts visible in the signature instead of provable from it.

These definitions live here, rather than in `Coupling/`, because they are part of
the audit surface: `Ttc/Audit/ClosureCheck.lean` requires the algorithm's output to
be defined entirely under `Ttc/Model/`, and a `Ttc.run` that reads a trajectory
directly reaches them. -/

namespace Ttc

variable {L : ℕ}

/-! ## Count vectors as multisets

The run's state is a `Multiset (Space n)`; the family is a count vector. This is the
dictionary between them, given an injective enumeration `pt` of the lattice points.
`Ttc.toMultiset` builds the multiset with prescribed multiplicities; that it *has*
those multiplicities (`Ttc.count_toMultiset`) is a theorem, and lives with the other
theorems in `Coupling/Family`. -/

/-- The multiset holding `k s` copies of the lattice point `pt s`. -/
noncomputable def toMultiset {n : ℕ} (pt : Fin L → Space n) (k : Fin L → ℕ) :
    Multiset (Space n) :=
  ∑ s, Multiset.replicate (k s) (pt s)

/-! ## The four read-offs

`vol` and `covered` are read off nothing — `Ttc.trajOracles` returns the functions it
was handed — so they need no definition here. The three that read `ω` do. -/

/-- **`thin`, read off the trajectory** (`alg:ttc` lines 33, 40): what survives of
`X` at a level whose count vector is `ωj`.

Capped at what `X` actually holds, so that the sub-multiset contract
(`Ttc.Oracles.thin_le`, discharged in `Coupling/Family`) holds for *every* multiset
and not only for the ones the run produces. On the states the run does reach the
multiplicities *are* the level's counts, so the `min` is inert — see `Coupling/Run`. -/
noncomputable def trajThin {n : ℕ} (pt : Fin L → Space n) (ωj : Fin L → ℕ)
    (X : Multiset (Space n)) : Multiset (Space n) :=
  toMultiset pt fun s => min (ωj s) (Multiset.count (pt s) X)

/-- **`Pois(λ)`, read off the trajectory** (`alg:ttc` lines 38, 41): the family's
total over the cube whose membership row is `m`, at a level whose count vector is
`ωj`. The rate `λ` is not read — the trajectory already carries it. -/
def trajPois (m : Fin L → Bool) (ωj : Fin L → ℕ) : ℕ :=
  ∑ s ∈ Finset.univ.filter fun s => m s = true, ωj s

/-- **`GenerateSamples`, read off the trajectory** (`alg:ttc` line 43): the family
restricted to the cube whose membership row is `m`, at a level whose count vector is
`ωj`.

`gen` must return exactly `N` points for **every** `N` (`Ttc.Oracles.gen_card`,
discharged in `Coupling/Family`), but the family's size is whatever `pois` returned.
So this falls back to `N` copies of `pad` when the two disagree — a branch the run
never takes, since it always passes the `N` that `trajPois` produced. The caller
supplies `pad` from the cube's own lattice points where it has any
(`Ttc.padPoint`), so that the membership contract still holds. -/
noncomputable def trajGen {n : ℕ} (pt : Fin L → Space n) (m : Fin L → Bool)
    (ωj : Fin L → ℕ) (N : ℕ) (pad : Space n) : Multiset (Space n) :=
  open Classical in
  if Multiset.card (toMultiset pt fun s => if m s then ωj s else 0) = N then
    toMultiset pt fun s => if m s then ωj s else 0
  else Multiset.replicate N pad

/-- A lattice point of the cube whose membership row is `m`, if it has one. Used only
as `Ttc.trajGen`'s `pad`, i.e. only on the branch the run never takes.
`Ttc.padPoint` (`Coupling/Family`) is this at the row `mem i`. -/
noncomputable def padRow {n : ℕ} (pt : Fin L → Space n) (m : Fin L → Bool) : Space n :=
  open Classical in
  if h : ∃ s, m s = true then pt h.choose else 0

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
entirely under `Ttc/Model/`, so the data half of the estimator lives in `Model/`
rather than in `Volume/`.

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
them into a radius (`Ttc.MonteCarlo.exists_ball_superset`).  `rad` picks one by choice,
totally: it is defined (as `1`) even when no radius exists, so that `est` is a total
function and `est_meas` needs no hypothesis. -/

open scoped Classical in
/-- A radius enclosing `K`, chosen classically; `1` if there is none. -/
noncomputable def rad (K : Set (Space n)) : ℝ :=
  if h : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R then h.choose else 1

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
constant `Ttc.ttcRun` unfolds to is defined under `Ttc/Model/`.  Three groups moved
into this file for that reason, each keeping its name and its proof:

* the **count-vector dictionary** and the two oracle **contracts**
  (`Ttc.count_toMultiset`, `Ttc.toMultiset_le_of_count_le`, `Ttc.trajThin_le`,
  `Ttc.card_trajGen`), formerly `Coupling/Family` — they are theorems *about* the
  read-offs already defined above, and the bundle's `thin_le` and `gen_card` fields
  are exactly these two;
* the **coverage test** (`Ttc.coverOfRegion`, `Ttc.memPtOfRegion`), formerly
  `Exec/Coverage` — `alg:ttc` line 27's membership query, classically;
* the **lattice enumeration** (`Ttc.HasLatticeEnum`, `Ttc.latticeEnum` and its three
  properties), formerly `Exec/Endgoal` — line 43's `GenerateSamples` draws from
  `Sol(F) ∩ 𝕃ⁿ`, so the enumeration of that set is part of the algorithm, not of its
  analysis.  `Ttc.hasLatticeEnum_of_finite` is the only substantive proof among them
  and it is pure `Nat.card` bookkeeping; the *geometric* input — that boundedness of
  `Sol(F)` makes the intersection finite — stays in `Exec/Geometry`, where it belongs,
  and is not needed to *define* the enumeration.

Nothing here asserts anything about the bundle: `Ttc.ttcRun`'s body is a closed term
and every proof it contains is discharged in this file. -/

namespace Ttc

open MeasureTheory Set

/-! ## The count-vector dictionary, and the two oracle contracts

`Ttc.toMultiset` (above) turns a count vector into the run's `Multiset (Space n)`
state.  These are the facts that make it a dictionary — that the multiplicities are
the prescribed ones — and the two contracts `Ttc.Oracles` demands of any bundle. -/

section Dictionary

variable {L : ℕ}

/-- The cardinality of `Ttc.toMultiset` is the total count. -/
@[simp] theorem card_toMultiset {n : ℕ} (pt : Fin L → Space n) (k : Fin L → ℕ) :
    Multiset.card (toMultiset pt k) = ∑ s, k s := by
  rw [toMultiset, Multiset.card_sum]
  exact Finset.sum_congr rfl fun s _ => Multiset.card_replicate _ _

/-- **The multiplicities are the ones prescribed** — the point of the dictionary.
Needs `pt` injective, so that distinct indices contribute to distinct points. -/
theorem count_toMultiset {n : ℕ} {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (k : Fin L → ℕ) (s : Fin L) :
    Multiset.count (pt s) (toMultiset pt k) = k s := by
  classical
  rw [toMultiset, Multiset.count_sum']
  rw [Finset.sum_eq_single s]
  · rw [Multiset.count_replicate_self]
  · intro t _ hts
    rw [Multiset.count_replicate, if_neg (fun h => hts (hpt h))]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- Points outside the enumeration do not occur. -/
theorem count_toMultiset_of_notMem {n : ℕ} (pt : Fin L → Space n) (k : Fin L → ℕ)
    {x : Space n} (hx : ∀ s, pt s ≠ x) :
    Multiset.count x (toMultiset pt k) = 0 := by
  classical
  rw [toMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [Multiset.count_replicate, if_neg (hx t)]

/-- **A count-bounded multiset is a sub-multiset** — the form `Ttc.Oracles.thin_le`
needs, where the ambient multiset is arbitrary rather than another `toMultiset`. -/
theorem toMultiset_le_of_count_le {n : ℕ} {pt : Fin L → Space n}
    (hpt : Function.Injective pt) {k : Fin L → ℕ} {X : Multiset (Space n)}
    (h : ∀ s, k s ≤ Multiset.count (pt s) X) :
    toMultiset pt k ≤ X := by
  classical
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : ∃ s, pt s = x
  · obtain ⟨s, rfl⟩ := hx
    rw [count_toMultiset hpt]
    exact h s
  · simp only [not_exists] at hx
    rw [count_toMultiset_of_notMem pt k hx]
    exact Nat.zero_le _

/-- **The `thin` contract**: `Ttc.trajThin` removes elements, it never invents them.
This is `Ttc.Oracles.thin_le` for the bundle `Ttc.ttcRun` builds. -/
theorem trajThin_le {n : ℕ} {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (ωj : Fin L → ℕ) (X : Multiset (Space n)) : trajThin pt ωj X ≤ X :=
  toMultiset_le_of_count_le hpt fun _ => min_le_right _ _

/-- **The `gen` contract**: `Ttc.trajGen` returns exactly `N` points.  This is
`Ttc.Oracles.gen_card` for the bundle `Ttc.ttcRun` builds. -/
theorem card_trajGen {n : ℕ} (pt : Fin L → Space n) (m : Fin L → Bool) (ωj : Fin L → ℕ)
    (N : ℕ) (pad : Space n) : Multiset.card (trajGen pt m ωj N pad) = N := by
  classical
  rw [trajGen]
  by_cases h : Multiset.card (toMultiset pt fun s => if m s then ωj s else 0) = N
  · simp only [h, if_pos]
  · simp only [h, if_false]
    exact Multiset.card_replicate _ _

end Dictionary

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

It is **unconditionally injective**, which is what the `thin` contract needs; the two
substantive properties (every enumerated point is a solution lattice point, and every
solution lattice point is enumerated) are guarded by `Ttc.HasLatticeEnum`, and
`Ttc.hasLatticeEnum_of_isBounded` (`Exec/Endgoal`) supplies that from boundedness of
`Sol(F)`.  When no enumeration exists the intersection is infinite, `Set.ncard` of an
infinite set is `0`, and `Fin 0` is empty — which is why injectivity is free. -/

variable {A : Type*} {n : ℕ}

/-- What an enumeration of `Sol(F) ∩ 𝕃ⁿ` is: a bijective listing by `Fin N`, at the
paper's own `N = |Sol(F) ∩ 𝕃ⁿ|` (`Ttc.latticeCount`). -/
def HasLatticeEnum (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) : Prop :=
  ∃ ptE : Fin (latticeCount M φ ρ) → Space n, Function.Injective ptE ∧
    (∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)) ∧
    (∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x)

/-- **Finiteness of `Sol(F) ∩ 𝕃ⁿ` is enough**: a finite set is equivalent to `Fin` of
its `Set.ncard`, and that count is literally `Ttc.latticeCount`.  Pure `Nat.card`
bookkeeping — the *geometric* fact that boundedness of `Sol(F)` gives finiteness is
`Ttc.exists_lattice_enum_of_isBounded` (`Exec/Geometry`) and is not needed here. -/
theorem hasLatticeEnum_of_finite {M : A → Set (Space n)} {φ : BForm A} (ρ : ℤ)
    (hfin : (sol M φ ∩ fineLattice n (latticeScale ρ)).Finite) : HasLatticeEnum M φ ρ := by
  have _ : Finite (sol M φ ∩ fineLattice n (latticeScale ρ) : Set (Space n)) := hfin.to_subtype
  have hcard : Nat.card (sol M φ ∩ fineLattice n (latticeScale ρ) : Set (Space n))
      = latticeCount M φ ρ := Nat.card_coe_set_eq _
  obtain e := Finite.equivFinOfCardEq hcard
  refine ⟨fun s => (e.symm s : Space n), fun a b hab => ?_, fun s => (e.symm s).property,
    fun x hx => ⟨e ⟨x, hx⟩, ?_⟩⟩
  · exact e.symm.injective (Subtype.ext hab)
  · simp

/-- The total version: an enumeration exists *unconditionally*, injective always, and
with the two membership properties whenever `Ttc.HasLatticeEnum` holds. -/
private theorem exists_latticeEnum (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) :
    ∃ ptE : Fin (latticeCount M φ ρ) → Space n, Function.Injective ptE ∧
      (HasLatticeEnum M φ ρ →
        (∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)) ∧
        (∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x)) := by
  by_cases h : HasLatticeEnum M φ ρ
  · obtain ⟨ptE, hinj, hmem, honto⟩ := h
    exact ⟨ptE, hinj, fun _ => ⟨hmem, honto⟩⟩
  · have hinf : (sol M φ ∩ fineLattice n (latticeScale ρ)).Infinite := by
      intro hfin
      exact h (hasLatticeEnum_of_finite ρ hfin)
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

/-- `ptE_mem`. -/
theorem latticeEnum_mem {M : A → Set (Space n)} {φ : BForm A} {ρ : ℤ}
    (h : HasLatticeEnum M φ ρ) (s : Fin (latticeCount M φ ρ)) :
    latticeEnum M φ ρ s ∈ sol M φ ∩ fineLattice n (latticeScale ρ) :=
  ((exists_latticeEnum M φ ρ).choose_spec.2 h).1 s

/-- `ptE_onto`. -/
theorem latticeEnum_onto {M : A → Set (Space n)} {φ : BForm A} {ρ : ℤ}
    (h : HasLatticeEnum M φ ρ) :
    ∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, latticeEnum M φ ρ s = x :=
  ((exists_latticeEnum M φ ρ).choose_spec.2 h).2

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
`Ttc.padRow`.  The bundle's two proof fields are `Ttc.trajThin_le` at
`Ttc.latticeEnum_injective` and `Ttc.card_trajGen`; both are proved above.

Nothing is assumed, and nothing is a proof: this is a closed term in
`(atoms, φ, ε, δ, c, t)`.  `Ttc.ttcRun_eq_ttcAlgOutput` (`Exec/Api`) proves that it
is `Ttc.ttcAlgOutput … (Ttc.ttcOracleBundle … c t)`, so this is not a second
description of the algorithm but the same term with its oracle argument filled
in. -/
noncomputable def ttcRun (c : ℕ → Space n)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) : ℝ :=
  ttcAlgOutput atoms φ ε δ
    { vol := mcVol (atomSet (algAtoms atoms φ ε δ))
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
          (padRow (algEnum atoms φ ε δ) (algMem atoms φ ε δ i)) }

end Run

end Ttc

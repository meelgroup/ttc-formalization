/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Dnf

/-!
# `Model/Pseudocode`: `alg:ttc`, **and the preprocessing that precedes it**

A line-by-line transcription of Algorithm 1, followed by a line-by-line
transcription of the **four preprocessing steps** the verified algorithm applies
before it. No proofs; the structural invariants of the modelled execution are in
`Invariants`, and every theorem about the preprocessing vocabulary stays in
`Exec/` (`Exec/Scale`, `Exec/ScaleFactor`, `Exec/Inscribed`, `Exec/Cleanup`,
`Exec/Prune`).

**This file imports no `Exec/` file.** `Ttc.toDNFd`, the deduplicated line-16
converter that `Ttc.pruneForm` and `Ttc.cleanForm` are defined over, used to live
in `Exec/Dedup`; it is defined *here* now (line A1 below), a two-line wrapper on
`Ttc.toDNF` of `Model/Prelude`. Its theorems (`Ttc.mem_toDNFd`,
`Ttc.toDNFd_nodup`, `Ttc.toDNFd_isDNFOf`, `Ttc.length_toDNFd_le_card`, …) stay in
`Exec/Dedup`, which now imports this file — the edge runs `Model/ → Exec/`, never
back. The single import here is `Ttc.Dnf` (for `Ttc.conj`, which `Ttc.cubeForm`
folds), and `Ttc.Dnf` itself depends on nothing but `Model/Prelude`.

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
| A8 (`SomeInscribedBall`) | `Ttc.ballData` | here |
| A8 (centres) | `Ttc.cenOf` | here |
| A9 (`γ̂`) | `Ttc.gammaOf` | here |
| A10 (`Vₙ`) | `Ttc.unitBallVol` | here |
| A10 (`q`) | `Ttc.scaleFactor` | here |
| A11 (dilate) | `Ttc.scaleAtoms` | here |
| A12 (the run) | `Ttc.run` / `Ttc.ttcOutput`, above | here |
| A13 (`/qⁿ`) | the division in `Ttc.ttcEstimate` | `Exec/Api` |

## Which of the four are in the paper

**Steps 1, 3 and 4 are not in the paper's `alg:ttc`.** Step 2 is not printed there
either, but unlike the other three it is not a change to the algorithm: it rewrites
the input syntax and leaves the body alone.

* **Step 1, the pruning (A2–A3), is not in `alg:ttc`.** It changes `Sol(F)` — by a
  **null set only**: the deleted cubes have convex regions with empty interior,
  `Ttc.sol_pruneForm_subset` is a genuine `⊆` that `Ttc.degForm` makes strict, and
  only the *measure* survives (`Ttc.volSol_pruneForm`). This is legitimate solely
  because the headline's conclusion merely **measures** `Ttc.sol`.
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

That the headline really measures these definitions is machine-checked, by two
lemmas whose proofs are `rfl` (both in `Exec/Api`):

* `Ttc.ttcEstimate_eq_ttcOutput` — the quantity `Ttc.ttc_volume_estimate` bounds is
  this file's `Ttc.ttcOutput`, at this file's parameter block and precision,
  divided by `qⁿ`. That is lines A12–A13.
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

end Ttc

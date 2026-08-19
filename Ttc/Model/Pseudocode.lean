/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.ModelSupport
import Ttc.Probability
import Arlib.MarkovChains.Continuous.HitAndRunMixing
import Arlib.Convexity.GaussianCooling.PhaseSchedule

/-!
# `Model/Pseudocode`: `alg:ttc`, **and the preprocessing that precedes it**

A line-by-line transcription of Algorithm 1, then of the four preprocessing steps the
verified algorithm applies before it, ending in `Ttc.ttcAlgOutput` (the output as one
term, over an oracle bundle).  No oracle is chosen here — `Ttc.ttc` and the bundle it runs
at are in `Model/Theorem`, downstream of the construction those oracles are built by.

**This file is not proof-free.**  It carries four theorems, one `private`, and no
instances — the smallest set that leaves it able to elaborate: `Ttc.exists_latticeEnum`
and the `private` `Ttc.exists_cubeOf` are what two `Classical.choose`s are taken from,
`Ttc.cubeOf_spec` is one of their `choose_spec`s, and `Ttc.latticeEnum_injective` is what
`Ttc.Oracles.thin_le` is applied at.  Each mentions a definition of this file, so none can
move out of the audit surface.  `AUDIT.md` §1h-iv has the full argument.

Every theorem *about* this vocabulary is downstream, in `Exec/`.  There is no geometry, no
measure theory beyond Mathlib's `volume`, and nothing about what the algorithm *achieves*.

## `alg:ttc`

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
**level** `j`, with `p = 2^(−j)`.  The level is carried instead of `p` so that the rate is
an index rather than a real — every randomised call is a read-off at a level.

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
deterministic given their answers; all the randomness sits at that boundary.  **Four
deviations from `algo.tex`** are recorded in `AUDIT.md` §1h-i.

## The preprocessing: what `Model/Theorem` certifies `alg:ttc` **plus**

The headline measures a run on an input four steps have already rewritten, with the
estimate divided by `qⁿ`.  Those steps are transcribed here because the audit path is
`Model/` and nothing outside it may carry a step of the algorithm.

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

Every line of that table is a definition of *this* file, and three `rfl` lemmas in
`Exec/Api` machine-check that the headline measures them.  **Which of the four steps are
in the paper** — steps 1, 3 and 4 are not, and step 1 changes `Sol` by a null set — is
`AUDIT.md` §1h-ii.
-/

namespace Ttc

open Multiset

variable {n : ℕ} {ι : Type*}

/-- The loop state: the sample multiset `X` (the paper's `𝒳`) and the **level** `j`,
with `p = 2^(−j)`. -/
structure SketchState (n : ℕ) where
  /-- The multiset `𝒳` of retained lattice points. -/
  X : Multiset (Space n)
  /-- The **level**: `p = 2^(−level)`. Incremented by every halving. -/
  level : ℕ

namespace SketchState

/-- The paper's sampling rate `p = 2^(−level)`. -/
noncomputable def p (st : SketchState n) : ℝ := (1 / 2 : ℝ) ^ st.level

end SketchState

/-- The four external calls, as fields.  Their *distributions* are what
`lem:numlattice` is about. -/
structure Oracles (n : ℕ) (ι : Type*) where
  /-- `Vol_ED(P(cᵢ), ε', δ')` (line 24). -/
  vol : ι → ℝ
  /-- Membership test `s ∈ P(cᵢ)` (line 27). -/
  covered : Space n → ι → Bool
  /-- "Remove every element of `X` with probability ½", iterated (lines 33, 40):
  what survives of `X` at level `j'`, entering at level `j₀`. -/
  thin : ℕ → ℕ → Multiset (Space n) → Multiset (Space n)
  /-- Thinning **removes** elements: the result is a sub-multiset. -/
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

/-- **Lines 32–35.** `while p ≥ Thresh/t`, as its exit level: the least level at or
above `j` whose rate is below `Thresh/t`.  Deterministic. -/
noncomputable def haltLevel (t : ℝ) (j : ℕ) : ℕ :=
  max j (sInf {j' | ¬ P.thresh / t ≤ (1 / 2 : ℝ) ^ j'})

/-- **Lines 39–42.** `while Nᵢ + |X| > Thresh`, as its exit level: the least `j' ≥ j₁`
at which the surviving sketch and the level-`j'` Poisson draw fit under `Thresh`.  `j₀`
is the level the step was entered at. -/
noncomputable def absorbLevel (i : ι) (t : ℝ) (X : Multiset (Space n)) (j₀ j₁ : ℕ) : ℕ :=
  max j₁ (sInf {j' | j₁ ≤ j' ∧ ¬ P.thresh <
    (O.pois i j' (t * (1 / 2 : ℝ) ^ j') : ℝ) + (card (O.thin j₀ j' X) : ℝ)})

/-- **Lines 24–42.** The state after both `while` loops of iteration `i`, paired with
the surviving Poisson draw `Nᵢ`. -/
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
`|X|/p`.  `ρ` is `GetPrecision`'s output (line 17). -/
noncomputable def run (ρ : ℤ) (cubes : List ι) : ℝ :=
  let final := cubes.foldl (step P O ρ) ⟨0, 0⟩
  (card final.X : ℝ) / final.p

/-! ## The charging model, `thm:runtime`.  Here because the headline *bounds* it, so a
referee must be able to read what the returned cost is.  The closed-form bound
`Ttc.ttcComplexity` is in `Exec/Complexity`. -/

/-- **The cost of one iteration**: one `Vol_ED` call plus one `GenerateSamples` draw per
point returned.  `N` is the surviving Poisson count `Nᵢ`. -/
def stepCost (cVol cSample N : ℕ) : ℕ := cVol + cSample * N

/-- **The cost of the whole run**: the per-iteration cost summed along `Ttc.run`'s own
fold, so each `Nᵢ` is the one the algorithm actually reaches. -/
noncomputable def runCost (cVol cSample : ℕ) (ρ : ℤ) (cubes : List ι) : ℕ :=
  (cubes.foldl
    (fun (acc : ℕ × SketchState n) i =>
      (acc.1 + stepCost cVol cSample (stepPre P O acc.2 i).2, step P O ρ acc.2 i))
    (0, ⟨0, 0⟩)).1

/-! # The preprocessing, lines A1–A13.  Definitions only: what each step *is*.
Everything proved about them stays in `Exec/`. -/

section Preprocess

variable {A : Type*}

/-! ## The interpretation: what an atom denotes. -/

/-- **The interpretation `M`**: the set each atom denotes.  Named, so that the binder
the headline used to take and its defining equation are both discharged by `rfl`. -/
def atomSet (atoms : A → LinAtom n) : A → Set (Space n) := fun a => (atoms a).halfspace

/-! ## Line A1: the converter, deduplicated -/

/-- **Line A1.** `Ttc.toDNF` (`alg:ttc` line 16) run through a deduplication pass.
Deduplication is needed because the side condition `(toDNF φ).length ≤ P.m` is a `Nodup`
condition in disguise, which the raw converter provably fails on `a ∨ a`
(`Ttc.toDNF_length_gt_card_cubes`).  Noncomputable only because `Cube A` carries no
`DecidableEq` for abstract `A`. -/
noncomputable def toDNFd (φ : BForm A) : DNF A :=
  @List.dedup _ (Classical.decEq (Cube A)) (toDNF φ)

/-! ## Step 2, lines A4–A6: cleaning the zero-normal atoms.  A literal whose atom has a
zero normal is not a constraint — with a nonnegative bound it denotes `Set.univ`, with a
negative bound `∅`.  Both filters decide classically. -/

/-- A literal is **vacuous** when its normal is `0` and its bound `≥ 0`: it constrains
nothing.  Line A5's `Vacuous`. -/
def VacuousLit (atoms : A → LinAtom n) (l : Lit A) : Prop :=
  (atoms l.atom).coeff = 0 ∧ 0 ≤ (atoms l.atom).bound

/-- A cube is **void** when it contains a literal with normal `0` and bound `< 0`: it is
unsatisfiable.  Line A4's `Void`. -/
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

/-! ## Lines A3 and A6: reading a cube list back as a formula.  Both rewrites rebuild
the *formula* rather than editing the DNF in place — they have to, since `Ttc.IsDNFOf`
quantifies over **all** Boolean assignments and neither rewrite is justified at an
arbitrary one (`Ttc.not_isDNFOf_cleanDNF`, `Ttc.not_isDNFOf_nondegenCubes_degForm` are the
machine-checked refutations). -/

/-- The formula of a cube: the conjunction of its atoms, via `Ttc.conj`. -/
def cubeForm (c : Cube A) : BForm A := conj (c.map Lit.atom)

/-- **Lines A3 and A6.** The disjunction of the cubes' formulas.  `[]` has no positive
formula denoting `∅`, so it is sent to the junk value `BForm.tt`; every theorem about
`dnfForm` assumes `D ≠ []`. -/
def dnfForm : DNF A → BForm A
  | [] => .tt
  | [c] => cubeForm c
  | c :: D => .or (cubeForm c) (dnfForm D)

/-! ## Step 1, lines A2–A3: pruning the degenerate cubes.  A cube whose region has
empty interior is unsatisfiable or lower-dimensional; either way convex and
Lebesgue-null. -/

/-- **Line A2.** The full-dimensional cubes: those whose region has nonempty
interior. -/
noncomputable def nondegenCubes (M : A → Set (Space n)) (D : DNF A) : DNF A :=
  D.filter fun c => @decide _ (Classical.propDecidable (interior (region M c)).Nonempty)

/-- **Lines A2–A3 as one step**: `φ` with its degenerate cubes pruned away.
`Ttc.volSol_pruneForm` says the deletion is invisible to the measure;
`Ttc.sol_pruneForm_subset` says it is *not* invisible to the set. -/
noncomputable def pruneForm (atoms : A → LinAtom n) (φ : BForm A) : BForm A :=
  dnfForm (nondegenCubes (atomSet atoms) (toDNFd φ))

/-- **Lines A4–A6 as one step.** The cleaned input formula.  `Ttc.sol_cleanForm` says it
denotes literally the same subset as `φ`. -/
noncomputable def cleanForm (atoms : A → LinAtom n) (φ : BForm A) : BForm A :=
  dnfForm (cleanDNF atoms (toDNFd φ))

/-- The input the amended algorithm actually runs on: degenerate cubes pruned,
then zero-normal atoms constant-folded. -/
noncomputable def preprocess (atoms : A → LinAtom n) (φ : BForm A) : BForm A :=
  cleanForm atoms (pruneForm atoms φ)

/-! ## Step 3, lines A7–A9: the inscribed ball.  `alg:prec` line 86 obtains `γ̂` from an
LP; what is transcribed here is weaker and total — *some* inscribed ball per cube, and the
least of the radii.  Non-maximality costs nothing: a smaller `γ̂` only makes the lattice
finer. -/

open Classical in
/-- **Line A8.** Some inscribed ball `(centre, radius)` of the region of `i`, or
`(0, 0)`.  Classical, and with **no** optimality claim. -/
noncomputable def ballData (M : A → Set (Space n)) (i : Cube A) : Space n × ℝ :=
  if h : ∃ p : Space n × ℝ, 0 < p.2 ∧ Metric.ball p.1 p.2 ⊆ region M i then h.choose else (0, 0)

/-- **Line A8.** The centre map: each cube gets its own inscribed-ball centre. -/
noncomputable def cenOf (M : A → Set (Space n)) (D : DNF A) :
    {c : Cube A // c ∈ D} → Space n := fun i => (ballData M i.val).1

/-- **Line A9.** The shared inscribed radius `γ̂`: the least of the per-cube radii.
Total — on an empty DNF it is `0`, which `Ttc.ball_subset_cenOf` tolerates. -/
noncomputable def gammaOf (M : A → Set (Space n)) (D : DNF A) : ℝ :=
  ⨅ i : {c : Cube A // c ∈ D}, (ballData M i.val).2

/-! ## Step 4, lines A10–A11: the dilation.  Volume is homogeneous of degree `n`, so
dilating by `q ≥ 1` multiplies `Vol(Sol F)` by exactly `qⁿ` — as large as needed to clear
`Thresh`, which the printed algorithm does not guarantee.  Line A13 undoes it; relative
error is invariant. -/

/-- **`Vₙ`**, the volume of the unit ball of `Ttc.Space n`.  Deliberately opaque: only
`Ttc.unitBallVol_pos` and `Ttc.volume_ball_eq` are ever needed. -/
noncomputable def unitBallVol (n : ℕ) : ℝ :=
  (MeasureTheory.volume (Metric.ball (0 : Space n) 1)).toReal

/-- **Line A10.** The dilation factor `q`, computed from `γ̂` and `n` with **no
knowledge of `Vol`** — which is what makes this preprocessing rather than a hypothesis.
`max 1 (…)` deliberately overshoots the exact `(Thresh/(Vₙ γ̂ⁿ))^{1/n}` to avoid an `n`-th
root; the overshoot is free because line A13 divides by `qⁿ`. -/
noncomputable def scaleFactor (n : ℕ) (P : Params) (gammaHat : ℝ) : ℝ :=
  max 1 (P.thresh / (unitBallVol n * gammaHat ^ n))

/-- **Line A11.** The atoms dilated by `c`: same normals, bounds scaled.  Scaling the
bound and not the normal is what dilates rather than rotates
(`Ttc.halfspace_scaleAtoms`). -/
def scaleAtoms (c : ℝ) (atoms : A → LinAtom n) : A → LinAtom n :=
  fun a => ⟨(atoms a).coeff, c * (atoms a).bound⟩

end Preprocess

/-! # The parameter block

`alg:ttc` lines 17–20 compute `η, ε', δ', Thresh, κ, γ, ρ` from `(F, ε, δ)`; all seven are
already `def`s on `Ttc.Params` (`Model/Prelude`), so what is left is the block itself.

**No proofs here.**  `Ttc.Params` bundles five *proof* fields, so `Ttc.ttcParams` cannot be
applied without them — but it is applied only inside `Ttc.ttcParamsTotal`, on the branch
where a `Decidable` instance has already produced them. -/

section ParamBlock

variable {A : Type*}

/-- **The parameter block `TTC(F, ε, δ)` computes**, from the returned DNF, the
dimension, and the requested accuracy and confidence.  `m` and `r` are the *exact* counts,
not bounds, which is what makes `Ttc.ttcParams_cubes_le`/`_facets_le` `le_refl` rather
than assumptions. -/
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

All five side conditions are propositions about the *data*, so they can be **decided**
classically rather than supplied, giving the block as a function of `(atoms, φ, ε, δ)`
alone.  That is what the run uses, and it is why the run carries no proof binder.
`Ttc.ttcParamsTotal_eq` (`Exec/Params`) says the junk branch is not taken wherever the
headline's hypotheses hold. -/

/-- **A `Ttc.Params` at constant data** — the fallback when the side conditions fail.
It asserts nothing: no lemma relates any of its fields to a formula. -/
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
/-- **The parameter block of `alg:ttc` lines 17–20, as a total function of the data.**
On the good branch this is literally `Ttc.ttcParams`; otherwise `Ttc.junkParams`, about
which nothing is claimed. -/
noncomputable def ttcParamsTotal (D : DNF A) (n : ℕ) (ε δ : ℝ) : Params :=
  if h : 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ n ∧ 1 ≤ Nat.card {c : Cube A // c ∈ D} ∧
      1 ≤ Nat.card (FacetIndex D) then
    ttcParams D n ε δ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  else junkParams

/-- **The block the run actually reads** — `Ttc.ttcParamsTotal` at `(toDNFd φ, n, ε,
4δ/5)`.  The `atoms` binder is unused in the data, and kept only so this is a drop-in
replacement for the proof-carrying `Ttc.inputParams` (`Exec/Dedup`). -/
noncomputable def inputParamsTotal {n : ℕ} (_atoms : A → LinAtom n) (φ : BForm A)
    (ε δ : ℝ) : Params :=
  ttcParamsTotal (toDNFd φ) n ε (4 * δ / 5)

end ParamBlock

/-! # The algorithm's output, lines A7–A13 completed

The rest of the preprocessing — the inscribed ball of lines A7–A9, the dilation factor of
line A10, the dilated atoms of line A11 — then line A12's run and line A13's division, so
that `Ttc.ttcAlgOutput` is `TTC(F, ε, δ)`'s output in one term. -/

section Algorithm

variable {A : Type*}

/-- **Lines A7–A8.**  The centre map `GetPrecision` produces. -/
noncomputable def autoCen {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) :
    {c : Cube A // c ∈ toDNFd φ} → Space n :=
  cenOf (atomSet atoms) (toDNFd φ)

/-- **Line A9.**  The inscribed radius `γ̂` `GetPrecision` produces. -/
noncomputable def autoGamma {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) : ℝ :=
  gammaOf (atomSet atoms) (toDNFd φ)

section Wrappers

variable {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **Line A10.**  The dilation `q`, at the parameter block the inputs determine.
Always `≥ 1`, and computable from `γ̂` and `n` alone. -/
noncomputable def runScale (gammaHat : ℝ) : ℝ :=
  scaleFactor n (inputParamsTotal atoms φ ε δ) gammaHat

/-- **`GetPrecision`'s output** (line 17): `ρ ← ⌈log₁₀(γ/γ̂)⌉`. -/
noncomputable def runPrec (gammaHat : ℝ) : ℤ :=
  (inputParamsTotal atoms φ ε δ).precision gammaHat

end Wrappers

/-- **`TTC(F, ε, δ)`'s output**, as `alg:ttc` computes it: the fold of lines 22–46 over
the preprocessed formula's cubes, at the computed parameter block and precision, with the
estimate divided by `qⁿ` (line A13).

`O` is the **oracle bundle** — line 24's `Vol_ED` and line 43's `GenerateSamples`, exactly
as the paper prints them.  Nothing about it is assumed; it is an argument, and
`Ttc.ttcAlgOutput_eq_ttcEstimate` (`Exec/Api`, `rfl`) identifies this term at the verified
bundle with the quantity the headline bounds.  **No proof binder**: the block is
`Ttc.inputParamsTotal`, so this is a closed function of the data. -/
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

/-! # No volume oracle is defined here

Until 2026-08-19 this file also defined `Ttc.mcVol` — hit-and-miss Monte Carlo — together
with the estimator data it unfolds to, because the run *called* it rather than receiving it.
`Ttc.ttcAlgOutput` takes `(O : Oracles n (Cube A))` as an argument, so nothing in `alg:ttc`
needs a volume oracle to be named here.  The oracle is Cousins-Vempala Gaussian cooling,
constructed in `Ttc/Volume/` and `Ttc/Exec/`. -/

namespace Ttc

open MeasureTheory Pointwise

/-- **The normalisation `Vol_ED` is called on**: `K` moved so its inscribed ball becomes
the unit ball at the origin, `y ↦ γ⁻¹ · (y − c)`.  Cousins–Vempala Theorem 1.1 speaks only
about bodies containing the unit ball; this is the change of variable that closes the gap,
*proved* in `Ttc/Volume/Bridge.lean`, not assumed. -/
noncomputable def roundBody {n : ℕ} (c : Space n) (γ : ℝ) (K : Set (Space n)) :
    Set (Space n) := γ⁻¹ • ((-c) +ᵥ K)

end Ttc

namespace Ttc.MonteCarlo

open MeasureTheory

variable {n : ℕ}

/-! ## The enclosing radius -/

open scoped Classical in
/-- **The least enclosing radius, plus one**; `1` if no radius exists.

`sInf` rather than `Exists.choose`, because the infimum is a *canonical* choice and so an
**upper** bound on `rad` is derivable (`Ttc.MonteCarlo.rad_le_of_subset_closedBall`), which
is what makes the sample count's closed form unconditional.  `Exists.choose_spec` gives
only lower-bound facts, and the satisfying set is upward closed.

The `+ 1` is load-bearing: `sInf` of the valid radii need not itself be valid (take `K` a
closed ball), so it reopens the ball and keeps `Ttc.MonteCarlo.subset_ball_rad`.  Total, so
`est` is total and `est_meas` needs no hypothesis. -/
noncomputable def rad (K : Set (Space n)) : ℝ :=
  if ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R
  then sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} + 1 else 1

/-! ## The target set.  `target K` is what the *coins* are tested against: the measurable
hull of `K`, pulled back along `x ↦ rad K • x`.  Measurable for **every** `K`, which is
what makes `Ttc.VolumeAlgorithm.est_meas` provable. -/

/-- The measurable hull of `K`, in unit-ball coordinates. -/
noncomputable def target (K : Set (Space n)) : Set (Space n) :=
  (fun x : Space n => rad K • x) ⁻¹' toMeasurable volume K

/-! ## The estimator -/

/-- **The hitting probability, as arithmetic**: `Vol K / Vol(ball 0 (rad K))`, in Lebesgue
volume alone.  Only this form defines the sample count, so the coin law stays out of the
algorithm's definitional closure; `Ttc.MonteCarlo.hit_eq_hitData` shows it agrees with the
law form. -/
noncomputable def hitData (K : Set (Space n)) : ℝ :=
  (rad K ^ n)⁻¹ * (volume K).toReal / (volume (Metric.ball (0 : Space n) 1)).toReal

/-- The volume of the enclosing ball, `Vol(ball 0 (rad K)) = (rad K)ⁿ · Vol(ball 0 1)`. -/
noncomputable def scale (K : Set (Space n)) : ℝ :=
  rad K ^ n * (volume (Metric.ball (0 : Space n) 1)).toReal

/-- The number of samples: `⌈(ε²·p·q)⁻¹⌉ + 1` at `q = Ttc.MonteCarlo.hitData K`.
`Θ(Rⁿ/(ε²p))` — **exponential in `n`**. -/
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
/-- **`Vol_ED`'s output, as a function of the volume oracle's coins.**  With the volume
oracle fixed to the *constructed* `Ttc.VolumeAlgorithm.monteCarlo`, this is no longer a
free function but a closed term, and the binder pinning it becomes the theorem
`Ttc.mcVol_eq` (`Exec/VolDischarge`).  Off the DNF the value is `0`; the algorithm never
reads it, and totality is what avoids a proof argument. -/
noncomputable def mcVol {A : Type*} {n : ℕ} (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ)
    (c : ℕ → Space n) (i : Cube A) : ℝ :=
  if hi : i ∈ D then
    γ ^ n * MonteCarlo.est (roundBody (cen ⟨i, hi⟩) γ (region M i)) ε' δ' c
  else 0

end Ttc

/-! # `TTC(F, ε, δ)` on one run

`Ttc.ttcAlgOutput` above takes the oracle bundle as an argument, because `alg:ttc` prints
`Vol_ED` and `GenerateSamples` as external calls.  Filling that argument in is what
`Ttc.ttcOracleBundle` (`Exec/Api`) does, and `Ttc.ttcEstimate` is the resulting number; both
are downstream of this file, because the oracles the paper specifies are built there.
Without that lemma this would be a rename; with it, it is the same term.  Everything the
bundle is built from is therefore in the audit surface: the coverage test, the lattice
enumeration, and the trajectory read-offs (the last in `Probability/Trajectory`). -/

namespace Ttc

open MeasureTheory Set

/-! ## Line 27: the coverage test — `alg:ttc` line 27's query `s ∈ P(cᵢ)` as a `Bool`,
classically, and its reindexing along an enumeration.  A *specification*, not an
implementation. -/

/-- **The coverage test, classically**: line 27's `s ∈ P(cᵢ)` as a `Bool`. -/
noncomputable def coverOfRegion {A X : Type*} (M : A → Set X) (x : X) (c : Cube A) : Bool :=
  @decide (x ∈ region M c) (Classical.propDecidable _)

/-- **The per-lattice-point form**: the test indexed by the enumeration rather than the
point, so `Ttc.coverOfRegion_memPtOfRegion` is `rfl`. -/
noncomputable def memPtOfRegion {A : Type*} {n L : ℕ} (M : A → Set (Space n))
    (ptE : Fin L → Space n) (c : Cube A) (s : Fin L) : Bool :=
  coverOfRegion M (ptE s) c

/-! ## Line 43: the enumeration of `Sol(F) ∩ 𝕃ⁿ`

`GenerateSamples` draws lattice points, so the algorithm needs an enumeration indexed by
`Fin |Sol(F) ∩ 𝕃ⁿ|` — the paper's `Fin N` — as a **total function of `(M, φ, ρ)` alone**,
so that the output does not mention a boundedness proof.

It is **unconditionally injective**, which is what the `thin` contract needs, and that is
all of it this file proves.  The two substantive properties are guarded by
`Ttc.HasLatticeEnum` and read off in `Exec/Endgoal`.  When no enumeration exists the
intersection is infinite, `Set.ncard` of an infinite set is `0`, and `Fin 0` is empty —
which is why injectivity is free. -/

variable {A : Type*} {n : ℕ}

/-- What an enumeration of `Sol(F) ∩ 𝕃ⁿ` is: a bijective listing by `Fin N`, at the
paper's own `N = |Sol(F) ∩ 𝕃ⁿ|` (`Ttc.latticeCount`). -/
def HasLatticeEnum (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) : Prop :=
  ∃ ptE : Fin (latticeCount M φ ρ) → Space n, Function.Injective ptE ∧
    (∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)) ∧
    (∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x)

/-- An enumeration exists *unconditionally*, injective always, with the two membership
properties whenever `Ttc.HasLatticeEnum` holds.  `Ttc.latticeEnum` is `choose`n from this,
so it is part of the algorithm — and, being reached through a `def`'s body, the one theorem
here that `#modelClosure` sees. -/
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

/-- **The enumeration of `Sol(F) ∩ 𝕃ⁿ`**, indexed by the paper's `Fin N`. -/
noncomputable def latticeEnum (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) :
    Fin (latticeCount M φ ρ) → Space n :=
  (exists_latticeEnum M φ ρ).choose

/-- `ptE_inj`, unconditionally. -/
theorem latticeEnum_injective (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) :
    Function.Injective (latticeEnum M φ ρ) :=
  (exists_latticeEnum M φ ρ).choose_spec.1

/-! ## Line 20: the level-`0` rates `θ`.  For each enumerated point `s`,
`θ(s) = sampD(c, s) · Vol_ED(P(c))` where `c` is the cube `s` is assigned to.  The
assignment is total in `s`, so the rates are a closed term. -/

/-- The choice principle behind `Ttc.cubeOf`. -/
private theorem exists_cubeOf (M : A → Set (Space n)) (D : DNF A) (x : Space n) :
    ∃ c : Cube A, (∃ c' : Cube A, c' ∈ D ∧ x ∈ region M c') → (c ∈ D ∧ x ∈ region M c) := by
  by_cases h : ∃ c' : Cube A, c' ∈ D ∧ x ∈ region M c'
  · exact ⟨h.choose, fun _ => h.choose_spec⟩
  · exact ⟨[], fun h' => absurd h' h⟩

/-- **A cube of `D` containing `x`**, total in `x` so the rates are a closed term. -/
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

/-- **The level-`0` rates of line 20**: the sampler's mass at the enumerated point, in
its assigned cube, times that cube's volume estimate. -/
noncomputable def rates (M : A → Set (Space n)) (φ : BForm A) (D : DNF A) (ρ : ℤ)
    (sampD : Cube A → Space n → ℝ) (vol : Cube A → ℝ) :
    Fin (latticeCount M φ ρ) → ℝ :=
  fun s => sampD (cubeAt M φ D ρ s) (latticeEnum M φ ρ s) * vol (cubeAt M φ D ρ s)

/-! ## The run's own data, and `TTC(F, ε, δ)` on one run

Nine abbreviations spelling out what lines A10–A13 and 17–20 compute.  They are what the
oracle bundle is built from downstream (`Ttc.ttcOracleBundle`, `Exec/Api`).  Nothing here is
a proof binder: all nine are closed functions of `(atoms, φ, ε, δ)`. -/

section Run

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The parameter block** lines 17–20 compute, at the preprocessed formula. -/
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

/-- **`N = |Sol(F) ∩ 𝕃ⁿ|`** for the dilated input — the index the sample coins range
over. -/
noncomputable def algIndex : ℕ :=
  latticeCount (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
    (algPrec atoms φ ε δ)

/-- **The enumeration `GenerateSamples` draws from**, at the dilated input. -/
noncomputable def algEnum : Fin (algIndex atoms φ ε δ) → Space n :=
  latticeEnum (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
    (algPrec atoms φ ε δ)

/-- **Lines A7–A8 + A11.**  The inscribed-ball centres, moved by the dilation. -/
noncomputable def algCen : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Space n :=
  fun i => algScale atoms φ ε δ • autoCen atoms (preprocess atoms φ) i

/-- **Line 27's membership table**: the coverage test at each enumerated point. -/
noncomputable def algMem : Cube A → Fin (algIndex atoms φ ε δ) → Bool :=
  memPtOfRegion (atomSet (algAtoms atoms φ ε δ)) (algEnum atoms φ ε δ)

/-! ## No oracle is chosen here

`alg:ttc` calls `Vol_ED` and `GenerateSamples`; it does not say how either is implemented,
and neither does this file.  `Ttc.ttcAlgOutput` above takes `(O : Oracles n (Cube A))` as an
argument, and that is the whole of the algorithm.

The oracles are **Cousins–Vempala Gaussian cooling** for volume and **hit-and-run** for
sampling, constructed in `Ttc/Volume/` and `Ttc/Exec/`, and `Ttc.ttc` — `alg:ttc` at those —
is defined in `Ttc/Model/Theorem.lean`.  It has to be: the construction is built on the
definitions *in this file* (`Ttc.algBlock`, `Ttc.preprocess`, `Ttc.ttcAlgOutput`, …), so it is
downstream of it, and only a file downstream of the construction can name it.  The layering
is `Prelude → ProblemSetting → ModelSupport → … → Pseudocode → Volume/Exec → Theorem`.

Until 2026-08-19 this file also defined a *reference* instantiation over `Ttc.mcVol`
(hit-and-miss Monte Carlo) and the lazy ball walk.  Both were exponential in `n` and neither
was the paper's oracle; they have been removed. -/

end Run

end Ttc

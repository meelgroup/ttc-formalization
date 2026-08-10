/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Coupling.Product
import Ttc.Exec.Params
import Ttc.Exec.Geometry
import Ttc.Exec.Coverage
import Ttc.Volume.VolSolCheck
import Ttc.Dnf

/-!
# `Model/Endgoal`: the capstone over the algorithm's own inputs

`END-TO-END-PLAN.md`'s **THE ENDGOAL** asks for one theorem shaped like
`ApproxNFA.approxNFA_countNFA` (`nfalean/ApproxNFA/Model/Theorem.lean:99`):

```lean
theorem ttc_volume (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε : 0 < ε) … <every remaining obligation as an EXPLICIT NAMED HYPOTHESIS> :
    1 - δ ≤ (… the constructed space …) … ∧ <the runtime half>
```

against today's

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) : …
```

which quantifies over a 59-field structure.  This file is that restatement, at the
strength the development supports **today**: `Ttc.ttc_volume` below takes
`(atoms, φ, ε, δ)`, constructs everything that can be constructed, and carries the
rest as named binders a reader sees in the type.  It is a *staging* file: nothing
in `Model/{Prelude,Pseudocode,ProblemSetting,Theorem}` is touched, and
`Ttc.TtcProb.volume_estimate` keeps its exact statement and axiom profile.

## What is constructed, and from what

| `Ttc.TtcProb` field | here | by |
| --- | --- | --- |
| `M`, `M_eq` | `fun a => (atoms a).halfspace` | the atoms denote it |
| `P` | `Ttc.ttcParams (toDNF φ) n ε δ …` | `Exec/Params` |
| `eps_eq`, `delta_eq`, `dim_eq` | `rfl` | `Ttc.ttcParams_eps/_delta/_dim` |
| `cubes_le`, `facets_le` | `le_rfl` | `Ttc.ttcParams_cubes_le/_facets_le` |
| `ρ`, `rho_eq` | `P.precision gammaHat`, `rfl` | `alg:ttc` line 17 |
| `L`, `L_eq` | `normalisedCount M φ ρ`, `rfl` | the definition |
| `normal_ne_zero` | `Ttc.normal_ne_zero_of_coeff_ne_zero hcoeff` | `Exec/Geometry` |
| `volume_ne_top` | `Ttc.volume_region_ne_top_of_isBounded isDNF hbdd` | `Exec/Geometry` |
| `Lidx` | `Ttc.latticeCount M φ ρ` — *the paper's* `N = |Sol(F) ∩ 𝕃ⁿ|` | `Exec/Geometry` |
| `ptE`, `ptE_inj`, `ptE_mem`, `ptE_onto` | `Ttc.latticeEnum M φ ρ` and its three lemmas | below |
| `Ω`, `mΩ`, `μ`, `isProb` | `ℕ → Fin (latticeCount M φ ρ) → ℕ`, `Ttc.trajLaw θ` | `Exec/Canonical` |
| `O` | `Ttc.coveredOracles M φ ρ vol` — coverage test constructed too | `Exec/Coverage` |
| `toTraj`, `toTraj_meas`, `law_eq`, `oracle_eq` | `id`, … | `Exec/Canonical` |

So the sample space is **built from the inputs**, not assumed: the probability in
the conclusion is `Ttc.trajLaw θ` on `ℕ → Fin (latticeCount M φ ρ) → ℕ`, exactly
the space `Ttc.canonicalTtcProb` constructs, and the output measured is
`Ttc.ttcOutput` — the transcription of `alg:ttc` — at the constructed oracle
bundle `Ttc.coveredOracles`.  Note in particular that the index type is now pinned to
`Fin |Sol(F) ∩ 𝕃ⁿ|`: the enumeration size is the paper's `N`, not an opaque `ℕ`.

## What is still an assumption — the project's progress metric

> **Counting convention — read this before "correcting" the numbers below.**
> Every count in this file is of **explicit** binders.  A probe that walks the raw
> `ConstantInfo.type` counting `Expr.forallE` reports **38**, because the two
> implicit ambient parameters `{A}` and `{n}` (from the `variable` line) are
> binders in the type but are not obligations anyone has to discharge.  Both
> numbers are right; they count different things.  Audit passes have twice
> flagged this as a discrepancy, so: 38 raw = 36 explicit + 2 implicit.

`Ttc.ttc_volume` has **36 binders**: 4 inputs (`atoms, φ, ε, δ`), 4 *definitional*
(`M`/`M_eq` and `P`/`hP` — each pins a datum to a canonical closed term and exists
only to keep the type short; inlining them would replace ~20 occurrences of
`fun a => (atoms a).halfspace` and `ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr`, and
they assume nothing), and **28 residual** — down from 37, then 32.  Of those 28,
five (`hε0, hε1, hδ0, hδ1, hn`) are the FPRAS parameter range that
`ApproxNFA.approxNFA_countNFA` also carries, so the honest gap against the template
is **23**.  Compare 59 opaque structure fields, none of which is visible in
`Ttc.TtcProb.volume_estimate`'s type.

The 28, grouped as they appear in the statement:

1. **Input conditions on `(φ, ε, δ, n)`** — `hε0, hε1, hδ0, hδ1, hn, hm, hr`.
   `hm`/`hr` say the DNF has a cube and that cube has a literal; `Ttc.one_le_card_cubes`
   and `Ttc.one_le_card_facets` reduce them to exactly that.
2. **The AllSAT call** — `toDNF, isDNF, isPositive`.  `Ttc.ttc_volume_toDNF` below
   discharges `isDNF` and reduces `isPositive` to `φ.IsPositive` by pinning
   `toDNF := Ttc.toDNF`; it is a *corollary*, not the main statement, because
   `thm:runtime`'s `m` is the optimised procedure's cube count (see
   `Model/Pseudocode.lean:195`).
3. **The geometry of the decomposition** — `hbdd, hcoeff` plus the inscribed ball
   `cen, gammaHat, hgammaHat, ball_subset`.  This cluster was **eleven** binders
   before `Ttc/Exec/Geometry.lean` landed; it is six now.
   * `hbdd : Bornology.IsBounded (sol M φ)` is **one readable condition on the
     input formula**.  It replaces the old `volume_ne_top` binder
     (`Ttc.volume_region_ne_top_of_isBounded`) *and* the whole five-binder
     enumeration cluster `Lidx, ptE, ptE_inj, ptE_mem, ptE_onto`
     (`Ttc.exists_lattice_enum_of_isBounded`), which are now constructed —
     `Ttc.latticeEnum` below.  `Ttc.isBounded_sol_iff_regions` shows `hbdd` is
     equivalent to the per-cube form the geometry actually consumes, and
     `Ttc.finite_of_lattice_enum` shows nothing weaker can replace the enumeration
     binders.
   * `hcoeff : ∀ j, (atoms j.2.val.atom).coeff ≠ 0` is the old `normal_ne_zero` in
     readable form (`Ttc.sq_sum_pos_iff`, an `iff`, so nothing is lost);
     `Ttc.normal_ne_zero_not_derivable` shows it is genuinely an assumption.
   * The four inscribed-ball binders are **kept as `∀`-binders on purpose**, and
     they cost nothing: `Ttc.exists_inscribed_ball_of_vol_pos` proves that
     `vol_pos` and `volCoins_good` — two binders the statement already has —
     already produce a `(cen, gammaHat, hgammaHat, ball_subset)`, so the four can
     always be supplied and never obstruct an application.  What they are *not* is
     canonical: `alg:ttc` line 17 computes `ρ = GetPrecision(γ̂)` from `γ̂`, so
     pinning `γ̂` to an arbitrary choice-witness would silently change the
     precision, the lattice, the sampler and the rates of every instance.  Keeping
     `γ̂` an input is what makes the theorem apply to *the* radius the
     implementation found, and is what keeps `Ttc.Box.ttc_volume_box` — the only
     non-vacuity witness — a witness.
4. **The sampling oracle** — `θ, sampD, sampler, theta_eq`.  `sampler` is
   `Ttc.KV97Sampler` (`Sampler/Interface.lean`), **15 fields** — `J`,
   `fintypeJ`, `Amat`, `bvec`, `dilate_eq`, `facetBound`, `one_le_facetBound`,
   `card_le_facetBound`, `contLaw`, `isProbContLaw`, `contVol`, `contVol_pos`,
   `contVol_eq`, `law_tv`, `sampD_eq` — of which all but one are *descriptive*
   (which polytope, which normalisation, what the output law **is**).  The single
   quantitative field is
   `law_tv : ∀ i, Arlib.TVLe (contLaw i)
      (Arlib.uniformOn volume (Arlib.KV97.inflated (Amat i) (bvec i) (cOf ε') facetBound))
      (ENNReal.ofReal (ε' / (4 * contVol i)))`,
   a **total-variation** bound on the continuous draw.  This is the open binder.

   *It is not a pointwise density hypothesis*, and an earlier revision of this
   docstring said otherwise.  The correction matters: a pointwise `(1 ± ε)`
   guarantee is **unattainable** for a real ball-walk sampler, whose law keeps an
   atom from the holding term, and one atom defeats pointwise closeness at every
   tolerance — `⊤` included.  So the TV formulation is not a weakening of
   convenience; it is the only formulation an actual sampler can meet.  See
   `AUDIT-KV97.md` §4b for what that costs on the KV97 side.
5. **The coverage test** — *gone*.  It cost four binders (`cover, memPt,
   memPt_eq, cover_eq`: two decision procedures of the implementation plus their
   specifications) until `Ttc/Exec/Coverage.lean` landed.  `Ttc.coveredOracles`
   now pins `alg:ttc` line 27 to the classical test `Ttc.coverOfRegion`, so
   `cover_eq` is `rfl` and `memPt_eq` is `Ttc.memPtOfRegion_spec`.

   Pinning one procedure would normally narrow the theorem.  `Coverage.lean` §2
   argues it does not — `Ttc.memPt_eq_memPtOfRegion` and
   `Ttc.cover_eq_coverOfRegion` show any admissible pair *is* this one wherever
   the algorithm reads it, and `Ttc.count_dropCovered_trajOracles` shows the free
   values are never read.  **Read the caveat**: that congruence is established at
   the level of the oracle bundle, **not yet at the level of the run** — the
   step-, run-, `runCost`- and `Terminates`-level congruences are drafted but
   unchecked, and `CLAUDE.md` §4 does not admit an unchecked proof.  Until they
   land, "the substitution loses no generality" is supported one level below the
   claim.
6. **`gen_mem`** — `GenerateSamples` returns lattice points of the cube it was
   asked about.  Not derivable: `Ttc.trajOracles`' filler branch pads with
   `Ttc.padPoint`, which is `0` at a cube no enumerated point meets.
   `Ttc.gen_mem_trajOracles` reduces it to "every cube of the decomposition
   contains an enumerated lattice point".
7. **The volume oracle** — `vol, volAlg, volCoins, volED_eq, volCoins_good,
   vol_pos`.  `volCoins_good` is Cousins–Vempala Theorem 1.1 at one good coin;
   `Ttc.volume_estimate_joint` already averages it over the coins at `1 − δ − δ/4`,
   at the cost of stating the conclusion as an iterated integral.  What is missing
   for a construction is `LocalizationHypothesis`
   (`Arlib/Convexity/GaussianCooling/`).
8. **The regime** — `big`, the paper's own `∑ θ ≥ (1−ε')·Thresh/8`.

## The runtime half

It **is** statable over the same constructed space, and is the second conjunct:
`Ttc.runCost` at the same `Ttc.enumOracles … t`, for every trajectory `t`.  Unlike
nfalean's, it is *conditional*: `Ttc.Terminates` is a hypothesis of the conjunct
rather than of the theorem, because the absorption loop's exit is only a
high-probability event and the paper never states it (`Model/Theorem.lean:70`).  It
is quantified inside the conjunct, so it costs the theorem no binder.
-/

namespace Ttc

open MeasureTheory Set

variable {A : Type*} {n : ℕ}

/-! ## The enumeration of `Sol(F) ∩ 𝕃ⁿ`, as a total function of the inputs

`Ttc.HasLatticeEnum`, `Ttc.latticeEnum` and its unconditional injectivity are in
`Model/Pseudocode`: `alg:ttc` line 43's `GenerateSamples` draws from
`Sol(F) ∩ 𝕃ⁿ`, so the enumeration is a step of the algorithm, and `Ttc.ttcRun`
builds its oracle bundle from it, which requires it inside the audit surface.
`Ttc.latticeEnum` is a total function of `(M, φ, ρ)` alone, carrying no proof
argument.

What stays here is everything that is *about* the enumeration rather than part of
it: the two guarded membership properties, read off `Ttc.exists_latticeEnum`'s
`choose_spec`, and the *geometric* input that boundedness of `Sol(F)` is enough to
guard them, via `Ttc.exists_lattice_enum_of_isBounded` (`Exec/Geometry`).
-/

/-- `ptE_mem`: every enumerated point is a solution lattice point, whenever an
enumeration exists at all. -/
theorem latticeEnum_mem {M : A → Set (Space n)} {φ : BForm A} {ρ : ℤ}
    (h : HasLatticeEnum M φ ρ) (s : Fin (latticeCount M φ ρ)) :
    latticeEnum M φ ρ s ∈ sol M φ ∩ fineLattice n (latticeScale ρ) :=
  ((exists_latticeEnum M φ ρ).choose_spec.2 h).1 s

/-- `ptE_onto`: every solution lattice point is enumerated, whenever an enumeration
exists at all. -/
theorem latticeEnum_onto {M : A → Set (Space n)} {φ : BForm A} {ρ : ℤ}
    (h : HasLatticeEnum M φ ρ) :
    ∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, latticeEnum M φ ρ s = x :=
  ((exists_latticeEnum M φ ρ).choose_spec.2 h).2

/-- **Boundedness of `Sol(F)` is enough** — `Ttc.exists_lattice_enum_of_isBounded`,
renamed. -/
theorem hasLatticeEnum_of_isBounded (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ)
    (hb : Bornology.IsBounded (sol M φ)) : HasLatticeEnum M φ ρ :=
  exists_lattice_enum_of_isBounded ρ hb

/-- **The oracle bundle of `alg:ttc`, at the constructed enumeration.**

`Ttc.trajOracles` with its injectivity proof supplied by `Ttc.latticeEnum_injective`
rather than assumed.  A plain function of the data `(M, φ, ρ, vol, cover, memPt)` —
no hypothesis is bundled — which is what keeps the conclusion of `Ttc.ttc_volume` a
closed term. -/
noncomputable def enumOracles (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ)
    (vol : Cube A → ℝ) (cover : Space n → Cube A → Bool)
    (memPt : Cube A → Fin (latticeCount M φ ρ) → Bool)
    (t : ℕ → Fin (latticeCount M φ ρ) → ℕ) : Oracles n (Cube A) :=
  trajOracles (latticeEnum_injective M φ ρ) vol cover memPt t

/-- **The oracle bundle with the coverage test constructed too.**

`Ttc.enumOracles` at the *classical* membership test of `Ttc/Exec/Coverage.lean`:
`Ttc.coverOfRegion M x c := decide (x ∈ region M c)` and its reindexing
`Ttc.memPtOfRegion`.  This removes `alg:ttc` line 27's decision procedure from the
inputs of `Ttc.ttc_volume` — the four binders `cover, memPt, memPt_eq, cover_eq`
become one closed term.

Pinning a *particular* decision procedure would normally narrow the theorem.  It
does not, and `Ttc/Exec/Coverage.lean` §2 is the reason: `Ttc.memPt_eq_memPtOfRegion`
and `Ttc.cover_eq_coverOfRegion` show that any pair satisfying the old
`memPt_eq`/`cover_eq` *is* this one wherever the algorithm reads it, and
`Ttc.count_dropCovered_trajOracles` shows the unconstrained values are never read.
Read the "Not yet in this file" paragraph of that module's docstring before quoting
this as full generality: the congruence is established at the level of the oracle
bundle, **not yet at the level of the run**. -/
noncomputable def coveredOracles (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ)
    (vol : Cube A → ℝ) (t : ℕ → Fin (latticeCount M φ ρ) → ℕ) : Oracles n (Cube A) :=
  enumOracles M φ ρ vol (coverOfRegion M) (memPtOfRegion M (latticeEnum M φ ρ)) t

/-- **`thm:volumettc` + `thm:runtime`, over the algorithm's own inputs.**

`TTC(F, ε, δ)` is run on `F = (atoms, φ)` — the linear atoms and the Boolean
structure over them — at accuracy `ε` and confidence `δ`.  The parameter block, the
precision `ρ`, the normalised count `L`, the lattice enumeration, the probability
space, its law and the oracle bundle are all **computed** here; see the module
docstring for the table and for the 28 residual binders.

* **Accuracy.**  On the constructed space `ℕ → Fin |Sol(F) ∩ 𝕃ⁿ| → ℕ` with the
  constructed law `Ttc.trajLaw θ`, the transcription's output `Ttc.ttcOutput` lies
  in `(1 ± ε)·Vol(F)` with probability at least `1 − δ`.
  `Ttc.VolSolCheck.volSol_eq_lra` rewrites the right-hand side into pure LRA
  syntax: the Lebesgue measure of
  `{x | evalBool (fun a => decide (∑ i, coeff a i * x i ≤ bound a)) φ}`.

* **Running time.**  For **every** trajectory `t` at which the absorption loops
  terminate, the charged cost is at most `m·(cVol + cSample·Thresh)` with `m` the
  cube count of the AllSAT output — `thm:runtime`, on the same space and the same
  sample point as the accuracy half.

Both halves are one application of an existing result:
`Ttc.TtcProb.volume_estimate_traj` and `Ttc.TtcProb.runtime` at
`Ttc.canonicalTtcProb`. -/
theorem ttc_volume
    -- the algorithm's inputs
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    -- the FPRAS parameter range, and the ambient dimension
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    -- definitional: the atoms denote closed half-spaces
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    -- `alg:ttc` line 16, the circuit-AllSAT call, and what it is assumed to deliver
    (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    -- the decomposition is nonempty and has a facet (`Ttc.one_le_card_cubes/_facets`)
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    -- definitional: the parameter block of `alg:ttc` lines 12–20, computed
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    -- the two input conditions the geometry needs: `Sol(F)` is bounded, and no atom
    -- occurring in the decomposition has a zero normal vector
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    -- the inscribed ball `alg:ttc` line 17 reads `γ̂` off; always available, by
    -- `Ttc.exists_inscribed_ball_of_vol_pos`, from `vol_pos` and `volCoins_good`
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    -- the volume oracle `Vol_ED` (`alg:ttc` line 24)
    (vol : Cube A → ℝ) (volAlg : VolumeAlgorithm n) (volCoins : volAlg.Ω)
    (volED_eq : ∀ (i : Cube A) (hi : i ∈ toDNF φ), vol i =
      gammaHat ^ n * volAlg.est (roundBody (cen ⟨i, hi⟩) gammaHat (region M i))
        P.epsPrime P.deltaPrime volCoins)
    (volCoins_good : ∀ i ∈ toDNF φ, vol i ∈ relErr P.epsPrime (volume (region M i)).toReal)
    (vol_pos : ∀ i ∈ toDNF φ, 0 < vol i)
    -- the sampling oracle `GenerateSamples` (`alg:ttc` line 43)
    (θ : Fin (latticeCount M φ (P.precision gammaHat)) → ℝ) (sampD : Cube A → Space n → ℝ)
    (sampler : KV97Sampler A n M (toDNF φ) (P.precision gammaHat) P.epsPrime sampD)
    (theta_eq : ∀ s, ∃ i, i ∈ toDNF φ ∧
      latticeEnum M φ (P.precision gammaHat) s ∈ region M i ∧
      θ s = sampD i (latticeEnum M φ (P.precision gammaHat) s) * vol i)
    -- the coverage test is CONSTRUCTED, not assumed: `Ttc.coveredOracles` pins
    -- `alg:ttc` line 27 to `Ttc.coverOfRegion`, which cost four binders before
    -- `GenerateSamples` returns lattice points of the cube it was asked about
    (gen_mem : ∀ (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ)
        (i : Cube A) (j N : ℕ), i ∈ toDNF φ →
      ∀ s ∈ (coveredOracles M φ (P.precision gammaHat) vol t).gen i j N
          (P.precision gammaHat),
        s ∈ region M i ∩ fineLattice n (latticeScale (P.precision gammaHat)))
    -- the instance is in the paper's regime
    (big : (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ s) :
    -- (accuracy) on the constructed space, the transcription's output is within
    -- `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤ (trajLaw θ
        {t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ |
          ttcOutput P (coveredOracles M φ (P.precision gammaHat) vol) toDNF
              (P.precision gammaHat) φ t
            ∈ relErr ε (volSol M φ)}).toReal)
    ∧
    -- (running time) at every trajectory whose absorption loops exit, the charged
    -- cost is `m·(cVol + cSample·Thresh)`
    (∀ (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles M φ (P.precision gammaHat) vol t) (toDNF φ) →
      runCost P (coveredOracles M φ (P.precision gammaHat) vol t) cVol cSample
          (P.precision gammaHat) (toDNF φ)
        ≤ (toDNF φ).length * (cVol + cSample * thr)) := by
  subst M_eq
  subst hP
  have hle : HasLatticeEnum (fun a => (atoms a).halfspace) φ
      ((ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr).precision gammaHat) :=
    hasLatticeEnum_of_isBounded _ _ _ hbdd
  set T := canonicalTtcProb ε δ hε0 hε1 hδ0 hδ1 atoms φ toDNF isDNF isPositive
    (ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr) rfl rfl rfl
    (ttcParams_cubes_le (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (ttcParams_facets_le (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (normal_ne_zero_of_coeff_ne_zero hcoeff) cen gammaHat hgammaHat ball_subset
    (volume_region_ne_top_of_isBounded isDNF hbdd)
    ((ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr).precision gammaHat) rfl
    (normalisedCount (fun a => (atoms a).halfspace) φ
      ((ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr).precision gammaHat)) rfl
    (latticeCount (fun a => (atoms a).halfspace) φ
      ((ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr).precision gammaHat))
    (latticeEnum (fun a => (atoms a).halfspace) φ
      ((ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr).precision gammaHat))
    (latticeEnum_injective _ _ _) (fun s => latticeEnum_mem hle s) (latticeEnum_onto hle)
    θ vol sampD sampler theta_eq
    (coverOfRegion (fun a => (atoms a).halfspace))
    (memPtOfRegion (fun a => (atoms a).halfspace)
      (latticeEnum (fun a => (atoms a).halfspace) φ
        ((ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr).precision gammaHat)))
    (memPtOfRegion_spec _ _ _)
    (fun s i => coverOfRegion_memPtOfRegion _ _ s i)
    gen_mem volAlg volCoins volED_eq volCoins_good vol_pos big with hT
  exact ⟨T.volume_estimate_traj,
    fun t cVol cSample thr hthr hterm => T.runtime (ω := t) cVol cSample thr hthr hterm⟩

/-- **The same guarantee with the AllSAT call pinned to `Ttc.toDNF`.**

`Ttc.ttc_volume` keeps the converter as an input because `thm:runtime`'s `m` is the
optimised procedure's cube count (`Model/Pseudocode.lean:195`).  Pinning it to the
development's own converter discharges `isDNF` outright (`Ttc.toDNF_isDNFOf`) and
reduces `isPositive` to a condition on the *input formula* (`Ttc.toDNF_isPositive`):
two residual binders become one, and that one is about `φ` rather than about an
external tool. -/
theorem ttc_volume_toDNF
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (hφ : φ.IsPositive)
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (vol : Cube A → ℝ) (volAlg : VolumeAlgorithm n) (volCoins : volAlg.Ω)
    (volED_eq : ∀ (i : Cube A) (hi : i ∈ toDNF φ), vol i =
      gammaHat ^ n * volAlg.est (roundBody (cen ⟨i, hi⟩) gammaHat (region M i))
        P.epsPrime P.deltaPrime volCoins)
    (volCoins_good : ∀ i ∈ toDNF φ, vol i ∈ relErr P.epsPrime (volume (region M i)).toReal)
    (vol_pos : ∀ i ∈ toDNF φ, 0 < vol i)
    (θ : Fin (latticeCount M φ (P.precision gammaHat)) → ℝ) (sampD : Cube A → Space n → ℝ)
    (sampler : KV97Sampler A n M (toDNF φ) (P.precision gammaHat) P.epsPrime sampD)
    (theta_eq : ∀ s, ∃ i, i ∈ toDNF φ ∧
      latticeEnum M φ (P.precision gammaHat) s ∈ region M i ∧
      θ s = sampD i (latticeEnum M φ (P.precision gammaHat) s) * vol i)
    (gen_mem : ∀ (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ)
        (i : Cube A) (j N : ℕ), i ∈ toDNF φ →
      ∀ s ∈ (coveredOracles M φ (P.precision gammaHat) vol t).gen i j N
          (P.precision gammaHat),
        s ∈ region M i ∩ fineLattice n (latticeScale (P.precision gammaHat)))
    (big : (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ s) :
    (1 - δ ≤ (trajLaw θ
        {t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ |
          ttcOutput P (coveredOracles M φ (P.precision gammaHat) vol) toDNF
              (P.precision gammaHat) φ t
            ∈ relErr ε (volSol M φ)}).toReal)
    ∧
    (∀ (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles M φ (P.precision gammaHat) vol t) (toDNF φ) →
      runCost P (coveredOracles M φ (P.precision gammaHat) vol t) cVol cSample
          (P.precision gammaHat) (toDNF φ)
        ≤ (toDNF φ).length * (cVol + cSample * thr)) :=
  ttc_volume atoms φ ε δ hε0 hε1 hδ0 hδ1 hn M M_eq toDNF (toDNF_isDNFOf φ)
    (toDNF_isPositive hφ) hm hr P hP hbdd hcoeff cen gammaHat hgammaHat ball_subset
    vol volAlg volCoins volED_eq volCoins_good vol_pos θ sampD sampler theta_eq
    gen_mem big

/-! ## Non-vacuity: the 28 residual binders are jointly satisfiable

A theorem with 32 hypotheses is worthless if they cannot all hold at once
(`CLAUDE.md` §11).  `Ttc.TtcProb.volume_estimate`'s guard is `Ttc.Box.nonempty_ttcProb`;
`Ttc.ttc_volume` needs its own, because it asks for two things `Ttc.TtcProb` does
not: `hP`, pinning the parameter block to the *computed* one, and the enumeration
pinned to `Ttc.latticeEnum`.  The box's `Ttc.Box.par` stores `m = max 1 (…)` and
`r = max 1 (…)` rather than the bare counts, so the two blocks are equal only once
the DNF is known nonempty — which it is; and the box's own enumeration
`Ttc.Box.pt : Fin (Lidx n hn) → Space n` has to be replaced by the canonical one at
`Fin (latticeCount …)`, which is what `Ttc.Box.thC` and the lemmas around it are
for.  Both index types have the same cardinality (`Ttc.Box.latticeCount_eq_Lidx`),
and the box's rates and coverage test are *constant* functions, so the transport is
a restatement rather than a `cast`.

`Ttc.Box.ttc_volume_box` below is `Ttc.ttc_volume` applied to the box's own data.
Its *statement* is uninformative (the box runs at `ε = δ = 1`, where `1 − δ = 0`);
its *proof* is the content, and that the application elaborates is exactly the
satisfiability check. -/

/-- Two parameter blocks with equal data fields are equal; the five `Prop` fields
match by proof irrelevance. -/
theorem params_eq {P Q : Params} (hε : P.ε = Q.ε) (hδ : P.δ = Q.δ) (hdim : P.n = Q.n)
    (hm : P.m = Q.m) (hr : P.r = Q.r) : P = Q := by
  cases P; cases Q; subst_vars; rfl

namespace Box

variable {n : ℕ}

/-- **The box's parameter block is the computed one.**  `Ttc.Box.par`'s `max 1 (…)`
guards are redundant once the DNF has a cube and that cube has a literal. -/
theorem par_eq_ttcParams (n : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ Nat.card {c : Cube (Fin n ⊕ Fin n) // c ∈ Ttc.toDNF (boxForm n hn)})
    (hr : 1 ≤ Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))) :
    par n hn = ttcParams (Ttc.toDNF (boxForm n hn)) n 1 1 one_pos le_rfl hn hm hr := by
  refine params_eq rfl rfl rfl ?_ ?_
  · show max 1 (Nat.card {c : Cube (Fin n ⊕ Fin n) // c ∈ boxDNF n})
      = Nat.card {c : Cube (Fin n ⊕ Fin n) // c ∈ Ttc.toDNF (boxForm n hn)}
    rw [toDNF_boxForm hn] at hm ⊢
    exact max_eq_right hm
  · show max 1 (Nat.card (FacetIndex (boxDNF n)) : ℝ)
      = (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn))) : ℝ)
    rw [toDNF_boxForm hn] at hr ⊢
    exact max_eq_right (by exact_mod_cast hr)

/-- The box's DNF has a cube. -/
theorem one_le_card_cubes_box (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ Nat.card {c : Cube (Fin n ⊕ Fin n) // c ∈ Ttc.toDNF (boxForm n hn)} :=
  one_le_card_cubes (c := boxCube n) (by rw [toDNF_boxForm hn]; exact List.mem_singleton_self _)

/-- The box's cube has a literal — every atom occurs in it. -/
theorem one_le_card_facets_box (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn))) :=
  one_le_card_facets (c := boxCube n)
    (by rw [toDNF_boxForm hn]; exact List.mem_singleton_self _)
    (l := ⟨Sum.inl ⟨0, hn⟩, true⟩) (mem_boxCube _)

/-! ### `hbdd`: the box is bounded

`Ttc.volume_box_ne_top` already contains the containment
`[0,c]ⁿ ⊆ closedBall 0 √(n·c²)`; boundedness is that containment without the
measure step. -/

/-- **The box is a bounded set.**  It sits inside the closed ball of radius
`√(n·c²)` about the origin. -/
theorem isBounded_box (n : ℕ) (c : ℝ) :
    Bornology.IsBounded {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} := by
  have hsub : {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c}
      ⊆ Metric.closedBall (0 : Space n) (Real.sqrt (n * c ^ 2)) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin n, c ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hx i
          rw [Real.norm_eq_abs, abs_of_nonneg h.1]
          nlinarith [h.1, h.2]
      _ = n * c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact Metric.isBounded_closedBall.subset hsub

/-- **`Ttc.ttc_volume`'s `hbdd`, for the box.** -/
theorem isBounded_sol_box (n : ℕ) (hn : 1 ≤ n) :
    Bornology.IsBounded (sol (fun a => (atm n hn a).halfspace) (boxForm n hn)) := by
  rw [sol_eq_bx hn]
  exact isBounded_box n (side n hn)

theorem hasLatticeEnum_box (n : ℕ) (hn : 1 ≤ n) :
    HasLatticeEnum (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) :=
  hasLatticeEnum_of_isBounded _ _ _ (isBounded_sol_box n hn)

/-- **The canonical enumeration lands in the box**, at every index. -/
theorem latticeEnum_mem_bx (n : ℕ) (hn : 1 ≤ n)
    (s : Fin (latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn))) :
    latticeEnum (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) s ∈ bx n hn := by
  have h := (latticeEnum_mem (hasLatticeEnum_box n hn) s).1
  rwa [sol_eq_bx hn] at h

/-- The count of the box's lattice points, as a `ℕ`. -/
theorem latticeCount_eq_Lidx (n : ℕ) (hn : 1 ≤ n) :
    latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) = Lidx n hn := by
  exact_mod_cast (Lidx_eq_count hn).symm

theorem latticeCount_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) := by
  rw [latticeCount_eq_Lidx n hn]; exact Lidx_pos hn

/-! ### The rates and the coverage test, at the canonical index type

`Ttc.Box.th` and `Ttc.Box.mm` are indexed by `Fin (Ttc.Box.Lidx n hn)`;
`Ttc.ttc_volume` asks for `Fin (latticeCount …)`.  The two are equal
(`Ttc.Box.latticeCount_eq_Lidx`) but not definitionally — and both box objects are
*constant* functions, so the cleanest transport is to restate them at the canonical
index type rather than to `cast`. -/

/-- The box's level-`0` rate, indexed by the canonical enumeration.  Same value as
`Ttc.Box.th`: the sampler's uniform mass times the exact volume. -/
noncomputable def thC (n : ℕ) (hn : 1 ≤ n) :
    Fin (latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)) → ℝ :=
  fun _ => 1 / ((bx n hn ∩ fineLattice n (latticeScale (rho n hn))).ncard : ℝ)
    * (volume (bx n hn)).toReal

/-- The box's cube-membership test, indexed by the canonical enumeration.  Same
value as `Ttc.Box.mm`: the single cube covers everything. -/
def mmC (n : ℕ) (hn : 1 ≤ n) : Cube (Fin n ⊕ Fin n) →
    Fin (latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)) → Bool :=
  fun _ _ => true

theorem sum_thC (n : ℕ) (hn : 1 ≤ n) : ∑ s, thC n hn s = (volume (bx n hn)).toReal := by
  have hL : (Lidx n hn : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Lidx_pos hn).ne'
  simp only [thC, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    latticeCount_eq_Lidx n hn]
  rw [ncard_lat hn]
  field_simp

/-- The single cube's region is the box. -/
theorem region_boxCube_eq (n : ℕ) (hn : 1 ≤ n) :
    region (fun a => (atm n hn a).halfspace) (boxCube n) = bx n hn := by
  simp only [atm]
  exact region_boxCube n (side n hn)

theorem region_eq_bx_of_mem (n : ℕ) (hn : 1 ≤ n) {i : Cube (Fin n ⊕ Fin n)}
    (hi : i ∈ Ttc.toDNF (boxForm n hn)) :
    region (fun a => (atm n hn a).halfspace) i = bx n hn := by
  have hi' : i ∈ boxDNF n := by rwa [toDNF_boxForm hn] at hi
  rw [eq_boxCube hi']
  exact region_boxCube_eq n hn

/-- **`Ttc.ttc_volume`'s `theta_eq`, for the box** — at the *canonical* enumeration.
The box's sampler mass is constant in the point, so nothing depends on which
enumeration is used. -/
theorem theta_eq_box (n : ℕ) (hn : 1 ≤ n)
    (s : Fin (latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn))) :
    ∃ i, i ∈ Ttc.toDNF (boxForm n hn) ∧
      latticeEnum (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) s
        ∈ region (fun a => (atm n hn a).halfspace) i ∧
      thC n hn s = smp n hn i
        (latticeEnum (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) s)
        * vl n hn i := by
  refine ⟨boxCube n, by rw [toDNF_boxForm hn]; exact List.mem_singleton_self _, ?_, ?_⟩
  · rw [region_boxCube_eq n hn]
    exact latticeEnum_mem_bx n hn s
  · simp only [thC, smp, vl, region_boxCube_eq n hn]

/-- **`Ttc.ttc_volume`'s `memPt_eq`, for the box.**  Every enumerated point lies in
the single cube, so the constant-`true` test is correct. -/
theorem memPt_eq_box (n : ℕ) (hn : 1 ≤ n) :
    ∀ i ∈ Ttc.toDNF (boxForm n hn), ∀ s, mmC n hn i s = true ↔
      latticeEnum (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) s
        ∈ region (fun a => (atm n hn a).halfspace) i := by
  intro i hi s
  rw [region_eq_bx_of_mem n hn hi]
  exact ⟨fun _ => latticeEnum_mem_bx n hn s, fun _ => rfl⟩

/-- **`Ttc.ttc_volume`'s `cover_eq`, for the box** — both tests are constant. -/
theorem cover_eq_box (n : ℕ) (hn : 1 ≤ n)
    (s : Fin (latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)))
    (i : Cube (Fin n ⊕ Fin n)) :
    cov n (latticeEnum (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) s) i
      = mmC n hn i s := rfl

/-- **`Ttc.ttc_volume`'s `gen_mem`, for the box.**  Every point the oracle bundle
hands back is an enumerated lattice point of the box — `Ttc.gen_mem_trajOracles`,
whose filler branch is safe because the box's cube is met by every enumerated
point. -/
theorem gen_mem_box (n : ℕ) (hn : 1 ≤ n)
    (t : ℕ → Fin (latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)) → ℕ)
    (i : Cube (Fin n ⊕ Fin n)) (j N : ℕ) (hi : i ∈ Ttc.toDNF (boxForm n hn)) :
    ∀ s ∈ (coveredOracles (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)
        (vl n hn) t).gen i j N (rho n hn),
      s ∈ region (fun a => (atm n hn a).halfspace) i
        ∩ fineLattice n (latticeScale (rho n hn)) := by
  have hmem : ∀ (c : Cube (Fin n ⊕ Fin n))
      (s : Fin (latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn))),
      memPtOfRegion (fun a => (atm n hn a).halfspace)
          (latticeEnum (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)) c s = true →
      latticeEnum (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) s
        ∈ bx n hn ∩ fineLattice n (latticeScale (rho n hn)) :=
    fun _ s _ => ⟨latticeEnum_mem_bx n hn s, (latticeEnum_mem (hasLatticeEnum_box n hn) s).2⟩
  have hne : ∃ s, memPtOfRegion (fun a => (atm n hn a).halfspace)
      (latticeEnum (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)) i s = true :=
    ⟨⟨0, latticeCount_pos n hn⟩,
      (memPtOfRegion_eq_true _ _ _ _).2
        (by rw [region_eq_bx_of_mem n hn hi]; exact latticeEnum_mem_bx n hn _)⟩
  intro x hx
  rw [region_eq_bx_of_mem n hn hi]
  exact gen_mem_trajOracles
    (T := fun _ => bx n hn ∩ fineLattice n (latticeScale (rho n hn)))
    (latticeEnum_injective _ _ _) t hmem hne j N (rho n hn) x hx

/-- **`Ttc.ttc_volume`'s hypotheses are satisfiable.**  The witness is the unit-box
instance of `Ttc/Witness/BoxProb.lean`: an axis-aligned box, its one-cube DNF, the
exact volume oracle, and the Kannan–Vempala sampler — with the enumeration replaced
by the canonical one `Ttc.ttc_volume` computes.  The proof is the 40-argument
application; the conclusion it produces is recorded here so that the reader can see
*which* instance of `Ttc.ttc_volume` was checked.

The box runs at `ε = δ = 1`, so `1 − δ = 0` and the accuracy half is trivially
true as a *statement* — non-vacuity is about the hypotheses, not the conclusion. -/
theorem ttc_volume_box (n : ℕ) (hn : 1 ≤ n) :
    ((1 : ℝ) - 1 ≤ (trajLaw (thC n hn)
        {t : ℕ → Fin (latticeCount (fun a => (atm n hn a).halfspace)
            (boxForm n hn) (rho n hn)) → ℕ |
          ttcOutput (par n hn)
              (coveredOracles (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)
                (vl n hn))
              Ttc.toDNF (rho n hn) (boxForm n hn) t
            ∈ relErr 1 (volSol (fun a => (atm n hn a).halfspace) (boxForm n hn))}).toReal)
    ∧
    (∀ (t : ℕ → Fin (latticeCount (fun a => (atm n hn a).halfspace)
        (boxForm n hn) (rho n hn)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = (par n hn).thresh →
      Terminates (par n hn)
          (coveredOracles (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)
            (vl n hn) t)
          (Ttc.toDNF (boxForm n hn)) →
      runCost (par n hn)
          (coveredOracles (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)
            (vl n hn) t)
          cVol cSample (rho n hn) (Ttc.toDNF (boxForm n hn))
        ≤ (Ttc.toDNF (boxForm n hn)).length * (cVol + cSample * thr)) :=
  ttc_volume (atm n hn) (boxForm n hn) 1 1 one_pos le_rfl one_pos le_rfl hn
    (fun a => (atm n hn a).halfspace) rfl Ttc.toDNF
    (boxProb n hn).isDNF (boxProb n hn).isPositive
    (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)
    (par n hn) (par_eq_ttcParams n hn (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn))
    (isBounded_sol_box n hn)
    (coeff_ne_zero_of_normal_ne_zero (boxProb n hn).normal_ne_zero)
    (fun _ => boxCentre n (side n hn)) (gam n hn) (gam_pos hn) (boxProb n hn).ball_subset
    (vl n hn) (VolumeAlgorithm.exact n) () (boxProb n hn).volED_eq
    (boxProb n hn).volCoins_good (boxProb n hn).vol_pos
    (thC n hn) (smp n hn) (boxProb n hn).sampler (theta_eq_box n hn)
    (fun t i j N hi => gen_mem_box n hn t i j N hi)
    -- `big`, as a *term*: the goal's index type is `Fin (latticeCount … ((par n hn).precision
    -- (gam n hn)))` while `Ttc.Box.sum_thC` is stated at `Ttc.Box.rho n hn`.  The two are
    -- definitionally equal (`rho` unfolds to exactly that) but not syntactically, so `rw`
    -- cannot see the pattern; a term is checked up to defeq and goes through.
    ((epsPrime_thresh_le_volume hn).trans (sum_thC n hn).ge)

end Box

/-! ## Axiom profile

Every declaration of this file, and every result it rests on, checked transitively
(`CLAUDE.md` §4). Expect `[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms ttc_volume
#print axioms Box.ttc_volume_box
#print axioms Box.par_eq_ttcParams
#print axioms ttc_volume_toDNF

-- the constructions this file adds
#print axioms latticeEnum
#print axioms latticeEnum_injective
#print axioms latticeEnum_mem
#print axioms latticeEnum_onto
#print axioms hasLatticeEnum_of_isBounded
#print axioms enumOracles

-- the materials
#print axioms ttcParams
#print axioms ttcParams_cubes_le
#print axioms ttcParams_facets_le
#print axioms one_le_card_cubes
#print axioms one_le_card_facets
#print axioms canonicalTtcProb
#print axioms Box.boxProb_eq_canonical
#print axioms TtcProb.volume_estimate
#print axioms TtcProb.volume_estimate_traj
#print axioms TtcProb.runtime
#print axioms volume_estimate_joint
#print axioms volume_estimate_joint_compProd
#print axioms Ttc.VolSolCheck.volSol_eq_lra
#print axioms Ttc.VolSolCheck.measurableSet_sol_lra
#print axioms toDNF_isDNFOf
#print axioms toDNF_isPositive
#print axioms exists_inscribed_ball_of_vol_pos
#print axioms exists_lattice_enum_of_isBounded
#print axioms volume_region_ne_top_of_isBounded
#print axioms normal_ne_zero_of_coeff_ne_zero

end Ttc

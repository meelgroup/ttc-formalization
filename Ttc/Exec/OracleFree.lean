/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.EndToEnd

/-!
# `Exec/OracleFree`: `Ttc.TtcProb` built from the algorithm's inputs alone

`Ttc.canonicalTtcProb` (`Exec/Canonical`) already fills ten fields of
`Ttc.TtcProb` by construction — the probability space `Ω`, its σ-algebra, its law
`Ttc.trajLaw θ`, `isProb`, the oracle bundle `O = Ttc.trajOracles`, `toTraj = id`,
`toTraj_meas`, `law_eq`, `oracle_eq`, and `M`/`M_eq`.  What it still *takes* is the
volume oracle (`volAlg`, `volCoins`, `vol`, `volED_eq`, `volCoins_good`,
`vol_pos`), the sampler (`sampD`, `sampler`), the rates (`θ`, `theta_eq`), the
precision (`ρ`, `rho_eq`), the enumeration (`Lidx`, `ptE`, …) and the coverage test
(`cover`, `memPt`, …).

This file is the **thin remaining layer**: `Ttc.ttcProbOfInputs` is
`Ttc.canonicalTtcProb` with every one of those supplied from a construction that
already exists in the development.  It is not a second constructor — it calls the
canonical one, so all ten canonical fields are inherited verbatim, and
`Ttc.Box.boxProb_eq_canonical` remains the faithfulness check for them.

## What is supplied, and by what

| Field | Supplied from |
| --- | --- |
| `Ω`, `mΩ`, `μ`, `isProb`, `O`, `toTraj`, `toTraj_meas`, `law_eq`, `oracle_eq`, `M`, `M_eq` | `Ttc.canonicalTtcProb` (unchanged) |
| `ρ` | `P.precision γ̂` — **`GetPrecision` itself** (`alg:prec` line 91) |
| `rho_eq` | `rfl` |
| `L` | `Ttc.normalisedCount` at that `ρ`; `L_eq` is `rfl` |
| `Lidx`, `ptE` | `Ttc.latticeCount`, `Ttc.latticeEnum` |
| `ptE_inj`, `ptE_mem`, `ptE_onto` | `Ttc.latticeEnum_injective`, `Ttc.latticeEnum_mem`, `Ttc.latticeEnum_onto`, the last two through `Ttc.hasLatticeEnum_of_isBounded` |
| `volAlg` | `Ttc.VolumeAlgorithm.monteCarlo n` — **no hypotheses** |
| `volCoins` | the supplied coin draw `c : ℕ → Space n` |
| `vol` | `Ttc.mcVol` — the oracle's own output at `c` |
| `volED_eq` | `Ttc.mcVol_eq` |
| `volCoins_good` | `Ttc.mcVol_mem_relErr`, from `hc : c ∈ Ttc.mcGood …` |
| `vol_pos` | `Ttc.mcVol_pos` |
| `sampD` | `Ttc.e2eSampD` — the rounding law of the lazy ball walk |
| `sampler` | `Ttc.e2eSampler`, whose `law_tv` is a **theorem** (`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`) |
| `θ` | `Ttc.rates` |
| `theta_eq` | `Ttc.theta_eq_rates` |
| `cover`, `memPt` | `Ttc.coverOfRegion`, `Ttc.memPtOfRegion` |
| `memPt_eq`, `cover_eq` | `Ttc.memPtOfRegion_spec`, `Ttc.coverOfRegion_memPtOfRegion` |
| `gen_mem` | `Ttc.gen_mem_of_geometry` |
| `normal_ne_zero` | `Ttc.normal_ne_zero_of_coeff_ne_zero` |
| `volume_ne_top` | `Ttc.volume_region_ne_top_of_isBounded` |
| `eps_eq`, `delta_eq`, `dim_eq`, `cubes_le`, `facets_le` | `Ttc.ttcParams…`, through `hP` |

## What is **not** supplied, and why

Three groups of arguments survive; none of them is an oracle.

* **`ε`, `δ`, `atoms`, `φ`, `toDNF`, `cen`, `γ̂`, `P`** — the algorithm's inputs and
  the parameter block it computes, plus the input conditions on them (`isDNF`,
  `isPositive`, `hm`, `hr`, `hP`, `hbdd`, `hcoeff`, `hgammaHat`, `ball_subset`).
* **`Jt`, `Am`, `bv`, `hdil`, `rfac`, `hr1`, `hcard`, `Dm`, `hDbody`** — a linear
  description of the *dilated input polytopes* and a diameter bound for the bodies
  it describes.  These are what `Ttc.kv97SamplerOfBody` needs in place of an
  accuracy assumption; `hdil` with `hDbody` forces the described bodies to be
  bounded supersets of the dilated regions, so the trivial `Am = 0` does not
  satisfy them.  This is the same trade `Ttc.ttc_volume_endToEnd` already makes.
* **`c`, `hc`, `big`** — a draw of the volume oracle's coins together with the
  statement that those coins landed in the good event, and the regime condition.
  `hc` is *not* an oracle: `Ttc.mcGood` is an explicitly constructed event of the
  constructed oracle's own coin law, `Ttc.exists_mcGood_coin` below shows it is
  inhabited from the same inputs, and `Ttc.measure_mcGood_ge` bounds its
  probability by `1 − δ/4`.  A single coin has to be fixed because `TtcProb.vol`
  is a field, not a random variable (see `Ttc.TtcProb.volCoins`'s own docstring);
  `Ttc.ttc_volume_monteCarlo` is the statement in which it is integrated out.

**`law_eq` and `oracle_eq` stay**, discharged canonically but as *modelling*
judgements: they say the algorithm's randomness **is** the coupled Poisson /
thinning family of `Coupling/Family`.  That is a description of the algorithm, not
an oracle, and it should not be removed.

## Costs, honestly

The `volAlg` supplied is `Ttc.VolumeAlgorithm.monteCarlo`: hit-and-miss Monte Carlo
whose sample count `Ttc.MonteCarlo.nSamp` is `⌈scale²/(ε²·pf)⌉`-many draws with
`scale` proportional to `rad K ^ n / Vol(B₁)`, i.e. **exponential in `n`**; it is
*not* Cousins–Vempala Theorem 1.1.  The `sampler` supplied is a lazy ball walk run
for `Ttc.mixSteps` steps, also exponential in `n`.  So `ttcProbOfInputs` delivers
the *accuracy* guarantee (`Ttc.TtcProb.volume_estimate_traj`: probability
`≥ 1 − δ`, at a coin the volume oracle got right, whose own probability is
`≥ 1 − δ/4` by `Ttc.measure_mcGood_ge`) and the *charged* running time
(`Ttc.TtcProb.runtime`: `m·(cVol + cSample·Thresh)` oracle calls) — **not** a
polynomial-time claim.  Nor is it claimed that the finite-time ball-walk iterate
differs from the uniform law on the inflated body.

## Non-vacuity

`Ttc.Box.exists_two_ttcProbOfInputs` exhibits **two** instances of
`Ttc.ttcProbOfInputs` on the box `[0,c]ⁿ`, at `(ε, δ) = (1/2, 1/2)` and
`(1/4, 1/4)`, and proves inside the statement that each one's own accuracy bound is
a **strictly positive** probability (`0 < (trajLaw θ {good}).toReal`, values `1/2`
and `3/4`), and that the two differ in `ε` and in `δ`.
-/

namespace Ttc

open MeasureTheory Pointwise

section OracleFree

variable {A : Type*} {n : ℕ}

/-! ## 1. The good coins are inhabited

`Ttc.ttcProbOfInputs` fixes one draw of the volume oracle's coins, and asks that
the draw landed in `Ttc.mcGood`.  That is not a hidden oracle: the event is
inhabited, from the very same inputs, because its probability is at least
`1 − δ/4 ≥ 3/4 > 0`. -/

/-- **A good coin exists.**  `Ttc.measure_mcGood_ge` gives the good event
probability `≥ 1 − δ/4`, which is positive for `δ ≤ 1`; a null-measure set cannot
have positive measure, so the event is nonempty. -/
theorem exists_mcGood_coin (atoms : A → LinAtom n) (φ : BForm A) {D : DNF A}
    (hD : IsDNFOf D φ) (P : Params) {δ : ℝ} (delta_eq : P.δ = δ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {gammaHat : ℝ} (hgammaHat : 0 < gammaHat)
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ))
    (cen : {c : Cube A // c ∈ D} → Space n)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (hlen : (D.length : ℝ) ≤ P.m) :
    ∃ c : ℕ → Space n, c ∈ mcGood (fun a => (atoms a).halfspace) D cen gammaHat
      P.epsPrime P.deltaPrime := by
  classical
  have hfin : ∀ i : {c : Cube A // c ∈ D},
      volume (region (fun a => (atoms a).halfspace) i.val) ≠ ⊤ :=
    volume_region_ne_top_of_isBounded hD hbdd
  have hconv : ∀ i : {c : Cube A // c ∈ D},
      Convex ℝ (region (fun a => (atoms a).halfspace) i.val) :=
    fun i => convex_region atoms _
  have hmeas := measure_mcGood_ge (fun a => (atoms a).halfspace) D P delta_eq hδ0 hδ1
    hgammaHat cen ball_subset hconv hfin hlen
  rcases Set.eq_empty_or_nonempty
      (mcGood (fun a => (atoms a).halfspace) D cen gammaHat P.epsPrime P.deltaPrime) with
    h | h
  · rw [h, measure_empty] at hmeas
    simp only [ENNReal.toReal_zero] at hmeas
    linarith
  · exact h

/-! ## 2. The constructor -/

/-- **`Ttc.TtcProb`, from the algorithm's inputs alone.**

`Ttc.canonicalTtcProb` with the volume oracle, the sampler, the rates, the
precision, the enumeration and the coverage test all **supplied from
constructions** rather than taken as arguments.  See the module docstring for the
field-by-field table and for what is *not* supplied.

No argument is an oracle.  In particular there is no `volAlg`, no `vol`, no
`volED_eq`, no `volCoins_good`, no `vol_pos`, no `sampD`, no `sampler`, no `θ`, no
`theta_eq`, no `gen_mem`, no `ρ` and no `rho_eq`: each is filled from
`Ttc.VolumeAlgorithm.monteCarlo`, `Ttc.mcVol`, `Ttc.e2eSampD`/`Ttc.e2eSampler`,
`Ttc.rates`, `Ttc.gen_mem_of_geometry` and `P.precision γ̂` respectively.

**Costs.**  The `volAlg` is hit-and-miss Monte Carlo — sample count exponential in
`n`, *not* Cousins–Vempala Theorem 1.1 — and the sampler is a lazy ball walk run
for `Ttc.mixSteps` steps, also exponential in `n`.  What the resulting bundle
delivers is `Ttc.TtcProb.volume_estimate_traj` (accuracy `1 ± ε` with probability
`≥ 1 − δ` on the constructed trajectory space, conditional on the coin `c` being
good, which happens with probability `≥ 1 − δ/4`) and `Ttc.TtcProb.runtime` (the
charged cost `m·(cVol + cSample·Thresh)`).  Neither is a polynomial-time claim. -/
noncomputable def ttcProbOfInputs
    -- the algorithm's inputs
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    -- the FPRAS parameter range, and the ambient dimension
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    -- `alg:ttc` line 16, the circuit-AllSAT call, and what it is assumed to deliver
    (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    -- definitional: the parameter block of `alg:ttc` lines 12–20, computed
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    -- the two input conditions the geometry needs
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    -- the inscribed ball `alg:ttc` line 17 reads `γ̂` off
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    -- a linear description of the dilated input polytopes, and a diameter bound for it
    (Jt : Type) [Fintype Jt]
    (Am : {c : Cube A // c ∈ toDNF φ} → Jt → Space n)
    (bv : {c : Cube A // c ∈ toDNF φ} → Jt → ℝ)
    (hdil : ∀ i, latticeScale (P.precision gammaHat)
      • region (fun a => (atoms a).halfspace) i.val ⊆ Arlib.Polytope.body (Am i) (bv i))
    (rfac : ℝ) (hr1 : 1 ≤ rfac) (hcard : (Fintype.card Jt : ℝ) ≤ rfac)
    (Dm : {c : Cube A // c ∈ toDNF φ} → ℝ)
    (hDbody : ∀ i, ∀ x ∈ Arlib.Polytope.body (Am i) (bv i),
      ∀ y ∈ Arlib.Polytope.body (Am i) (bv i), dist x y ≤ Dm i)
    -- a draw of the *constructed* volume oracle's coins, landing in its good event
    (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
      P.epsPrime P.deltaPrime)
    -- the instance is in the paper's regime, at the constructed rates
    (big : (1 - P.epsPrime) * P.thresh / 8
      ≤ ∑ s, rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
          (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
            P.epsPrime rfac Am bv cen gammaHat Dm)
          (mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
            P.epsPrime P.deltaPrime c) s) :
    TtcProb A n :=
  canonicalTtcProb ε δ hε0 hε1 hδ0 hδ1 atoms φ toDNF isDNF isPositive P
    (by rw [hP]; rfl) (by rw [hP]; rfl) (by rw [hP]; rfl)
    (by rw [hP]; exact ttcParams_cubes_le (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (by rw [hP]; exact ttcParams_facets_le (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (normal_ne_zero_of_coeff_ne_zero hcoeff)
    cen gammaHat hgammaHat ball_subset
    (volume_region_ne_top_of_isBounded isDNF hbdd)
    -- **the precision is `GetPrecision`'s own output**, so `rho_eq` is `rfl`
    (P.precision gammaHat) rfl
    (normalisedCount (fun a => (atoms a).halfspace) φ (P.precision gammaHat)) rfl
    -- **the enumeration of `Sol(F) ∩ 𝕃ⁿ`**, constructed
    (latticeCount (fun a => (atoms a).halfspace) φ (P.precision gammaHat))
    (latticeEnum (fun a => (atoms a).halfspace) φ (P.precision gammaHat))
    (latticeEnum_injective _ _ _)
    (fun s => latticeEnum_mem (hasLatticeEnum_of_isBounded _ _ _ hbdd) s)
    (latticeEnum_onto (hasLatticeEnum_of_isBounded _ _ _ hbdd))
    -- **the rates**, **the volume estimates** and **the sampler**, all constructed
    (rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
      (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
        P.epsPrime rfac Am bv cen gammaHat Dm)
      (mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
        P.epsPrime P.deltaPrime c))
    (mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c)
    (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
      P.epsPrime rfac Am bv cen gammaHat Dm)
    (e2eSampler hn
      (by
        have h0 : (0 : ℝ) < P.ε := P.hε0
        unfold Params.epsPrime; linarith)
      Jt Am bv hdil rfac hr1 hcard cen gammaHat hgammaHat ball_subset Dm hDbody)
    (fun s => theta_eq_rates isDNF (hasLatticeEnum_of_isBounded _ _ _ hbdd) _ _ s)
    -- **the coverage test**, constructed
    (coverOfRegion (fun a => (atoms a).halfspace))
    (memPtOfRegion (fun a => (atoms a).halfspace)
      (latticeEnum (fun a => (atoms a).halfspace) φ (P.precision gammaHat)))
    (memPtOfRegion_spec _ _ _)
    (fun s i => coverOfRegion_memPtOfRegion _ _ s i)
    -- **`gen_mem`**, proved from the geometry
    (fun t i j N hi => gen_mem_of_geometry atoms isDNF isPositive hbdd hcoeff P
      (by rw [hP]; rfl)
      (by rw [hP]; exact ttcParams_facets_le (toDNF φ) n ε δ hε0 hε1 hn hm hr)
      cen hgammaHat ball_subset rfl _ t i j N hi)
    -- **the volume oracle**, constructed
    (VolumeAlgorithm.monteCarlo n) c
    (fun i hi => mcVol_eq (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
      P.epsPrime P.deltaPrime c i hi)
    (mcVol_mem_relErr (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
      P.epsPrime P.deltaPrime hc)
    (mcVol_pos (fun a => (atoms a).halfspace) (toDNF φ) cen hgammaHat
      (by
        have h0 : (0 : ℝ) < P.ε := P.hε0
        have h1 : P.ε ≤ 1 := P.hε1
        unfold Params.epsPrime; linarith)
      ball_subset (volume_region_ne_top_of_isBounded isDNF hbdd) hc)
    big

/-! ## 3. The payoff: every oracle field reads back as its construction

These are what make the eventual **deletion** of the fields from `Ttc.TtcProb`
sound: each says the field carries no information beyond the construction, so
nothing downstream can be reading anything else out of it.  All are `rfl`. -/

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
  (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
  (toDNF : BForm A → DNF A)
  (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
  (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
  (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
  (P : Params) (hP : P = ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr)
  (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ))
  (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
  (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
  (ball_subset : ∀ i, Metric.ball (cen i) gammaHat
    ⊆ region (fun a => (atoms a).halfspace) i.val)
  (Jt : Type) [Fintype Jt]
  (Am : {c : Cube A // c ∈ toDNF φ} → Jt → Space n)
  (bv : {c : Cube A // c ∈ toDNF φ} → Jt → ℝ)
  (hdil : ∀ i, latticeScale (P.precision gammaHat)
    • region (fun a => (atoms a).halfspace) i.val ⊆ Arlib.Polytope.body (Am i) (bv i))
  (rfac : ℝ) (hr1 : 1 ≤ rfac) (hcard : (Fintype.card Jt : ℝ) ≤ rfac)
  (Dm : {c : Cube A // c ∈ toDNF φ} → ℝ)
  (hDbody : ∀ i, ∀ x ∈ Arlib.Polytope.body (Am i) (bv i),
    ∀ y ∈ Arlib.Polytope.body (Am i) (bv i), dist x y ≤ Dm i)
  (c : ℕ → Space n)
  (hc : c ∈ mcGood (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
    P.epsPrime P.deltaPrime)
  (big : (1 - P.epsPrime) * P.thresh / 8
    ≤ ∑ s, rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
        (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
          P.epsPrime rfac Am bv cen gammaHat Dm)
        (mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
          P.epsPrime P.deltaPrime c) s)

/-- Abbreviation for the constructed bundle, used by the read-back lemmas below. -/
private noncomputable abbrev Tof : TtcProb A n :=
  ttcProbOfInputs atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP
    hbdd hcoeff cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
    c hc big

/-- **The volume algorithm is `Ttc.VolumeAlgorithm.monteCarlo`** — a term with no
hypotheses, not an argument. -/
theorem ttcProbOfInputs_volAlg :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).volAlg = VolumeAlgorithm.monteCarlo n := rfl

/-- **The volume oracle's coins are the supplied draw** — the only thing the caller
hands the volume oracle is a sample point of its own, constructed, coin law. -/
theorem ttcProbOfInputs_volCoins :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).volCoins = c := rfl

/-- **The volume estimates are `Ttc.mcVol`** — the Monte-Carlo oracle's own output
at those coins, not a free function. -/
theorem ttcProbOfInputs_vol :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).vol
      = mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
          P.epsPrime P.deltaPrime c := rfl

/-- **The precision is `GetPrecision`'s output.**  `P.precision γ̂` *is*
`⌈log₁₀(γ/γ̂)⌉` (`Ttc.Params.precision`, `alg:prec` line 91), so the field `ρ` and
the field `rho_eq` together carry exactly nothing. -/
theorem ttcProbOfInputs_rho :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).ρ = P.precision gammaHat := rfl

/-- **The sampler's discrete law is `Ttc.e2eSampD`** — the rounding-then-rejection
law of the lazy ball walk, not an argument. -/
theorem ttcProbOfInputs_sampD :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).sampD
      = e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
          P.epsPrime rfac Am bv cen gammaHat Dm := rfl

/-- **The rates are `Ttc.rates`** at the constructed sampler and the constructed
volume estimates — so `big` cannot be met by collapsing `θ` (`Ttc.rates_pos`). -/
theorem ttcProbOfInputs_theta :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).θ
      = rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
          (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
            P.epsPrime rfac Am bv cen gammaHat Dm)
          (mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
            P.epsPrime P.deltaPrime c) := rfl

/-- **The lattice index count is `Ttc.latticeCount`.** -/
theorem ttcProbOfInputs_Lidx :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).Lidx
      = latticeCount (fun a => (atoms a).halfspace) φ (P.precision gammaHat) := rfl

/-- **The enumeration is `Ttc.latticeEnum`.** -/
theorem ttcProbOfInputs_ptE :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).ptE
      = latticeEnum (fun a => (atoms a).halfspace) φ (P.precision gammaHat) := rfl

/-- **The normalised count is `Ttc.normalisedCount`** at the constructed precision. -/
theorem ttcProbOfInputs_L :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).L
      = normalisedCount (fun a => (atoms a).halfspace) φ (P.precision gammaHat) := rfl

/-- **The coverage test is `Ttc.coverOfRegion`.** -/
theorem ttcProbOfInputs_cover :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).cover = coverOfRegion (fun a => (atoms a).halfspace) := rfl

/-- **Cube membership on the enumerated points is `Ttc.memPtOfRegion`.** -/
theorem ttcProbOfInputs_memPt :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).memPt
      = memPtOfRegion (fun a => (atoms a).halfspace)
          (latticeEnum (fun a => (atoms a).halfspace) φ (P.precision gammaHat)) := rfl

/-- **The interpretation of the atoms is the one they denote** — inherited from
`Ttc.canonicalTtcProb`. -/
theorem ttcProbOfInputs_M :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).M = fun a => (atoms a).halfspace := rfl

/-- **The sample space is the trajectory space** — inherited from
`Ttc.canonicalTtcProb`. -/
theorem ttcProbOfInputs_Omega :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).Ω
      = (ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ (P.precision gammaHat)) → ℕ) :=
  rfl

/-- **The law is `Ttc.trajLaw` at the constructed rates** — inherited from
`Ttc.canonicalTtcProb`, now at rates that are themselves constructed. -/
theorem ttcProbOfInputs_mu :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).μ
      = trajLaw (rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
          (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
            P.epsPrime rfac Am bv cen gammaHat Dm)
          (mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
            P.epsPrime P.deltaPrime c)) := rfl

/-- **The reading of the sample point is the identity** — inherited from
`Ttc.canonicalTtcProb`, so `law_eq` and `oracle_eq` are `Ttc.Measure.map_id` and
`rfl`.  These two *stay* as fields: they are the modelling judgement that the
algorithm's randomness is the coupled Poisson/thinning family. -/
theorem ttcProbOfInputs_toTraj :
    (Tof atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      c hc big).toTraj = id := rfl

end OracleFree

/-! ## 4. Non-vacuity: **two** instances of the constructor, at two accuracy pairs

`CLAUDE.md` §11.  A constructor no one can go through certifies nothing, and one
instance cannot distinguish "the inputs are satisfiable" from "the inputs force one
accuracy pair".  The witness is `Ttc/Witness/BoxSharp.lean`'s box `[0,c]ⁿ` with
`c = max 1 Thresh(ε, δ)` — the same instance `Ttc.Box.ttc_volume_endToEnd_box_at`
uses, with the same Monte-Carlo volume oracle and the same ball-walk sampler — built
here at `(ε, δ) = (1/2, 1/2)` and at `(1/4, 1/4)`.

Both are checked to be informative *inside* the statement: each carries a
**strictly positive** lower bound on the probability that the run's output lands in
`(1 ± ε)·Vol(F)` (`1/2` and `3/4`), and strictly positive rates. -/

namespace Box

open MeasureTheory Set

variable (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)

/-- **The box's volume oracle has a good coin**, at every `(ε, δ) ∈ (0,1]²`. -/
theorem exists_mcGood_coin_box (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c : ℕ → Space n,
      c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
        (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime :=
  exists_mcGood_coin (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn)
    (toDNF_isDNFOf _) (parS n hn ε δ hε0 hε1) rfl hδ0 hδ1 (gamS_pos hn hε0 hε1)
    (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn) (cenMC n hn ε δ hε0 hε1)
    (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn) (hlen_box n hn ε δ hε0 hε1)

/-- One such coin, chosen. -/
noncomputable def bxCoin (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : ℕ → Space n :=
  (exists_mcGood_coin_box n hn ε δ hε0 hε1 hδ0 hδ1).choose

theorem bxCoin_good (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    bxCoin n hn ε δ hε0 hε1 hδ0 hδ1
      ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
        (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime :=
  (exists_mcGood_coin_box n hn ε δ hε0 hε1 hδ0 hδ1).choose_spec

/-- **The box as a `Ttc.TtcProb`, built with no oracle argument.**
`Ttc.ttcProbOfInputs` at the box's geometry: the volume oracle is
`Ttc.VolumeAlgorithm.monteCarlo`, the sampler is the lazy ball walk, the rates are
`Ttc.rates`, and the precision is `GetPrecision`'s output. -/
noncomputable def bxTtcProb (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : TtcProb (Fin n ⊕ Fin n) n :=
  ttcProbOfInputs (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn) ε δ
    hε0 hε1 hδ0 hδ1 hn Ttc.toDNF (toDNF_isDNFOf _)
    (toDNF_isPositive (boxForm_isPositive hn))
    (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)
    (parS n hn ε δ hε0 hε1) rfl
    (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (coeff_ne_zero_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1)
    (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (Fin n ⊕ Fin n) (fun _ => bxNormal n)
    (fun _ => bxOffsetOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
    (hdil_box n hn ε δ hε0 hε1) (bfac n) one_le_bfac card_le_bfac
    (bxDm n hn ε δ hε0 hε1) (hDbody_box n hn ε δ hε0 hε1)
    (bxCoin n hn ε δ hε0 hε1 hδ0 hδ1) (bxCoin_good n hn ε δ hε0 hε1 hδ0 hδ1)
    (big_ballWalk_box n hn ε δ hε0 hε1 hδ0 hδ1 _ (bxCoin_good n hn ε δ hε0 hε1 hδ0 hδ1))

theorem bxTtcProb_eps (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).ε = ε := rfl

theorem bxTtcProb_delta (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).δ = δ := rfl

theorem bxTtcProb_volAlg (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).volAlg = VolumeAlgorithm.monteCarlo n := rfl

theorem bxTtcProb_rho (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).ρ = rhoS n hn ε δ hε0 hε1 := rfl

/-- **The rates are strictly positive** — the instance is not the collapsed `θ ≡ 0`
that would satisfy `theta_eq` vacuously. -/
theorem bxTtcProb_theta_pos (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Fin (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).Lidx) :
    0 < (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).θ s :=
  bxRates_pos n hn ε δ hε0 hε1 _ (bxCoin_good n hn ε δ hε0 hε1 hδ0 hδ1) s

/-- **The accuracy guarantee this instance carries**, read off
`Ttc.TtcProb.volume_estimate_traj`. -/
theorem bxTtcProb_accuracy (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ (trajLaw (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).θ
      {t | ttcOutput (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).P
             (fun t => trajOracles (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).ptE_inj
               (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).vol
               (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).cover
               (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).memPt t)
             (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).toDNF
             (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).ρ
             (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).φ t
           ∈ relErr (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).ε
               (volSol (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).M
                 (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).φ)}).toReal :=
  (bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1).volume_estimate_traj

/-- **Two structurally different instances of `Ttc.ttcProbOfInputs`, and both say
something.**

`T₁` is the box at `(ε, δ) = (1/2, 1/2)` and `T₂` the box at `(1/4, 1/4)`: they
differ in `ε` and in `δ`, hence in the parameter block, the precision and the
sampler.  Both are built by `Ttc.ttcProbOfInputs`, so neither takes an oracle —
`volAlg` is `Ttc.VolumeAlgorithm.monteCarlo` and `ρ` is `GetPrecision`'s output in
each.

The last two conjuncts are the non-vacuity bar: the probability that the run's
output lands in `(1 ± ε)·Vol(F)` is bounded **strictly below by `1/2`** for `T₁` and
**by `3/4`** for `T₂`.  These are `0 < x` statements about an `ENNReal.toReal`, so
they also rule out the degenerate `ENNReal.toReal ⊤ = 0`.  Together with
`0 < T.θ s` they rule out the collapsed-rate instance. -/
theorem exists_two_ttcProbOfInputs (n : ℕ) (hn : 1 ≤ n) :
    ∃ T₁ T₂ : TtcProb (Fin n ⊕ Fin n) n,
      -- both come out of the oracle-free constructor
      T₁.volAlg = VolumeAlgorithm.monteCarlo n ∧ T₂.volAlg = VolumeAlgorithm.monteCarlo n ∧
      T₁.ρ = T₁.P.precision T₁.gammaHat ∧ T₂.ρ = T₂.P.precision T₂.gammaHat ∧
      -- they differ in a parameter
      T₁.ε = 1/2 ∧ T₂.ε = 1/4 ∧ T₁.δ = 1/2 ∧ T₂.δ = 1/4 ∧ T₁.ε ≠ T₂.ε ∧ T₁.δ ≠ T₂.δ ∧
      -- the rates are not collapsed
      (∀ s, 0 < T₁.θ s) ∧ (∀ s, 0 < T₂.θ s) ∧
      -- and each accuracy guarantee is a STRICTLY POSITIVE probability
      (1/2 : ℝ) ≤ (trajLaw T₁.θ
        {t | ttcOutput T₁.P (fun t => trajOracles T₁.ptE_inj T₁.vol T₁.cover T₁.memPt t)
               T₁.toDNF T₁.ρ T₁.φ t ∈ relErr T₁.ε (volSol T₁.M T₁.φ)}).toReal ∧
      (3/4 : ℝ) ≤ (trajLaw T₂.θ
        {t | ttcOutput T₂.P (fun t => trajOracles T₂.ptE_inj T₂.vol T₂.cover T₂.memPt t)
               T₂.toDNF T₂.ρ T₂.φ t ∈ relErr T₂.ε (volSol T₂.M T₂.φ)}).toReal ∧
      0 < (trajLaw T₁.θ
        {t | ttcOutput T₁.P (fun t => trajOracles T₁.ptE_inj T₁.vol T₁.cover T₁.memPt t)
               T₁.toDNF T₁.ρ T₁.φ t ∈ relErr T₁.ε (volSol T₁.M T₁.φ)}).toReal ∧
      0 < (trajLaw T₂.θ
        {t | ttcOutput T₂.P (fun t => trajOracles T₂.ptE_inj T₂.vol T₂.cover T₂.memPt t)
               T₂.toDNF T₂.ρ T₂.φ t ∈ relErr T₂.ε (volSol T₂.M T₂.φ)}).toReal := by
  have h1 := bxTtcProb_accuracy n hn (1/2) (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h2 := bxTtcProb_accuracy n hn (1/4) (1/4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨bxTtcProb n hn (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    bxTtcProb n hn (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_,
    fun s => bxTtcProb_theta_pos n hn (1/2) (1/2) _ _ _ _ s,
    fun s => bxTtcProb_theta_pos n hn (1/4) (1/4) _ _ _ _ s,
    by linarith, by linarith, by linarith, by linarith⟩
  · rw [bxTtcProb_eps, bxTtcProb_eps]; norm_num
  · rw [bxTtcProb_delta, bxTtcProb_delta]; norm_num

end Box

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms exists_mcGood_coin
#print axioms ttcProbOfInputs
#print axioms ttcProbOfInputs_volAlg
#print axioms ttcProbOfInputs_volCoins
#print axioms ttcProbOfInputs_vol
#print axioms ttcProbOfInputs_rho
#print axioms ttcProbOfInputs_sampD
#print axioms ttcProbOfInputs_theta
#print axioms ttcProbOfInputs_Lidx
#print axioms ttcProbOfInputs_ptE
#print axioms ttcProbOfInputs_L
#print axioms ttcProbOfInputs_cover
#print axioms ttcProbOfInputs_memPt
#print axioms ttcProbOfInputs_M
#print axioms ttcProbOfInputs_Omega
#print axioms ttcProbOfInputs_mu
#print axioms ttcProbOfInputs_toTraj
#print axioms Box.exists_mcGood_coin_box
#print axioms Box.bxCoin
#print axioms Box.bxCoin_good
#print axioms Box.bxTtcProb
#print axioms Box.bxTtcProb_eps
#print axioms Box.bxTtcProb_delta
#print axioms Box.bxTtcProb_volAlg
#print axioms Box.bxTtcProb_rho
#print axioms Box.bxTtcProb_theta_pos
#print axioms Box.bxTtcProb_accuracy
#print axioms Box.exists_two_ttcProbOfInputs

end Ttc

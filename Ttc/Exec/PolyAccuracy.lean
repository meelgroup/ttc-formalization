/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.PolyRun
import Ttc.Exec.Api

/-!
# `Exec/PolyAccuracy`: the **accuracy half** of `Ttc.ttcPoly`, and the two-conjunct capstone

`Ttc.all_ttcPoly_cost_le_quartic` (`Exec/PolyRun`) is the *cost* half of `Ttc.ttcPoly`,
and it is **unconditional**.  This file adds the *accuracy* half, which is **not**.

## READ THIS FIRST — the accuracy half proved here is CONDITIONAL

`Ttc.ttcPoly_volume_estimate_cv`'s accuracy conjunct rests, as **visible binders**, on

* `Ttc.HitAndRunTheorem11Input` (Lovász–Vempala Theorem 1.1) — a structure **inhabited
  nowhere** in this development, whose own proof would rest on the unproved `hLS`
  (Lovász–Simonovits 1993, Corollary 1.5).  It enters through
  `Ttc.kv97SamplerOfHitAndRun`, the only route to a `Ttc.KV97Sampler` certificate for
  `Ttc.polySampD`;
* Cousins–Vempala's `hphase_mean` and `hphase_var`, the two hypotheses
  `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns` still carries
  (`Ttc/Volume/CVInstantiate.lean:83`: "this is where the development actually stops");
* `thm:iso`, the isoperimetry input those rest on in turn.

The paper's regime condition `big` (README finding 20) is **not** in that list: it is
*discharged* here (`Ttc.big_polyRates`), see below.

**`Ttc.ttc`'s accuracy is unconditional and stays that way.**  `Ttc.ttc_volume_estimate`
(`Model/Theorem.lean:60`) is proved outright, at exponential prices.  So: `Ttc.ttc` has
unconditional accuracy at exponential prices; `Ttc.ttcPoly` has a polynomial *charged*
cost at conditional accuracy.  **Neither theorem dominates the other**, and nothing here
weakens or replaces `Ttc.ttc_volume_estimate`.

## THE REGIME CAVEAT — the `n⁴` needs a temperature-scale body (`R = O(σ)`)

`Ttc.all_ttcPoly_cost_le_quartic`'s `n⁴` holds where the body is temperature-scale.  In
the Cousins–Vempala regime `R ≍ σ√n` the conductance floor forces a smaller step, the
draw cost degrades, and the total is `n⁵`.
`Arlib.MarkovChains.exists_halfspace_max_lt` proves that the obvious route to recovering
the missing `√n` is **false**, not merely open.

## NOTHING HERE PROVES THAT `TTC` RUNS IN `O(m·n⁴)`

The cost coordinate of `Ttc.ttcPoly` charges one unit per oracle call and nothing else:
it prices at zero the arithmetic inside a call, the rejection rounds, and `alg:ttc`'s
lines 32–42 `while` loops.  See `Exec/PolyRun`'s docstring.

## What was actually closed, and how

`Exec/PolyRun` left the accuracy half **reduced but not closed**: the gap it named was
the *preprocessing and dilation bridge*, which on the Monte-Carlo path is carried by
`Exec/Final`, `Exec/Inputs` and `Exec/Prune` — each naming `Ttc.mcVol` and
`Ttc.e2eSampD` verbatim.

That bridge is **not re-derived generically here, because it does not have to be.**
`Ttc.volume_estimate_joint` (`Coupling/Product.lean:328`) is generic not only in
`volAlg`, `vol`, `θ`, `sampD` and the `Ttc.KV97Sampler` certificate, but also in
`atoms`, `φ`, `toDNF`, `P`, `cen`, `γ̂`, `ρ`, `ptE`, `cover` and `memPt`.  So it can be
instantiated **directly** at the dilated preprocessed data the algorithm itself
computes — `Ttc.algAtoms`, `Ttc.algCen`, `Ttc.algGamma`, `Ttc.algPrec`, `Ttc.algBlock`,
`Ttc.algEnum`, `Ttc.algMem` — and the entire ten-file chain
`VolDischarge → EndToEnd → CanonPolytope → Budget → Final → Inputs →
Rescaled/Cleanup/CleanInput → Prune → BddFromPos → Api`
collapses to three facts:

1. `Ttc.ttcPolyRun_eq_ttcOutput` — the run's output *is* `Ttc.ttcOutput` at the
   preprocessed formula divided by `qⁿ`, **by `rfl`** (the analogue of
   `Ttc.ttcEstimate_eq_ttcOutput`, `Exec/Api.lean:543`);
2. `Ttc.volSol_algAtoms_of_isPositive` — `Vol(q·Sol(preprocess F)) = qⁿ·Vol(Sol F)`, from
   `Ttc.volSol_scaleAtoms`, `Ttc.volSol_pruneForm` and `Ttc.volSol_cleanForm`; combined
   with `Ttc.setOf_mem_relErr_div` this moves the accuracy target back to the user's own
   `Vol(F)`;
3. the `δ`-repricing: `Ttc.algBlock` runs the parameter block at the internal
   `δ₀ = 4δ/5` (`Ttc.ttcBlock_delta`), so `1 − δ₀ − δ₀/4 = 1 − δ`.

Everything else is the *input-side* obligation block, discharged here at the alg-data by
the same lemmas the Monte-Carlo chain uses (`Ttc.pruneInt`, `Ttc.cleanInt`,
`Ttc.coeff_ne_zero_toDNFd_cleanForm`, `Ttc.gammaOf_pos_of_interior`,
`Ttc.ball_subset_cenOf`, `Ttc.ball_subset_scaleAtoms`, `Ttc.ttcAtoms_bdd`,
`Ttc.ttcBlock_eps/delta/n/m/r`), none of which mentions an oracle or a sampler.

## The one leg of the bridge that is NOT generic as stated: `big`

`Ttc.big_of_volume` (`Exec/RegimeMain.lean:168`) is what removes the regime condition on
the Monte-Carlo path, and its *statement* is **specific to both** `Ttc.e2eSampD` and
`Ttc.mcVol` — both names occur in it — so it does not transfer to the hit-and-run law.
Its *proof*, though, reads the sampler only through `eq:almostuniform` and the volume
oracle only through the lower half of the two-sided estimate.
`Ttc.big_of_volume_generic` redoes it with `Ttc.almostUniform_of_kv97Sampler`
(`Exec/EndToEnd.lean:292`, a bare `Ttc.KV97Sampler`) and
`Ttc.sum_rates_ge_of_pointwise` (`Exec/RegimeSum.lean:134`, generic in `sampD`/`vol`)
in place of the two specific ingredients; `Ttc.big_polyRates` then instantiates it at
the run's own data, with the volume hypothesis supplied by `Ttc.hvol_scaled` — the
dilation `Ttc.algScale` exists precisely to make the body clear `Thresh`.

So `big` is **discharged**, not assumed, and the capstones below carry no regime binder.
`Ttc.lintegral_ttcPolyRun_ge` and `Ttc.pr_ttcPoly_accuracy` keep it as a binder because
they are the general forms, at an arbitrary `sampD`-certificate pairing.

## Non-vacuity — one check passes, one is BLOCKED

* `Ttc.nonempty_polyGood` — the good event every coin-conditional statement here is
  quantified over is **inhabited** at every `V`, so those are real statements rather
  than `∀`s over `∅`.
* `Ttc.isProbabilityMeasure_ttcPoly` (`Exec/PolyRun`) — the measure-level check: the
  `MeasureTheory.Measure.bind` is not the junk zero measure, at which every `Pr[…]`
  would be `0`.
* **BLOCKED: there is no full witness for `Ttc.ttcPoly_volume_estimate_cv`.**  A witness
  would have to inhabit `Ttc.HitAndRunTheorem11Input`, which nothing in this development
  does and which is exactly the assumed content of Lovász–Vempala Theorem 1.1; and it
  would have to supply `hphase_mean`/`hphase_var`.  No witness is faked.  Contrast
  `Ttc.ttc_volume_estimate_poly_two_cube` (`Model/TheoremPoly.lean:626`), which is a
  witness on the *unconditional* path.

## What is here

| declaration | what it is |
| --- | --- |
| `Ttc.ttcPolyRun_eq_ttcOutput` | the dilation bridge, `rfl` |
| `Ttc.algScale_pos_uncond`, `Ttc.volSol_preprocess_alg`, `Ttc.volSol_algAtoms_of_isPositive` | the target-set transport |
| `Ttc.preprocess_int`, `Ttc.preprocess_coeff`, `Ttc.algGamma_pos_of_isPositive`, `Ttc.ball_subset_algCen`, `Ttc.algAtoms_bdd`, `Ttc.one_le_canonRfac_preprocess` | the input-side obligations, at the alg-data |
| `Ttc.polyGood` | the volume oracle's good event, at the run's geometry |
| `Ttc.almostUniform_of_sampler` | `eq:almostuniform` from a bare `Ttc.KV97Sampler` |
| `Ttc.big_of_volume_generic` | `Ttc.big_of_volume`, generic in `sampD` and `vol` |
| `Ttc.big_polyRates` | **`big`, discharged** at the run's own data |
| `Ttc.lintegral_ttcPolyRun_ge` | **the accuracy half**, as an iterated integral |
| `Ttc.pr_ttcPoly_accuracy` | the same over the program `Ttc.ttcPoly` |
| `Ttc.pr_ttcPoly_accuracy_hitAndRun` | the same at `Ttc.kv97SamplerOfHitAndRun` |
| `Ttc.ttcPoly_volume_estimate` | **the capstone**, both conjuncts, generic in `V` |
| `Ttc.ttcPoly_volume_estimate_cv` | the capstone at `Ttc.cvVolAlg` and hit-and-run |
| `Ttc.nonempty_polyGood` | the `big` binder is not a `∀` over `∅` |
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Set Pointwise

variable {A : Type*} {n : ℕ}

section PolyAccuracy

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The run's output is `Ttc.ttcOutput` at the preprocessed formula, divided by
`qⁿ`** — by `rfl`.  The polynomial-path analogue of `Ttc.ttcEstimate_eq_ttcOutput`
(`Exec/Api.lean:543`); this is the shape `Ttc.volume_estimate_joint` concludes in. -/
theorem ttcPolyRun_eq_ttcOutput (V : VolumeAlgorithm n) (ω : V.Ω)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) :
    ttcPolyRun atoms φ ε δ V ω t
      = ttcOutput (algBlock atoms φ ε δ)
            (fun t => polyOracles atoms φ ε δ V ω t) toDNFd
            (algPrec atoms φ ε δ) (preprocess atoms φ) t
          / (algScale atoms φ ε δ) ^ n := rfl

/-- The dilation `q` the algorithm applies is positive — `Ttc.scaleFactor_pos`, with
no hypothesis at all. -/
-- Named apart from `Ttc.algScale_pos` (`Ttc/Exec/InflateBound.lean:385`), which proves the
-- same thing at five hypotheses.  This form needs none.
theorem algScale_pos_uncond : 0 < algScale atoms φ ε δ := scaleFactor_pos _ _ _

/-- **Neither preprocessing pass moves the volume.**  `Ttc.volSol_pruneForm` (the
pruned cubes are null) then `Ttc.volSol_cleanForm` (the cleaned formula denotes the
same set). -/
theorem volSol_preprocess_alg (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    volSol (atomSet atoms) (preprocess atoms φ) = volSol (atomSet atoms) φ := by
  have h1 : volSol (atomSet atoms) (cleanForm atoms (pruneForm atoms φ))
      = volSol (atomSet atoms) (pruneForm atoms φ) :=
    volSol_cleanForm atoms (isPositive_pruneForm atoms φ)
      (cleanDNF_ne_nil_of_interior atoms (isPositive_pruneForm atoms φ)
        (pruneInt atoms hφ hpos))
  exact h1.trans (volSol_pruneForm atoms hφ (pruneNeNil atoms hpos))

/-- **The dilated preprocessed body has volume `qⁿ · Vol(F)`.**  `Ttc.volSol_scaleAtoms`
over `Ttc.volSol_preprocess_alg`. -/
theorem volSol_algAtoms_of_isPositive (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    volSol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
      = (algScale atoms φ ε δ) ^ n * volSol (atomSet atoms) φ := by
  rw [algAtoms, volSol_scaleAtoms (algScale_pos_uncond atoms φ ε δ),
    volSol_preprocess_alg atoms φ hφ hpos]

/-! ## The preprocessed / dilated geometry

Five obligations `Ttc.volume_estimate_joint` asks of the *input*, at the data
`Ttc.algAtoms` / `Ttc.algCen` / `Ttc.algGamma` the algorithm itself computes.  None of
them mentions an oracle, a sampler or a coin: this is the part of the chain
`Exec/Prune → Exec/CleanInput → Exec/Rescaled → Exec/Api` that is *about the input*,
collected here so that it can be spent at an arbitrary volume algorithm. -/

/-- **Every cube of the preprocessed formula is full-dimensional.**  `Ttc.pruneInt`
(pruning *makes* it true; `Ttc.hint_not_derivable` shows it is not derivable) followed
by `Ttc.cleanInt` (the cleanup only deletes literals denoting `Set.univ`). -/
theorem preprocess_int (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    ∀ i : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)},
      (interior (region (atomSet atoms) i.val)).Nonempty :=
  cleanInt atoms (isPositive_pruneForm atoms φ) (pruneInt atoms hφ hpos)

/-- **No atom of the preprocessed formula has a zero normal** —
`Ttc.coeff_ne_zero_toDNFd_cleanForm`, which is exactly what the cleaning pass buys. -/
theorem preprocess_coeff (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    ∀ j : FacetIndex (toDNFd (preprocess atoms φ)), (atoms j.2.val.atom).coeff ≠ 0 :=
  coeff_ne_zero_toDNFd_cleanForm atoms (isPositive_pruneForm atoms φ)
    (cleanDNF_ne_nil_of_interior atoms (isPositive_pruneForm atoms φ)
      (pruneInt atoms hφ hpos))

/-- **The dilated inscribed radius is positive** — `Ttc.gammaOf_pos_of_interior` at the
preprocessed formula, times the positive dilation.

Named apart from `Ttc.algGamma_pos` (`Ttc/Exec/PriceList.lean:216`), which is the same
conclusion at **five** hypotheses (`hε0 hε1 hn hφ hpos`) rather than two.  This form is
strictly stronger; the other is left alone because it is already consumed elsewhere. -/
theorem algGamma_pos_of_isPositive (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    0 < algGamma atoms φ ε δ :=
  mul_pos (algScale_pos_uncond atoms φ ε δ)
    (gammaOf_pos_of_interior (atomSet atoms)
      (toDNFd_ne_nil (preprocess_isPositive atoms φ)) (preprocess_int atoms φ hφ hpos))

/-- **The dilated inscribed ball sits inside the dilated region** —
`Ttc.ball_subset_cenOf` (unconditional) moved by `Ttc.ball_subset_scaleAtoms`. -/
theorem ball_subset_algCen :
    ∀ i : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)},
      Metric.ball (algCen atoms φ ε δ i) (algGamma atoms φ ε δ)
        ⊆ region (atomSet (algAtoms atoms φ ε δ)) i.val :=
  ball_subset_scaleAtoms (algScale_pos_uncond atoms φ ε δ)
    (ball_subset_cenOf (atomSet atoms) (toDNFd (preprocess atoms φ)))

/-- **`Sol` of the dilated preprocessed formula is bounded** — `Ttc.ttcAtoms_bdd`,
whose `Ttc.ttcAtoms` is `Ttc.algAtoms` by `rfl`. -/
theorem algAtoms_bdd (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    Bornology.IsBounded
      (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)) :=
  ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos

/-- **The canonical facet bound is at least `1`** — `Ttc.Params.hr` ("there is at
least one facet") is a field of the block the algorithm computes, and
`Ttc.ttcBlock_r` identifies that field with the canonical facet count. -/
theorem one_le_canonRfac_preprocess (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    (1 : ℝ) ≤ canonRfac (toDNFd (preprocess atoms φ)) := by
  have h : (1 : ℝ) ≤ (algBlock atoms φ ε (0 : ℝ)).r := (algBlock atoms φ ε (0 : ℝ)).hr
  have he : (algBlock atoms φ ε (0 : ℝ)).r
      = (Nat.card (FacetIndex (toDNFd (preprocess atoms φ))) : ℝ) :=
    ttcBlock_r atoms φ ε (0 : ℝ) hε0 hε1 hn hφ hpos
  rw [he] at h
  rw [canonRfac]
  exact h

/-- **The good event of the `m` `Vol_ED` calls**, at the run's own geometry and an
arbitrary volume algorithm.  `Ttc.volGoodOf` (`Exec/CVBackend`) at
`Ttc.algAtoms`/`Ttc.algCen`/`Ttc.algGamma`; at `V = Ttc.VolumeAlgorithm.monteCarlo` it
is `Ttc.mcGood` by `rfl`. -/
noncomputable def polyGood (V : VolumeAlgorithm n) : Set V.Ω :=
  volGoodOf V (atomSet (algAtoms atoms φ ε δ)) (toDNFd (preprocess atoms φ))
    (algCen atoms φ ε δ) (algGamma atoms φ ε δ)
    (algBlock atoms φ ε δ).epsPrime (algBlock atoms φ ε δ).deltaPrime

/-! # Discharging `big` at the hit-and-run sampler

`Ttc.big_of_volume` (`Exec/RegimeMain.lean:168`) names `Ttc.e2eSampD` **and**
`Ttc.mcVol` in its statement, so it does not transfer.  Its *proof*, however, reads the
sampler only through `eq:almostuniform` and the volume oracle only through the lower
half of its two-sided estimate — and both of those are available generically:
`Ttc.almostUniform_of_kv97Sampler` (`Exec/EndToEnd.lean:292`) from a bare
`Ttc.KV97Sampler`, and `Ttc.volOfAlg_mem_relErr` from the good event.  The three lemmas
below redo it that way, and `Ttc.big_polyRates` then discharges the binder at the run's
own data. -/

/-- **`eq:almostuniform` for an arbitrary `Ttc.KV97Sampler`**, with the two side
conditions of `Ttc.almostUniform_of_kv97Sampler` supplied from the geometry.

`Ttc.e2eSampD_almostUniform` (`Exec/RegimeInputs.lean:194`) with the sampler taken as a
parameter instead of built: its proof constructs `Ttc.e2eSampler` and then applies
`Ttc.almostUniform_of_kv97Sampler`; everything after that construction — finiteness of
the dilated lattice and its non-emptiness from the inscribed ball — uses nothing about
which sampler it is. -/
theorem almostUniform_of_sampler (atoms : A → LinAtom n) {D : DNF A} {ψ : BForm A}
    (hD : IsDNFOf D ψ) (P : Params) (hnP : P.n = n)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) ψ))
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat ⊆ region (atomSet atoms) i.val)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat)
    {sampD : Cube A → Space n → ℝ}
    (S : KV97Sampler A n (atomSet atoms) D ρ P.epsPrime sampD)
    (i : {c : Cube A // c ∈ D}) :
    AlmostUniform (sampD i.val)
      (region (atomSet atoms) i.val ∩ fineLattice n (latticeScale ρ)) P.epsPrime := by
  classical
  have hn1 : 1 ≤ n := by have := P.hn; rwa [hnP] at this
  have hep0 : 0 < P.epsPrime := P.epsPrime_pos
  have hep : P.epsPrime ≤ 1 / 2 := by
    rw [Params.epsPrime]; linarith [P.hε1, P.hε0]
  have hs : (0 : ℝ) < latticeScale ρ := latticeScale_pos ρ
  have hbi : ∀ j : {c : Cube A // c ∈ D},
      Bornology.IsBounded (region (atomSet atoms) j.val) :=
    fun j => isBounded_region_of_isBounded_sol hD hbdd j.property
  have hfin : ((latticeScale ρ • region (atomSet atoms) i.val)
      ∩ intLattice n : Set (Space n)).Finite :=
    Arlib.Lattice.finite_inter_intLattice ((hbi i).smul₀ _)
  have hne : ((latticeScale ρ • region (atomSet atoms) i.val)
      ∩ intLattice n : Set (Space n)).Nonempty := by
    have hsub : Metric.ball (latticeScale ρ • cen i) (latticeScale ρ * gammaHat)
        ⊆ latticeScale ρ • region (atomSet atoms) i.val :=
      ball_radius_scales hs _ _ (hball i)
    have hgam : P.gamma ≤ latticeScale ρ * gammaHat := by
      rw [hρ]; exact gamma_le_latticeScale_mul P hg
    obtain ⟨y, hy1, hy2⟩ :=
      exists_intLattice_mem_ball (latticeScale ρ • cen i) (sqrt_dim_half_lt_gamma P hnP)
    exact ⟨y, hsub (Metric.ball_subset_ball hgam hy1), hy2⟩
  exact almostUniform_of_kv97Sampler S hep0 hep i hfin hne

/-- **`Ttc.big_of_volume`, generic in the sampler and in the volume estimates.**

Same statement and same proof as `Ttc.big_of_volume` (`Exec/RegimeMain.lean:168`), with
`Ttc.e2eSampD` replaced by any `sampD` carrying a `Ttc.KV97Sampler` certificate and
`Ttc.mcVol … c` by any `vol` satisfying the *lower* half of the two-sided volume
estimate.  Nothing else changes. -/
theorem big_of_volume_generic (atoms : A → LinAtom n) {D : DNF A} {ψ : BForm A}
    (hD : IsDNFOf D ψ) (hposD : DNF.IsPositive D)
    (P : Params) (hnP : P.n = n)
    (hm : (Nat.card {c : Cube A // c ∈ D} : ℝ) ≤ P.m)
    (hr : (Nat.card (FacetIndex D) : ℝ) ≤ P.r)
    (hAnz : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) ψ))
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat ⊆ region (atomSet atoms) i.val)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat)
    (hvol : P.thresh / 4 ≤ volSol (atomSet atoms) ψ)
    {sampD : Cube A → Space n → ℝ}
    (S : KV97Sampler A n (atomSet atoms) D ρ P.epsPrime sampD)
    {vol : Cube A → ℝ}
    (hvolLo : ∀ i : {c : Cube A // c ∈ D},
      (1 - P.epsPrime) * (volume (region (atomSet atoms) i.val)).toReal ≤ vol i.val) :
    (1 - P.epsPrime) * P.thresh / 8
      ≤ ∑ s, rates (atomSet atoms) ψ D ρ sampD vol s := by
  classical
  have hm1 : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.hm
  have hle : HasLatticeEnum (atomSet atoms) ψ ρ := hasLatticeEnum_of_isBounded _ _ _ hbdd
  have hfin := volume_region_ne_top_of_isBounded (M := atomSet atoms) hD hbdd
  have hep1 : P.epsPrime ≤ 1 := by rw [Params.epsPrime]; nlinarith [P.hε0, P.hε1]
  have hη1 : P.eta ≤ 1 := by rw [Params.eta]; nlinarith [P.hε0, P.hε1]
  have hfinLat := finite_region_lattice_of_dnf atoms hposD P hnP hm1 hr hAnz cen hg hball hfin hρ
  have hlatc := lattice_cube_of_dnf atoms hposD P hnP hm1 hr hAnz cen hg hball hfin hρ
  have hAU := fun i => almostUniform_of_sampler atoms hD P hnP hbdd cen hg hball hρ S i
  have hsum := sum_rates_ge_of_pointwise (M := atomSet atoms) hD hle _ _ hep1 hη1
    hfinLat hAU hvolLo hlatc
  have hlat := (lattice_of_dnf atoms hD hposD P hnP hm hr hAnz cen hg hball hfin hρ).1.2
  exact sum_ge_of_volume_aux hep1 (by rw [Params.eta]; linarith [P.hε0])
    (two_mul_le_of_eps P) hsum hlat hvol ENNReal.toReal_nonneg

set_option maxHeartbeats 1000000 in
/-- **`big`, DISCHARGED at the run's own data** — the regime condition is *not* a binder
of the theorems below.

`Ttc.big_of_volume_generic` at the dilated preprocessed input, with the volume
hypothesis `hvol` supplied by `Ttc.hvol_scaled` (the dilation `Ttc.algScale` is chosen
precisely so the dilated body clears `Thresh`) and the lower volume estimate by
`Ttc.volOfAlg_mem_relErr` at a good coin.  So the only thing `big` costs at the
polynomial oracles is the `Ttc.KV97Sampler` certificate, which is already a binder. -/
theorem big_polyRates
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (sampler : KV97Sampler A n (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algPrec atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (polySampD atoms φ ε δ rin Rout Mw sigma)) :
    ∀ ω ∈ polyGood atoms φ ε δ V,
      (1 - (algBlock atoms φ ε δ).epsPrime) * (algBlock atoms φ ε δ).thresh / 8
        ≤ ∑ s, polyRates atoms φ ε δ V ω rin Rout Mw sigma s := by
  intro ω hω
  have hbddP : Bornology.IsBounded (sol (atomSet atoms) (preprocess atoms φ)) :=
    preprocess_bdd atoms φ hφ hpos
  have hvol : (algBlock atoms φ ε δ).thresh / 4
      ≤ volSol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ) :=
    hvol_scaled atoms (preprocess atoms φ) ε δ hε0 hε1 hn
      (preprocess_isPositive atoms φ) hbddP
      (gammaOf_pos_of_interior (atomSet atoms)
        (toDNFd_ne_nil (preprocess_isPositive atoms φ))
        (preprocess_int atoms φ hφ hpos))
      (autoCen atoms (preprocess atoms φ))
      (ball_subset_cenOf (atomSet atoms) (toDNFd (preprocess atoms φ)))
  have hvolLo : ∀ i : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)},
      (1 - (algBlock atoms φ ε δ).epsPrime)
          * (volume (region (atomSet (algAtoms atoms φ ε δ)) i.val)).toReal
        ≤ polyVol atoms φ ε δ V ω i.val := fun i =>
    (volOfAlg_mem_relErr V (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algCen atoms φ ε δ) (algGamma atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (algBlock atoms φ ε δ).deltaPrime hω
      i.val i.property).1
  have hPr : (algBlock atoms φ ε δ).r
      = (Nat.card (FacetIndex (toDNFd (preprocess atoms φ))) : ℝ) :=
    ttcBlock_r atoms φ ε δ hε0 hε1 hn hφ hpos
  have hPm : (algBlock atoms φ ε δ).m = ttcNumCubes atoms φ :=
    ttcBlock_m atoms φ ε δ hε0 hε1 hn hφ hpos
  exact big_of_volume_generic (algAtoms atoms φ ε δ) (toDNFd_isDNFOf _)
    (toDNFd_isPositive (preprocess_isPositive atoms φ)) (algBlock atoms φ ε δ)
    (ttcBlock_n atoms φ ε δ hε0 hε1 hn hφ hpos)
    (by rw [hPm, ← ttcNumCubes_eq_card atoms φ]) (by rw [hPr])
    (normal_ne_zero_of_coeff_ne_zero (preprocess_coeff atoms φ hφ hpos))
    (algAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (algCen atoms φ ε δ) (algGamma_pos_of_isPositive atoms φ ε δ hφ hpos)
    (ball_subset_algCen atoms φ ε δ) rfl hvol sampler hvolLo

/-! ## The workhorse: `Ttc.volume_estimate_joint` at the algorithm's own data -/

set_option maxHeartbeats 1000000 in
/-- **THE ACCURACY HALF, as an iterated integral.**

`Ttc.volume_estimate_joint` (`Coupling/Product.lean:328`) instantiated at the data
`Ttc.ttcPoly` actually runs on — the *dilated preprocessed* input `Ttc.algAtoms`,
`Ttc.algCen`, `Ttc.algGamma`, `Ttc.algPrec`, the parameter block `Ttc.algBlock`, the
enumeration `Ttc.algEnum` and the coverage table `Ttc.algMem` — with the volume
algorithm `V`, its estimates `Ttc.polyVol`, the hit-and-run law `Ttc.polySampD` and
the rates `Ttc.polyRates`.  The preprocessing/dilation bridge is closed here by
`Ttc.ttcPolyRun_eq_ttcOutput` (`rfl`) and `Ttc.volSol_algAtoms_of_isPositive` + `Ttc.mem_relErr_div`,
so no theorem of `Exec/Final`, `Exec/Inputs` or `Exec/Prune` — each of which names
`Ttc.mcVol` and `Ttc.e2eSampD` verbatim — is used.

`1 − δ` rather than `1 − δ − δ/4`: `Ttc.algBlock` runs the parameter block at the
internal `δ₀ = 4δ/5` (`Ttc.ttcBlock_delta`), and `1 − 4δ/5 − δ/5 = 1 − δ`.

**The two binders that remain.**  `sampler` is the `Ttc.KV97Sampler` certificate for the
law `Ttc.polySampD` — at hit-and-run this is where `Ttc.HitAndRunTheorem11Input` enters
(`Ttc.pr_ttcPoly_accuracy_hitAndRun`).  `big` is the paper's regime condition; it is a
binder *here* only because this is the general form — `Ttc.big_polyRates` discharges it
from the same `sampler`, and the capstones below carry no regime binder. -/
theorem lintegral_ttcPolyRun_ge
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (sampler : KV97Sampler A n (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algPrec atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (polySampD atoms φ ε δ rin Rout Mw sigma))
    (big : ∀ ω ∈ polyGood atoms φ ε δ V,
      (1 - (algBlock atoms φ ε δ).epsPrime) * (algBlock atoms φ ε δ).thresh / 8
        ≤ ∑ s, polyRates atoms φ ε δ V ω rin Rout Mw sigma s) :
    1 - δ ≤
      letI := V.mΩ
      (∫⁻ ω, trajLaw (polyRates atoms φ ε δ V ω rin Rout Mw sigma)
          {t | ttcPolyRun atoms φ ε δ V ω t
            ∈ relErr ε (volSol (atomSet atoms) φ)} ∂V.μ).toReal := by
  classical
  letI := V.mΩ
  haveI := V.isProb
  have hbdd : Bornology.IsBounded
      (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)) :=
    algAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos
  have hisD : IsDNFOf (toDNFd (preprocess atoms φ)) (preprocess atoms φ) :=
    toDNFd_isDNFOf _
  have hisP : DNF.IsPositive (toDNFd (preprocess atoms φ)) :=
    toDNFd_isPositive (preprocess_isPositive atoms φ)
  have hg : 0 < algGamma atoms φ ε δ := algGamma_pos_of_isPositive atoms φ ε δ hφ hpos
  have hball := ball_subset_algCen atoms φ ε δ
  have hfin : ∀ i : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)},
      volume (region (atomSet (algAtoms atoms φ ε δ)) i.val) ≠ ⊤ :=
    volume_region_ne_top_of_isBounded hisD hbdd
  have hconv : ∀ i : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)},
      Convex ℝ (region (atomSet (algAtoms atoms φ ε δ)) i.val) :=
    fun i => convex_region (algAtoms atoms φ ε δ) _
  have hle : HasLatticeEnum (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
      (algPrec atoms φ ε δ) := hasLatticeEnum_of_isBounded _ _ _ hbdd
  have heps0 : (0 : ℝ) < (algBlock atoms φ ε δ).ε := (algBlock atoms φ ε δ).hε0
  have heps1 : (algBlock atoms φ ε δ).ε ≤ 1 := (algBlock atoms φ ε δ).hε1
  have hep1 : (algBlock atoms φ ε δ).epsPrime < 1 := by
    unfold Params.epsPrime; linarith
  have hPm : (algBlock atoms φ ε δ).m = ttcNumCubes atoms φ :=
    ttcBlock_m atoms φ ε δ hε0 hε1 hn hφ hpos
  have hPr : (algBlock atoms φ ε δ).r
      = (Nat.card (FacetIndex (toDNFd (preprocess atoms φ))) : ℝ) :=
    ttcBlock_r atoms φ ε δ hε0 hε1 hn hφ hpos
  have hmlen : (((toDNFd (preprocess atoms φ)).length : ℝ)) ≤ (algBlock atoms φ ε δ).m := by
    rw [hPm]; exact le_rfl
  have hcubes : (Nat.card {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} : ℝ)
      ≤ (algBlock atoms φ ε δ).m := by
    rw [hPm, ← ttcNumCubes_eq_card atoms φ]
  have hfacets : (Nat.card (FacetIndex (toDNFd (preprocess atoms φ))) : ℝ)
      ≤ (algBlock atoms φ ε δ).r := by rw [hPr]
  have hδ0' : (0 : ℝ) < 4 * δ / 5 := by linarith
  have hδ1' : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  have hkey := volume_estimate_joint ε (4 * δ / 5) hε0 hε1 hδ0' hδ1'
    (algAtoms atoms φ ε δ) (atomSet (algAtoms atoms φ ε δ)) rfl (preprocess atoms φ)
    toDNFd hisD hisP (algBlock atoms φ ε δ)
    (ttcBlock_eps atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcBlock_delta atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcBlock_n atoms φ ε δ hε0 hε1 hn hφ hpos)
    hcubes hfacets
    (normal_ne_zero_of_coeff_ne_zero (preprocess_coeff atoms φ hφ hpos))
    (algCen atoms φ ε δ) (algGamma atoms φ ε δ) hg hball hfin
    (algPrec atoms φ ε δ) rfl _ rfl (algIndex atoms φ ε δ) (algEnum atoms φ ε δ)
    (latticeEnum_injective _ _ _) (fun s => latticeEnum_mem hle s) (latticeEnum_onto hle)
    V (fun ω => polyRates atoms φ ε δ V ω rin Rout Mw sigma)
    (fun ω => polyVol atoms φ ε δ V ω) (polySampD atoms φ ε δ rin Rout Mw sigma) sampler
    (fun ω s => theta_eq_rates hisD hle _ _ s)
    (coverOfRegion (atomSet (algAtoms atoms φ ε δ))) (algMem atoms φ ε δ)
    (memPtOfRegion_spec _ _ _)
    (fun s i => coverOfRegion_memPtOfRegion _ _ s i)
    (fun ω t i j N hi => gen_mem_of_geometry (algAtoms atoms φ ε δ) hisD hisP hbdd
      (preprocess_coeff atoms φ hφ hpos) (algBlock atoms φ ε δ)
      (ttcBlock_n atoms φ ε δ hε0 hε1 hn hφ hpos) hfacets
      (algCen atoms φ ε δ) hg hball rfl (polyVol atoms φ ε δ V ω) t i j N hi)
    (fun ω i hi => volOfAlg_eq V (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algCen atoms φ ε δ) (algGamma atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (algBlock atoms φ ε δ).deltaPrime ω i hi)
    (polyGood atoms φ ε δ V) (measurableSet_volGood V _ _ _ _ _)
    (measure_volGood_ge_of_length V (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algBlock atoms φ ε δ)
      (ttcBlock_delta atoms φ ε δ hε0 hε1 hn hφ hpos) hδ0' hδ1' hg
      (algCen atoms φ ε δ) hball hconv hfin hmlen)
    (fun ω hω => volOfAlg_mem_relErr V (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algCen atoms φ ε δ) (algGamma atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (algBlock atoms φ ε δ).deltaPrime hω)
    (fun ω hω => volOfAlg_pos V (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algCen atoms φ ε δ) hg hep1 hball hfin hω)
    big
  -- the target set, brought back to the user's own `Vol(F)`
  rw [volSol_algAtoms_of_isPositive atoms φ ε δ hφ hpos] at hkey
  simp only [setOf_mem_relErr_div _ (pow_pos (algScale_pos_uncond atoms φ ε δ) n)] at hkey
  refine le_trans (by linarith) hkey

/-! ## The same bound over the program `Ttc.ttcPoly` -/

open Ttc.Monadic in
/-- **THE ACCURACY HALF OF `Ttc.ttcPoly`.**

`Ttc.pr_ttcPoly_fst_eq_lintegral` (`Exec/PolyRun`) unfolds the `Pr[…]` to the iterated
integral, and `Ttc.lintegral_ttcPolyRun_ge` bounds it.  The prices
`gam R Mwarm Lc kap cc pf Mcool epsDraw` do not occur in the accuracy conjunct and are
carried only because `Ttc.ttcPoly` takes them. -/
theorem pr_ttcPoly_accuracy
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ)
    (sampler : KV97Sampler A n (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algPrec atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (polySampD atoms φ ε δ rin Rout Mw sigma))
    (big : ∀ ω ∈ polyGood atoms φ ε δ V,
      (1 - (algBlock atoms φ ε δ).epsPrime) * (algBlock atoms φ ε δ).thresh / 8
        ≤ ∑ s, polyRates atoms φ ε δ V ω rin Rout Mw sigma s) :
    1 - δ ≤
      Pr[r ← ttcPoly atoms φ ε δ V rin Rout Mw sigma
            gam R Mwarm Lc kap cc pf Mcool epsDraw;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)] := by
  rw [pr_ttcPoly_fst_eq_lintegral atoms φ ε δ V rin Rout Mw sigma
    gam R Mwarm Lc kap cc pf Mcool epsDraw _ measurableSet_Icc]
  exact lintegral_ttcPolyRun_ge atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos V
    rin Rout Mw sigma sampler big

/-! ## The instantiation at the hit-and-run sampler

`Ttc.kv97SamplerOfHitAndRun` (`Sampler/ConstructHitAndRun.lean:299`) produces exactly a
`Ttc.KV97Sampler` for `Ttc.kv97SampD … (Ttc.kv97HitAndRunContLaw …)`, which at the run's
canonical description **is** `Ttc.polySampD` — the law `Ttc.ttcPoly` already pins in its
rates.  Its own hypothesis `H : Ttc.HitAndRunTheorem11Input` is **inhabited nowhere** in
this development (its proof would rest on the unproved `hLS`), and it stays a visible
binder here; so does every piece of warm-start data it needs. -/

set_option maxHeartbeats 1000000 in
/-- **`Ttc.ttcPoly`'s accuracy at the hit-and-run sampler**, with the sampler
certificate replaced by Lovász–Vempala Theorem 1.1 (`H`) plus the warm-start data.

Every condition is a binder: `H` (uninhabited — see the module docstring), the
inner/outer ball data `zin/hrin/hin`, `zout/hRout/hout`, the tail set `Sx` and the
warmness `Mw`/`sigma` bounds.  Nothing is discharged by a convenient choice.  The regime
condition `big` is **not** a binder: `Ttc.big_polyRates` proves it from the certificate
this theorem already builds. -/
theorem pr_ttcPoly_accuracy_hitAndRun
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ)
    -- **Lovász–Vempala Theorem 1.1, ASSUMED** (`Ttc.HitAndRunTheorem11Input`)
    (H : HitAndRunTheorem11Input)
    -- the warm-start data the hit-and-run mixing bound consumes
    (zin : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Space n)
    (hrin : ∀ i, 0 < rin i)
    (hin : ∀ i, Metric.closedBall (zin i) (rin i) ⊆
      Arlib.KV97.inflated
        (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
        (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
          (latticeScale (algPrec atoms φ ε δ)) i)
        (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))))
    (zout : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Space n)
    (hRout : ∀ i, 0 ≤ Rout i)
    (hout : ∀ i, Arlib.KV97.inflated
        (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
        (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
          (latticeScale (algPrec atoms φ ε δ)) i)
        (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ)))
      ⊆ Metric.closedBall (zout i) (Rout i))
    (heps1 : ∀ i, (algBlock atoms φ ε δ).epsPrime / (4 *
      (volume (Arlib.KV97.inflated
        (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
        (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
          (latticeScale (algPrec atoms φ ε δ)) i)
        (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))))).toReal) ≤ 1)
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hM : ∀ i, 1 ≤ Mw i)
    (Sx : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Set (Space n))
    (hSm : ∀ i, MeasurableSet (Sx i))
    (hS : ∀ i, sigma i (Sx i) ≤ ENNReal.ofReal
      ((algBlock atoms φ ε δ).epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
          (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
            (latticeScale (algPrec atoms φ ε δ)) i)
          (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
          (canonRfac (toDNFd (preprocess atoms φ))))).toReal) / 2))
    (hdom : ∀ i, ∀ T, MeasurableSet T →
      sigma i (T \ Sx i) ≤ ENNReal.ofReal (Mw i) *
        Arlib.uniformOn volume (Arlib.KV97.inflated
          (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
          (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
            (latticeScale (algPrec atoms φ ε δ)) i)
          (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
          (canonRfac (toDNFd (preprocess atoms φ)))) (T \ Sx i))
    :
    1 - δ ≤
      Pr[r ← ttcPoly atoms φ ε δ V rin Rout Mw sigma
            gam R Mwarm Lc kap cc pf Mcool epsDraw;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)] := by
  have hep0 : 0 < (algBlock atoms φ ε δ).epsPrime := by
    have := (algBlock atoms φ ε δ).hε0
    unfold Params.epsPrime; linarith
  have S : KV97Sampler A n (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algPrec atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (polySampD atoms φ ε δ rin Rout Mw sigma) :=
    kv97SamplerOfHitAndRun H hn hep0 (Fin (Nat.card (FacetIndex
        (toDNFd (preprocess atoms φ)))))
      (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)))
      (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
        (latticeScale (algPrec atoms φ ε δ)))
      (fun i => canon_smul_region_subset_body (algAtoms atoms φ ε δ)
        (toDNFd_isPositive (preprocess_isPositive atoms φ))
        (latticeScale_pos (algPrec atoms φ ε δ)) i)
      (canonRfac (toDNFd (preprocess atoms φ)))
      (one_le_canonRfac_preprocess atoms φ ε hε0 hε1 hn hφ hpos)
      (by rw [canonRfac, Fintype.card_fin])
      zin rin hrin hin zout Rout hRout hout heps1 sigma hsigma Mw hM Sx hSm hS hdom
  exact pr_ttcPoly_accuracy atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos V
    rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw S
    (big_polyRates atoms φ ε δ hε0 hε1 hn hφ hpos V rin Rout Mw sigma S)

/-! # THE CAPSTONE: both halves of `Ttc.ttcPoly`, in the shape of
`Ttc.ttc_volume_estimate`

Same two conjuncts as `Ttc.ttc_volume_estimate` (`Model/Theorem.lean:60`) — the
accuracy conjunct **identical in form** — but with **no `cVol`/`cSample` binders**:
`Ttc.ttcPoly` fixes the two prices to the closed terms `Ttc.polyVolPrice` and
`Ttc.polySamplePrice`, and the runtime conjunct is the collapsed `m·n⁴·(…)`. -/

open Ttc.Monadic in
/-- **`Ttc.ttcPoly`: accuracy `1 − δ` and charged cost `≤ m·n⁴·(explicit factors)`.**

Read the module docstring before quoting this.  The accuracy conjunct is
**conditional** — on `sampler`, on whatever `V` assumes, and on `big` — while
`Ttc.ttc_volume_estimate`'s is unconditional; the runtime conjunct is
`Ttc.all_ttcPoly_cost_le_quartic`, which is unconditional but charges only oracle
calls. -/
theorem ttcPoly_volume_estimate
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ)
    -- the sampler certificate, and the regime condition: the accuracy side
    (sampler : KV97Sampler A n (atomSet (algAtoms atoms φ ε δ))
      (toDNFd (preprocess atoms φ)) (algPrec atoms φ ε δ)
      (algBlock atoms φ ε δ).epsPrime (polySampD atoms φ ε δ rin Rout Mw sigma))
    -- the sampler-side regime: the cost side
    (hrfac : 1 ≤ canonRfac (toDNFd (preprocess atoms φ)))
    (hR1 : 1 ≤ R) (hgam0 : 0 < gam) (hgamR : gam ≤ R)
    (hMw1 : 1 ≤ Mwarm) (hMwB : Mwarm ≤ (2 * R) ^ n)
    (hep0 : 0 < (algBlock atoms φ ε δ).epsPrime)
    (hep1 : (algBlock atoms φ ε δ).epsPrime ≤ 1)
    (hepn : 1 / 2 ^ n ≤ (algBlock atoms φ ε δ).epsPrime)
    -- the volume-side (Gaussian cooling) regime: the cost side
    (hL : 1 ≤ Lc) (hkap0 : 0 < kap) (hkap1 : kap ≤ 1) (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : ℝ)) (hp0 : 0 < pf) (hp1 : pf ≤ 1 / 2)
    (hMc : 1 ≤ Mcool) (hed0 : 0 < epsDraw) (hed1 : epsDraw ≤ 1) :
    -- (accuracy) identical in form to `Ttc.ttc_volume_estimate`'s
    (1 - δ ≤
      Pr[r ← ttcPoly atoms φ ε δ V rin Rout Mw sigma
            gam R Mwarm Lc kap cc pf Mcool epsDraw;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) `m · n⁴ · (explicit factors)`, no price binder
    (All[r ← ttcPoly atoms φ ε δ V rin Rout Mw sigma
          gam R Mwarm Lc kap cc pf Mcool epsDraw;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
          * (2 ^ 42 * (canonRfac (toDNFd (preprocess atoms φ)) + 1)
                * Real.log (8 * Mcool / epsDraw ^ 2)
                * (Lc ^ 4 * Real.log (1 / pf) / kap ^ 3)
              + 2 ^ 62 * canonRfac (toDNFd (preprocess atoms φ))
                  * (R ^ 2 / gam ^ 2) * Real.log (2 * R)
                  * PolyComplexity.threshFactor ε δ
                      (toDNFd (preprocess atoms φ)).length)]) :=
  ⟨pr_ttcPoly_accuracy atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos V rin Rout Mw sigma
      gam R Mwarm Lc kap cc pf Mcool epsDraw sampler
      (big_polyRates atoms φ ε δ hε0 hε1 hn hφ hpos V rin Rout Mw sigma sampler),
    all_ttcPoly_cost_le_quartic atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 V
      rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw
      hrfac hR1 hgam0 hgamR hMw1 hMwB hep0 hep1 hepn
      hL hkap0 hkap1 hcc1 hcc hp0 hp1 hMc hed0 hed1⟩

/-! # The instantiation at Cousins–Vempala

`Ttc.cvVolAlg` (`Exec/CVBackend.lean:533`) is the `Ttc.VolumeAlgorithm` built from
Cousins–Vempala's Gaussian-cooling estimator.  It is an `abbrev` for
`Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`, whose two remaining hypotheses
`hphase_mean` and `hphase_var` are **binders** — `Ttc/Volume/CVInstantiate.lean:83`
records that "this is where the development actually stops".  They stay binders here.

This is the pairing the two prices of `Ttc.ttcPoly` are actually justified for (see
`Exec/PolyRun`'s docstring on the price/`V` gap): Cousins–Vempala on the volume side,
hit-and-run on the sampler side. -/

open Ttc.Monadic in
set_option maxHeartbeats 1000000 in
/-- **`Ttc.ttcPoly` at the Cousins–Vempala volume oracle and the hit-and-run sampler:
accuracy `1 − δ` and charged cost `≤ m·n⁴·(explicit factors)`.**

`Ttc.ttcPoly_volume_estimate` at `V := Ttc.cvVolAlg …` and
`sampler := Ttc.kv97SamplerOfHitAndRun H …`.  **Every** condition of the accuracy half
is a visible binder of this statement:

* `H : Ttc.HitAndRunTheorem11Input` — Lovász–Vempala Theorem 1.1, **inhabited nowhere**
  in this development; its own proof would rest on the unproved `hLS`;
* `hphase_mean`, `hphase_var` — Cousins–Vempala's two remaining sampler hypotheses;
* the warm-start data `zin/hrin/hin`, `zout/hRout/hout`, `heps1`, `hsigma`, `hM`,
  `Sx/hSm/hS/hdom`;
The regime condition `big` is **not** among them (`Ttc.big_polyRates`).

`Ttc.ttc_volume_estimate`'s accuracy half is **unconditional** and stays so; neither of
the two results dominates the other. -/
theorem ttcPoly_volume_estimate_cv
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    -- **the Cousins–Vempala data, and its two unproved hypotheses**
    (E : Type) [MeasurableSpace E] (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)]
    (phases : Set (Space n) → ℝ → ℝ → ℕ) (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ) (B : ℝ)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j) (hg : ∀ K ε p j i, Measurable (g K ε p j i))
    (hgb : ∀ K ε p j i x, |g K ε p j i x| ≤ B)
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) =
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
          Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ))
    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + Arlib.GaussianCooling.varBudget ε / (phases K ε p : ℝ)) *
            (∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ))) ^ 2)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ)
    -- **Lovász–Vempala Theorem 1.1, ASSUMED**
    (H : HitAndRunTheorem11Input)
    (zin : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Space n)
    (hrin : ∀ i, 0 < rin i)
    (hin : ∀ i, Metric.closedBall (zin i) (rin i) ⊆
      Arlib.KV97.inflated
        (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
        (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
          (latticeScale (algPrec atoms φ ε δ)) i)
        (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))))
    (zout : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Space n)
    (hRout : ∀ i, 0 ≤ Rout i)
    (hout : ∀ i, Arlib.KV97.inflated
        (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
        (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
          (latticeScale (algPrec atoms φ ε δ)) i)
        (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ)))
      ⊆ Metric.closedBall (zout i) (Rout i))
    (heps1 : ∀ i, (algBlock atoms φ ε δ).epsPrime / (4 *
      (volume (Arlib.KV97.inflated
        (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
        (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
          (latticeScale (algPrec atoms φ ε δ)) i)
        (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))))).toReal) ≤ 1)
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hM : ∀ i, 1 ≤ Mw i)
    (Sx : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Set (Space n))
    (hSm : ∀ i, MeasurableSet (Sx i))
    (hS : ∀ i, sigma i (Sx i) ≤ ENNReal.ofReal
      ((algBlock atoms φ ε δ).epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
          (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
            (latticeScale (algPrec atoms φ ε δ)) i)
          (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
          (canonRfac (toDNFd (preprocess atoms φ))))).toReal) / 2))
    (hdom : ∀ i, ∀ T, MeasurableSet T →
      sigma i (T \ Sx i) ≤ ENNReal.ofReal (Mw i) *
        Arlib.uniformOn volume (Arlib.KV97.inflated
          (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
          (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
            (latticeScale (algPrec atoms φ ε δ)) i)
          (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
          (canonRfac (toDNFd (preprocess atoms φ)))) (T \ Sx i))
    -- the cost-side regime conditions of `Ttc.all_ttcPoly_cost_le_quartic`
    (hrfac : 1 ≤ canonRfac (toDNFd (preprocess atoms φ)))
    (hR1 : 1 ≤ R) (hgam0 : 0 < gam) (hgamR : gam ≤ R)
    (hMw1 : 1 ≤ Mwarm) (hMwB : Mwarm ≤ (2 * R) ^ n)
    (hep0 : 0 < (algBlock atoms φ ε δ).epsPrime)
    (hep1 : (algBlock atoms φ ε δ).epsPrime ≤ 1)
    (hepn : 1 / 2 ^ n ≤ (algBlock atoms φ ε δ).epsPrime)
    (hL : 1 ≤ Lc) (hkap0 : 0 < kap) (hkap1 : kap ≤ 1) (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : ℝ)) (hp0 : 0 < pf) (hp1 : pf ≤ 1 / 2)
    (hMc : 1 ≤ Mcool) (hed0 : 0 < epsDraw) (hed1 : epsDraw ≤ 1) :
    (1 - δ ≤
      Pr[r ← ttcPoly atoms φ ε δ
            (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var)
            rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    (All[r ← ttcPoly atoms φ ε δ
          (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var)
          rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
          * (2 ^ 42 * (canonRfac (toDNFd (preprocess atoms φ)) + 1)
                * Real.log (8 * Mcool / epsDraw ^ 2)
                * (Lc ^ 4 * Real.log (1 / pf) / kap ^ 3)
              + 2 ^ 62 * canonRfac (toDNFd (preprocess atoms φ))
                  * (R ^ 2 / gam ^ 2) * Real.log (2 * R)
                  * PolyComplexity.threshFactor ε δ
                      (toDNFd (preprocess atoms φ)).length)]) :=
  ⟨pr_ttcPoly_accuracy_hitAndRun atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
      (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var)
      rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw
      H zin hrin hin zout hRout hout heps1 hsigma hM Sx hSm hS hdom,
    all_ttcPoly_cost_le_quartic atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
      (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var)
      rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw
      hrfac hR1 hgam0 hgamR hMw1 hMwB hep0 hep1 hepn
      hL hkap0 hkap1 hcc1 hcc hp0 hp1 hMc hed0 hed1⟩

/-! # Non-vacuity (`CLAUDE.md` §11)

Three checks, and one **failure that is reported rather than papered over**. -/

/-- **The good event `Ttc.polyGood` is inhabited, at every volume algorithm.**

`Ttc.polyGood` is the event `Ttc.big_polyRates` and the volume-estimate hypotheses are
quantified over; over an *empty* event a `∀` says nothing.  `Ttc.exists_volGood_coin`
(`Exec/CVBackend.lean:216`) shows the event has probability at least `1 − δ₀/4 > 0`,
hence is nonempty, at any `V` — it certifies inhabitation only, and says nothing about
the cost of *finding* a good coin. -/
theorem nonempty_polyGood (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : 1 ≤ n) (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (V : VolumeAlgorithm n) :
    ∃ ω : V.Ω, ω ∈ polyGood atoms φ ε δ V := by
  have hδ0' : (0 : ℝ) < 4 * δ / 5 := by linarith
  have hδ1' : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  have hPm : (algBlock atoms φ ε δ).m = ttcNumCubes atoms φ :=
    ttcBlock_m atoms φ ε δ hε0 hε1 hn hφ hpos
  have hmlen : (((toDNFd (preprocess atoms φ)).length : ℝ)) ≤ (algBlock atoms φ ε δ).m := by
    rw [hPm]; exact le_rfl
  exact exists_volGood_coin V (algAtoms atoms φ ε δ) (preprocess atoms φ)
    (toDNFd_isDNFOf _) (algBlock atoms φ ε δ)
    (ttcBlock_delta atoms φ ε δ hε0 hε1 hn hφ hpos) hδ0' hδ1'
    (algGamma_pos_of_isPositive atoms φ ε δ hφ hpos)
    (algAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (algCen atoms φ ε δ) (ball_subset_algCen atoms φ ε δ) hmlen

end PolyAccuracy

end Ttc

/-! ## Axiom profile (`CLAUDE.md` §4) -/

#print axioms Ttc.ttcPolyRun_eq_ttcOutput
#print axioms Ttc.algScale_pos_uncond
#print axioms Ttc.volSol_preprocess_alg
#print axioms Ttc.volSol_algAtoms_of_isPositive
#print axioms Ttc.preprocess_int
#print axioms Ttc.preprocess_coeff
#print axioms Ttc.algGamma_pos_of_isPositive
#print axioms Ttc.ball_subset_algCen
#print axioms Ttc.algAtoms_bdd
#print axioms Ttc.one_le_canonRfac_preprocess
#print axioms Ttc.polyGood
#print axioms Ttc.almostUniform_of_sampler
#print axioms Ttc.big_of_volume_generic
#print axioms Ttc.big_polyRates
#print axioms Ttc.lintegral_ttcPolyRun_ge
#print axioms Ttc.pr_ttcPoly_accuracy
#print axioms Ttc.pr_ttcPoly_accuracy_hitAndRun
#print axioms Ttc.ttcPoly_volume_estimate
#print axioms Ttc.ttcPoly_volume_estimate_cv
#print axioms Ttc.nonempty_polyGood

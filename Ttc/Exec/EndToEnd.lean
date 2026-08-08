/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.VolDischarge
import Ttc.Sampler.Rates
import Ttc.Sampler.Construct

/-!
# `Exec/EndToEnd`: every oracle removed from the capstone at once

`Ttc.ttc_volume` (`Model/Endgoal`) is stated over two *assumed* oracles: a volume
estimator (`vol`, `volAlg`, `volCoins`, `volED_eq`, `volCoins_good`, `vol_pos`) and
a rate function for the sampling loop (`θ`, `theta_eq`, together with `gen_mem`).
Two corollaries already remove one set each:

* `Ttc.ttc_volume_monteCarlo` (`Exec/VolDischarge`) removes the **volume** set — the
  oracle is constructed (`Ttc.VolumeAlgorithm.monteCarlo`), its coins are integrated
  out against `Ttc.MonteCarlo.coins`, and `volCoins_good` is averaged out at
  probability `≥ 1 − δ/4`, so the guarantee reads `1 − δ − δ/4`.
* `Ttc.ttc_volume_rates` (`Sampler/Rates`) removes `θ`, `theta_eq` and `gen_mem` —
  the rates are constructed as `Ttc.rates`, and `gen_mem` follows from the geometry.

Neither is the end-to-end statement.  `Ttc.ttc_volume_endToEnd_ofSampler` below is their
**composition**: `Ttc.ttc_volume_monteCarlo` applied with its `θ` supplied by
`Ttc.rates` and its `theta_eq`/`gen_mem` by `Ttc.theta_eq_rates`/
`Ttc.gen_mem_of_geometry`.

## The join

`Ttc.mcVol` is a function of the volume oracle's coins, so the constructed rates
are too — which is exactly why `Ttc.ttc_volume_monteCarlo` already carries a
*coin-indexed* `θ`.  The composition takes

```lean
θ := fun c => Ttc.rates M φ (toDNF φ) (P.precision γ̂) sampD
                (Ttc.mcVol M (toDNF φ) cen γ̂ P.epsPrime P.deltaPrime c)
```

and `theta_eq` at each coin `c` is `Ttc.theta_eq_rates` instantiated at
`Ttc.mcVol … c`.  Nothing is restated or weakened: both corollaries are applied.

## The third oracle: the sampler

`Ttc.ttc_volume_endToEnd_ofSampler` still binds `sampD` and `sampler`, and
`Ttc.KV97Sampler` carries `law_tv` — an accuracy guarantee — so that is still an
oracle.  **`Ttc.ttc_volume_endToEnd`** removes it too, by supplying
`Ttc.kv97SamplerOfBody`: `sampD` becomes `Ttc.e2eSampD` (the rounding law of a lazy
ball walk) and `sampler` becomes `Ttc.e2eSampler`, whose `law_tv` is *proved* from
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`.

The bridge that keeps this from costing new geometric binders is
`Ttc.ball_smul_subset_body_of_dilate`: `Ttc.kv97SamplerOfBody` wants an inscribed
ball for the *dilated described body*, and the capstone already carries one for
`region M i`, so scaling by `10^ρ` and composing with `hdil` supplies it.

## What is left, and why

| binder | status |
| --- | --- |
| `Jt`, `Am`, `bv`, `hdil`, `rfac`, `hr1`, `hcard`, `Dm`, `hDbody` | a **description of the input polytopes**: a linear system whose body contains each dilated region, a facet bound, and a diameter bound for those bodies.  `hdil` and `hDbody` together force the described bodies to be *bounded* supersets of the dilated regions, so the trivial `Am = 0` does not satisfy them |
| `big` | a genuine **regime condition on the instance** — `(1 − ε')·Thresh/8 ≤ ∑ θ`, a statement about the *constructed* rates, so it cannot be met by collapsing `θ` (`Ttc.rates_pos`) |
| `hlen` | the AllSAT call returns no duplicate cube; inherited from `Ttc.ttc_volume_monteCarlo`, still needed |
| `atoms`, `φ`, `ε`, `δ`, `M`, `toDNF`, `P`, `cen`, `γ̂` | the algorithm's **inputs** and the parameter block it computes |
| `isDNF`, `isPositive`, `hm`, `hr`, `hbdd`, `hcoeff`, `hgammaHat`, `ball_subset` | the **input conditions** on those inputs |

No oracle remains: there is no `volAlg`, no `volCoins`, no `volED_eq`, no
`volCoins_good`, no `vol`, no `vol_pos`, no `θ`, no `theta_eq`, no `gen_mem`, no
`sampD` and no `sampler`.

## Honest scope

Two things are **not** claimed.

* `Ttc.VolumeAlgorithm.monteCarlo` is hit-and-miss Monte Carlo and the ball walk's
  step count is exponential in `n`; the running-time conjunct is the charged cost of
  `alg:ttc`'s loops, not a polynomial-time claim.
* The sampler is *a lazy ball-walk iterate from a non-stationary start meeting the
  total-variation tolerance*.  It is **not** proved that the finite-time iterate
  differs from the uniform law on the inflated body — that needs an
  `L²`/aperiodicity argument absent from the development.

## Non-vacuity

`Ttc.Box.ttc_volume_endToEnd_box_at` instantiates `Ttc.ttc_volume_endToEnd` on the
box `[0,c]ⁿ` at **every** `(ε, δ) ∈ (0,1]²` — Monte-Carlo volume oracle, constructed
rates, ball-walk sampler — and `Ttc.Box.exists_two_ttc_volume_endToEnd_instances`
exhibits two instances at `(1/2, 1/2)` and `(1/4, 1/4)`, where the guarantee reads
`3/8` and `11/16`: strictly positive, so the conclusion says something.  (Above
`δ = 4/5` the budget `1 − δ − δ/4` is not positive; that corner is uninformative and
is not claimed.)

Two degeneracies are ruled out explicitly: `Ttc.Box.bxRates_pos` (the rates are not
the collapsed `θ ≡ 0`, which would satisfy `theta_eq` vacuously and fail `big`), and
`Ttc.Box.endToEnd_box_lintegral_pos_ne_top` (the integral inside the `toReal` is
finite and nonzero, so the bound is not the vacuous `… ≤ ENNReal.toReal ⊤ = 0`).
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Set Pointwise

variable {A : Type*} {n : ℕ}

/-! ## The end-to-end capstone -/

/-- **`thm:volumettc` with both oracles removed.**

`Ttc.ttc_volume_monteCarlo` — which has already constructed the volume oracle,
integrated its coins out and paid `δ/4` for its failure — applied at the
*constructed* rates `Ttc.rates`, with

* `θ` **constructed**, `fun c => Ttc.rates M φ (toDNF φ) (P.precision γ̂) sampD
  (Ttc.mcVol … c)`: coin-indexed, because `Ttc.mcVol` is;
* `theta_eq` **proved**, `Ttc.theta_eq_rates` at `Ttc.mcVol … c`;
* `gen_mem` **proved**, `Ttc.gen_mem_of_geometry`, from `isDNF`, `isPositive`,
  `hbdd`, `hcoeff`, `ball_subset` and the computed `P` — all already present.

So of `Ttc.ttc_volume`'s nine oracle binders none survives.  What remains is the
sampler (`sampD`, `sampler`), the regime condition `big`, the loop-length bound
`hlen`, and the algorithm's inputs together with their input conditions. -/
theorem ttc_volume_endToEnd_ofSampler
    -- the algorithm's inputs
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    -- the FPRAS parameter range, and the ambient dimension
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    -- definitional: the atoms denote closed half-spaces
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    -- `alg:ttc` line 16, the circuit-AllSAT call, and what it is assumed to deliver
    (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    -- definitional: the parameter block of `alg:ttc` lines 12–20, computed
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    -- the main loop runs at most `m` times: the AllSAT call returns no duplicate cube
    (hlen : ((toDNF φ).length : ℝ) ≤ P.m)
    -- the two input conditions the geometry needs
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    -- the inscribed ball `alg:ttc` line 17 reads `γ̂` off
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    -- the sampling oracle `GenerateSamples` (`alg:ttc` line 43) — the only oracle left
    (sampD : Cube A → Space n → ℝ)
    (sampler : KV97Sampler A n M (toDNF φ) (P.precision gammaHat) P.epsPrime sampD)
    -- the instance is in the paper's regime, at every coin the volume oracle got right
    (big : ∀ c ∈ mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime,
      (1 - P.epsPrime) * P.thresh / 8
        ≤ ∑ s, rates M φ (toDNF φ) (P.precision gammaHat) sampD
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) s) :
    -- (accuracy) over the joint law of the run *and* the volume oracle's coins, the
    -- transcription's output is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ − δ/4`
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (rates M φ (toDNF φ) (P.precision gammaHat) sampD
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c))
          {t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ |
            ttcOutput P (coveredOracles M φ (P.precision gammaHat)
                (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c))
                toDNF (P.precision gammaHat) φ t
              ∈ relErr ε (volSol M φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    -- (running time) at every pair (volume coins, trajectory) whose absorption loops
    -- exit, the charged cost is `m·(cVol + cSample·Thresh)`
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles M φ (P.precision gammaHat)
          (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) t) (toDNF φ) →
      runCost P (coveredOracles M φ (P.precision gammaHat)
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) t)
          cVol cSample (P.precision gammaHat) (toDNF φ)
        ≤ (toDNF φ).length * (cVol + cSample * thr)) := by
  subst M_eq
  have hle : HasLatticeEnum (fun a => (atoms a).halfspace) φ (P.precision gammaHat) :=
    hasLatticeEnum_of_isBounded _ _ _ hbdd
  have hnq : P.n = n := by rw [hP]; rfl
  have hfa : (Nat.card (FacetIndex (toDNF φ)) : ℝ) ≤ P.r := by
    rw [hP]; exact ttcParams_facets_le (toDNF φ) n ε δ hε0 hε1 hn hm hr
  exact ttc_volume_monteCarlo atoms φ ε δ hε0 hε1 hδ0 hδ1 hn _ rfl toDNF isDNF isPositive
    hm hr P hP hlen hbdd hcoeff cen gammaHat hgammaHat ball_subset
    (fun c => rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat) sampD
      (mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat P.epsPrime
        P.deltaPrime c))
    sampD sampler
    (fun c s => theta_eq_rates isDNF hle sampD
      (mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat P.epsPrime
        P.deltaPrime c) s)
    (fun c t i j N hi => gen_mem_of_geometry atoms isDNF isPositive hbdd hcoeff P hnq hfa
      cen hgammaHat ball_subset rfl
      (mcVol (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat P.epsPrime
        P.deltaPrime c) t i j N hi)
    big

/-! ## The sampler, constructed as well

`Ttc.ttc_volume_endToEnd_ofSampler` still binds `sampD` and `sampler`.  `Ttc.KV97Sampler`
carries `law_tv` — the total-variation accuracy of the continuous draw — so a bound
`sampler` really is an *assumption about an oracle*.  `Ttc.kv97SamplerOfBody`
(`Sampler/Construct`) removes it: it builds the inflated geometry and the warm start
itself and proves `law_tv` from
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`.  What it asks for instead
are facts about the **input polytopes** — a linear description of the dilated
regions and a diameter bound for the described bodies.

Two of its inputs are already binders of the capstone and must not be duplicated:

* `hballBody` — an inscribed ball for the *described body*.  The capstone's
  `ball_subset` is an inscribed ball for `region M i`, on the **undilated** scale;
  `Ttc.ball_smul_subset_body_of_dilate` below is the bridge (scale the ball by
  `10^ρ` and push it through `hdil`), so `hballBody` costs nothing new.
* `hγ` — from the capstone's `hgammaHat`, at the dilated radius `10^ρ·γ̂`.

The ball-walk step `δ` is taken to be that same dilated radius, so `hδ`/`hδγ` are
discharged from `Arlib.KV97.kappaOf_nonneg` and need no binder either. -/

/-- **The capstone's inscribed ball, dilated and pushed into the described body.**

`Ttc.kv97SamplerOfBody` wants `B(cen', γ') ⊆ body (Am i) (bv i)`; the capstone has
`B(cen i, γ̂) ⊆ region M i`, and `hdil` says `10^ρ · region M i ⊆ body (Am i) (bv i)`.
Scaling the ball by `10^ρ > 0` closes the gap, at `cen' = 10^ρ · cen i` and
`γ' = 10^ρ · γ̂`. -/
theorem ball_smul_subset_body_of_dilate {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ}
    {Jt : Type} {Am : {c : Cube A // c ∈ D} → Jt → Space n}
    {bv : {c : Cube A // c ∈ D} → Jt → ℝ}
    (hdil : ∀ i, latticeScale ρ • region M i.val ⊆ Arlib.Polytope.body (Am i) (bv i))
    {cen : {c : Cube A // c ∈ D} → Space n} {gammaHat : ℝ}
    (hball : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (i : {c : Cube A // c ∈ D}) :
    Metric.ball (latticeScale ρ • cen i) (latticeScale ρ * gammaHat)
      ⊆ Arlib.Polytope.body (Am i) (bv i) := by
  have hs : (0 : ℝ) < latticeScale ρ := latticeScale_pos ρ
  intro x hx
  have hdx : dist x (latticeScale ρ • cen i) < latticeScale ρ * gammaHat := hx
  refine hdil i ⟨(latticeScale ρ)⁻¹ • x, hball i ?_, ?_⟩
  · have hsub : (latticeScale ρ)⁻¹ • x - cen i
        = (latticeScale ρ)⁻¹ • (x - latticeScale ρ • cen i) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    have hnx : ‖x - latticeScale ρ • cen i‖ < latticeScale ρ * gammaHat := by
      rw [← dist_eq_norm]; exact hdx
    show dist ((latticeScale ρ)⁻¹ • x) (cen i) < gammaHat
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
    calc (latticeScale ρ)⁻¹ * ‖x - latticeScale ρ • cen i‖
        < (latticeScale ρ)⁻¹ * (latticeScale ρ * gammaHat) :=
          mul_lt_mul_of_pos_left hnx (inv_pos.2 hs)
      _ = gammaHat := by field_simp
  · show latticeScale ρ • (latticeScale ρ)⁻¹ • x = x
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

/-- **The sampler's discrete law, at the geometry the capstone already carries.**

Literally `Ttc.kv97SamplerOfBody`'s own `sampD` — the rounding-then-rejection law of
the lazy ball walk on the inflated dilated body — with its inscribed ball taken to be
the capstone's, dilated (`Ttc.ball_smul_subset_body_of_dilate`), and its ball-walk
step taken equal to that dilated radius.  Nothing is asserted by this definition:
`Ttc.e2eSampler` is the proof that a `Ttc.KV97Sampler` for it exists. -/
noncomputable def e2eSampD (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (epsPrime rfac : ℝ) {Jt : Type}
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ)
    (Dm : {c : Cube A // c ∈ D} → ℝ) : Cube A → Space n → ℝ :=
  kv97SampD M D ρ (kv97ContLaw epsPrime rfac Am bv
    (fun i => (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac /
        (latticeScale ρ * gammaHat)) * Dm i)
    (fun _ => latticeScale ρ * gammaHat
      + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
    (fun _ => latticeScale ρ * gammaHat)
    (fun i => (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac) /
      volume (Metric.ball (latticeScale ρ • cen i)
        (latticeScale ρ * gammaHat
          + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal)
    (fun i => Arlib.uniformOn volume (Metric.ball (latticeScale ρ • cen i)
      (latticeScale ρ * gammaHat
        + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))))

/-- **A `Ttc.KV97Sampler` for `Ttc.e2eSampD`, assuming nothing about the sampler.**

`Ttc.kv97SamplerOfBody` at the capstone's own geometry.  Its remaining inputs are
the linear description `Am`/`bv`/`hdil` of the dilated regions, the facet bound
`rfac`/`hr1`/`hcard`, and a diameter bound `Dm`/`hDbody` for the described bodies —
all facts about the **input polytope**, none about the sampler. -/
noncomputable def e2eSampler {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ} {epsPrime : ℝ}
    (hn : 1 ≤ n) (hEps : 0 < epsPrime)
    (Jt : Type) [Fintype Jt]
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (hdil : ∀ i, latticeScale ρ • region M i.val ⊆ Arlib.Polytope.body (Am i) (bv i))
    (rfac : ℝ) (hr1 : 1 ≤ rfac) (hcard : (Fintype.card Jt : ℝ) ≤ rfac)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (Dm : {c : Cube A // c ∈ D} → ℝ)
    (hDbody : ∀ i, ∀ x ∈ Arlib.Polytope.body (Am i) (bv i),
      ∀ y ∈ Arlib.Polytope.body (Am i) (bv i), dist x y ≤ Dm i) :
    KV97Sampler A n M D ρ epsPrime
      (e2eSampD M D ρ epsPrime rfac Am bv cen gammaHat Dm) :=
  kv97SamplerOfBody hn hEps Jt Am bv hdil rfac hr1 hcard
    (fun i => latticeScale ρ • cen i) (fun _ => latticeScale ρ * gammaHat) Dm
    (fun _ => mul_pos (latticeScale_pos ρ) hgammaHat)
    (ball_smul_subset_body_of_dilate hdil ball_subset) hDbody
    (fun _ => latticeScale ρ * gammaHat)
    (fun _ => mul_pos (latticeScale_pos ρ) hgammaHat)
    (fun _ => by
      have := Arlib.KV97.kappaOf_nonneg (Arlib.KV97.cOf_nonneg (ε := epsPrime)) (r := rfac)
      linarith)

/-- **`eq:almostuniform` from a bare `Ttc.KV97Sampler`.**

`Ttc.TtcProb.samp_almostUniform_subtype` (`Sampler/Bridge`) proves exactly this, but
as a method of the bundled `Ttc.TtcProb`; the two facts it reads off the bundle
beyond the sampler itself are that the dilated integer lattice of the cube is finite
and nonempty, and `0 < ε' ≤ 1/2`.  Taking those four as hypotheses makes the
statement usable *before* a `Ttc.TtcProb` exists — which is what is needed to check
`big` for a constructed sampler.

Nothing here is assumed about the sampler's accuracy: `law_tv` is the sampler's own
field, proved by `Ttc.kv97SamplerOfBody` for the ball walk. -/
theorem almostUniform_of_kv97Sampler {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ}
    {epsPrime : ℝ} {sampD : Cube A → Space n → ℝ}
    (S : KV97Sampler A n M D ρ epsPrime sampD)
    (heps0 : 0 < epsPrime) (heps12 : epsPrime ≤ 1 / 2)
    (i : {c : Cube A // c ∈ D})
    (hfin : ((latticeScale ρ • region M i.val) ∩ intLattice n : Set (Space n)).Finite)
    (hne : ((latticeScale ρ • region M i.val) ∩ intLattice n : Set (Space n)).Nonempty) :
    AlmostUniform (sampD i.val)
      (region M i.val ∩ fineLattice n (latticeScale ρ)) epsPrime := by
  letI : Fintype ((latticeScale ρ • region M i.val) ∩ intLattice n : Set (Space n)) :=
    hfin.fintype
  haveI : Nonempty ((latticeScale ρ • region M i.val) ∩ intLattice n : Set (Space n)) :=
    hne.to_subtype
  haveI : IsProbabilityMeasure (S.contLaw i) := S.isProbContLaw i
  have hVpos : 0 < (volume (Arlib.KV97.inflated (S.Amat i) (S.bvec i)
      (Arlib.KV97.cOf epsPrime) S.facetBound)).toReal := by
    rw [← S.contVol_eq i]; exact S.contVol_pos i
  have htv : Arlib.TVLe (S.contLaw i)
      (Arlib.uniformOn volume (Arlib.KV97.inflated (S.Amat i) (S.bvec i)
        (Arlib.KV97.cOf epsPrime) S.facetBound))
      (ENNReal.ofReal (epsPrime / (4 *
        (volume (Arlib.KV97.inflated (S.Amat i) (S.bvec i)
          (Arlib.KV97.cOf epsPrime) S.facetBound)).toReal))) := by
    have h := S.law_tv i
    rwa [S.contVol_eq i] at h
  refine almostUniform_of_kv97_law (latticeScale_pos ρ) (Equiv.refl _)
    hVpos heps0 heps12
    (S.volume_inflated_ne_zero i) (S.volume_inflated_ne_top i) rfl htv
    (fun k => escape_of_mem_body _ _ S.one_le_facetBound S.card_le_facetBound
      (S.dilate_subset i k.2.1))
    (Dint := fun z =>
      (∫ p, Arlib.Lattice.Rounding.prodTent z p ∂(S.contLaw i)) /
      ∑ k : ((latticeScale ρ • region M i.val) ∩ intLattice n : Set (Space n)),
        ∫ p, Arlib.Lattice.Rounding.prodTent (k : Space n) p ∂(S.contLaw i))
    (fun _ => rfl) ?_
  intro x hx
  rw [S.sampD_eq i x hx, finsum_eq_sum_of_fintype]

/-- **`thm:volumettc` with both oracles *and* the sampler removed.**

`Ttc.ttc_volume_endToEnd_ofSampler` at the constructed sampler: `sampD` is `Ttc.e2eSampD` and
`sampler` is `Ttc.e2eSampler`, so neither is a binder.  Of `Ttc.ttc_volume`'s eleven
oracle binders — six for `Vol_ED`, three for the rates, `sampD` and `sampler` — none
survives.

What appears instead is a **description of the input polytopes**: `Jt`, `Am`, `bv`,
`hdil` (a linear system whose body contains the dilated region of each cube), the
facet bound `rfac`/`hr1`/`hcard`, and a diameter bound `Dm`/`hDbody` for those
bodies.  These are properties of the instance, not of any oracle — `hdil` together
with `hDbody` forces the described bodies to be bounded supersets of the dilated
regions, so they cannot be met by the trivial `Am = 0`.

**Scope, stated plainly.**  The sampler produced is a *lazy ball-walk iterate*, from
a warm start supported on an inscribed ball, meeting the total-variation tolerance
of `Ttc.KV97Sampler.law_tv`.  It is **not** claimed that the finite-time iterate
differs from the uniform law on the inflated body; that would need an
`L²`/aperiodicity argument which is not in the development.  What is claimed is that
no *accuracy assumption* about the sampler is made: `law_tv` is proved, by
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`.

**Non-vacuity.**  `Ttc.Box.ttc_volume_endToEnd_box_at` instantiates *this* statement
on the box at every `(ε, δ) ∈ (0,1]²`, with the ball-walk sampler and the
Monte-Carlo volume oracle; in particular `big` is discharged for the constructed
`sampD` by `Ttc.Box.big_ballWalk_box`, whose only route to the rates is
`eq:almostuniform` (`Ttc.almostUniform_of_kv97Sampler`), i.e. mixing. -/
theorem ttc_volume_endToEnd
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (hlen : ((toDNF φ).length : ℝ) ≤ P.m)
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    -- a linear description of the dilated regions, and a diameter bound for it
    (Jt : Type) [Fintype Jt]
    (Am : {c : Cube A // c ∈ toDNF φ} → Jt → Space n)
    (bv : {c : Cube A // c ∈ toDNF φ} → Jt → ℝ)
    (hdil : ∀ i, latticeScale (P.precision gammaHat) • region M i.val
      ⊆ Arlib.Polytope.body (Am i) (bv i))
    (rfac : ℝ) (hr1 : 1 ≤ rfac) (hcard : (Fintype.card Jt : ℝ) ≤ rfac)
    (Dm : {c : Cube A // c ∈ toDNF φ} → ℝ)
    (hDbody : ∀ i, ∀ x ∈ Arlib.Polytope.body (Am i) (bv i),
      ∀ y ∈ Arlib.Polytope.body (Am i) (bv i), dist x y ≤ Dm i)
    (big : ∀ c ∈ mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime,
      (1 - P.epsPrime) * P.thresh / 8
        ≤ ∑ s, rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime rfac Am bv cen gammaHat Dm)
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) s) :
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime rfac Am bv cen gammaHat Dm)
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c))
          {t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ |
            ttcOutput P (coveredOracles M φ (P.precision gammaHat)
                (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c))
                toDNF (P.precision gammaHat) φ t
              ∈ relErr ε (volSol M φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles M φ (P.precision gammaHat)
          (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) t) (toDNF φ) →
      runCost P (coveredOracles M φ (P.precision gammaHat)
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) t)
          cVol cSample (P.precision gammaHat) (toDNF φ)
        ≤ (toDNF φ).length * (cVol + cSample * thr)) := by
  have hEps : 0 < P.epsPrime := by
    have h0 : (0 : ℝ) < P.ε := P.hε0
    unfold Params.epsPrime; linarith
  exact ttc_volume_endToEnd_ofSampler atoms φ ε δ hε0 hε1 hδ0 hδ1 hn M M_eq toDNF isDNF isPositive
    hm hr P hP hlen hbdd hcoeff cen gammaHat hgammaHat ball_subset
    (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime rfac Am bv cen gammaHat Dm)
    (e2eSampler hn hEps Jt Am bv hdil rfac hr1 hcard cen gammaHat hgammaHat ball_subset
      Dm hDbody)
    big

/-! ## Non-vacuity: the box, at two accuracy pairs strictly inside `(0,1)`

`CLAUDE.md` §11.  The witness is `Ttc/Witness/BoxSharp.lean`'s box `[0,c]ⁿ` with
`c = max 1 Thresh(ε, δ)`, carrying **both** constructions: the Monte-Carlo volume
oracle of `Exec/VolDischarge` and the rates of `Sampler/Rates`.  The two hypothesis
sets `Ttc.Box.ttc_volume_monteCarlo_box_at` and `Ttc.Box.ttc_volume_box_rates`
discharge separately are here discharged **together**, on one instance.
-/

namespace Box

open MeasureTheory Set

variable (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)

/-- **The general construction reproduces the box's coin-indexed rates.**
`Ttc.Box.rates_eq_thOf` with the exact estimates `Ttc.Box.vlOf` replaced by the
Monte-Carlo ones `Ttc.Box.volMC`: the box's DNF has one cube, so `Ttc.cubeAt` can
only pick it, and then `Ttc.Box.smpOf` and `Ttc.Box.volMC` are read at that cube. -/
theorem rates_eq_thMC (c : ℕ → Space n) :
    rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) (boxForm n hn)
        (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
        (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
        (volMC n hn ε δ hε0 hε1 c)
      = thMC n hn ε δ hε0 hε1 c := by
  funext s
  have hspec := cubeAt_spec (toDNF_isDNFOf (boxForm n hn))
    (hasLatticeEnum_bxOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1)) s
  have hcu : cubeAt (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1) s = boxCube n := by
    have h := hspec.1
    simpa only [toDNF_boxForm hn, boxDNF, List.mem_singleton] using h
  simp only [rates, thMC, hcu]

/-- **`Ttc.ttc_volume_endToEnd_ofSampler`'s `big`, for the box**, at every coin on which the
volume oracle got the volume right — `Ttc.Box.big_MC` transported along
`Ttc.Box.rates_eq_thMC`. -/
theorem big_rates_MC (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime) :
    (1 - (parS n hn ε δ hε0 hε1).epsPrime) * (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ ∑ s, rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
          (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
          (volMC n hn ε δ hε0 hε1 c) s := by
  rw [rates_eq_thMC n hn ε δ hε0 hε1 c]
  exact big_MC n hn ε δ hε0 hε1 hδ0 hδ1 c hc

/-- **The constructed rates are strictly positive on the box, at every coin the
volume oracle got right.**  The end-to-end witness is therefore not a collapsed
`θ ≡ 0` — the degenerate solution that would satisfy `theta_eq` and fail `big`. -/
theorem rates_MC_pos (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime)
    (s : Fin (latticeCount (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (rhoS n hn ε δ hε0 hε1))) :
    0 < rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
      (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
      (volMC n hn ε δ hε0 hε1 c) s := by
  have heps1 : (parS n hn ε δ hε0 hε1).epsPrime < 1 := by
    have h0 : (0:ℝ) < (parS n hn ε δ hε0 hε1).ε := (parS n hn ε δ hε0 hε1).hε0
    have h1 : (parS n hn ε δ hε0 hε1).ε ≤ 1 := (parS n hn ε δ hε0 hε1).hε1
    unfold Params.epsPrime; linarith
  exact rates_pos (toDNF_isDNFOf (boxForm n hn))
    (hasLatticeEnum_bxOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1))
    (mcVol_pos (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1) heps1
      (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
      (volume_region_ne_top_of_isBounded (toDNF_isDNFOf (boxForm n hn))
        (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn))
      hc)
    (fun i hi x _ => smpOf_pos n (sideS_pos hn hε0 hε1) hn (rhoS n hn ε δ hε0 hε1) hi x) s

/-- **`Ttc.ttc_volume_endToEnd_ofSampler`'s hypotheses are satisfiable, at every
`(ε, δ) ∈ (0,1]²`.**

The box `[0,c]ⁿ` with `c = max 1 Thresh(ε, δ)`, its one-cube DNF, the
Kannan–Vempala sampler `Ttc.Box.samplerOf` — with **no** volume oracle and **no**
rate function assumed: the volume estimates are `Ttc.Box.volMC`, the oracle's own
Monte-Carlo output, and the rates are `Ttc.rates` built on top of them.  The proof
is the 28-argument application of `Ttc.ttc_volume_endToEnd_ofSampler`. -/
theorem ttc_volume_endToEnd_ofSampler_box_at (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
            (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
            (volMC n hn ε δ hε0 hε1 c))
          {t : ℕ → Fin (latticeCount
              (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
              (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ |
            ttcOutput (parS n hn ε δ hε0 hε1)
                (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
                Ttc.toDNF (rhoS n hn ε δ hε0 hε1) (boxForm n hn) t
              ∈ relErr ε (volSol
                  (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn))}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (latticeCount
        (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = (parS n hn ε δ hε0 hε1).thresh →
      Terminates (parS n hn ε δ hε0 hε1)
          (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) t)
          (Ttc.toDNF (boxForm n hn)) →
      runCost (parS n hn ε δ hε0 hε1)
          (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) t)
          cVol cSample (rhoS n hn ε δ hε0 hε1) (Ttc.toDNF (boxForm n hn))
        ≤ (Ttc.toDNF (boxForm n hn)).length * (cVol + cSample * thr)) := by
  have hcpos : 0 < sideS n hn ε δ hε0 hε1 := sideS_pos hn hε0 hε1
  exact ttc_volume_endToEnd_ofSampler (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn) ε δ
    hε0 hε1 hδ0 hδ1 hn
    (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) rfl Ttc.toDNF
    (toDNF_isDNFOf _) (toDNF_isPositive (boxForm_isPositive hn))
    (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)
    (parS n hn ε δ hε0 hε1) rfl (hlen_box n hn ε δ hε0 hε1)
    (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (coeff_ne_zero_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1)
    (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
    (samplerOf n hn hcpos (rhoS n hn ε δ hε0 hε1)
      (parS_epsPrime_pos (δ := δ) hn hε0 hε1) (parS_epsPrime_le (δ := δ) hn hε0 hε1))
    (big_rates_MC n hn ε δ hε0 hε1 hδ0 hδ1)

/-! ### The box, for the *constructed* sampler

Everything above witnesses `Ttc.ttc_volume_endToEnd_ofSampler`, whose sampler is a binder.
What follows discharges, on the same box, the extra inputs
`Ttc.ttc_volume_endToEnd` asks for — the linear description of the dilated
box, its facet bound, and a diameter bound — and then its `big`, for the *ball-walk*
`Ttc.e2eSampD` rather than for the box's own uniform `Ttc.Box.smpOf`. -/

/-- **A box has diameter at most `s·√n`.** -/
theorem dist_le_of_mem_bxOf (n : ℕ) {s : ℝ} (hs : 0 ≤ s) {x y : Space n}
    (hx : x ∈ bxOf n s) (hy : y ∈ bxOf n s) : dist x y ≤ s * Real.sqrt n := by
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ s ^ 2 * (n : ℝ) := by
    have hle : ∀ i ∈ Finset.univ, dist (x i) (y i) ^ 2 ≤ s ^ 2 := by
      intro i _
      have h1 := hx i
      have h2 := hy i
      rw [Real.dist_eq, sq_abs]
      nlinarith [h1.1, h1.2, h2.1, h2.2]
    calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin n, s ^ 2 := Finset.sum_le_sum hle
      _ = s ^ 2 * (n : ℝ) := by simp [mul_comm]
  calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt (s ^ 2 * (n : ℝ)) :=
        Real.sqrt_le_sqrt hsum
    _ = s * Real.sqrt n := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs]

/-- **`Ttc.ttc_volume_endToEnd`'s `hdil`, for the box** — the linear system
`±x k ≤ (10^ρ·c, 0)` cuts out the dilated box exactly (`Ttc.Box.bxBodyOf_eq`). -/
theorem hdil_box (i : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)}) :
    latticeScale (rhoS n hn ε δ hε0 hε1)
        • region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) i.val
      ⊆ Arlib.Polytope.body (bxNormal n)
          (bxOffsetOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1)) := by
  have h : latticeScale (rhoS n hn ε δ hε0 hε1)
        • region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) i.val
      = Arlib.Polytope.body (bxNormal n)
          (bxOffsetOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1)) := by
    rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn i.property, smul_bxOf, bxBodyOf_eq]
  exact h.le

/-- **`Ttc.ttc_volume_endToEnd`'s `Dm`, for the box.** -/
noncomputable def bxDm :
    {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)} → ℝ :=
  fun _ => latticeScale (rhoS n hn ε δ hε0 hε1) * sideS n hn ε δ hε0 hε1 * Real.sqrt n

/-- **`Ttc.ttc_volume_endToEnd`'s `hDbody`, for the box.** -/
theorem hDbody_box (i : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)}) :
    ∀ x ∈ Arlib.Polytope.body (bxNormal n)
        (bxOffsetOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1)),
      ∀ y ∈ Arlib.Polytope.body (bxNormal n)
        (bxOffsetOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1)),
      dist x y ≤ bxDm n hn ε δ hε0 hε1 i := by
  intro x hx y hy
  rw [bxBodyOf_eq] at hx hy
  exact dist_le_of_mem_bxOf n
    (mul_nonneg (latticeScale_pos _).le (sideS_pos hn hε0 hε1).le) hx hy

/-- **The box's ball-walk sampler's discrete law** — `Ttc.e2eSampD` at the box's
data.  Unlike `Ttc.Box.smpOf`, this is not uniform by fiat: it is the rounding law of
a lazy ball walk, and the only thing known about it is `Ttc.KV97Sampler.law_tv`. -/
noncomputable def bxSampD : Cube (Fin n ⊕ Fin n) → Space n → ℝ :=
  e2eSampD (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
    (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
    (parS n hn ε δ hε0 hε1).epsPrime (bfac n)
    (fun _ => bxNormal n)
    (fun _ => bxOffsetOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) (bxDm n hn ε δ hε0 hε1)

/-- **The box's ball-walk sampler**, with no accuracy assumption. -/
noncomputable def bxSampler :
    KV97Sampler (Fin n ⊕ Fin n) n
      (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (bxSampD n hn ε δ hε0 hε1) :=
  e2eSampler hn (parS_epsPrime_pos (δ := δ) hn hε0 hε1) (Fin n ⊕ Fin n)
    (fun _ => bxNormal n)
    (fun _ => bxOffsetOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
    (hdil_box n hn ε δ hε0 hε1) (bfac n) one_le_bfac card_le_bfac
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1)
    (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn) (bxDm n hn ε δ hε0 hε1)
    (hDbody_box n hn ε δ hε0 hε1)

/-- The dilated box has finitely many integer points. -/
theorem dilate_finite_box
    (i : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)}) :
    ((latticeScale (rhoS n hn ε δ hε0 hε1)
      • region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) i.val)
        ∩ intLattice n : Set (Space n)).Finite := by
  rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn i.property]
  exact dilFiniteOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1)

/-- The dilated box has at least one integer point. -/
theorem dilate_nonempty_box
    (i : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)}) :
    ((latticeScale (rhoS n hn ε δ hε0 hε1)
      • region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) i.val)
        ∩ intLattice n : Set (Space n)).Nonempty := by
  rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn i.property]
  have h : (latticeScale (rhoS n hn ε δ hε0 hε1) • bxOf n (sideS n hn ε δ hε0 hε1)
        ∩ intLattice n : Set (Space n))
      = (fun x => latticeScale (rhoS n hn ε δ hε0 hε1) • x) ''
        (bxOf n (sideS n hn ε δ hε0 hε1)
          ∩ fineLattice n (latticeScale (rhoS n hn ε δ hε0 hε1))) :=
    (Arlib.Lattice.image_smul_inter_fineLattice (latticeScale_pos _)
      (bxOf n (sideS n hn ε δ hε0 hε1))).symm
  rw [h]
  exact (latNonemptyOf n (sideS_pos hn hε0 hε1).le (rhoS n hn ε δ hε0 hε1)).image _

/-- **`eq:almostuniform` for the box's ball-walk sampler** — `Ttc.almostUniform_of_kv97Sampler`
at `Ttc.Box.bxSampler`.  This is the fact `Ttc.Box.smpOf` had by construction and the
ball walk has only through mixing. -/
theorem bxSampD_almostUniform :
    AlmostUniform (bxSampD n hn ε δ hε0 hε1 (boxCube n))
      (region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) (boxCube n)
        ∩ fineLattice n (latticeScale (rhoS n hn ε δ hε0 hε1)))
      (parS n hn ε δ hε0 hε1).epsPrime :=
  almostUniform_of_kv97Sampler (bxSampler n hn ε δ hε0 hε1)
    (parS_epsPrime_pos (δ := δ) hn hε0 hε1)
    (by have := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1; linarith)
    ⟨boxCube n, mem_toDNF_boxCube n hn⟩
    (dilate_finite_box n hn ε δ hε0 hε1 ⟨boxCube n, mem_toDNF_boxCube n hn⟩)
    (dilate_nonempty_box n hn ε δ hε0 hε1 ⟨boxCube n, mem_toDNF_boxCube n hn⟩)

/-- **The ball-walk rates sum to at least `(1−ε')·Vol_ED`.**  `Ttc.Box.sum_thMC` gave
the total *exactly*, because `Ttc.Box.smpOf` is exactly uniform; here only
`eq:almostuniform` is available, and it gives the lower half — which is all `big`
needs. -/
theorem sum_bxRates_ge (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime) :
    (1 - (parS n hn ε δ hε0 hε1).epsPrime) * volMC n hn ε δ hε0 hε1 c (boxCube n)
      ≤ ∑ s, rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
          (bxSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) s := by
  set c0 := sideS n hn ε δ hε0 hε1 with hc0
  set ρ := rhoS n hn ε δ hε0 hε1 with hρ
  set N := (region (fun a => (boxAtoms n c0 a).halfspace) (boxCube n)
    ∩ fineLattice n (latticeScale ρ)).ncard with hNdef
  have heps1 : (parS n hn ε δ hε0 hε1).epsPrime < 1 := by
    have := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1; linarith
  have hvpos : 0 < volMC n hn ε δ hε0 hε1 c (boxCube n) :=
    mcVol_pos (fun a => (boxAtoms n c0 a).halfspace) (Ttc.toDNF (boxForm n hn))
      (cenMC n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1) heps1
      (ball_subset_bxOf n c0 hn)
      (volume_region_ne_top_of_isBounded (toDNF_isDNFOf (boxForm n hn))
        (isBounded_sol_bxOf n c0 hn))
      hc (boxCube n) (mem_toDNF_boxCube n hn)
  have hAU := bxSampD_almostUniform n hn ε δ hε0 hε1
  have hL : latticeCount (fun a => (boxAtoms n c0 a).halfspace) (boxForm n hn) ρ = N := by
    rw [hNdef, region_eq_bxOf n c0 hn (mem_toDNF_boxCube n hn),
      latticeCount_eq_ncard n c0 hn ρ]
  have hNpos : 0 < N := by
    rw [hNdef, region_eq_bxOf n c0 hn (mem_toDNF_boxCube n hn)]
    exact ncard_lat_pos n (sideS_pos hn hε0 hε1).le ρ
  have key : ∀ s, (1 - (parS n hn ε δ hε0 hε1).epsPrime) / (N : ℝ)
      * volMC n hn ε δ hε0 hε1 c (boxCube n)
      ≤ rates (fun a => (boxAtoms n c0 a).halfspace) (boxForm n hn)
          (Ttc.toDNF (boxForm n hn)) ρ (bxSampD n hn ε δ hε0 hε1)
          (volMC n hn ε δ hε0 hε1 c) s := by
    intro s
    have hspec := cubeAt_spec (toDNF_isDNFOf (boxForm n hn))
      (hasLatticeEnum_bxOf n c0 hn ρ) s
    have hcu : cubeAt (fun a => (boxAtoms n c0 a).halfspace) (boxForm n hn)
        (Ttc.toDNF (boxForm n hn)) ρ s = boxCube n := by
      simpa only [toDNF_boxForm hn, boxDNF, List.mem_singleton] using hspec.1
    have hmem : latticeEnum (fun a => (boxAtoms n c0 a).halfspace) (boxForm n hn) ρ s
        ∈ region (fun a => (boxAtoms n c0 a).halfspace) (boxCube n)
          ∩ fineLattice n (latticeScale ρ) :=
      ⟨hcu ▸ hspec.2, (latticeEnum_mem (hasLatticeEnum_bxOf n c0 hn ρ) s).2⟩
    simp only [rates, hcu]
    exact mul_le_mul_of_nonneg_right (hAU.lower hmem) hvpos.le
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun s _ => key s))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hL]
  have hNne : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  field_simp

/-- **`Thresh/8` fits inside `(1−ε')·Vol`.**  `Ttc.Box.thresh_div_eight_le_volumeS`
strengthened by the factor its own proof leaves in hand: `Ttc.Box.lattice_lo_bxS`
gives `Vol ≥ (1−ε/8)·L ≥ (7/8)·Thresh`, and `ε' ≤ 1/12`, so `(1−ε')·Vol ≥
(11/12)(7/8)·Thresh ≥ Thresh/8`.  Needed because the ball-walk rates only sum to
`(1−ε')·Vol_ED`, so the `(1−ε')` has to be paid for a third time. -/
theorem thresh_div_eight_le_epsPrime_volumeS (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ (1 - (parS n hn ε δ hε0 hε1).epsPrime)
        * (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal := by
  have hlat := lattice_lo_bxS (n := n) (δ := δ) hn hε0 hε1
  have hs := sideS_le_LvalS (n := n) (δ := δ) hn hε0 hε1
  have hts := thresh_le_sideS (n := n) (δ := δ) hn hε0 hε1
  have hT := parS_thresh_pos (n := n) hn hε0 hε1 hδ0 hδ1
  have heps := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1
  rw [parS_eta] at hlat
  have h1 : (1 - ε / 8) * (parS n hn ε δ hε0 hε1).thresh
      ≤ (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal := by
    nlinarith [hlat, hs, hts, hε1, hε0]
  have h2 : (7 / 8 : ℝ) * (parS n hn ε δ hε0 hε1).thresh
      ≤ (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal := by nlinarith [h1, hT, hε1]
  nlinarith [h2, heps, hT]

/-- **`Ttc.ttc_volume_endToEnd`'s `big`, for the box**, at every coin on
which the volume oracle got the volume right — the regime condition met by the
*constructed* sampler, not by a hand-written uniform one. -/
theorem big_ballWalk_box (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime) :
    (1 - (parS n hn ε δ hε0 hε1).epsPrime) * (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ ∑ s, rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
          (bxSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) s := by
  refine le_trans ?_ (sum_bxRates_ge n hn ε δ hε0 hε1 c hc)
  have heps := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1
  have hlo := (mcVol_mem_relErr (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
    (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
    (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime hc
    (boxCube n) (mem_toDNF_boxCube n hn)).1
  rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn (mem_toDNF_boxCube n hn)] at hlo
  have hthr := thresh_div_eight_le_epsPrime_volumeS n hn ε δ hε0 hε1 hδ0 hδ1
  have hstep : (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ volMC n hn ε δ hε0 hε1 c (boxCube n) := le_trans hthr hlo
  nlinarith [hstep, heps]

/-- **The constructed rates are strictly positive on the box**, at every coin the
volume oracle got right — `Ttc.rates_pos_of_almostUniform` at
`Ttc.Box.bxSampD_almostUniform`.  So the end-to-end witness is not the collapsed
`θ ≡ 0` that would satisfy `theta_eq` vacuously and fail `big`. -/
theorem bxRates_pos (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime)
    (s : Fin (latticeCount (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (rhoS n hn ε δ hε0 hε1))) :
    0 < rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
      (bxSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) s := by
  have heps1 : (parS n hn ε δ hε0 hε1).epsPrime < 1 := by
    have := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1; linarith
  refine rates_pos_of_almostUniform (toDNF_isDNFOf (boxForm n hn))
    (hasLatticeEnum_bxOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1))
    (mcVol_pos (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1) heps1
      (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
      (volume_region_ne_top_of_isBounded (toDNF_isDNFOf (boxForm n hn))
        (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn))
      hc)
    heps1 (fun i hi => ?_) s
  have hib : i = boxCube n := by
    simpa only [toDNF_boxForm hn, boxDNF, List.mem_singleton] using hi
  subst hib
  exact bxSampD_almostUniform n hn ε δ hε0 hε1

/-- **`Ttc.ttc_volume_endToEnd`'s hypotheses are satisfiable, at every
`(ε, δ) ∈ (0,1]²`.**

The box `[0,c]ⁿ` with `c = max 1 Thresh(ε, δ)`, carrying **no oracle at all**: the
volume estimates are the Monte-Carlo oracle's own output, the rates are `Ttc.rates`
built on top of them, and the sampler is the lazy ball walk of
`Ttc.kv97SamplerOfBody` — not the box's hand-written uniform `Ttc.Box.samplerOf`.
The only inputs are the box's geometry. -/
theorem ttc_volume_endToEnd_box_at (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
            (bxSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
          {t : ℕ → Fin (latticeCount
              (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
              (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ |
            ttcOutput (parS n hn ε δ hε0 hε1)
                (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
                Ttc.toDNF (rhoS n hn ε δ hε0 hε1) (boxForm n hn) t
              ∈ relErr ε (volSol
                  (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn))}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (latticeCount
        (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = (parS n hn ε δ hε0 hε1).thresh →
      Terminates (parS n hn ε δ hε0 hε1)
          (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) t)
          (Ttc.toDNF (boxForm n hn)) →
      runCost (parS n hn ε δ hε0 hε1)
          (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) t)
          cVol cSample (rhoS n hn ε δ hε0 hε1) (Ttc.toDNF (boxForm n hn))
        ≤ (Ttc.toDNF (boxForm n hn)).length * (cVol + cSample * thr)) :=
  ttc_volume_endToEnd (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn) ε δ
    hε0 hε1 hδ0 hδ1 hn
    (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) rfl Ttc.toDNF
    (toDNF_isDNFOf _) (toDNF_isPositive (boxForm_isPositive hn))
    (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)
    (parS n hn ε δ hε0 hε1) rfl (hlen_box n hn ε δ hε0 hε1)
    (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (coeff_ne_zero_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1)
    (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (Fin n ⊕ Fin n) (fun _ => bxNormal n)
    (fun _ => bxOffsetOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
    (hdil_box n hn ε δ hε0 hε1) (bfac n) one_le_bfac card_le_bfac
    (bxDm n hn ε δ hε0 hε1) (hDbody_box n hn ε δ hε0 hε1)
    (big_ballWalk_box n hn ε δ hε0 hε1 hδ0 hδ1)

/-! ### The pair, and the guarantee is a real number

One witness cannot distinguish "the hypotheses are satisfiable" from "the
hypotheses force one accuracy pair".  `Ttc.Box.AtParamsE2E` packages the
end-to-end conclusion over the data it is stated about, with `(ε, δ)` exposed, so
two instances at different parameters can be compared. -/

/-- **`Ttc.ttc_volume_endToEnd`'s conclusion, with `(ε, δ)` exposed.**

Five of the theorem's own hypotheses travel with it — the parameter block really is
at the stated accuracy, the solution set is bounded, `γ̂ > 0`, the **sampler exists**
at these parameters, and the constructed rates are **strictly positive** at every
coin the volume oracle got right — so a degenerate instance (an uninhabited
`Ttc.KV97Sampler`, or the collapsed `θ ≡ 0` that satisfies `theta_eq` vacuously)
cannot satisfy it. -/
def AtParamsE2E (n : ℕ) (ε δ : ℝ) : Prop :=
  ∃ (atoms : (Fin n ⊕ Fin n) → LinAtom n) (φ : BForm (Fin n ⊕ Fin n)) (P : Params)
      (gammaHat : ℝ)
      (cen : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF φ} → Space n)
      (sampD : Cube (Fin n ⊕ Fin n) → Space n → ℝ),
    0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ P.ε = ε ∧ P.δ = δ ∧ P.n = n ∧ 0 < gammaHat ∧
    Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ) ∧
    Nonempty (KV97Sampler (Fin n ⊕ Fin n) n (fun a => (atoms a).halfspace) (Ttc.toDNF φ)
      (P.precision gammaHat) P.epsPrime sampD) ∧
    (∀ c ∈ mcGood (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
        P.epsPrime P.deltaPrime,
      ∀ s, 0 < rates (fun a => (atoms a).halfspace) φ (Ttc.toDNF φ) (P.precision gammaHat)
        sampD (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
          P.epsPrime P.deltaPrime c) s) ∧
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (rates (fun a => (atoms a).halfspace) φ (Ttc.toDNF φ)
            (P.precision gammaHat) sampD
            (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
              P.epsPrime P.deltaPrime c))
          {t : ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ
              (P.precision gammaHat)) → ℕ |
            ttcOutput P (coveredOracles (fun a => (atoms a).halfspace) φ
                (P.precision gammaHat)
                (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
                  P.epsPrime P.deltaPrime c))
                Ttc.toDNF (P.precision gammaHat) φ t
              ∈ relErr ε (volSol (fun a => (atoms a).halfspace) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ
        (P.precision gammaHat)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles (fun a => (atoms a).halfspace) φ (P.precision gammaHat)
          (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
            P.epsPrime P.deltaPrime c) t) (Ttc.toDNF φ) →
      runCost P (coveredOracles (fun a => (atoms a).halfspace) φ (P.precision gammaHat)
            (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
              P.epsPrime P.deltaPrime c) t)
          cVol cSample (P.precision gammaHat) (Ttc.toDNF φ)
        ≤ (Ttc.toDNF φ).length * (cVol + cSample * thr))

/-- **The oracle-free capstone is instantiable at every accuracy pair in `(0,1]²`.**

The `sampD` witness is `Ttc.Box.bxSampD`, the *ball-walk* law of
`Ttc.kv97SamplerOfBody`, and the `Nonempty` witness is `Ttc.Box.bxSampler`, so this
witnesses `Ttc.ttc_volume_endToEnd` — nothing is assumed anywhere. -/
theorem atParamsE2E_of (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : AtParamsE2E n ε δ := by
  obtain ⟨hacc, hrun⟩ := ttc_volume_endToEnd_box_at n hn ε δ hε0 hε1 hδ0 hδ1
  exact ⟨boxAtoms n (sideS n hn ε δ hε0 hε1), boxForm n hn, parS n hn ε δ hε0 hε1,
    gamS n hn ε δ hε0 hε1, cenMC n hn ε δ hε0 hε1, bxSampD n hn ε δ hε0 hε1,
    hε0, hε1, hδ0, hδ1, rfl, rfl, rfl, gamS_pos hn hε0 hε1,
    isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn,
    ⟨bxSampler n hn ε δ hε0 hε1⟩,
    fun c hc s => bxRates_pos n hn ε δ hε0 hε1 c hc s, hacc, hrun⟩

/-- **The guarantee is a genuine number, not `ENNReal.toReal ⊤ = 0`.**

The conclusion of `Ttc.ttc_volume_endToEnd` puts a `toReal` around a `∫⁻`, and
`ENNReal.toReal ⊤ = 0`; so wherever the budget `1 − δ − δ/4` is **positive**, the
bound itself forces the integral to be finite and nonzero.  Nothing is assumed
here — this is read off the theorem. -/
theorem endToEnd_box_lintegral_pos_ne_top (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbudget : 0 < 1 - δ - δ / 4) (I : ENNReal)
    (hI : I = ∫⁻ c, trajLaw (rates
            (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
            (bxSampD n hn ε δ hε0 hε1)
            (volMC n hn ε δ hε0 hε1 c))
          {t : ℕ → Fin (latticeCount
              (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
              (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ |
            ttcOutput (parS n hn ε δ hε0 hε1)
                (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
                Ttc.toDNF (rhoS n hn ε δ hε0 hε1) (boxForm n hn) t
              ∈ relErr ε (volSol
                  (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn))}
        ∂(MonteCarlo.coins n)) :
    0 < I ∧ I ≠ ⊤ := by
  have hacc := (ttc_volume_endToEnd_box_at n hn ε δ hε0 hε1 hδ0 hδ1).1
  rw [← hI] at hacc
  have hpos : 0 < I.toReal := lt_of_lt_of_le hbudget hacc
  exact ⟨(ENNReal.toReal_pos_iff.1 hpos).1, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩

/-- **`ε` and `δ` are not forced, and both instances are informative.**

Two end-to-end instances at *different* accuracy pairs, both strictly inside
`(0,1)`, so both conclusions are genuine positive lower bounds on a probability —
`3/8` at `(1/2, 1/2)` and `11/16` at `(1/4, 1/4)`.  The corner `ε = δ = 1` is
excluded on purpose: there the budget `1 − δ − δ/4` is `−1/4` and certifies
nothing. -/
theorem exists_two_ttc_volume_endToEnd_instances (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε₁ δ₁ ε₂ δ₂ : ℝ,
      AtParamsE2E n ε₁ δ₁ ∧ AtParamsE2E n ε₂ δ₂ ∧
      ε₁ ≠ ε₂ ∧ δ₁ ≠ δ₂ ∧
      (0 < ε₁ ∧ ε₁ < 1) ∧ (0 < δ₁ ∧ δ₁ < 1) ∧
      (0 < ε₂ ∧ ε₂ < 1) ∧ (0 < δ₂ ∧ δ₂ < 1) ∧
      1 - δ₁ - δ₁ / 4 = 3 / 8 ∧ 1 - δ₂ - δ₂ / 4 = 11 / 16 ∧
      0 < 1 - δ₁ - δ₁ / 4 ∧ 0 < 1 - δ₂ - δ₂ / 4 :=
  ⟨1/2, 1/2, 1/4, 1/4,
    atParamsE2E_of n hn (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    atParamsE2E_of n hn (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    by norm_num, by norm_num, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

end Box

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

-- the two capstones
#print axioms ttc_volume_endToEnd_ofSampler
#print axioms ttc_volume_endToEnd

-- the sampler, constructed
#print axioms ball_smul_subset_body_of_dilate
#print axioms e2eSampD
#print axioms e2eSampler
#print axioms almostUniform_of_kv97Sampler

-- the box, with the sampler still a binder
#print axioms Box.rates_eq_thMC
#print axioms Box.big_rates_MC
#print axioms Box.rates_MC_pos
#print axioms Box.ttc_volume_endToEnd_ofSampler_box_at

-- the box, with the sampler constructed
#print axioms Box.dist_le_of_mem_bxOf
#print axioms Box.hdil_box
#print axioms Box.bxDm
#print axioms Box.hDbody_box
#print axioms Box.bxSampD
#print axioms Box.bxSampler
#print axioms Box.dilate_finite_box
#print axioms Box.dilate_nonempty_box
#print axioms Box.bxSampD_almostUniform
#print axioms Box.sum_bxRates_ge
#print axioms Box.thresh_div_eight_le_epsPrime_volumeS
#print axioms Box.big_ballWalk_box
#print axioms Box.bxRates_pos
#print axioms Box.ttc_volume_endToEnd_box_at

-- the packaged pair
#print axioms Box.AtParamsE2E
#print axioms Box.atParamsE2E_of
#print axioms Box.endToEnd_box_lintegral_pos_ne_top
#print axioms Box.exists_two_ttc_volume_endToEnd_instances

end Ttc

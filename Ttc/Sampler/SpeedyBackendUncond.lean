/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Sampler.SpeedyBackend
import Arlib.MarkovChains.Continuous.SpeedyAffine

/-!
# The speedy-walk sampler backend with **no** open hypothesis

`Ttc/Sampler/SpeedyBackend.lean` gives TTC a sampler contract as a `theorem` rather than an
assumed `structure` field, but two of its results —
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed` (`:460`) and
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_inflated` (`:509`) — carry one open binder, the
affine equivariance of the speedy walk under the normalising chart `y ↦ cen + γ • y`.  That
binder was left open because the equivariance was being proved elsewhere at the time.

It is now proved.  `Arlib/MarkovChains/Continuous/SpeedyAffine.lean` establishes the
equivariance of `Arlib.MarkovChains.speedyWalk` under exactly this chart, and this file
**composes it with the two theorems above, closing the binder**.

## Main results

* `Ttc.tvLe_transport_inscribedAffine` — the open hypothesis, **proved**, for `0 < γ` and
  measurable `K`, at a *generic* step size `δ` (so it serves both consumers below).
* `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_uncond` — the inscribed-ball
  theorem with the `hequiv` binder **deleted**.  Its conclusion, and every other binder, is
  character-for-character the original's.
* `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_uncond` — likewise for the
  `Arlib.KV97.inflated` specialisation.
* §4: **witnesses at nontrivial scaling** — `γ = 1/2 ≠ 1` for the inscribed theorem (with a
  nonzero centre as well), and `γ + κ = 3/4 ≠ 1` for the inflated one.  The pre-existing
  witnesses in `SpeedyBackend.lean` discharged `hequiv` only because their parameters made
  the chart the *identity*; these do not, so the affine machinery is genuinely exercised.
  `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_half_dim2` has **no hypotheses at
  all**.

## How the two charts and the two step sizes line up

`SpeedyBackend` writes the chart as `aff y = cen + γ • y`; `SpeedyAffine` writes it as
`S z = γ • z + cen`.  These are the same function but **not syntactically equal**, so
`Ttc.tvLe_transport_inscribedAffine` opens with a one-line `funext`/`add_comm` bridge and
rewrites the hypothesis into `SpeedyAffine`'s orientation.

The step sizes line up too, but again **not syntactically**.  `SpeedyAffine`'s crux
`Arlib.MarkovChains.map_speedyWalk_affineChart` carries `δ / γ` on the preimage side against
`δ` on the `K` side; `SpeedyBackend`'s `hequiv` carries `ρ/(4n)` against `γ·(ρ/(4n))`.
Instantiating the crux at `δ := γ * (ρ/(4n))` and cancelling with `mul_div_cancel_left₀`
(`γ·δ/γ = δ`, valid since `γ ≠ 0`) makes them identical.  That single rewrite is the whole
reconciliation; no scaling had to be changed on either side.

## What the proof is

Write `S z = γ • z + cen`.  Four transports from `SpeedyAffine`, in this order:

1. `Arlib.MarkovChains.map_speedyWalk_affineChart` — the kernel identity, at `δ := γ·(ρ/(4n))`;
2. `Arlib.MarkovChains.map_lazy_of_map_kernel` — lift it through `lazy`;
3. `Arlib.MarkovChains.tvLe_map` + `Arlib.MarkovChains.map_iterate_of_map_kernel` — push the
   total-variation bound forward along `S` and commute `S` past the `t`-fold iterate;
4. `Arlib.MarkovChains.map_uniformOn_affineChart`, twice — once to turn
   `Measure.map S (Arlib.uniformOn volume (S ⁻¹' K))` into `Arlib.uniformOn volume K`, and
   once, via `Arlib.MarkovChains.preimage_affineChart_ball` at `y = 0` (which gives
   `S ⁻¹' B(cen,γ) = B(0,1)`), to turn `Measure.map S (Arlib.uniformOn volume (B(0,1)))` into
   `Arlib.uniformOn volume (B(cen,γ))`.

No Jacobian survives: it cancels inside each of `map_speedyWalk_affineChart` and
`map_uniformOn_affineChart`.

## Scope — read before quoting anything from this file

Every theorem here is a **Markov-chain mixing statement**, exactly as in
`Ttc/Sampler/SpeedyBackend.lean`: after `m` applications of the kernel
`Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk K δ)`, the law of the walk is within
total variation `ρ` of `Arlib.uniformOn volume K`.  It is **not**:

* a running-time claim about TTC or about any algorithm.  `m` counts abstract kernel
  applications; nothing here bounds the cost of **one** step (which needs a membership oracle
  for `K` and a sample from a ball), nor bit complexity, nor the number of oracle calls.  In
  particular **nothing of the form `O(m·n⁴)` is claimed or implied**;
* a proof that **TTC is polynomial-time** — it is not, and this file does not make it so.
  TTC's volume oracle is independently exponential, the rounding/rejection stage of the
  sampler (`Ttc.kv97SampD`, `Ttc/Sampler/Construct.lean`) is uncosted here, and TTC's cost
  model carries no complexity field at all, so no complexity statement about the pipeline
  can even be phrased against it;
* a bound on volume computation or lattice counting, and not a replacement for
  `Ttc.HitAndRunTheorem11Input`: nothing in `Ttc/` is rewired by this file.

Closing `hequiv` removes an *assumption*; it adds no new capability and changes no cost.

## Declarations

No `def`, `structure`, `class`, `axiom`, `sorry`, `admit` or `native_decide` occurs below:
every declaration is a `theorem`.  The step counts quoted in §4 are the existing
`Ttc.speedyMixSteps`, whose meaning is pinned in `SpeedyBackend.lean`.
-/

namespace Ttc

open MeasureTheory
open scoped ENNReal

/-! ## 1. The open hypothesis, proved -/

/-- **The affine-equivariance hypothesis of
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed`, proved.**

For measurable `K` and `0 < γ`: a total-variation bound for the lazy speedy walk with step
`δ` on the *normalised* body `(fun y => cen + γ • y) ⁻¹' K`, started from
`Arlib.uniformOn volume (Metric.ball 0 1)`, transports to a bound with the **same** step
count `t` and the **same** tolerance `e` for the lazy speedy walk with step `γ * δ` on `K`,
started from `Arlib.uniformOn volume (Metric.ball cen γ)`.

Stated at a generic `δ` — the two consumers below use it at `δ = ρ/(4n)`, with `γ` taken to
be the inscribed radius, resp. the inflated inscribed radius `γ + Arlib.KV97.kappaOf cp r`.

The chart is spelled `fun y => cen + γ • y` here, matching `SpeedyBackend.lean`; the first
step of the proof rewrites it to `fun z => γ • z + cen`, matching `SpeedyAffine.lean`.  See
the module docstring for the step-size reconciliation `γ·δ/γ = δ`. -/
theorem tvLe_transport_inscribedAffine {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {cen : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (δ : ℝ) :
    ∀ (t : ℕ) (e : ℝ≥0∞),
      Arlib.TVLe
          (Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
              ((fun y => cen + γ • y) ⁻¹' K) δ))
            (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) t)
          (Arlib.uniformOn volume ((fun y => cen + γ • y) ⁻¹' K)) e →
      Arlib.TVLe
          (Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk K (γ * δ)))
            (Arlib.uniformOn volume (Metric.ball cen γ)) t)
          (Arlib.uniformOn volume K) e := by
  -- the two spellings of the chart
  have hchart : (fun y : EuclideanSpace ℝ (Fin n) => cen + γ • y)
      = fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen := by
    funext y; exact add_comm cen (γ • y)
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) :=
    Arlib.MarkovChains.measurable_affineChart γ cen
  -- the step-size reconciliation: the crux's `δ/γ` at `δ := γ * δ` is `δ`
  have hstep : γ * δ / γ = δ := mul_div_cancel_left₀ _ hγ.ne'
  have hker : ∀ y : EuclideanSpace ℝ (Fin n),
      Measure.map (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen)
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
            ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) δ) y)
        = Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk K (γ * δ)) (γ • y + cen) := by
    refine Arlib.MarkovChains.map_lazy_of_map_kernel hS (fun z => ?_)
    have h := Arlib.MarkovChains.map_speedyWalk_affineChart hKm hγ cen (γ * δ) z
    rwa [hstep] at h
  -- the chart carries `B(0,1)` onto `B(cen, γ)`
  have hcen : γ • (0 : EuclideanSpace ℝ (Fin n)) + cen = cen := by rw [smul_zero, zero_add]
  have hball0 : (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' (Metric.ball cen γ)
      = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    have h := Arlib.MarkovChains.preimage_affineChart_ball hγ cen
      (0 : EuclideanSpace ℝ (Fin n)) γ
    rw [hcen, div_self hγ.ne'] at h
    exact h
  intro t e h
  rw [hchart] at h
  have hmap := Arlib.MarkovChains.tvLe_map hS h
  rw [Arlib.MarkovChains.map_iterate_of_map_kernel hS hker,
    Arlib.MarkovChains.map_uniformOn_affineChart hγ cen hKm, ← hball0,
    Arlib.MarkovChains.map_uniformOn_affineChart hγ cen measurableSet_ball] at hmap
  exact hmap

/-! ## 2. The two theorems, restated without `hequiv`

The statements below are the originals with the `hequiv` binder **deleted and nothing else
changed** — same binder names, same order, same conclusion character for character. -/

/-- **`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed` with no open hypothesis.**

Identical to `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed`
(`Ttc/Sampler/SpeedyBackend.lean:460`) except that the `hequiv` binder is gone: it is
supplied by `Ttc.tvLe_transport_inscribedAffine` at `δ = ρ/(4n)`.

So: for measurable convex `K ⊆ ℝⁿ` (`2 ≤ n`) with an inscribed ball `Metric.ball cen γ ⊆ K`
at *any* centre and *any* positive radius, and all pairwise distances at most `Dm`, the lazy
speedy walk with step `γ·ρ/(4n)`, started from `Arlib.uniformOn volume (Metric.ball cen γ)`,
is within total variation `ρ` of `Arlib.uniformOn volume K` after `Ttc.speedyMixSteps n
(Dm/γ) ρ` steps. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_uncond {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    {cen : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ K)
    {Dm : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ Dm)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    {m : ℕ} (hm : speedyMixSteps n (Dm / γ) rho ≤ m) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk K
          (γ * (rho / (4 * (n : ℝ))))))
        (Arlib.uniformOn volume (Metric.ball cen γ)) m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal rho) :=
  tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed hn hKm hKc hγ hball hD hrho0 hrho1
    (tvLe_transport_inscribedAffine hKm hγ (rho / (4 * (n : ℝ)))) hm

/-- **`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_inflated` with no open hypothesis.**

Identical to `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_inflated`
(`Ttc/Sampler/SpeedyBackend.lean:509`) except that the `hequiv` binder is gone.  Here the
chart's scaling is the inflated inscribed radius `γ + Arlib.KV97.kappaOf cp r`, which is
positive because `Arlib.KV97.kappaOf_nonneg hcp` gives `0 ≤ kappaOf cp r` and `hγ` gives
`0 < γ`.

Every remaining input is a fact about the *problem instance* — an inscribed ball and a
diameter for the original polytope `Arlib.Polytope.body A b` — exactly as in
`Ttc.kv97SamplerOfBody` (`Ttc/Sampler/Construct.lean:353`). -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_uncond {n : ℕ} {ι : Type*} (hn : 2 ≤ n)
    (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) {cp : ℝ} (hcp : 0 ≤ cp) (r : ℝ)
    {cen : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hballBody : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    {Dm : ℝ} (hDbody : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b,
      dist x y ≤ Dm)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    {m : ℕ} (hm : speedyMixSteps n
      ((1 + Arlib.KV97.kappaOf cp r / γ) * Dm / (γ + Arlib.KV97.kappaOf cp r)) rho ≤ m) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
          (Arlib.KV97.inflated A b cp r)
          ((γ + Arlib.KV97.kappaOf cp r) * (rho / (4 * (n : ℝ))))))
        (Arlib.uniformOn volume (Metric.ball cen (γ + Arlib.KV97.kappaOf cp r))) m)
      (Arlib.uniformOn volume (Arlib.KV97.inflated A b cp r)) (ENNReal.ofReal rho) := by
  have hκ : (0 : ℝ) ≤ Arlib.KV97.kappaOf cp r := Arlib.KV97.kappaOf_nonneg hcp
  exact tvLe_iterate_lazy_speedyWalk_uniformOn_inflated hn A b hcp r hγ hballBody hDbody
    hrho0 hrho1
    (tvLe_transport_inscribedAffine (Arlib.KV97.measurableSet_inflated A b cp r)
      (by linarith : (0 : ℝ) < γ + Arlib.KV97.kappaOf cp r) (rho / (4 * (n : ℝ)))) hm

/-! ## 3. The chart of the inflated witness is genuinely non-identity -/

/-- `Arlib.KV97.kappaOf (1/4) 1 = 1/4`: at facet bound `r = 1` the `√(2 log r)` term
vanishes, so the inflation displacement is exactly the confidence parameter. -/
theorem kappaOf_quarter_one : Arlib.KV97.kappaOf (1 / 4 : ℝ) 1 = 1 / 4 := by
  simp [Arlib.KV97.kappaOf]

/-- **The inflated witness of §4 has a nontrivial scaling**: its chart scales by
`γ + κ = 1/2 + 1/4 = 3/4 ≠ 1`, so — unlike
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_box`, where `γ + κ = 1` — the chart is
not the identity and the equivariance is genuinely used.  Machine-checked here rather than
asserted in prose. -/
theorem inflatedBox_scale_ne_one : (1 / 2 : ℝ) + Arlib.KV97.kappaOf (1 / 4 : ℝ) 1 ≠ 1 := by
  rw [kappaOf_quarter_one]; norm_num

/-! ## 4. Witnesses at **nontrivial** scaling (`CLAUDE.md` §11)

`SpeedyBackend.lean`'s `..._of_inscribed_ballTwo` and `..._inflated_box` discharge `hequiv`
only because their parameters make the normalising map the *identity* (`cen = 0`, `γ = 1`,
resp. `γ + κ = 1`).  They therefore witness satisfiability of the hypothesis bundle but
exercise no affine machinery.  The witnesses below do:

| witness | chart | discharges | leaves open |
| --- | --- | --- | --- |
| `..._of_inscribed_half` | `y ↦ 3e₀ + (1/2)•y`, **both** parts nontrivial | everything | `2 ≤ n` |
| `..._of_inscribed_half_dim2` | the same at `n = 2` | **everything** — no hypotheses | — |
| `..._inflated_box_quarter` | `y ↦ 3e₀ + (3/4)•y`, on a genuine `Arlib.KV97.inflated` body | everything | `2 ≤ n` |

`ρ = 1/2` is a non-trivial tolerance (`ENNReal.ofReal 1` is the vacuous total-variation
bound), and in each case the start's support is a *strict* subset of the body, so the bound
is not `Arlib.TVLe.refl` in disguise.  What is **not** claimed, exactly as in
`SpeedyBackend.lean`: that the `m`-step law itself differs from the target. -/

/-- **Witness for the inscribed-ball theorem at a nontrivial chart.**

`cen = 3·e₀ ≠ 0` (a nonzero translation), `γ = 1/2 ≠ 1` (a non-unit scaling),
`K = Metric.ball cen 1`, `Dm = 2`, `ρ = 1/2`, `m` the canonical step count at the
well-roundedness ratio `Dm/γ = 4`.  Every hypothesis of
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_uncond` is discharged
(`measurableSet_ball`, `convex_ball`, `norm_num`, `Metric.ball_subset_ball`,
`Arlib.MarkovChains.dist_le_two_of_mem_ball_one`, `le_rfl`); only `2 ≤ n` survives, and it
is the scope limit inherited from `Arlib.hiso_ellProb_of_ball_bound`.

Neither half of the chart is the identity, so this witness — unlike
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_ballTwo` — genuinely exercises
`Ttc.tvLe_transport_inscribedAffine`. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_half {n : ℕ} (hn : 2 ≤ n) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
          (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ)) 1)
          ((1 / 2 : ℝ) * ((1 / 2 : ℝ) / (4 * (n : ℝ))))))
        (Arlib.uniformOn volume
          (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ)) (1 / 2 : ℝ)))
        (speedyMixSteps n ((2 : ℝ) / (1 / 2 : ℝ)) (1 / 2)))
      (Arlib.uniformOn volume
        (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ)) 1))
      (ENNReal.ofReal (1 / 2)) :=
  tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_uncond hn measurableSet_ball
    (convex_ball _ _) (γ := 1 / 2) (by norm_num) (Metric.ball_subset_ball (by norm_num))
    (Dm := 2) (Arlib.MarkovChains.dist_le_two_of_mem_ball_one _) (by norm_num) (by norm_num)
    le_rfl

/-- **The same witness at `n = 2`: a nontrivially-scaled instance with no hypotheses at all.**

The lazy speedy walk on `B(3e₀, 1) ⊆ ℝ²` with step `(1/2)·(1/2)/8 = 1/32`, started from the
uniform law on `B(3e₀, 1/2)`, is within total variation `1/2` of the uniform law on
`B(3e₀, 1)` after `Ttc.speedyMixSteps 2 4 (1/2)` steps.  Nothing is assumed, and the chart
`y ↦ 3e₀ + (1/2)•y` is neither a translation-free nor a scaling-free map. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_half_dim2 :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
          (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin 2) (3 : ℝ)) 1)
          ((1 / 2 : ℝ) * ((1 / 2 : ℝ) / (4 * ((2 : ℕ) : ℝ))))))
        (Arlib.uniformOn volume
          (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin 2) (3 : ℝ)) (1 / 2 : ℝ)))
        (speedyMixSteps 2 ((2 : ℝ) / (1 / 2 : ℝ)) (1 / 2)))
      (Arlib.uniformOn volume
        (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin 2) (3 : ℝ)) 1))
      (ENNReal.ofReal (1 / 2)) :=
  tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_half (n := 2) le_rfl

/-- **Witness for the inflated-polytope theorem at a nontrivial chart.**

The body is the Kannan--Vempala inflation, by `κ = Arlib.KV97.kappaOf (1/4) 1 = 1/4`, of the
axis-aligned box of half-width `1/2` centred at `3·e₀`.  The inscribed radius of the
inflation is `γ + κ = 1/2 + 1/4 = 3/4`, which `Ttc.inflatedBox_scale_ne_one` proves is
**not** `1` — so, unlike `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_box`, the
normalising map here is not the identity in either its translation or its scaling.

Every hypothesis of `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_uncond` is
discharged (`norm_num` for `0 ≤ cp` and `0 < γ`, `Arlib.KV97.ball_subset_box`,
`Arlib.KV97.dist_le_of_mem_box`, `norm_num` for `0 < ρ ≤ 1`, `le_rfl` for the step count);
only `2 ≤ n` survives.  The inflation displacement is genuinely positive. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_box_quarter {n : ℕ} (hn : 2 ≤ n) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
          (Arlib.KV97.inflated (Arlib.KV97.boxA n)
            (Arlib.KV97.boxB (1 / 2)
              (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ))) (1 / 4) 1)
          ((1 / 2 + Arlib.KV97.kappaOf (1 / 4 : ℝ) 1) * ((1 / 2 : ℝ) / (4 * (n : ℝ))))))
        (Arlib.uniformOn volume
          (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ))
            (1 / 2 + Arlib.KV97.kappaOf (1 / 4 : ℝ) 1)))
        (speedyMixSteps n
          ((1 + Arlib.KV97.kappaOf (1 / 4 : ℝ) 1 / (1 / 2))
              * (2 * (1 / 2) * Real.sqrt (n : ℝ))
            / (1 / 2 + Arlib.KV97.kappaOf (1 / 4 : ℝ) 1)) (1 / 2)))
      (Arlib.uniformOn volume (Arlib.KV97.inflated (Arlib.KV97.boxA n)
        (Arlib.KV97.boxB (1 / 2)
          (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ))) (1 / 4) 1))
      (ENNReal.ofReal (1 / 2)) :=
  tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_uncond hn (Arlib.KV97.boxA n)
    (Arlib.KV97.boxB (1 / 2) (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ)))
    (by norm_num) 1 (γ := 1 / 2) (by norm_num) (Arlib.KV97.ball_subset_box _)
    (Arlib.KV97.dist_le_of_mem_box (R := 1 / 2) (by norm_num) _)
    (by norm_num) (by norm_num) le_rfl

/-! ### Axiom audit (`CLAUDE.md` §4)

Every declaration in this file must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms tvLe_transport_inscribedAffine
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_uncond
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_uncond
#print axioms kappaOf_quarter_one
#print axioms inflatedBox_scale_ne_one
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_half
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_half_dim2
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_box_quarter

end Ttc

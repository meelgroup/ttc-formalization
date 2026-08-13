/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.UniformSamplerUncond
import Arlib.Lattice.KV97.InflateGeom
import Ttc.Probability.BallWalk

/-!
# A speedy-walk sampler backend whose mixing bound is a **theorem**

`Ttc.HitAndRunTheorem11Input` (`Ttc/Sampler/HitAndRunTheorem11.lean:94`) is a `structure`
whose single field `mixing` *assumes* a total-variation bound of the shape

    Arlib.TVLe (Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun K) sigma m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps).

That structure is **inhabited nowhere** in `Ttc/` or `Arlib/`: no constructor for it is
applied anywhere, so every hit-and-run cost number downstream is arithmetic about an object
nobody has exhibited.

This file supplies the same *shape* for a different kernel — the **lazy speedy walk**
`Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk K δ)` — and **proves** it.  Nothing
here is a `structure`, a `class`, an `axiom`, or a field: every declaration below except the
single step-count `def` is a `theorem`, and the analytic content is
`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond`
(`Arlib/MarkovChains/Continuous/UniformSamplerUncond.lean:291`), which carries **no**
isoperimetry, warmness or smoothness binder.

## Main results

* `Ttc.speedyMixSteps` — the step count.  The **only** `def` in the file; see below.
* `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn` — the contract-shaped mixing theorem.
* `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_at_steps` — the same at the canonical count,
  the analogue of `Ttc.HitAndRunTheorem11Input.at_steps` (`:117`).
* `Ttc.speedyMixSteps_le` — the step count in closed form: **polynomial**.
* `Ttc.ballWalkConductance_le`, `Ttc.exp_mul_log_le_mixSteps` — the contrast with
  `Ttc.mixSteps` (`Ttc/Probability/BallWalk.lean:40`), which is **exponential**.
* `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed` — the same theorem for a body
  presented by an inscribed ball `B(cen, γ)` and a diameter `Dm`, i.e. the presentation TTC
  actually has.  Carries the affine-equivariance hypothesis described below.
* `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_inflated` — that, specialised to
  `Arlib.KV97.inflated`, TTC's actual sampling body, with the geometry stated about the
  *original* polytope.
* Three non-vacuity witnesses (§7), one of them with **no hypotheses whatsoever**.

## How this differs in shape from `HitAndRunTheorem11Input.mixing`

Read this before treating the two as interchangeable.

| | hit-and-run contract | here |
| --- | --- | --- |
| status | **assumed** (a `structure` field, never inhabited) | **proved** |
| kernel | `hitAndRun K` | `lazy (speedyWalk K δ)`, `δ = ρ/(4n)` |
| target | `Arlib.uniformOn volume K` | the same |
| start | any `sigma`, with warmness binders `M`, `S`, `hS`, `hdom` | **fixed** to
  `Arlib.uniformOn volume (Metric.ball 0 1)` — a law one can sample directly |
| geometry | `closedBall zin r ⊆ K ⊆ closedBall zout R` | `B(0,1) ⊆ K`, `diam K ≤ D` |
| dimension | `1 ≤ n` | `2 ≤ n` |

Two of these are genuine scope differences, not improvements:

* **the start is fixed, not universally quantified.**  The hit-and-run contract would give a
  bound from *any* warm `sigma`; the theorems here give one from the specific samplable law
  `uniformOn volume (Metric.ball 0 1)`.  Fewer assumptions, narrower conclusion.  A caller
  who needs an arbitrary warm start does not get it from this file.
* **`2 ≤ n`, not `1 ≤ n`.**  Inherited from `Arlib.hiso_ellProb_of_ball_bound`, the
  isoperimetric input of `..._uncond`.  It is a real limit of the upstream proof and is
  **not** widened here.

## The step count: polynomial, against `Ttc.mixSteps`'s exponential

Both counts are the *same* function `Arlib.MarkovChains.conductanceMixingTime` of a
warm-start constant, a **conductance floor**, and an accuracy — so the comparison is a
comparison of floors.

    Ttc.mixSteps n γ Dm δ Mw eps   floor = min ((γ/(γ+Dm))ⁿ/32)
                                             ((1/2)ⁿ/Dm · ((γ/(γ+Dm))ⁿ)² · δ/(128n))
    Ttc.speedyMixSteps n D rho     floor = min (1/32) (ρ/(8192·D·n²))

`Ttc.ballWalkConductance_le` proves the ball-walk floor is at most `2⁻ⁿ/32` as soon as
`0 < γ ≤ Dm`, and `Ttc.exp_mul_log_le_mixSteps` turns that into a **lower** bound

    Ttc.mixSteps n γ Dm δ Mw eps ≥ 2048 · 4ⁿ · log(√Mw / eps),

so `Ttc.mixSteps` is `2^{Θ(n)}`: it is not a polynomial-time step count and must never be
quoted as one.  `Ttc.speedyConductance_eq` proves the speedy floor is exactly
`ρ/(8192·D·n²)` below the cap, and `Ttc.speedyMixSteps_le` proves

    Ttc.speedyMixSteps n D ρ ≤ (2n·log(1+D) + 2·log(2/ρ)) · (1024 + (8192·D·n²/ρ)²) + 1
                             = O(n⁵ · D² · log(1+D) / ρ²),

polynomial in `n`, `D` and `1/ρ`.  **The improvement is exactly this: an exponential
`4ⁿ` factor is replaced by a polynomial one.**  On a TTC body with inscribed radius `γ` and
diameter `Dm` the normalised diameter is `D = Dm/γ`, so the speedy count is
`O(n⁵ (Dm/γ)² log(1+Dm/γ) / ρ²)` — polynomial in the aspect ratio, where the ball walk's is
exponential in `n`.

## The equivariance hypothesis (`CLAUDE.md` §1)

`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond` needs `B(0,1) ⊆ K`; TTC's
bodies satisfy `Metric.ball cen γ ⊆ Arlib.KV97.inflated A b c r` instead
(`Arlib/Lattice/KV97/Inflate.lean:115-116`, exported as `Arlib.KV97.ball_subset_inflated`).
The normalisation is `x ↦ (x − cen)/γ`, equivalently the preimage under
`aff : y ↦ cen + γ • y`.  This file proves, unconditionally, everything about
`aff ⁻¹' K` that the sampler theorem needs:

* `Ttc.ball_subset_inscribedPreimage` — `B(0,1) ⊆ aff ⁻¹' K`;
* `Ttc.convex_inscribedPreimage` — `aff ⁻¹' K` is convex;
* `Ttc.dist_le_of_mem_inscribedPreimage` — its diameter is at most `Dm/γ`;
* `Ttc.measurable_inscribedAffine` — hence `aff ⁻¹' K` is measurable.

What it does **not** prove is that the speedy walk itself commutes with `aff`.  That is
carried as an explicit hypothesis, in exactly the shape needed and no larger:

    hequiv : ∀ (t : ℕ) (e : ℝ≥0∞),
      Arlib.TVLe (iterate (lazy (speedyWalk (aff ⁻¹' K) (ρ/(4n))))
                    (uniformOn volume (ball 0 1)) t)
                 (uniformOn volume (aff ⁻¹' K)) e →
      Arlib.TVLe (iterate (lazy (speedyWalk K (γ · ρ/(4n))))
                    (uniformOn volume (ball cen γ)) t)
                 (uniformOn volume K) e

— note the step size scales, `δ ↦ γ·δ`, and the start law transports from
`uniformOn volume (ball 0 1)` to `uniformOn volume (ball cen γ)`.  A sibling development is
proving the affine equivariance of `speedyWalk`; composing it with the pushforward identity
`Measure.map aff (uniformOn volume (ball 0 1)) = uniformOn volume (ball cen γ)` discharges
`hequiv` in one step.  Until then it is an **open hypothesis**, and §7 says exactly how far
the witnesses certify it.

## Scope — read before quoting anything from this file

Every theorem here is a **Markov-chain mixing statement**: after `m` applications of the
kernel `lazy (speedyWalk K δ)`, the law of the walk is within total variation `ρ` of
`Arlib.uniformOn volume K`.  It is **not**:

* a running-time claim about TTC or about any algorithm.  `m` counts abstract kernel
  applications; nothing here bounds the cost of **one** step (which needs a membership
  oracle for `K` and a sample from a ball), nor the bit complexity, nor the number of oracle
  calls.  In particular **nothing of the form `O(m·n⁴)` is claimed or implied, and this file
  does not make TTC polynomial-time**;
* a bound on the rounding or rejection stage of the TTC sampler (`Ttc.kv97SampD`,
  `Ttc/Sampler/Construct.lean`), nor on volume computation or lattice counting;
* a replacement for `Ttc.HitAndRunTheorem11Input`.  Nothing in `Ttc/` is rewired to use the
  speedy walk by this file; it adds a *provable* backend beside the assumed one.

## The one `def` (`CLAUDE.md` §11)

`Ttc.speedyMixSteps` is the only `def`.  Its name promises "a number of steps of the lazy
speedy walk that suffices", and that promise is **proved in this file** by
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_at_steps`; its size is pinned by
`Ttc.speedyMixSteps_le`.  No `structure`, `class`, `axiom`, `sorry`, `admit` or
`native_decide` occurs anywhere below.
-/

namespace Ttc

open MeasureTheory
open scoped ENNReal

/-! ## 1. The step count -/

/-- **The step count for the lazy speedy walk.**

`Arlib.MarkovChains.conductanceMixingTime` at the warm-start constant `M = (1+D)^(2n)` and
the conductance floor `min (1/32) (ρ/(8192·D·n²))` that
`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond` certifies for a convex
body `K` with `B(0,1) ⊆ K` and `diam K ≤ D`, to reach total-variation accuracy `ρ`.

Deliberately the **same** `conductanceMixingTime` as `Ttc.mixSteps`
(`Ttc/Probability/BallWalk.lean:40`), so that the two differ only in the conductance floor.

`CLAUDE.md` §11: the meaning this name promises — "enough steps" — is not left to the name.
It is proved by `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_at_steps` immediately below, and
its size is pinned by `Ttc.speedyMixSteps_le`.  Nothing else is asserted about it. -/
noncomputable def speedyMixSteps (n : ℕ) (D rho : ℝ) : ℕ :=
  Arlib.MarkovChains.conductanceMixingTime ((1 + D) ^ (2 * n))
    (min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) (rho / 2)

/-! ## 2. The mixing theorem in the shape TTC consumes -/

/-- **The sampler contract, for the lazy speedy walk, as a theorem.**

For measurable convex `K ⊆ ℝⁿ` (`2 ≤ n`) with `B(0,1) ⊆ K` and all pairwise distances at
most `D`, and for `0 < ρ ≤ 1`: started from the samplable law
`Arlib.uniformOn volume (Metric.ball 0 1)` and run for any `m ≥ Ttc.speedyMixSteps n D ρ`
steps, the lazy speedy walk with step `δ = ρ/(4n)` is within total variation `ρ` of
`Arlib.uniformOn volume K`.

The conclusion is verbatim the conclusion of `Ttc.HitAndRunTheorem11Input.mixing`
(`Ttc/Sampler/HitAndRunTheorem11.lean:111-113`) with `hitAndRun K` replaced by
`lazy (speedyWalk K δ)` and `sigma` fixed to the unit-ball law — **but it is a `theorem`,
not a `structure` field**.  Its analytic content is
`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond`, which assumes no
isoperimetric inequality, no warmness and no smoothness.

See the module docstring for the two places the shape differs from the hit-and-run
contract (fixed start; `2 ≤ n`), and for the scope caveat. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    {m : ℕ} (hm : speedyMixSteps n D rho ≤ m) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyWalk K (rho / (4 * (n : ℝ)))))
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal rho) :=
  (Arlib.MarkovChains.mixesWithin_iff _ _ _ _ _).1
    (Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond hn hKm hKc hball hD
      hrho0 hrho1 hm)

/-- **The contract instantiated at the canonical step count** — the analogue of
`Ttc.HitAndRunTheorem11Input.at_steps` (`Ttc/Sampler/HitAndRunTheorem11.lean:117`), which
takes the contract structure as its first argument.  This one takes nothing: there is no
structure to take.

This is also what pins the meaning of the `def` `Ttc.speedyMixSteps` (`CLAUDE.md` §11). -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_at_steps {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyWalk K (rho / (4 * (n : ℝ)))))
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
        (speedyMixSteps n D rho))
      (Arlib.uniformOn volume K) (ENNReal.ofReal rho) :=
  tvLe_iterate_lazy_speedyWalk_uniformOn hn hKm hKc hball hD hrho0 hrho1 le_rfl

/-! ## 3. The step count is polynomial -/

/-- **The speedy conductance floor in lowest terms**: the second branch of the `min` inside
`Ttc.speedyMixSteps` is exactly `ρ/(8192·D·n²)`.  Inverse-polynomial in `n` and `D` — this
is the single number that separates this file's step count from `Ttc.mixSteps`'s. -/
theorem speedyConductance_eq {n : ℕ} {D rho : ℝ} (hD : D ≠ 0) (hn : (n : ℝ) ≠ 0) :
    1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))
      = rho / (8192 * D * (n : ℝ) ^ 2) := by
  field_simp
  ring

/-- **`Ttc.speedyMixSteps` is polynomial**, with the constants written out:

    speedyMixSteps n D ρ ≤ (2n·log(1+D) + 2·log(2/ρ)) · (1024 + (8192·D·n²/ρ)²) + 1.

The right-hand side is `O(n⁵ · D² · log(1+D) / ρ²)`: polynomial in `n`, `D` and `1/ρ`.  The
`1024` is the `1/32` cap on the conductance and the squared term is `(ρ/(8192 D n²))⁻²`.

`hD : 1/2 ≤ D` is not an extra assumption in context — it is forced by `B(0,1) ⊆ K`
(`Arlib.MarkovChains.half_le_diam_bound_of_ball_subset`).  The exponent is not sharp; see
`UniformSamplerUncond.lean`'s module docstring for the three upstream `√n` losses. -/
theorem speedyMixSteps_le {n : ℕ} (hn : 1 ≤ n) {D rho : ℝ} (hD : (1 : ℝ) / 2 ≤ D)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    (speedyMixSteps n D rho : ℝ)
      ≤ (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
          * (1024 + (8192 * D * (n : ℝ) ^ 2 / rho) ^ 2) + 1 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD0 : (0 : ℝ) < D := by linarith
  have hM : (1 : ℝ) ≤ (1 + D) ^ (2 * n) := one_le_pow₀ (by linarith)
  have hceq : 1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))
      = rho / (8192 * D * (n : ℝ) ^ 2) :=
    speedyConductance_eq hD0.ne' (by linarith)
  have hc0 : (0 : ℝ) < 1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)) := by positivity
  have hphi0 : (0 : ℝ) < min (1 / 32)
      (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))) := lt_min (by norm_num) hc0
  have heps : (0 : ℝ) < rho / 2 := by linarith
  have hsqrt : rho / 2 ≤ Real.sqrt ((1 + D) ^ (2 * n)) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt ((1 + D) ^ (2 * n)) := by
      have h2 := Real.sqrt_le_sqrt hM
      rwa [Real.sqrt_one] at h2
    linarith
  have hlogM : Real.log ((1 + D) ^ (2 * n)) = 2 * (n : ℝ) * Real.log (1 + D) := by
    rw [Real.log_pow]; push_cast; ring
  have hlogeps : Real.log (1 / (rho / 2)) = Real.log (2 / rho) := by rw [one_div_div]
  have hle := Arlib.MarkovChains.conductanceMixingTime_le (M := (1 + D) ^ (2 * n))
    (phi := min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))))
    (eps := rho / 2) hM hphi0 heps hsqrt
  rw [hlogM, hlogeps] at hle
  -- the numerator is nonnegative
  have hlog1 : (0 : ℝ) ≤ Real.log (1 + D) := Real.log_nonneg (by linarith)
  have hlog2 : (0 : ℝ) ≤ Real.log (2 / rho) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hrho0]; linarith
  have hNnn : (0 : ℝ) ≤ 2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho) := by
    have h1 : (0 : ℝ) ≤ 2 * (n : ℝ) * Real.log (1 + D) :=
      mul_nonneg (by positivity) hlog1
    linarith
  -- the conductance floor's inverse square is polynomial
  have hinv : ((min (1 / 32)
        (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2)⁻¹
      ≤ 1024 + (8192 * D * (n : ℝ) ^ 2 / rho) ^ 2 := by
    have hX : (0 : ℝ) ≤ (8192 * D * (n : ℝ) ^ 2 / rho) ^ 2 := sq_nonneg _
    rcases min_cases (1 / 32 : ℝ)
      (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; norm_num; linarith
    · rw [h1, hceq, ← inv_pow, inv_div]; linarith
  have hstep : (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
        * ((min (1 / 32)
            (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2)⁻¹
      ≤ (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
        * (1024 + (8192 * D * (n : ℝ) ^ 2 / rho) ^ 2) :=
    mul_le_mul_of_nonneg_left hinv hNnn
  have hle' : (speedyMixSteps n D rho : ℝ)
      ≤ (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
          * ((min (1 / 32)
              (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2)⁻¹ + 1 := by
    rw [← div_eq_mul_inv]
    simpa [speedyMixSteps] using hle
  linarith

/-! ## 4. `Ttc.mixSteps`, by contrast, is exponential -/

/-- The lazy-ball-walk conductance floor behind `Ttc.mixSteps` is at most `2⁻ⁿ/32`. -/
theorem ballWalkConductance_le {n : ℕ} {γ Dm δ : ℝ} (hγ : 0 < γ) (hγD : γ ≤ Dm) :
    min ((γ / (γ + Dm)) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * δ / (128 * (n : ℝ)))
      ≤ (1 / 2 : ℝ) ^ n / 32 := by
  refine (min_le_left _ _).trans ?_
  have hsum : (0 : ℝ) < γ + Dm := by linarith
  have hhalf : γ / (γ + Dm) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hsum (by norm_num)]
    linarith
  have hpow : (γ / (γ + Dm)) ^ n ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_left₀ (by positivity) hhalf n
  linarith

/-- **`Ttc.mixSteps` is at least `2048 · 4ⁿ · log(√Mw/eps)`** — an *exponential* lower bound
on the ball-walk step count TTC currently uses.

`Ttc.mixSteps` is `⌈log(√Mw/eps)/(φ²/2)⌉₊` at the floor `φ` of `Ttc.ballWalkConductance_le`,
so `φ² ≤ 4⁻ⁿ/1024` and the ceiling's argument is at least `2048·4ⁿ·log(√Mw/eps)`.

Contrast `Ttc.speedyMixSteps_le`, which is `O(n⁵ D² log(1+D)/ρ²)`.  **The improvement this
file delivers is exactly the removal of this `4ⁿ`.**

`γ ≤ Dm` is harmless: the inscribed radius of a body never exceeds its diameter, so it holds
in every intended application.  The bound is non-trivial exactly when `eps < √Mw` — the
logarithm vanishes at `eps = √Mw` and the statement degenerates to `0 ≤ mixSteps`, so read
the `2^{Θ(n)}` claim only in the regime where the sampler is actually asked for accuracy. -/
theorem exp_mul_log_le_mixSteps {n : ℕ} (hn : 1 ≤ n) {γ Dm δ Mw eps : ℝ}
    (hγ : 0 < γ) (hγD : γ ≤ Dm) (hδ : 0 < δ) (hMw : 1 ≤ Mw)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    2048 * 4 ^ n * Real.log (Real.sqrt Mw / eps) ≤ (mixSteps n γ Dm δ Mw eps : ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hDm : (0 : ℝ) < Dm := lt_of_lt_of_le hγ hγD
  have hsum : (0 : ℝ) < γ + Dm := by linarith
  set phi : ℝ := min ((γ / (γ + Dm)) ^ n / 32)
    ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * δ / (128 * (n : ℝ))) with hphidef
  have hratio : (0 : ℝ) < γ / (γ + Dm) := by positivity
  have hphi0 : 0 < phi := by
    rw [hphidef]
    refine lt_min (by positivity) ?_
    have : (0 : ℝ) < (γ / (γ + Dm)) ^ n := by positivity
    positivity
  have hphile : phi ≤ (1 / 2 : ℝ) ^ n / 32 := ballWalkConductance_le hγ hγD
  -- the log is nonnegative
  have hsq1 : (1 : ℝ) ≤ Real.sqrt Mw := by
    have := Real.sqrt_le_sqrt hMw
    rwa [Real.sqrt_one] at this
  have hL : (0 : ℝ) ≤ Real.log (Real.sqrt Mw / eps) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ heps0]; linarith
  -- the square of the floor is exponentially small
  have hphisq : phi ^ 2 ≤ (1 / 4 : ℝ) ^ n / 1024 := by
    have h : phi * phi ≤ (1 / 2 : ℝ) ^ n / 32 * ((1 / 2 : ℝ) ^ n / 32) :=
      mul_self_le_mul_self hphi0.le hphile
    have hrw : (1 / 2 : ℝ) ^ n / 32 * ((1 / 2 : ℝ) ^ n / 32) = (1 / 4 : ℝ) ^ n / 1024 := by
      rw [div_mul_div_comm, ← mul_pow]
      norm_num
    rw [pow_two]
    exact h.trans_eq hrw
  have hpow4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hquarter : (1 / 4 : ℝ) ^ n / 1024 = ((4 : ℝ) ^ n * 1024)⁻¹ := by
    rw [div_pow, one_pow]
    field_simp
  -- the ceiling dominates its argument
  have hceil : Real.log (Real.sqrt Mw / eps) / (phi ^ 2 / 2)
      ≤ (mixSteps n γ Dm δ Mw eps : ℝ) := by
    rw [hphidef]
    exact Nat.le_ceil _
  refine le_trans ?_ hceil
  have hden : (0 : ℝ) < phi ^ 2 / 2 := by positivity
  have hdenle : phi ^ 2 / 2 ≤ ((4 : ℝ) ^ n * 2048)⁻¹ := by
    rw [hquarter] at hphisq
    have h2 : ((4 : ℝ) ^ n * 1024)⁻¹ / 2 = ((4 : ℝ) ^ n * 2048)⁻¹ := by
      field_simp
      ring
    calc phi ^ 2 / 2 ≤ ((4 : ℝ) ^ n * 1024)⁻¹ / 2 := by linarith
      _ = ((4 : ℝ) ^ n * 2048)⁻¹ := h2
  have hmain := div_le_div_of_nonneg_left hL hden hdenle
  refine le_trans (le_of_eq ?_) hmain
  field_simp

/-! ## 5. Normalising a body with an inscribed ball -/

/-- The normalising map `y ↦ cen + γ • y` is measurable. -/
theorem measurable_inscribedAffine {n : ℕ} (cen : EuclideanSpace ℝ (Fin n)) (γ : ℝ) :
    Measurable (fun y : EuclideanSpace ℝ (Fin n) => cen + γ • y) := by
  fun_prop

/-- `B(0,1)` sits inside the normalised body. -/
theorem ball_subset_inscribedPreimage {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {cen : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ K) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ (fun y => cen + γ • y) ⁻¹' K := by
  intro y hy
  have hyn : ‖y‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hy
  refine hball ?_
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hγ]
  nlinarith [norm_nonneg y]

/-- At `cen = 0`, `γ = 1` the normalising map is the identity. -/
theorem preimage_inscribedAffine_id {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    (fun y : EuclideanSpace ℝ (Fin n) => (0 : EuclideanSpace ℝ (Fin n)) + (1 : ℝ) • y) ⁻¹' S
      = S := by
  ext y; simp

/-- The normalised body is convex. -/
theorem convex_inscribedPreimage {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (cen : EuclideanSpace ℝ (Fin n)) (γ : ℝ) (hKc : Convex ℝ K) :
    Convex ℝ ((fun y => cen + γ • y) ⁻¹' K) := by
  intro x hx y hy a b ha hb hab
  have hid : cen + γ • (a • x + b • y) = a • (cen + γ • x) + b • (cen + γ • y) := by
    have h1 : a • (cen + γ • x) + b • (cen + γ • y)
        = (a + b) • cen + γ • (a • x + b • y) := by module
    rw [h1, hab, one_smul]
  show cen + γ • (a • x + b • y) ∈ K
  rw [hid]
  exact hKc hx hy ha hb hab

/-- The normalised body has diameter at most `Dm/γ`. -/
theorem dist_le_of_mem_inscribedPreimage {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {cen : EuclideanSpace ℝ (Fin n)} {γ Dm : ℝ} (hγ : 0 < γ)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ Dm) :
    ∀ x ∈ (fun y => cen + γ • y) ⁻¹' K, ∀ y ∈ (fun y => cen + γ • y) ⁻¹' K,
      dist x y ≤ Dm / γ := by
  intro x hx y hy
  have h := hD _ hx _ hy
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hγ] at h
  rw [le_div_iff₀ hγ]
  linarith

/-- **The speedy walk mixes on a body presented by an inscribed ball and a diameter** — the
presentation TTC actually has.

Given `Metric.ball cen γ ⊆ K` and `diam K ≤ Dm`, the normalised body `aff ⁻¹' K` (with
`aff y = cen + γ • y`) satisfies every hypothesis of
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn` at `D = Dm/γ`, and all four of those facts are
proved above without assumption.

`hequiv` is the **only** open hypothesis: it says the mixing bound transports back along
`aff`, at step size `γ·δ` and start law `uniformOn volume (ball cen γ)`.  It is stated in
the minimal shape needed — quantified over the step count and the tolerance only — and a
sibling development is proving it.  See the module docstring. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    {cen : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ K)
    {Dm : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ Dm)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (hequiv : ∀ (t : ℕ) (e : ℝ≥0∞),
      Arlib.TVLe
          (Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
              ((fun y => cen + γ • y) ⁻¹' K) (rho / (4 * (n : ℝ)))))
            (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) t)
          (Arlib.uniformOn volume ((fun y => cen + γ • y) ⁻¹' K)) e →
      Arlib.TVLe
          (Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk K
              (γ * (rho / (4 * (n : ℝ))))))
            (Arlib.uniformOn volume (Metric.ball cen γ)) t)
          (Arlib.uniformOn volume K) e)
    {m : ℕ} (hm : speedyMixSteps n (Dm / γ) rho ≤ m) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk K
          (γ * (rho / (4 * (n : ℝ))))))
        (Arlib.uniformOn volume (Metric.ball cen γ)) m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal rho) :=
  hequiv m _
    (tvLe_iterate_lazy_speedyWalk_uniformOn hn
      (hKm.preimage (measurable_inscribedAffine cen γ))
      (convex_inscribedPreimage cen γ hKc)
      (ball_subset_inscribedPreimage hγ hball)
      (dist_le_of_mem_inscribedPreimage hγ hD) hrho0 hrho1 hm)

/-! ## 6. TTC's actual bodies: the Kannan--Vempala inflated polytope -/

/-- **The speedy walk mixes on `Arlib.KV97.inflated`** — TTC's actual sampling body — with
every geometric input stated about the *original* polytope `Arlib.Polytope.body A b`.

`Arlib.KV97.ball_subset_inflated` lifts an inscribed ball `B(cen, γ) ⊆ P` to
`B(cen, γ + κ) ⊆ P'` and `Arlib.KV97.dist_le_of_mem_inflated` lifts a diameter `Dm` for `P`
to `(1 + κ/γ)·Dm` for `P'`, with `κ = Arlib.KV97.kappaOf cp r`; measurability and convexity
of `P'` are `Arlib.KV97.measurableSet_inflated` / `Arlib.KV97.convex_inflated`.  So the only
inputs are facts about the *problem instance*, exactly as in `Ttc.kv97SamplerOfBody`
(`Ttc/Sampler/Construct.lean:353`).

The step count is `Ttc.speedyMixSteps` at the normalised diameter
`(1 + κ/γ)·Dm / (γ + κ)`, i.e. at the inflated body's aspect ratio.

`hequiv` remains open, as in `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed`. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_inflated {n : ℕ} {ι : Type*} (hn : 2 ≤ n)
    (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) {cp : ℝ} (hcp : 0 ≤ cp) (r : ℝ)
    {cen : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hballBody : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    {Dm : ℝ} (hDbody : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b,
      dist x y ≤ Dm)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (hequiv : ∀ (t : ℕ) (e : ℝ≥0∞),
      Arlib.TVLe
          (Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
              ((fun y => cen + (γ + Arlib.KV97.kappaOf cp r) • y) ⁻¹'
                Arlib.KV97.inflated A b cp r) (rho / (4 * (n : ℝ)))))
            (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) t)
          (Arlib.uniformOn volume ((fun y => cen + (γ + Arlib.KV97.kappaOf cp r) • y) ⁻¹'
            Arlib.KV97.inflated A b cp r)) e →
      Arlib.TVLe
          (Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
              (Arlib.KV97.inflated A b cp r)
              ((γ + Arlib.KV97.kappaOf cp r) * (rho / (4 * (n : ℝ))))))
            (Arlib.uniformOn volume (Metric.ball cen (γ + Arlib.KV97.kappaOf cp r))) t)
          (Arlib.uniformOn volume (Arlib.KV97.inflated A b cp r)) e)
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
  exact tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed hn
    (Arlib.KV97.measurableSet_inflated A b cp r) (Arlib.KV97.convex_inflated A b cp r)
    (by linarith : (0:ℝ) < γ + Arlib.KV97.kappaOf cp r)
    (Arlib.KV97.ball_subset_inflated hγ hballBody)
    (Arlib.KV97.dist_le_of_mem_inflated hγ hcp hballBody hDbody) hrho0 hrho1 hequiv hm

/-! ## 7. Non-vacuity witnesses (`CLAUDE.md` §11)

`Ttc.HitAndRunTheorem11Input` has **no** witness: nothing in the repository constructs one,
so every consequence of it is an implication with an unexhibited antecedent.  The theorems
above are implications too, so they need the same audit — here it is, and here is exactly
how far it goes.

| witness | discharges | leaves open |
| --- | --- | --- |
| `..._ballTwo` | every hypothesis of the core theorem, at `K = B(0,2)`, `ρ = 1/2` | `2 ≤ n` |
| `..._ballTwo_dim2` | **everything**, at `n = 2` — no hypotheses at all | — |
| `..._of_inscribed_ballTwo` | every hypothesis **including `hequiv`**, at `cen = 0`, `γ = 1` | the equivariance at `γ ≠ 1` |
| `..._inflated_box` | every hypothesis **including `hequiv`**, on a genuine `Arlib.KV97.inflated` body with `κ = 1/2 > 0` | the equivariance at `γ + κ ≠ 1` |

**What remains uncertified, stated plainly.**  `hequiv` is discharged in the last two
witnesses only because the parameters are chosen so that the normalising map `y ↦ cen + γ•y`
is the *identity* (`cen = 0`, `γ = 1`, resp. `γ + κ = 1/2 + 1/2 = 1`).  That proves the
hypothesis bundle is **satisfiable** — the theorems are not vacuous — but it does **not**
certify affine equivariance of `speedyWalk` at a nontrivial scaling, which is the sibling
development's job.  Note this is the *only* uncertified item: `..._ballTwo_dim2` shows the
core mixing theorem itself has a completely hypothesis-free instance.

The tolerance `ρ = 1/2` is non-trivial (`ENNReal.ofReal 1` would be the vacuous
total-variation bound), and the body `B(0,2)` is strictly larger than the start's support
`B(0,1)`, so the start is not the target and the bound is not `Arlib.TVLe.refl` in disguise.
What is **not** claimed, exactly as in `Ttc/Sampler/Construct.lean`: that the `m`-step law
itself differs from the target. -/

/-- **Witness for the core mixing theorem.**  `K = B(0,2)`, `ρ = 1/2`, `D = 4`, `m` the
canonical step count.  Every hypothesis of
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_at_steps` is discharged
(`measurableSet_ball`, `convex_ball`, `Metric.ball_subset_ball`,
`Arlib.MarkovChains.dist_le_four_of_mem_ballTwo`, `norm_num`); `2 ≤ n` survives. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_ballTwo {n : ℕ} (hn : 2 ≤ n) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) ((1 / 2 : ℝ) / (4 * (n : ℝ)))))
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
        (speedyMixSteps n 4 (1 / 2)))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2))
      (ENNReal.ofReal (1 / 2)) :=
  tvLe_iterate_lazy_speedyWalk_uniformOn_at_steps hn measurableSet_ball (convex_ball _ _)
    (Metric.ball_subset_ball (by norm_num))
    Arlib.MarkovChains.dist_le_four_of_mem_ballTwo (by norm_num) (by norm_num)

/-- **The same witness at `n = 2`: a theorem with no hypotheses at all.**

The strongest non-vacuity artefact available: the lazy speedy walk on `B(0,2) ⊆ ℝ²` with
step `1/16`, started from the uniform law on `B(0,1)`, is within total variation `1/2` of
the uniform law on `B(0,2)` after `Ttc.speedyMixSteps 2 4 (1/2)` steps.  Nothing is
assumed. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_ballTwo_dim2 :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
          (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 2) ((1 / 2 : ℝ) / (4 * ((2 : ℕ) : ℝ)))))
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))
        (speedyMixSteps 2 4 (1 / 2)))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 2))
      (ENNReal.ofReal (1 / 2)) :=
  tvLe_iterate_lazy_speedyWalk_uniformOn_ballTwo (n := 2) le_rfl

/-- **Witness for the inscribed-ball theorem, `hequiv` included.**  At `cen = 0`, `γ = 1` the
normalising map is the identity, so the equivariance hypothesis is discharged by rewriting. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_ballTwo {n : ℕ} (hn : 2 ≤ n) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
          (1 * ((1 / 2 : ℝ) / (4 * (n : ℝ))))))
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
        (speedyMixSteps n (4 / 1) (1 / 2)))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2))
      (ENNReal.ofReal (1 / 2)) := by
  refine tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed hn measurableSet_ball
    (convex_ball _ _) (γ := 1) (cen := 0) one_pos (Metric.ball_subset_ball (by norm_num))
    (Dm := 4) Arlib.MarkovChains.dist_le_four_of_mem_ballTwo (by norm_num) (by norm_num)
    ?_ le_rfl
  intro t e h
  rw [preimage_inscribedAffine_id] at h
  rw [one_mul]
  exact h

/-- `Arlib.KV97.kappaOf (1/2) 1 = 1/2`: at facet bound `r = 1` the `√(2 log r)` term vanishes. -/
theorem kappaOf_half_one : Arlib.KV97.kappaOf (1 / 2 : ℝ) 1 = 1 / 2 := by
  simp [Arlib.KV97.kappaOf]

/-- **Witness for the inflated-polytope theorem, `hequiv` included.**

The body is the Kannan--Vempala inflation, by `κ = kappaOf (1/2) 1 = 1/2`, of the axis-aligned
box of half-width `1/2` centred at the origin.  The inscribed radius of the inflation is
`γ + κ = 1/2 + 1/2 = 1`, so the normalising map is again the identity and `hequiv` is
discharged.  The inflation displacement is genuinely positive. -/
theorem tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_box {n : ℕ} (hn : 2 ≤ n) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
          (Arlib.KV97.inflated (Arlib.KV97.boxA n)
            (Arlib.KV97.boxB (1 / 2) (0 : EuclideanSpace ℝ (Fin n))) (1 / 2) 1)
          ((1 / 2 + Arlib.KV97.kappaOf (1 / 2 : ℝ) 1) * ((1 / 2 : ℝ) / (4 * (n : ℝ))))))
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n))
          (1 / 2 + Arlib.KV97.kappaOf (1 / 2 : ℝ) 1)))
        (speedyMixSteps n
          ((1 + Arlib.KV97.kappaOf (1 / 2 : ℝ) 1 / (1 / 2))
              * (2 * (1 / 2) * Real.sqrt (n : ℝ))
            / (1 / 2 + Arlib.KV97.kappaOf (1 / 2 : ℝ) 1)) (1 / 2)))
      (Arlib.uniformOn volume (Arlib.KV97.inflated (Arlib.KV97.boxA n)
        (Arlib.KV97.boxB (1 / 2) (0 : EuclideanSpace ℝ (Fin n))) (1 / 2) 1))
      (ENNReal.ofReal (1 / 2)) := by
  have hk : (1 / 2 : ℝ) + Arlib.KV97.kappaOf (1 / 2 : ℝ) 1 = 1 := by
    rw [kappaOf_half_one]; norm_num
  refine tvLe_iterate_lazy_speedyWalk_uniformOn_inflated hn (Arlib.KV97.boxA n)
    (Arlib.KV97.boxB (1 / 2) (0 : EuclideanSpace ℝ (Fin n))) (by norm_num) 1
    (γ := 1 / 2) (by norm_num) (Arlib.KV97.ball_subset_box _)
    (Arlib.KV97.dist_le_of_mem_box (R := 1 / 2) (by norm_num) _)
    (by norm_num) (by norm_num) ?_ le_rfl
  intro t e h
  rw [hk] at h ⊢
  rw [preimage_inscribedAffine_id] at h
  rw [one_mul]
  exact h

/-! ### Axiom audit (`CLAUDE.md` §4)

Every declaration in this file must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms speedyMixSteps
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_at_steps
#print axioms speedyConductance_eq
#print axioms speedyMixSteps_le
#print axioms ballWalkConductance_le
#print axioms exp_mul_log_le_mixSteps
#print axioms measurable_inscribedAffine
#print axioms ball_subset_inscribedPreimage
#print axioms preimage_inscribedAffine_id
#print axioms convex_inscribedPreimage
#print axioms dist_le_of_mem_inscribedPreimage
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_inflated
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_ballTwo
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_ballTwo_dim2
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_ballTwo
#print axioms kappaOf_half_one
#print axioms tvLe_iterate_lazy_speedyWalk_uniformOn_inflated_box

end Ttc

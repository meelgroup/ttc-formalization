/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Process.Thinning
import Ttc.Process.Sketch

/-!
# The level-`j` process, and the two branches of `lem:numlattice`

## Why the invariant is *not* a conditional statement

The paper's invariant reads "`𝒳⁽ⁱ⁾ⱼ` — the state of `𝒳` when `p` is `2^(−j)` —
contains `k` copies of each point of `S⁽ⁱ⁾`, `k ∼ Pois(p̃ⱼ)`". Read as
*conditioning on the rate being `2^(−j)`* that is *false*, and the smallest
counterexample is two points under the rule "while `|𝒳| > 1`, halve": conditioned
on stopping at `p = ½` the state is `Bernoulli(½)²` conditioned on `|𝒳| ≤ 1`,
which puts mass `0` — not `¼` — on both points surviving. Halting is a stopping
time, and conditioning on it distorts the law.

What the proof actually needs, and what survives, is the **non-adaptive** reading:
for *each* level `j` there is a process `Ttc.levelLaw` in which every lattice point
independently carries `Pois(θ/2ʲ)` copies, defined whether or not the run stops
there. The paper's own union bound is what licenses this — it bounds
`Pr[Nois(j) ∧ Err(j)]` by `Pr[Err(j)]`, discarding the conditioning, so `Err(j)`
only ever has to be an unconditional event about the level-`j` process.

This file builds that process and proves both branch estimates over it:

* `Ttc.levelLaw_err_le` — `Pr[Err(j)] ≤ 2exp(−ε'²·L·θ/(3·2ʲ))`, from
  `Ttc.poisson_relative` transported along `Ttc.map_sum_pi_poisson`;
* `Ttc.err_branch_sum` — summing those over `j < j*` gives `4exp(−a)`, the
  doubly-exponential collapse, hence `δ/6` by `Ttc.err_sum_le_delta`;
* `Ttc.levelLaw_noise_le` — `Pr[|𝒳| > Thresh] ≤ exp(−Thresh/6)` at any level
  whose rate is at most `Thresh/2`, hence `δ/6` over the `m` cubes by
  `Ttc.noise_bound_le_delta`.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-! ## The level-`j` process -/

/-- **The level-`j` count vector.** Each lattice point `i` of `S` independently
carries `Pois(θᵢ/2ʲ)` copies, where `θᵢ` is *that point's* rate at level `0`.
Defined for every `j`, adaptively or not — see the module docstring.

The rates are **per point, not uniform**: a point's rate comes from the last cube
containing it, via that cube's `Vol_ED` estimate, so distinct points genuinely
have distinct rates. What `lem:lattice` gives is that they all lie in a common
`(1±ε')(1±ε/8)/(2ʲ10^(ρn))` window — which is why only their *sum* is ever
needed. -/
noncomputable def levelLaw {L : ℕ} (θ : Fin L → ℝ) (j : ℕ) : Measure (Fin L → ℕ) :=
  Measure.pi fun i => poissonMeasure (θ i / 2 ^ j).toNNReal

instance isProbabilityMeasure_levelLaw {L : ℕ} (θ : Fin L → ℝ) (j : ℕ) :
    IsProbabilityMeasure (levelLaw θ j) := by
  rw [levelLaw]; infer_instance

/-- The total rate at level `j`. -/
noncomputable def totalRate {L : ℕ} (θ : Fin L → ℝ) (j : ℕ) : ℝ := (∑ i, θ i) / 2 ^ j

theorem totalRate_pos {L : ℕ} {θ : Fin L → ℝ} (hθ : 0 < ∑ i, θ i) (j : ℕ) :
    0 < totalRate θ j := by
  rw [totalRate]; positivity

/-- **The total count at level `j` is `Pois(∑ᵢ θᵢ/2ʲ)`** — superposition over the
points. -/
theorem map_sum_levelLaw {L : ℕ} {θ : Fin L → ℝ} (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : 0 < ∑ i, θ i) (j : ℕ) :
    (levelLaw θ j).map (fun r => ∑ i, r i)
      = poissonMeasure (totalRate θ j).toNNReal := by
  have hf : ∀ i : Fin L, (0:ℝ) ≤ θ i / 2 ^ j := fun i => by
    have := hθ0 i; positivity
  have hsum : ∑ i, θ i / 2 ^ j = totalRate θ j := by
    rw [totalRate, ← Finset.sum_div]
  have hpos : (0:ℝ) < ∑ i, θ i / 2 ^ j := by
    rw [hsum]; exact totalRate_pos hθ j
  have h := map_sum_pi_poisson hf hpos
  rw [hsum] at h
  exact h

/-! ## The coupled family, by iterated thinning

Finding 15: the paper's `Err(j)` needs a family `𝒳ⱼ` defined for **every** `j` on
one space, not just at the run's own stopping level. The construction is nested
thinning — `𝒳_{j+1}` is a `Binomial(·,½)` thinning of `𝒳ⱼ` — which couples all
the levels on the same coins while giving each one the right marginal.

`Ttc.chainLaw` is that chain, and `Ttc.chainLaw_eq_levelLaw` is the backbone
fact: **thinning down from level `0` reproduces the level-`j` law at every `j`**.
It is `Ttc.pi_poisson_bind_binomial_half` iterated.
-/

/-- The level process built by **iterated thinning** from level `0`. -/
noncomputable def chainLaw {L : ℕ} (θ : Fin L → ℝ) : ℕ → Measure (Fin L → ℕ)
  | 0 => Measure.pi fun i => poissonMeasure (θ i).toNNReal
  | j + 1 => (chainLaw θ j).bind (fun k => Measure.pi fun i => binomial (k i) half)

/-- **Nested thinning reproduces every level's law.** Level `j` of the chain is
exactly `Ttc.levelLaw θ j`, so the coupled family the union bound needs has the
marginals the estimates were proved for. -/
theorem chainLaw_eq_levelLaw {L : ℕ} {θ : Fin L → ℝ} (hθ : ∀ i, 0 ≤ θ i) (j : ℕ) :
    chainLaw θ j = levelLaw θ j := by
  induction j with
  | zero =>
      rw [chainLaw, levelLaw]
      simp
  | succ j ih =>
      rw [chainLaw, ih, levelLaw]
      have hrate : ∀ i, (0:ℝ) ≤ θ i / 2 ^ j := fun i => by have := hθ i; positivity
      rw [pi_poisson_bind_binomial_half hrate]
      rw [levelLaw]
      congr 1
      funext i
      congr 2
      rw [pow_succ]
      ring

/-! ## The `Err` branch -/

/-- **`Err(j)` has probability at most `2exp(−ε'²·L·θ/(3·2ʲ))`.**

`Err(j)` is the event that the level-`j` total misses the window
`(1 ± ε')·L·θ/2ʲ` around its mean. The estimate is `Ttc.poisson_relative` — the
paper's `Pr[err(j)] ≤ 2exp(−ε'²|S|p̃ⱼ/3)` — transported along the superposition
map. -/
theorem levelLaw_err_le {L : ℕ} {θ : Fin L → ℝ} {ε : ℝ} (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : 0 < ∑ i, θ i) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (j : ℕ) :
    (levelLaw θ j).real
        {r | ¬ ((1 - ε) * totalRate θ j ≤ (∑ i, r i : ℕ) ∧
              ((∑ i, r i : ℕ) : ℝ) ≤ (1 + ε) * totalRate θ j)}
      ≤ 2 * Real.exp (-(ε ^ 2 * totalRate θ j / 3)) := by
  classical
  set lam : ℝ := totalRate θ j with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; exact totalRate_pos hθ j
  have hcoe : ((lam.toNNReal : ℝ≥0) : ℝ) = lam := Real.coe_toNNReal lam hlam.le
  -- the failure event pulls back to the two Poisson tails
  have hsub : {r : Fin L → ℕ | ¬ ((1 - ε) * lam ≤ (∑ i, r i : ℕ) ∧
        ((∑ i, r i : ℕ) : ℝ) ≤ (1 + ε) * lam)}
      ⊆ (fun r : Fin L → ℕ => ∑ i, r i) ⁻¹'
          ({k : ℕ | lam + ε * lam ≤ (k : ℝ)} ∪ {k : ℕ | (k : ℝ) ≤ lam - ε * lam}) := by
    intro r hr
    simp only [Set.mem_setOf_eq, not_and_or, not_le] at hr
    rcases hr with h | h
    · exact Or.inr (by simp only [Set.mem_setOf_eq]; nlinarith)
    · exact Or.inl (by simp only [Set.mem_setOf_eq]; nlinarith)
  calc (levelLaw θ j).real {r | ¬ ((1 - ε) * lam ≤ (∑ i, r i : ℕ) ∧
          ((∑ i, r i : ℕ) : ℝ) ≤ (1 + ε) * lam)}
      ≤ (levelLaw θ j).real ((fun r : Fin L → ℕ => ∑ i, r i) ⁻¹'
          ({k : ℕ | lam + ε * lam ≤ (k : ℝ)} ∪ {k : ℕ | (k : ℝ) ≤ lam - ε * lam})) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = (poissonMeasure lam.toNNReal).real
          ({k : ℕ | lam + ε * lam ≤ (k : ℝ)} ∪ {k : ℕ | (k : ℝ) ≤ lam - ε * lam}) := by
        rw [Measure.real, Measure.real,
          ← Measure.map_apply (Measurable.of_discrete) (MeasurableSet.of_discrete),
          map_sum_levelLaw hθ0 hθ j]
    _ ≤ (poissonMeasure lam.toNNReal).real {k : ℕ | lam + ε * lam ≤ (k : ℝ)}
          + (poissonMeasure lam.toNNReal).real {k : ℕ | (k : ℝ) ≤ lam - ε * lam} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-(ε ^ 2 * lam / 3)) := by
        have h := poisson_relative (r := lam.toNNReal) (by rw [hcoe]; exact hlam) hε0 hε1
        rw [hcoe] at h
        exact h

/-! ## Summing the `Err` branch over the epochs

Halving doubles the exponent, so the per-epoch bounds form a doubly-exponential
series — that is `Ttc.epoch_series_le`, and it collapses to `4exp(−a)`.
-/

/-- **The `Err` branch, summed over `j < j*`.**

Indexing the epochs downwards from `j* − 1` (so `t = 0` is the *last* epoch, with
the smallest rate), the rate at epoch `t` is `lamStar·2ᵗ` and the bounds double.
`Ttc.epoch_series_le` sums them. -/
theorem err_branch_sum {ε lamStar : ℝ} (jstar : ℕ) (pr : ℕ → ℝ)
    (hprb : ∀ t, pr t ≤ 2 * Real.exp (-(ε ^ 2 * (lamStar * 2 ^ t) / 3)))
    (ha : Real.log 2 ≤ ε ^ 2 * lamStar / 3) :
    ∑ t ∈ Finset.range jstar, pr t ≤ 4 * Real.exp (-(ε ^ 2 * lamStar / 3)) := by
  refine le_trans (Finset.sum_le_sum fun t _ => hprb t) ?_
  have hrw : ∀ t : ℕ, 2 * Real.exp (-(ε ^ 2 * (lamStar * 2 ^ t) / 3))
      = 2 * Real.exp (-(ε ^ 2 * lamStar / 3 * 2 ^ t)) := by
    intro t; congr 2; ring
  rw [Finset.sum_congr rfl fun t _ => hrw t]
  exact epoch_series_le ha jstar

/-! ## The `Noise` branch -/

/-- **`Pr[|𝒳| > Thresh] ≤ exp(−Thresh/6)`** at any level whose total rate is at
most `Thresh/2` — the paper's overflow estimate, over the level process. -/
theorem levelLaw_noise_le {L : ℕ} {θ : Fin L → ℝ} {Thresh : ℝ} (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : 0 < ∑ i, θ i) (j : ℕ) (hrate : 2 * totalRate θ j ≤ Thresh) :
    (levelLaw θ j).real {r | Thresh ≤ (∑ i, r i : ℕ)}
      ≤ Real.exp (-(Thresh / 6)) := by
  set lam : ℝ := totalRate θ j with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; exact totalRate_pos hθ j
  have hcoe : ((lam.toNNReal : ℝ≥0) : ℝ) = lam := Real.coe_toNNReal lam hlam.le
  have hpre : {r : Fin L → ℕ | Thresh ≤ (∑ i, r i : ℕ)}
      = (fun r : Fin L → ℕ => ∑ i, r i) ⁻¹' {k : ℕ | Thresh ≤ (k : ℝ)} := rfl
  rw [hpre, Measure.real,
    ← Measure.map_apply (Measurable.of_discrete) (MeasurableSet.of_discrete),
    map_sum_levelLaw hθ0 hθ j]
  have h := poisson_overflow (r := lam.toNNReal) (by rw [hcoe]; exact hlam)
    (Thresh := Thresh) (by rw [hcoe]; exact hrate)
  exact h

/-! ## `lem:numlattice`'s failure bound, assembled

Everything the paper's proof does *after* the invariant, with the algorithm's own
constants and nothing posited: the `Err` epochs collapse to `δ/6`, the `Noise`
union bound over the `m` cubes gives `δ/6`, and the `m` `Vol_ED` calls a further
`δ/2` (finding 13). What is *not* here is the invariant itself — see
`Ttc.levelLaw`'s docstring and the README.
-/

/-- The exponent is large enough for the doubly-exponential series to converge:
`ε'²·λ*/3 ≥ log(24/δ) ≥ log 2`. Forced by `Thresh ≥ 24log(24/δ)/((1−ε')ε'²)`. -/
theorem log_two_le_exponent {ε Thresh δ lamStar : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hT : 24 * Real.log (24 / δ) / ((1 - ε) * ε ^ 2) ≤ Thresh)
    (hlam : (1 - ε) * Thresh / 8 ≤ lamStar) :
    Real.log 2 ≤ ε ^ 2 * lamStar / 3 := by
  have hc : (0:ℝ) < (1 - ε) * ε ^ 2 := by positivity
  have hTge : 24 * Real.log (24 / δ) ≤ (1 - ε) * ε ^ 2 * Thresh := by
    rw [div_le_iff₀ hc] at hT; linarith
  have hstep : Real.log (24 / δ) ≤ ε ^ 2 * lamStar / 3 := by
    have h1 : ε ^ 2 * ((1 - ε) * Thresh / 8) ≤ ε ^ 2 * lamStar :=
      mul_le_mul_of_nonneg_left hlam (by positivity)
    nlinarith
  have h24 : Real.log 2 ≤ Real.log (24 / δ) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hδ0]; linarith
  linarith

/-- **The failure probability of `lem:numlattice` is at most `δ`.**

The three contributions, each proved rather than posited: the `Err` epochs
(`Ttc.err_branch_sum` into `Ttc.err_sum_le_delta`), the `Noise` overflow over the
`m` cubes (`Ttc.levelLaw_noise_le` into `Ttc.noise_bound_le_delta`), and the `m`
`Vol_ED` calls (`Ttc.numlattice_failure_bound_with_vol`). The budget comes out at
`5δ/6`, so the algorithm's `Thresh` and `δ'` are confirmed correct with `δ/6` to
spare. -/
theorem numlattice_failure_le {ε Thresh δ m lamStar errSum noiseSum volSum : ℝ}
    (jstar : ℕ) (pr : ℕ → ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1) (hm : 1 ≤ m)
    (hT1 : 24 * Real.log (24 / δ) / ((1 - ε) * ε ^ 2) ≤ Thresh)
    (hT2 : 6 * (Real.log (6 / δ) + Real.log m) ≤ Thresh)
    (hlamStar : (1 - ε) * Thresh / 8 ≤ lamStar)
    (hpr : ∀ t, pr t ≤ 2 * Real.exp (-(ε ^ 2 * (lamStar * 2 ^ t) / 3)))
    (herr : errSum ≤ ∑ t ∈ Finset.range jstar, pr t)
    (hnoise : noiseSum ≤ m * Real.exp (-(Thresh / 6)))
    -- `volSum` is the **combined** oracle budget `Pr[E_vol] + Pr[E_samp]`: since
    -- `eq:sampler`, `δ' = δ/(4m)` and each family of `m` calls costs `δ/4`, so the
    -- two together are the same `δ/2` this hypothesis has always allowed.
    (hvol : volSum ≤ δ / 2) :
    errSum + noiseSum + volSum ≤ δ := by
  have ha := log_two_le_exponent hδ0 hδ1 hε0 hε1 hT1 hlamStar
  -- the `Err` branch
  have herr1 : errSum ≤ 4 * Real.exp (-(ε ^ 2 * lamStar / 3)) :=
    le_trans herr (err_branch_sum jstar pr hpr ha)
  have herr2 : 4 * Real.exp (-(ε ^ 2 * lamStar / 3))
      ≤ 4 * Real.exp (-((1 - ε) * ε ^ 2 * Thresh / 24)) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have h1 : ε ^ 2 * ((1 - ε) * Thresh / 8) ≤ ε ^ 2 * lamStar :=
      mul_le_mul_of_nonneg_left hlamStar (by positivity)
    nlinarith
  have herr3 : 4 * Real.exp (-((1 - ε) * ε ^ 2 * Thresh / 24)) ≤ δ / 6 :=
    err_sum_le_delta hδ0 hδ1 hε0 hε1 hT1
  -- the `Noise` branch
  have hnoise3 : m * Real.exp (-(Thresh / 6)) ≤ δ / 6 :=
    noise_bound_le_delta hδ0 hm hT2
  -- `Ttc.numlattice_failure_bound_with_vol` with `volSum` split as `δ/4 + δ/4`
  linarith

end Ttc

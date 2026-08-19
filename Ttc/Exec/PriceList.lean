/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.SampleBound
import Ttc.Volume.RadBound

/-!
# `Exec/PriceList`: one price for every cube

`Ttc.runCost` — and therefore `Ttc.ttcCost` and the headline's `cVol`/`cSample` — charges
**one** price at every cube.  The two closed forms that exist are **per-cube**:

* `Ttc.MonteCarlo.nSamp_roundBody_le` (`Volume/RadBound`) bounds the volume oracle's coin
  count at cube `i` by `⌈(γ⁻¹·diam (region M i) + 1)ⁿ / (ε'²·δ')⌉₊ + 1`, and
  `diam (region M i)` moves with `i`;
* `Ttc.mixSteps_le` (`Exec/SampleBound`) bounds the sampler's chain length at cube `i` by
  `Ttc.mixStepsBound` at `Ttc.ttcSampDiam … i`, `Ttc.ttcSampWarm … i` and
  `Ttc.ttcSampTol … i`, all three of which move with `i`.

So substituting either into a *uniform* price needs a bound over the DNF's cubes.  This
file supplies it for the volume oracle, and says exactly why it cannot supply one for the
sampler.

## The volume oracle: uniform, and closed

Every cube's region is inside the solution set (`Ttc.region_subset_sol`), and the solution
set of the preprocessed formula is bounded (`Ttc.ttcInput_bdd`, from `hφ` and `hpos`
alone).  `Metric.diam` is monotone on bounded sets, so

    diam (region M i) ≤ diam (sol M φ)     for every cube `i` of the DNF,

a quantity depending only on the input.  `Ttc.ttcVolPrice` is the per-cube closed form
evaluated at that uniform diameter, and `Ttc.ttcVolCoins_le_ttcVolPrice` is the proof that
it dominates every cube's coin count:

```
ttcVolPrice atoms φ ε δ
  = ⌈(γ⁻¹ · diam (Sol(preprocess atoms φ) at the dilated atoms) + 1)ⁿ / (ε'² · δ')⌉₊ + 1
γ  = algGamma atoms φ ε δ                       -- `q·γ̂`, the dilated inscribed radius
ε' = (algBlock atoms φ ε δ).epsPrime  = ε/12
δ' = (algBlock atoms φ ε δ).deltaPrime = δ/(5m)
```

Every name in it is defined under `Ttc/Model/` — `Ttc.algGamma`, `Ttc.algAtoms`,
`Ttc.algBlock`, `Ttc.preprocess`, `Ttc.sol`, `Ttc.atomSet` — which is what let the headline
carry it in its *statement* without breaking `#modelClosureOfType`.  ⚠ No statement carries
it now: the fixed-price headline was deleted on 2026-08-19, and `Ttc.ttc_volume` is stated at
the constructed oracles and is not closure-checked.  The vocabulary property is still true
and still recorded; nothing depends on it any more.

**It is exponential in `n`, and must not be read otherwise.**  The `(…)ⁿ` is the
hit-and-miss estimator's rejection factor: sampling uniformly from a ball of radius `R`
to hit a body of inradius `1` needs `Θ(Rⁿ)` draws, and no rearrangement avoids it.  The
price is `Θ((diam/γ)ⁿ / (ε'²·δ'))`.

## The sampler: uniform too — in `Exec/SamplePrice`, deleted 2026-08-19

⚠ **Read this section as history.**  `Ttc/Exec/SamplePrice.lean` assembled the ball-walk
price `Ttc.ttcSampPrice` and its domination lemma, and it was deleted on 2026-08-19 with the
rest of the reference-oracle apparatus: `Ttc.ttc` no longer charges a fixed per-sample price
for calling a sampler, it *executes* the hit-and-run / ball-walk hybrid, and what bounds its
sampling work is `Ttc.TTCSourceSharpOperationalFinal.canonicalCappedSampleQueryEnvelope`
(`Model/Theorem`).  Every named lemma below that lived in that file is gone with it.  The
account is kept because the *finding* it records — that the sampler price does have a uniform
closed form — is still true of the arithmetic, and because the reasoning about `hD` and
`heps1` at the end was instructive.

This section used to read "**no** uniform closed form, and this is the finding".  **That is
no longer true and the claim is withdrawn.**

`Ttc.mixStepsBound n γ Dmᵢ dl Mwᵢ epsᵢ` is increasing in `Dmᵢ` and in `Mwᵢ` and
decreasing in `epsᵢ`, so a uniform bound needs an upper bound on `Ttc.ttcSampDiam … i` and
on `Ttc.ttcSampWarm … i` and a lower bound — note the direction — on `Ttc.ttcSampTol … i`.
The last two are

```
Mwᵢ   = Vol(P'ᵢ) / Vol(B(10^ρ·cᵢ, γ))          epsᵢ = ε' / (4 · Vol(P'ᵢ))
```

with `P'ᵢ = Arlib.KV97.inflated …` the Kannan–Vempala inflated dilated polytope of cube
`i`, and all three are now supplied: `Ttc/Exec/InflateBound.lean` §2–§3 bounds `Vol(P'ᵢ)`
uniformly — reducing to the user's own `volSol` — and derives the three cube-free values,
`Ttc/Exec/SampleDischarge.lean` discharges all sixteen side conditions of
`Ttc.mixCost_le_mixSteps` and `Ttc.mixCost_le_ceil_mixStepsBound` at the run's own data,
and `Ttc/Exec/SamplePrice.lean` assembles the natural-valued price
`Ttc.ttcSampPrice = ⌈Ttc.ttcSampStepsPrice⌉₊` with its domination lemma
`Ttc.ttcSampleSteps_le_ttcSampPrice` — the exact analogue of
`Ttc.ttcVolCoins_le_ttcVolPrice` below, under the same five conditions on the input.

It is filed one directory-level later purely for import order: `Exec/InflateBound` imports
*this* file, so `Ttc.ttcSampStepsPrice` does not exist yet here.  Logically the two prices
are one list.

Two corrections to what this section used to say, both worth keeping because they were
wrong in instructive ways.  `hD` was **never** the obstruction: it is a *diameter* bound,
not a volume one, and it is discharged outright by `Ttc.dist_le_ttcSampDiam`.  And the
hypothesis with real content, `heps1`, needs a *lower* bound on `Vol(P'ᵢ)` — the opposite
direction from the one this section used to ask for.

`Ttc.ttcCoinAndStepCharge_le_volPrice` below is therefore **not** the last word: it is the
mixed shape — the volume half uniform and closed, the sampler half still a sum over cubes —
and it is kept only because it is the weaker statement.
`Ttc.ttcCoinAndStepCharge_le_prices` (`Exec/SamplePrice`) is the same bound with **both**
halves uniform, `charge ≤ m · (ttcVolPrice + ttcSampPrice · ⌈Thresh⌉₊)`, and supersedes it.

## What a number here does and does not mean

Three undercounts are unchanged by this file and are not made smaller by putting a
concrete numeral where a parameter was:

* `Ttc.kv97SampD`'s **rejection rounds are unbounded and uncounted** — it is a density,
  consumes no coins and carries no budget, so neither `Ttc.coinCost` nor `Ttc.mixCost`
  applies to it (`Ttc/CostModel.lean` §4);
* the **`while` loops of `alg:ttc` lines 32–42 are uncharged** (`Runtime`, "Two honest
  gaps");
* **per-step arithmetic is free**;
* `Ttc.mixSteps` **does not occur in `Ttc.ttcEstimate`'s definitional closure** — it enters
  through `Ttc.ttcRates`, the *law*, while `GenerateSamples` is the read-off
  `Ttc.trajGen`.  So `cSample` prices the chain the sampler's law is defined by, not steps
  the modelled run takes.

A bound on an undercount is not a bound on the count, and nothing here bounds a running
time.
-/

namespace Ttc

open MeasureTheory Metric Set

variable {A : Type*} {n : ℕ}

/-! # §1  The uniform diameter, and the uniform coin count

Nothing in this section mentions the run: it is the per-cube closed form of
`Volume/RadBound` with `diam (region M i)` replaced by `diam (sol M φ)`, which dominates
it at every cube of a DNF of `φ`. -/

/-- **Every cube's region is no wider than the solution set.**  `Ttc.region_subset_sol`
plus monotonicity of `Metric.diam` on bounded sets — this is the one geometric step that
makes a *uniform* price possible at all. -/
theorem diam_region_le_diam_sol {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hb : Bornology.IsBounded (sol M φ)) {c : Cube A} (hc : c ∈ D) :
    Metric.diam (region M c) ≤ Metric.diam (sol M φ) :=
  Metric.diam_mono (region_subset_sol hD hc) hb

/-- **The uniform enclosing radius dominates the per-cube one.** -/
theorem roundRad_le_of_mem {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {γ : ℝ}
    (hγ : 0 < γ) (hD : IsDNFOf D φ) (hb : Bornology.IsBounded (sol M φ)) {c : Cube A}
    (hc : c ∈ D) :
    roundRad γ (region M c) ≤ γ⁻¹ * Metric.diam (sol M φ) + 1 := by
  rw [roundRad]
  have := diam_region_le_diam_sol hD hb hc
  have hinv : (0 : ℝ) ≤ γ⁻¹ := (inv_pos.mpr hγ).le
  nlinarith

/-- **The volume oracle's coin count at cube `i`, bounded uniformly.**

    mcVolCoins M D cen γ ε' δ' i ≤ ⌈(γ⁻¹·diam (sol M φ) + 1)ⁿ / (ε'²·δ')⌉₊ + 1

The right-hand side does not mention `i`.  Off the DNF `Ttc.mcVolCoins` is `0` and the
bound is trivial; on it, `Ttc.MonteCarlo.nSamp_roundBody_le` gives the per-cube form and
`Ttc.roundRad_le_of_mem` widens it.

**Exponential in `n`** — see the module docstring. -/
theorem mcVolCoins_le {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (cen : {c : Cube A // c ∈ D} → Space n) {γ ε' δ' : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε') (hδ : 0 < δ')
    (hball : ∀ i : {c : Cube A // c ∈ D}, Metric.ball (cen i) γ ⊆ region M i.val)
    (hb : Bornology.IsBounded (sol M φ)) (i : Cube A) :
    mcVolCoins M D cen γ ε' δ' i
      ≤ ⌈(γ⁻¹ * Metric.diam (sol M φ) + 1) ^ n / (ε' ^ 2 * δ')⌉₊ + 1 := by
  classical
  by_cases hi : i ∈ D
  · rw [mcVolCoins, dif_pos hi]
    have hbdd : Bornology.IsBounded (region M i) :=
      isBounded_region_of_isBounded_sol hD hb hi
    have hfin : volume (region M i) ≠ ⊤ := hbdd.measure_lt_top.ne
    refine le_trans
      (MonteCarlo.nSamp_roundBody_le hγ hε hδ (hball ⟨i, hi⟩) hbdd hfin) ?_
    have hle : roundRad γ (region M i) ≤ γ⁻¹ * Metric.diam (sol M φ) + 1 :=
      roundRad_le_of_mem hγ hD hb hi
    have hpow : roundRad γ (region M i) ^ n
        ≤ (γ⁻¹ * Metric.diam (sol M φ) + 1) ^ n :=
      pow_le_pow_left₀ (roundRad_pos hγ).le hle n
    have hden : (0 : ℝ) < ε' ^ 2 * δ' := by positivity
    have hdiv : roundRad γ (region M i) ^ n / (ε' ^ 2 * δ')
        ≤ (γ⁻¹ * Metric.diam (sol M φ) + 1) ^ n / (ε' ^ 2 * δ') :=
      div_le_div_of_nonneg_right hpow hden.le
    exact Nat.add_le_add_right (Nat.ceil_le_ceil hdiv) 1
  · rw [mcVolCoins, dif_neg hi]
    exact Nat.zero_le _

/-! # §2  At the run's own data

`Ttc.ttcVolCoins` is `Ttc.mcVolCoins` at the dilated atoms, the dilated centres and the
dilated inscribed radius.  All three have `Model/` names — `Ttc.algAtoms`, `Ttc.algCen`,
`Ttc.algGamma` — and are `rfl`-equal to the `Exec/Api` spellings, which is what lets the
price below be written in `Model/` vocabulary. -/

section AtTheRun

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The dilated inscribed ball, at the run's own data.**  `Ttc.ball_subset_cenOf` is
unconditional and `Ttc.ball_subset_scaleAtoms` carries it through the dilation, so this
needs only that the dilation is positive. -/
theorem ball_subset_region_algAtoms (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)}) :
    Metric.ball (algCen atoms φ ε δ i) (algGamma atoms φ ε δ)
      ⊆ region (atomSet (algAtoms atoms φ ε δ)) i.val :=
  ball_subset_scaleAtoms
    (runScale_pos atoms (preprocess atoms φ) ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
      (ttcInput_bdd atoms φ hφ hpos) (autoGamma atoms (preprocess atoms φ)))
    (ball_subset_cenOf (atomSet atoms) (toDNFd (preprocess atoms φ))) i

/-- **`Sol` of the preprocessed formula at the dilated atoms is bounded** —
`Ttc.ttcAtoms_bdd`, read at the `Model/` spelling of the dilated atoms. -/
theorem isBounded_sol_algAtoms (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    Bornology.IsBounded (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)) :=
  ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos

/-- **The dilated inscribed radius is positive.**  `γ̂ = gammaOf …` is positive because
every cube of the preprocessed formula's DNF has nonempty interior — `Ttc.pruneInt` then
`Ttc.cleanInt`, both derived from `hφ` and `hpos` — and the dilation is positive. -/
theorem algGamma_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : 0 < algGamma atoms φ ε δ := by
  refine mul_pos (runScale_pos atoms (preprocess atoms φ) ε δ hε0 hε1 hn
      (ttcInput_isPositive atoms φ) (ttcInput_bdd atoms φ hφ hpos) _) ?_
  exact gammaOf_pos_of_interior (atomSet atoms)
    (toDNFd_ne_nil (ttcInput_isPositive atoms φ))
    (cleanInt atoms (isPositive_pruneForm atoms φ) (pruneInt atoms hφ hpos))

/-- **`ε' = ε/12 > 0`** — from `Ttc.Params.hε0`, which every `Ttc.Params` carries, so no
branch analysis of `Ttc.ttcParamsTotal` is needed. -/
theorem algBlock_epsPrime_pos : 0 < (algBlock atoms φ ε δ).epsPrime :=
  Params.epsPrime_pos _

/-- **`δ' = δ₀/(4m) > 0`.**  Unlike `ε'` this needs the *good* branch of
`Ttc.ttcParamsTotal`, since `Ttc.Params` carries no positivity field for `δ`: on it the
block's `δ` is the internal failure parameter `4δ/5`. -/
theorem algBlock_deltaPrime_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) :
    0 < (algBlock atoms φ ε δ).deltaPrime := by
  have hδblk : (algBlock atoms φ ε δ).δ = 4 * δ / 5 :=
    ttcBlock_delta atoms φ ε δ hε0 hε1 hn hφ hpos
  have hm : 1 ≤ (algBlock atoms φ ε δ).m := (algBlock atoms φ ε δ).hm
  have hmR : (0 : ℝ) < ((algBlock atoms φ ε δ).m : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  show 0 < (algBlock atoms φ ε δ).δ / (4 * ((algBlock atoms φ ε δ).m : ℝ))
  rw [hδblk]
  positivity

/-- **The uniform per-call price of the constructed `Vol_ED`.**

```
⌈(γ⁻¹ · diam (Sol at the dilated atoms) + 1)ⁿ / (ε'² · δ')⌉₊ + 1
```

at `γ = Ttc.algGamma`, `ε' = (Ttc.algBlock …).epsPrime`, `δ' = (Ttc.algBlock …).deltaPrime`.
Every constant it names is defined under `Ttc/Model/`, which is what lets
`Ttc.ttc_volume` carry the expression in its statement.

The name promises a semantic identity — "the price that dominates the coins the volume
oracle reads" — and `Ttc.ttcVolCoins_le_ttcVolPrice` is the lemma that proves it.

**Exponential in `n`.** -/
noncomputable def ttcVolPrice : ℕ :=
  ⌈((algGamma atoms φ ε δ)⁻¹
        * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)) + 1) ^ n
      / ((algBlock atoms φ ε δ).epsPrime ^ 2 * (algBlock atoms φ ε δ).deltaPrime)⌉₊ + 1

theorem ttcVolPrice_def :
    ttcVolPrice atoms φ ε δ
      = ⌈((algGamma atoms φ ε δ)⁻¹
            * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))
              + 1) ^ n
          / ((algBlock atoms φ ε δ).epsPrime ^ 2
              * (algBlock atoms φ ε δ).deltaPrime)⌉₊ + 1 := rfl

/-- **The price dominates the coins, at every cube.**

This is what makes `Ttc.ttcVolPrice` a price rather than a numeral: `Ttc.ttcVolCoins` is
the number of coins the run's own `Vol_ED` reads at cube `i`
(`Ttc.ttcOracleBundle_vol_congr`), and it is at most `Ttc.ttcVolPrice` for **every** `i`,
with no dependence on the cube left on the right. -/
theorem ttcVolCoins_le_ttcVolPrice (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (i : Cube A) :
    ttcVolCoins atoms φ ε δ i ≤ ttcVolPrice atoms φ ε δ :=
  mcVolCoins_le (M := atomSet (algAtoms atoms φ ε δ)) (φ := preprocess atoms φ)
    (toDNFd_isDNFOf (preprocess atoms φ)) (algCen atoms φ ε δ)
    (algGamma_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (algBlock_epsPrime_pos atoms φ ε δ)
    (algBlock_deltaPrime_pos atoms φ ε δ hε0 hε1 hn hφ hpos hδ0)
    (ball_subset_region_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
    (isBounded_sol_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) i

/-! # §3  The charge, with the volume half uniform

`Ttc.ttcCoinAndStepCharge_le_sum` (`Exec/Complexity` §4) bounds the run's per-cube charge
by `∑ᵢ (coinsᵢ + stepsᵢ·⌈Thresh⌉₊)`.  With §2 the first summand becomes a single number.
The second does **not** — see the module docstring — so the statement below is mixed, and
deliberately so: it is what is proved, not what would look tidiest. -/

/-- **The run's charge, with the volume price uniform and closed.**

```
charge ≤ ∑ᵢ (ttcVolPrice + stepsᵢ · ⌈Thresh⌉₊)
```

The `Ttc.ttcVolPrice` on the right is the closed form of §2; `stepsᵢ` is
`Ttc.ttcSampleSteps`, which stays inside the sum because no uniform bound on it is
available (module docstring).

**Not a running-time bound**: three undercounts stand (module docstring). -/
theorem ttcCoinAndStepCharge_le_volPrice (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ)
    (c : ℕ → Space n) (t : ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ)
    (hterm : ttcTerminates atoms φ ε δ c t) :
    ttcCoinAndStepCharge atoms φ ε δ c t
      ≤ ((toDNFd (preprocess atoms φ)).map (fun i =>
          ttcVolPrice atoms φ ε δ
            + ttcSampleSteps atoms φ ε δ i * ⌈ttcThresh atoms φ ε δ⌉₊)).sum := by
  refine le_trans (ttcCoinAndStepCharge_le_sum atoms φ ε δ c t hterm) ?_
  refine List.sum_le_sum ?_
  intro i _
  exact Nat.add_le_add_right
    (ttcVolCoins_le_ttcVolPrice atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 i) _

end AtTheRun

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.diam_region_le_diam_sol
#print axioms Ttc.roundRad_le_of_mem
#print axioms Ttc.mcVolCoins_le
#print axioms Ttc.ball_subset_region_algAtoms
#print axioms Ttc.isBounded_sol_algAtoms
#print axioms Ttc.algGamma_pos
#print axioms Ttc.algBlock_epsPrime_pos
#print axioms Ttc.algBlock_deltaPrime_pos
#print axioms Ttc.ttcVolPrice
#print axioms Ttc.ttcVolPrice_def
#print axioms Ttc.ttcVolCoins_le_ttcVolPrice
#print axioms Ttc.ttcCoinAndStepCharge_le_volPrice

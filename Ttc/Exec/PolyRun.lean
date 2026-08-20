/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVBackend
import Ttc.Exec.PolyComplexity
import Ttc.Exec.SamplerCost
import Ttc.Exec.CoolDrawPrice
import Ttc.Sampler.ConstructHitAndRun
import Ttc.Monadic.Program

/-!
# `Exec/PolyRun`: `TTC` *run* on the polynomial oracles

⚠ **Read the next paragraph as history.**  `Ttc.ttc` used to be the algorithm at the
**hit-and-miss Monte Carlo** volume estimator and the **lazy ball walk**, with the two
per-call prices `cVol`, `cSample` left as binders; the headline was its *unconditional*
accuracy result, and `Exec/TheoremPoly` priced those binders — but only by **hypothesis**:
nothing there said the run executed a polynomial oracle.  Since 2026-08-19 `Ttc.ttc`
executes the Cousins–Vempala estimator and the hit-and-run / ball-walk hybrid, there are no
price binders anywhere, and `Exec/TheoremPoly` is deleted.  What this file supplies is still
what it always was: the run with `vol` taken from a supplied `VolumeAlgorithm`.

This file is **additive**.  It builds, beside `Ttc.ttc` and changing nothing about it,
a second program `Ttc.ttcPoly` whose oracle bundle is Cousins–Vempala (an arbitrary
`Ttc.VolumeAlgorithm`, drawn from *its own* coin space) plus the **hit-and-run**
sampler, and whose two prices are **closed terms** rather than binders.  `Ttc.ttc`,
`Ttc.ttcOracleBundle`, `Ttc.mcVol` and everything in `Ttc/Model/` are untouched: not one
declaration below rewrites them.

## THE TRADE, STATED PLAINLY — neither theorem dominates the other

`Ttc.ttcPoly` buys a polynomial runtime by making its **accuracy** conditional.  Its
accuracy — which this file *reduces* but does not close, see "what is not here" —
rests on

* `Ttc.HitAndRunTheorem11Input` (Lovász–Vempala Theorem 1.1), an assumed structure
  **inhabited nowhere**, whose own proof would rest on the unproved `hLS`
  (Lovász–Simonovits 1993, Corollary 1.5);
* Cousins–Vempala's `hphase_mean` and `hphase_var`, the two hypotheses
  `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns` still carries
  (`Ttc/Volume/CVInstantiate.lean:83`: "this is where the development actually
  stops");
* `thm:iso`, the isoperimetry input.

`Ttc.ttc`'s accuracy is **unconditional** and stays that way.  So: `Ttc.ttc` has
unconditional accuracy at exponential prices; `Ttc.ttcPoly` has a polynomial charged
cost at conditional accuracy.  **Neither dominates the other.**

## THE REGIME CAVEAT — the `n⁴` needs `R = O(σ)`

`Ttc.all_ttcPoly_cost_le_quartic`'s `n⁴` holds where the body is temperature-scale.
In the Cousins–Vempala regime `R ≍ σ√n` the conductance floor forces a smaller step,
the draw cost degrades and the total is `n⁵`.
`Arlib.MarkovChains.exists_halfspace_max_lt` shows the obvious route to recovering the
missing `√n` is **false**, not merely open.

## THE PRICE IS NOT TIED TO `V` BY THE TYPE SYSTEM — read this before quoting the cost

`Ttc.ttcPoly` takes `V : Ttc.VolumeAlgorithm n` as a **binder**, because
`Ttc.VolumeAlgorithm` has no complexity field (`Ttc/Volume/Oracle.lean:70-93`): it
asserts accuracy and measurability and says nothing about running time.  So the two
closed prices `Ttc.polyVolPrice`/`Ttc.polySamplePrice` are the *Cousins–Vempala and
hit-and-run* charges, and charging them is only justified at
`V := Ttc.cvVolAlg …` (`Ttc/Exec/CVBackend.lean:533`) together with the hit-and-run
sampler that `Ttc.polySampD` already pins in the rates.  Instantiating the cost
theorems at, say, `Ttc.VolumeAlgorithm.monteCarlo` yields a true statement about a
*differently priced* fold and must not be read as "Monte Carlo costs `n⁴`".  The
sampler side has no such gap: `Ttc.polySampD` **is** the hit-and-run law, in
`Ttc.ttcPoly`'s definitional closure.

## NOTHING HERE PROVES THAT `TTC` RUNS IN `O(m·n⁴)`

The cost coordinate of `Ttc.ttcPoly` charges one unit per oracle call and nothing
else: it prices at zero the arithmetic inside a call, the rejection rounds, and
`alg:ttc`'s lines 32–42 `while` loops.  What is proved is that the **charged** cost is
almost surely at most `m·n⁴·(explicit factors)` — and that the two numbers being
charged are the ones `Ttc.SamplerCost.samplePrice_le_quartic` and
`Ttc.CoolCost.cvVolumeOpsPrice_le_cool` bound, not free parameters.

## What is here

| declaration | what it is |
| --- | --- |
| `Ttc.polyOracles` | the bundle: `Ttc.trajOracles` at `Ttc.volOfAlg V` — **only `vol` differs** from `Ttc.ttcOracleBundle` |
| `Ttc.algOracles_eq_trajOracles` | `rfl`: the run's own bundle is `Ttc.trajOracles` at `Ttc.mcVol` |
| `Ttc.polySampD` | the hit-and-run discrete law, at the run's canonical geometry |
| `Ttc.polyVolPrice`, `Ttc.polySamplePrice` | the two prices, as **closed** naturals |
| `Ttc.ttcPoly` | the program, mirroring `Ttc.ttc` at `V.μ` and those prices |
| `Ttc.trajLaw_max_zero` | `Ttc.trajLaw` sees only `θ⁺` — this is what makes the cost half unconditional |
| `Ttc.ae_terminates_polyOracles` | `Ttc.Terminates`, a.s., with **no** hypothesis about `V` |
| `Ttc.ttcPoly_eq_map_compProd`, `Ttc.isProbabilityMeasure_ttcPoly` | the `bind` is not the junk zero measure |
| `Ttc.all_ttcPoly_cost_le_ttcComplexity` | **the cost half**, at the closed prices |
| `Ttc.all_ttcPoly_cost_le_quartic` | the same collapsed to `m·n⁴·(…)` |
| `Ttc.pr_ttcPoly_fst_eq_lintegral` | the accuracy conjunct, unfolded to `Ttc.volume_estimate_joint`'s shape |
| `Ttc.isBigO_ttcPolyCost_quartic` | `O(n⁴)`, with `m`, `ε`, `δ` and the geometry outside the `O(·)` |

## What is NOT here — the accuracy half is reduced, not closed

`Ttc.volume_estimate_joint` (`Ttc/Coupling/Product.lean:328`) is already generic in
the volume algorithm, its coins, `sampD` and the `Ttc.KV97Sampler` certificate, and it
is stated over `Ttc.trajOracles` — so it applies to `Ttc.polyOracles` with no change.
`Ttc.pr_ttcPoly_fst_eq_lintegral` unfolds `Ttc.ttcPoly`'s accuracy conjunct to exactly
its iterated-integral shape.  What still separates the two is the **preprocessing and
dilation bridge**: `Ttc.volume_estimate_joint` concludes about `ttcOutput P … φ t` at
the user's `M`, whereas `Ttc.ttcPolyRun` is `Ttc.ttcAlgOutput`, i.e. the same run at
the *dilated preprocessed* input divided by `qⁿ`.  On the Monte-Carlo path that bridge
is `Ttc/Exec/Final.lean:96`, `Ttc/Exec/Inputs.lean:109` and `Ttc/Exec/Prune.lean:294`,
each of which names `Ttc.mcVol` (`Exec/Inputs.lean:224`) and `Ttc.e2eSampD`
(`Exec/Inputs.lean:245`) in its statement; re-deriving those three generically is what
closing the accuracy half needs, and it is **not attempted here**.  No theorem in this
file may be read as an accuracy guarantee for `Ttc.ttcPoly`.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Set Pointwise

variable {A : Type*} {n : ℕ}

section Defs

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- `Vol_ED`'s output at the run's own geometry, for an arbitrary volume algorithm. -/
noncomputable def polyVol (V : VolumeAlgorithm n) (ω : V.Ω) : Cube A → ℝ :=
  volOfAlg V (atomSet (algAtoms atoms φ ε δ)) (toDNFd (preprocess atoms φ))
    (algCen atoms φ ε δ) (algGamma atoms φ ε δ)
    (algBlock atoms φ ε δ).epsPrime (algBlock atoms φ ε δ).deltaPrime ω

/-- The oracle bundle, with `vol` supplied by `V` instead of `Ttc.mcVol`. -/
noncomputable def polyOracles (V : VolumeAlgorithm n) (ω : V.Ω)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) : Oracles n (Cube A) :=
  trajOracles
    (latticeEnum_injective (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
      (algPrec atoms φ ε δ))
    (polyVol atoms φ ε δ V ω)
    (coverOfRegion (atomSet (algAtoms atoms φ ε δ)))
    (algMem atoms φ ε δ) t

/-- Only `vol` differs. -/
theorem polyOracles_vol (V : VolumeAlgorithm n) (ω : V.Ω)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) :
    (polyOracles atoms φ ε δ V ω t).vol = polyVol atoms φ ε δ V ω := rfl

theorem polyOracles_covered (V : VolumeAlgorithm n) (ω : V.Ω)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) :
    (polyOracles atoms φ ε δ V ω t).covered
      = coverOfRegion (atomSet (algAtoms atoms φ ε δ)) := rfl

/-! ## The hit-and-run sampler's discrete law, at the run's own geometry -/

/-- The continuous law of one draw: the **hit-and-run** chain on the inflated dilated
polytope, at the run's canonical linear description. -/
noncomputable def polyHRLaw
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n)) :
    {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n) :=
  kv97HitAndRunContLaw (D := toDNFd (preprocess atoms φ))
    (algBlock atoms φ ε δ).epsPrime (canonRfac (toDNFd (preprocess atoms φ)))
    (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)))
    (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
      (latticeScale (algPrec atoms φ ε δ)))
    rin Rout Mw sigma

/-- The sampler's **discrete** law: rounding-then-rejection of the hit-and-run draw. -/
noncomputable def polySampD
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n)) :
    Cube A → Space n → ℝ :=
  kv97SampD (atomSet (algAtoms atoms φ ε δ)) (toDNFd (preprocess atoms φ))
    (algPrec atoms φ ε δ) (polyHRLaw atoms φ ε δ rin Rout Mw sigma)

/-- The level-`0` rate vector at the polynomial oracles. -/
noncomputable def polyRates (V : VolumeAlgorithm n) (ω : V.Ω)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n)) :
    Fin (algIndex atoms φ ε δ) → ℝ :=
  rates (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
    (toDNFd (preprocess atoms φ)) (algPrec atoms φ ε δ)
    (polySampD atoms φ ε δ rin Rout Mw sigma) (polyVol atoms φ ε δ V ω)

/-! ## The two prices, as closed natural numbers -/

/-- **The per-sample price**: `Ttc.SamplerCost.samplePrice` at the run's own `ε'` and
facet bound.  A closed arithmetic term — no binder. -/
noncomputable def polySamplePrice (gam R Mwarm : ℝ) : ℕ :=
  SamplerCost.samplePrice n gam R Mwarm (algBlock atoms φ ε δ).epsPrime
    (canonRfac (toDNFd (preprocess atoms φ)))

/-- **The per-`Vol_ED`-call price**: `Ttc.CVCost.cvVolumeOpsPrice` with the per-draw
charge `q` supplied by `Ttc.CoolCost.coolDrawPrice`.  A closed arithmetic term. -/
noncomputable def polyVolPrice {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A)
    (Lc kap cc pf Mcool epsDraw : ℝ) : ℕ :=
  CVCost.cvVolumeOpsPrice n Lc kap cc pf
    (CoolCost.coolDrawPrice n Mcool epsDraw
      (CoolCost.coolStepOpCharge n (canonRfac (toDNFd (preprocess atoms φ)))))

/-! ## The run and its charged cost, on the polynomial bundle -/

/-- `TTC(F, ε, δ)`'s output on the run `(ω, t)` at the polynomial oracles. -/
noncomputable def ttcPolyRun (V : VolumeAlgorithm n) (ω : V.Ω)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) : ℝ :=
  ttcAlgOutput atoms φ ε δ (polyOracles atoms φ ε δ V ω t)

/-- The charged cost of the run `(ω, t)` at the two polynomial prices. -/
noncomputable def ttcPolyCost (V : VolumeAlgorithm n) (ω : V.Ω)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) (cVol cSample : ℕ) : ℕ :=
  runCost (algBlock atoms φ ε δ) (polyOracles atoms φ ε δ V ω t) cVol cSample
    (algPrec atoms φ ε δ) (toDNFd (preprocess atoms φ))

/-- **`TTC` on the polynomial oracle bundle, as one program.**  Mirrors `Ttc.ttc`
(`Model/Pseudocode.lean:816`) with the volume coins drawn from `V.μ` instead of
`Ttc.MonteCarlo.coins`, the rates carrying the hit-and-run sampler, and the two prices
**closed terms** rather than binders. -/
noncomputable def ttcPoly (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ) : Measure (ℝ × ℕ) :=
  letI := V.mΩ
  V.μ.bind fun ω =>
    (trajLaw (polyRates atoms φ ε δ V ω rin Rout Mw sigma)).map fun t =>
      (ttcPolyRun atoms φ ε δ V ω t,
        ttcPolyCost atoms φ ε δ V ω t
          (polyVolPrice atoms φ Lc kap cc pf Mcool epsDraw)
          (polySamplePrice atoms φ ε δ gam R Mwarm))

end Defs

/-! # The cost half

Everything here is generic in the oracle bundle: `Ttc.trajOracles` takes `vol` as a
parameter, so `Ttc/Process/Truncation.lean`'s termination and cost lemmas apply to
`Ttc.polyOracles` verbatim.  The one thing that had to be repaired is the
nonnegativity of the rate vector — see `Ttc.trajLaw_max_zero`. -/

section Cost

/-- `Real.toNNReal` clamps at `0`, so `max · 0` is invisible to it. -/
theorem toNNReal_max_zero (x : ℝ) : (max x 0).toNNReal = x.toNNReal := by
  apply NNReal.coe_injective
  simp [Real.coe_toNNReal']

/-- **`Ttc.trajLaw` only sees the positive part of its rate vector.**

`Ttc.trajLaw θ` is built from `Po((θ s).toNNReal)`, so replacing `θ` by `θ⁺` changes
nothing.  This is what removes the nonnegativity leak from the cost half:
`Ttc/Process/Truncation.lean`'s lemmas want `0 ≤ θ s`, and a general
`Ttc.VolumeAlgorithm` does not give `0 ≤ V.est`. -/
theorem trajLaw_max_zero {L : ℕ} (θ : Fin L → ℝ) :
    trajLaw θ = trajLaw (fun s => max (θ s) 0) := by
  simp only [trajLaw, toNNReal_max_zero]

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **`Ttc.Terminates` holds `Ttc.trajLaw`-almost surely at the polynomial bundle.**

`Ttc.trajLaw_ae_terminates` (`Process/Truncation.lean:273`) is stated over
`Ttc.trajOracles` at an arbitrary `vol`, so it applies with no change; its `0 ≤ θ s`
hypothesis is met at `θ⁺` and transported by `Ttc.trajLaw_max_zero`. -/
theorem ae_terminates_polyOracles
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (V : VolumeAlgorithm n) (ω : V.Ω)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n)) :
    ∀ᵐ t ∂(trajLaw (polyRates atoms φ ε δ V ω rin Rout Mw sigma)),
      Terminates (algBlock atoms φ ε δ) (polyOracles atoms φ ε δ V ω t)
        (toDNFd (preprocess atoms φ)) := by
  rw [trajLaw_max_zero]
  exact trajLaw_ae_terminates _ (algBlock atoms φ ε δ) (polyVol atoms φ ε δ V ω)
    (coverOfRegion (atomSet (algAtoms atoms φ ε δ))) (algMem atoms φ ε δ)
    (fun s => le_max_right _ _)
    (ttcThresh_nonneg atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1)
    (toDNFd (preprocess atoms φ))

/-- **The charged cost is at most `Ttc.ttcComplexity`, at any prices, under
termination.**  `Ttc.runCostAt_le_uniform` at the ceiling of `Thresh`, then
`Ttc.ttcThresh_le_sum`; the same arithmetic as `Ttc.ttcCost_le_ttcComplexity`, at the
polynomial bundle instead of `Ttc.ttcOracleBundle`. -/
theorem ttcPolyCost_le_ttcComplexity
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (V : VolumeAlgorithm n) (ω : V.Ω)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) (cVol cSample : ℕ)
    (hterm : Terminates (algBlock atoms φ ε δ) (polyOracles atoms φ ε δ V ω t)
      (toDNFd (preprocess atoms φ))) :
    (ttcPolyCost atoms φ ε δ V ω t cVol cSample : ℝ)
      ≤ ttcComplexity atoms φ ε δ cVol cSample := by
  have hceil : ttcThresh atoms φ ε δ ≤ (⌈ttcThresh atoms φ ε δ⌉₊ : ℝ) := Nat.le_ceil _
  have hnat : ttcPolyCost atoms φ ε δ V ω t cVol cSample
      ≤ (toDNFd (preprocess atoms φ)).length
          * (cVol + cSample * ⌈ttcThresh atoms φ ε δ⌉₊) :=
    runCostAt_le_uniform (algBlock atoms φ ε δ) (polyOracles atoms φ ε δ V ω t)
      (fun _ => cVol) (fun _ => cSample) cVol cSample (algPrec atoms φ ε δ)
      (toDNFd (preprocess atoms φ)) ⌈ttcThresh atoms φ ε δ⌉₊ hceil hterm
      (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have hreal : (ttcPolyCost atoms φ ε δ V ω t cVol cSample : ℝ)
      ≤ ((toDNFd (preprocess atoms φ)).length : ℝ)
          * ((cVol : ℝ) + (cSample : ℝ) * (⌈ttcThresh atoms φ ε δ⌉₊ : ℝ)) := by
    exact_mod_cast hnat
  rw [ttcComplexity_def]
  refine le_trans hreal ?_
  have hceil_lt : (⌈ttcThresh atoms φ ε δ⌉₊ : ℝ) < ttcThresh atoms φ ε δ + 1 :=
    Nat.ceil_lt_add_one (ttcThresh_nonneg atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1)
  have hthr := ttcThresh_le_sum atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
  have hprice : (⌈ttcThresh atoms φ ε δ⌉₊ : ℝ)
      ≤ 41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
          + 15 * (Real.log (15 / (2 * δ))
              + Real.log ((toDNFd (preprocess atoms φ)).length)) + 1 := by
    linarith
  gcongr

end Cost

/-! # The measurable structure: the polynomial run as one measure

`Ttc.ttcPoly` is a `MeasureTheory.Measure.bind`, and `MeasureTheory.Measure.bind`
degenerates to the zero measure unless the family is measurable.  The four lemmas
below supply exactly what `Ttc.ttcCharged_eq_ttcPairLaw` (`Monadic/Program.lean:359`)
supplies for `Ttc.ttc`, at an arbitrary `Ttc.VolumeAlgorithm`: the coin-measurability
of the volume estimates (which is `Ttc.VolumeAlgorithm.est_meas`, a field), of the
rate vector, the kernel they define, and the joint measurability of the read-off
`(estimate, cost)`. -/

section Measurability

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The volume estimates are measurable in the volume algorithm's own coins.**
This is `Ttc.VolumeAlgorithm.est_meas` — a field of the structure, not a new
assumption. -/
theorem measurable_polyVol (V : VolumeAlgorithm n) (i : Cube A) :
    Measurable[V.mΩ] fun ω : V.Ω => polyVol atoms φ ε δ V ω i := by
  classical
  letI := V.mΩ
  by_cases hi : i ∈ toDNFd (preprocess atoms φ)
  · simp only [polyVol, volOfAlg, dif_pos hi]
    exact measurable_const.mul (V.est_meas _ _ _)
  · simp only [polyVol, volOfAlg, dif_neg hi]
    exact measurable_const

/-- **The rate vector is measurable in the volume coins.**  `Ttc.rates` is a product
of a coin-free sampler mass with the volume estimate. -/
theorem measurable_polyRates (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n)) :
    Measurable[V.mΩ] fun ω : V.Ω => polyRates atoms φ ε δ V ω rin Rout Mw sigma := by
  letI := V.mΩ
  exact measurable_pi_lambda _ fun s =>
    measurable_const.mul (measurable_polyVol atoms φ ε δ V _)

/-- **The coin-indexed family of trajectory laws, as an honest kernel.** -/
noncomputable def polyKernel (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n)) :
    @Kernel V.Ω (ℕ → Fin (algIndex atoms φ ε δ) → ℕ) V.mΩ _ :=
  letI := V.mΩ
  { toFun := fun ω => trajLaw (polyRates atoms φ ε δ V ω rin Rout Mw sigma)
    measurable' := measurable_trajLaw.comp
      (measurable_polyRates atoms φ ε δ V rin Rout Mw sigma) }

theorem polyKernel_apply (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (ω : V.Ω) :
    polyKernel atoms φ ε δ V rin Rout Mw sigma ω
      = trajLaw (polyRates atoms φ ε δ V ω rin Rout Mw sigma) := rfl

instance isMarkovKernel_polyKernel (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n)) :
    IsMarkovKernel (polyKernel atoms φ ε δ V rin Rout Mw sigma) :=
  ⟨fun _ => isProbabilityMeasure_trajLaw _⟩

/-- **The read-off `(estimate, cost)` of one run**, jointly in the volume coins and
the trajectory. -/
noncomputable def polyPair (V : VolumeAlgorithm n) (cVol cSample : ℕ) :
    V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ) → ℝ × ℕ :=
  fun p => (ttcPolyRun atoms φ ε δ V p.1 p.2,
    ttcPolyCost atoms φ ε δ V p.1 p.2 cVol cSample)

/-- **The read-off is countably determined**, hence measurable.  Both components go
through `Ttc/Monadic/`'s fold lemmas, which are stated over `Ttc.trajOracles` at an
arbitrary measurable coin space and an arbitrary `vol`. -/
theorem countablyDetermined_polyPair (V : VolumeAlgorithm n) (cVol cSample : ℕ) :
    @CountablyDetermined (V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ))
      (@Prod.instMeasurableSpace _ _ V.mΩ _) (ℝ × ℕ)
      (polyPair atoms φ ε δ V cVol cSample) := by
  letI := V.mΩ
  have hT : ∀ k, CountablyDetermined
      fun p : V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ) => p.2 k :=
    fun k => (countablyDetermined_apply (Y := Fin (algIndex atoms φ ε δ) → ℕ) k).precomp
      measurable_snd
  have hV : ∀ i, Measurable
      fun p : V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ) =>
        polyVol atoms φ ε δ V p.1 i :=
    fun i => (measurable_polyVol atoms φ ε δ V i).comp measurable_fst
  exact (countablyDetermined_run_div _ _ _ _ _ _ _ _ _ hT hV).prodMk
    (countablyDetermined_runCost _ _ _ _ _ _ _ cVol cSample _ hT hV)

theorem measurable_polyPair (V : VolumeAlgorithm n) (cVol cSample : ℕ) :
    @Measurable (V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ)) (ℝ × ℕ)
      (@Prod.instMeasurableSpace _ _ V.mΩ _) _
      (polyPair atoms φ ε δ V cVol cSample) := by
  letI := V.mΩ
  exact (countablyDetermined_polyPair atoms φ ε δ V cVol cSample).measurable

/-! ## The same read-off in the elementary cost model

`Ttc.polyPair` charges two supplied prices.  The pair below charges
`Ttc.elemRunCost` — the three elementary costs of `Model/Pseudocode`, folded along the
run — and is measurable for the same reason. -/

/-- **The elementary cost of one run at the canonical data.**  `Ttc.ttcPolyCost` with the
two supplied prices replaced by the elementary cost model. -/
noncomputable def ttcPolyElemCost (V : VolumeAlgorithm n) (ω : V.Ω)
    (t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ) (r Q Tw : ℕ) : ℕ :=
  elemRunCost (algBlock atoms φ ε δ) (polyOracles atoms φ ε δ V ω t) r Q Tw
    (algPrec atoms φ ε δ) (toDNFd (preprocess atoms φ))

/-- **The read-off `(estimate, elementary cost)` of one run.**  The first component is
`Ttc.polyPair`'s verbatim, so the estimate's law is untouched by the change of cost
model. -/
noncomputable def elemPolyPair (V : VolumeAlgorithm n) (r Q Tw : ℕ) :
    V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ) → ℝ × ℕ :=
  fun p => (ttcPolyRun atoms φ ε δ V p.1 p.2,
    ttcPolyElemCost atoms φ ε δ V p.1 p.2 r Q Tw)

theorem countablyDetermined_elemPolyPair (V : VolumeAlgorithm n) (r Q Tw : ℕ) :
    @CountablyDetermined (V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ))
      (@Prod.instMeasurableSpace _ _ V.mΩ _) (ℝ × ℕ)
      (elemPolyPair atoms φ ε δ V r Q Tw) := by
  letI := V.mΩ
  have hT : ∀ k, CountablyDetermined
      fun p : V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ) => p.2 k :=
    fun k => (countablyDetermined_apply (Y := Fin (algIndex atoms φ ε δ) → ℕ) k).precomp
      measurable_snd
  have hV : ∀ i, Measurable
      fun p : V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ) =>
        polyVol atoms φ ε δ V p.1 i :=
    fun i => (measurable_polyVol atoms φ ε δ V i).comp measurable_fst
  exact (countablyDetermined_run_div _ _ _ _ _ _ _ _ _ hT hV).prodMk
    (countablyDetermined_elemRunCost _ _ _ _ _ _ _ r Q Tw _ hT hV)

theorem measurable_elemPolyPair (V : VolumeAlgorithm n) (r Q Tw : ℕ) :
    @Measurable (V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ)) (ℝ × ℕ)
      (@Prod.instMeasurableSpace _ _ V.mΩ _) _
      (elemPolyPair atoms φ ε δ V r Q Tw) := by
  letI := V.mΩ
  exact (countablyDetermined_elemPolyPair atoms φ ε δ V r Q Tw).measurable

/-- **The elementary cost as an `ℝ≥0∞`-valued measurable function.**  Straight from
countable determinacy, which gives measurability into *any* target — so this needs no
composition lemma for the `ℕ → ℝ≥0∞` coercion. -/
theorem measurable_ttcPolyElemCost_ennreal (V : VolumeAlgorithm n) (r Q Tw : ℕ) :
    @Measurable (V.Ω × (ℕ → Fin (algIndex atoms φ ε δ) → ℕ)) ENNReal
      (@Prod.instMeasurableSpace _ _ V.mΩ _) _
      (fun p => (ttcPolyElemCost atoms φ ε δ V p.1 p.2 r Q Tw : ENNReal)) := by
  letI := V.mΩ
  exact ((countablyDetermined_elemPolyPair atoms φ ε δ V r Q Tw).map
    (fun p : ℝ × ℕ => (p.2 : ENNReal))).measurable

#print axioms measurable_elemPolyPair
#print axioms measurable_ttcPolyElemCost_ennreal

/-- **`Ttc.ttcPoly` is the composition–product pushed along the read-off.**  Verbatim
`Ttc.ttcCharged_eq_ttcPairLaw` (`Monadic/Program.lean:359`), at `V.μ` instead of
`Ttc.MonteCarlo.coins`.  This is what shows the `Measure.bind` is not the junk zero
measure. -/
theorem ttcPoly_eq_map_compProd (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ) :
    ttcPoly atoms φ ε δ V rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw
      = letI := V.mΩ
        haveI := V.isProb
        (V.μ ⊗ₘ polyKernel atoms φ ε δ V rin Rout Mw sigma).map
          (polyPair atoms φ ε δ V (polyVolPrice atoms φ Lc kap cc pf Mcool epsDraw)
            (polySamplePrice atoms φ ε δ gam R Mwarm)) := by
  letI := V.mΩ
  haveI := V.isProb
  have hpair := measurable_polyPair atoms φ ε δ V
    (polyVolPrice atoms φ Lc kap cc pf Mcool epsDraw)
    (polySamplePrice atoms φ ε δ gam R Mwarm)
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hpair]
  refine congrArg (Measure.bind V.μ) ?_
  funext ω
  rw [Kernel.map_apply _ hpair, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hpair measurable_prodMk_left]
  rfl

/-- **`Ttc.ttcPoly` is a probability measure** — the measure-level non-vacuity check.
A `MeasureTheory.Measure.bind` of a non-measurable family is the zero measure, and
every statement about it would be vacuous; this rules that out. -/
instance isProbabilityMeasure_ttcPoly (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ) :
    IsProbabilityMeasure
      (ttcPoly atoms φ ε δ V rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw) := by
  letI := V.mΩ
  haveI := V.isProb
  rw [ttcPoly_eq_map_compProd]
  exact Measure.isProbabilityMeasure_map
    (measurable_polyPair atoms φ ε δ V _ _).aemeasurable

end Measurability

/-! # The cost half, over the program

`All[r ← ttcPoly …; (r.2 : ℝ) ≤ …]` — no termination hypothesis, no price binder. -/

section CostProgram

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

open Ttc.Monadic

/-- **`Ttc.ttcPoly`'s charged cost is at most `Ttc.ttcComplexity` at the two closed
prices, almost surely.**

`Ttc.ttcComplexity` is `m · (C_vol + C_sample · (Θ + 1))`, and here `C_vol` and
`C_sample` are the **closed terms** `Ttc.polyVolPrice` and `Ttc.polySamplePrice` — not
binders.  The `Ttc.Terminates` guard is discharged by
`Ttc.ae_terminates_polyOracles`. -/
theorem all_ttcPoly_cost_le_ttcComplexity
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ) :
    All[r ← ttcPoly atoms φ ε δ V rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw;
      (r.2 : ℝ) ≤ ttcComplexity atoms φ ε δ
        (polyVolPrice atoms φ Lc kap cc pf Mcool epsDraw)
        (polySamplePrice atoms φ ε δ gam R Mwarm)] := by
  letI := V.mΩ
  haveI := V.isProb
  set B : ℝ := ttcComplexity atoms φ ε δ
    (polyVolPrice atoms φ Lc kap cc pf Mcool epsDraw)
    (polySamplePrice atoms φ ε δ gam R Mwarm) with hB
  set cV : ℕ := polyVolPrice atoms φ Lc kap cc pf Mcool epsDraw with hcV
  set cS : ℕ := polySamplePrice atoms φ ε δ gam R Mwarm with hcS
  have hpair := measurable_polyPair atoms φ ε δ V cV cS
  have hbad : MeasurableSet {r : ℝ × ℕ | ¬ ((r.2 : ℝ) ≤ B)} := by
    have hm : Measurable fun r : ℝ × ℕ => (r.2 : ℝ) := by fun_prop
    have hset : {r : ℝ × ℕ | ¬ ((r.2 : ℝ) ≤ B)}
        = (fun r : ℝ × ℕ => (r.2 : ℝ)) ⁻¹' Set.Ioi B := by
      ext r; simp [not_le]
    rw [hset]
    exact hm measurableSet_Ioi
  rw [MeasureTheory.ae_iff, ttcPoly_eq_map_compProd,
    Measure.map_apply hpair hbad,
    Measure.compProd_apply (hpair hbad)]
  have hzero : ∀ ω : V.Ω, polyKernel atoms φ ε δ V rin Rout Mw sigma ω
      {t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ |
        B < ((polyPair atoms φ ε δ V cV cS (ω, t)).2 : ℝ)} = 0 := by
    intro ω
    have hset : {t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ |
          B < ((polyPair atoms φ ε δ V cV cS (ω, t)).2 : ℝ)}
        = {t : ℕ → Fin (algIndex atoms φ ε δ) → ℕ |
            ¬ ((ttcPolyCost atoms φ ε δ V ω t cV cS : ℝ) ≤ B)} := by
      ext t; simp [polyPair, not_le]
    rw [polyKernel_apply, hset, ← MeasureTheory.ae_iff]
    filter_upwards [ae_terminates_polyOracles atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
      V ω rin Rout Mw sigma] with t ht
    exact ttcPolyCost_le_ttcComplexity atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 V ω t
      cV cS ht
  simp [hzero]

/-- **THE COST HALF: `m · n⁴ · (explicit factors)`, with no price binder.**

`Ttc.ttcPoly`'s cost coordinate is the fold of `Ttc.stepCost` at the two *closed*
prices `Ttc.polyVolPrice` and `Ttc.polySamplePrice`; this theorem collapses them by
`Ttc.CoolCost.cvVolumeOpsPrice_le_cool` and
`Ttc.SamplerCost.samplePrice_le_quartic`.

The remaining hypotheses are **regime conditions on the geometry**, all visible: the
facet bound, the inradius/circumradius pair `(gam, R)`, the warmness `Mwarm`/`Mcool`,
the cooling parameters `(Lc, kap, cc, pf)` and the per-draw tolerance `epsDraw`.  None
of them is about the algorithm's randomness, and none is a price. -/
theorem all_ttcPoly_cost_le_quartic
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ)
    -- the sampler-side regime
    (hrfac : 1 ≤ canonRfac (toDNFd (preprocess atoms φ)))
    (hR1 : 1 ≤ R) (hgam0 : 0 < gam) (hgamR : gam ≤ R)
    (hMw1 : 1 ≤ Mwarm) (hMwB : Mwarm ≤ (2 * R) ^ n)
    (hep0 : 0 < (algBlock atoms φ ε δ).epsPrime)
    (hep1 : (algBlock atoms φ ε δ).epsPrime ≤ 1)
    (hepn : 1 / 2 ^ n ≤ (algBlock atoms φ ε δ).epsPrime)
    -- the volume-side (Gaussian cooling) regime
    (hL : 1 ≤ Lc) (hkap0 : 0 < kap) (hkap1 : kap ≤ 1) (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : ℝ)) (hp0 : 0 < pf) (hp1 : pf ≤ 1 / 2)
    (hMc : 1 ≤ Mcool) (hed0 : 0 < epsDraw) (hed1 : epsDraw ≤ 1) :
    All[r ← ttcPoly atoms φ ε δ V rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
          * (2 ^ 42 * (canonRfac (toDNFd (preprocess atoms φ)) + 1)
                * Real.log (8 * Mcool / epsDraw ^ 2)
                * (Lc ^ 4 * Real.log (1 / pf) / kap ^ 3)
              + 2 ^ 62 * canonRfac (toDNFd (preprocess atoms φ))
                  * (R ^ 2 / gam ^ 2) * Real.log (2 * R)
                  * PolyComplexity.threshFactor ε δ
                      (toDNFd (preprocess atoms φ)).length)] := by
  have hrfac0 : (0 : ℝ) ≤ canonRfac (toDNFd (preprocess atoms φ)) := by linarith
  have hlogd : (0 : ℝ) ≤ Real.log (8 * Mcool / epsDraw ^ 2) := by
    have h := CoolCost.two_le_log_deadline hMc hed0 hed1
    linarith
  have hlogp : (0 : ℝ) ≤ Real.log (1 / pf) := by
    have h2 : (2 : ℝ) ≤ 1 / pf := by rw [le_div_iff₀ hp0]; linarith
    have h3 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
    have h4 := Real.log_two_gt_d9
    linarith
  have hCv0 : (0 : ℝ) ≤ 2 ^ 42 * (canonRfac (toDNFd (preprocess atoms φ)) + 1)
      * Real.log (8 * Mcool / epsDraw ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hlogd
  have hvolFac0 : (0 : ℝ) ≤ Lc ^ 4 * Real.log (1 / pf) / kap ^ 3 :=
    div_nonneg (mul_nonneg (by positivity) hlogp) (by positivity)
  have hcVol : ((polyVolPrice atoms φ Lc kap cc pf Mcool epsDraw : ℕ) : ℝ)
      ≤ 2 ^ 42 * (canonRfac (toDNFd (preprocess atoms φ)) + 1)
            * Real.log (8 * Mcool / epsDraw ^ 2)
          * (n : ℝ) ^ 4 * (Lc ^ 4 * Real.log (1 / pf) / kap ^ 3) :=
    CoolCost.cvVolumeOpsPrice_le_cool hn hL hkap0 hkap1 hcc1 hcc hp0 hp1 hMc hed0 hed1
      hrfac0
  have hcSample : ((polySamplePrice atoms φ ε δ gam R Mwarm : ℕ) : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * canonRfac (toDNFd (preprocess atoms φ))
          * (R ^ 2 / gam ^ 2) * Real.log (2 * R) :=
    SamplerCost.samplePrice_le_quartic n hn hrfac hR1 hgam0 hgamR hMw1 hMwB hep0 hep1 hepn
  have hb := PolyComplexity.ttcComplexity_le_quartic atoms φ ε δ
    (polyVolPrice atoms φ Lc kap cc pf Mcool epsDraw)
    (polySamplePrice atoms φ ε δ gam R Mwarm) 4 hn le_rfl
    hCv0 hvolFac0 hrfac hR1 hgam0 hε0 hε1 hδ0 hδ1 hcVol hcSample
  filter_upwards [all_ttcPoly_cost_le_ttcComplexity atoms φ ε δ hε0 hε1 hn hφ hpos
    hδ0 hδ1 V rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw] with r hr
  exact hr.trans hb

end CostProgram

/-! # The accuracy half: the reduction to `Ttc.volume_estimate_joint`

`Ttc.volume_estimate_joint` (`Coupling/Product.lean:328`) is **already generic** in the
volume algorithm, its coins, the volume estimates, the sampler `sampD` and its
`Ttc.KV97Sampler` certificate, and it is stated over `Ttc.trajOracles` — the very
bundle `Ttc.polyOracles` is.  Its conclusion is an iterated integral over `volAlg.μ`
of a trajectory-law measure, which is exactly the shape `Ttc.ttcPoly`'s accuracy
conjunct unfolds to.  The lemma below performs that unfolding. -/

section Accuracy

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

open Ttc.Monadic

/-- **`Ttc.ttcPoly`'s accuracy conjunct is the iterated integral of
`Ttc.volume_estimate_joint`'s shape.**

The left-hand side is what the capstone states; the right-hand side is what
`Ttc.volume_estimate_joint` bounds, at `volAlg := V`, `vol := Ttc.polyVol`,
`sampD := Ttc.polySampD` and `θ := Ttc.polyRates`.  No hypothesis beyond
measurability of the target set. -/
theorem pr_ttcPoly_fst_eq_lintegral
    (V : VolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) :
    Pr[r ← ttcPoly atoms φ ε δ V rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw;
        r.1 ∈ S]
      = letI := V.mΩ
        (∫⁻ ω, trajLaw (polyRates atoms φ ε δ V ω rin Rout Mw sigma)
            {t | ttcPolyRun atoms φ ε δ V ω t ∈ S} ∂V.μ).toReal := by
  letI := V.mΩ
  haveI := V.isProb
  set cV : ℕ := polyVolPrice atoms φ Lc kap cc pf Mcool epsDraw with hcV
  set cS : ℕ := polySamplePrice atoms φ ε δ gam R Mwarm with hcS
  have hpair := measurable_polyPair atoms φ ε δ V cV cS
  have hgood : MeasurableSet {r : ℝ × ℕ | r.1 ∈ S} := measurable_fst hS
  refine congrArg ENNReal.toReal ?_
  rw [ttcPoly_eq_map_compProd, Measure.map_apply hpair hgood,
    Measure.compProd_apply (hpair hgood)]
  rfl

end Accuracy

/-! # The asymptotic form

`m`, `ε`, `δ` and every geometric quantity are **binders of the statement**, never
inside the `O(·)`. -/

section Asymptotic

/-- **`O(n⁴)` for the polynomial run's charged cost**, over a family of inputs of
dimension `N`.

Everything that is not `N` is a visible binder: the cube-count bound `mBound`, the
accuracy/confidence `(ε, δ)`, the facet bound `rf`, the ball radii `(gam, R)`, the
cooling constants `(Cv, volFac)`.  The two price hypotheses are
`Ttc.CoolCost.cvVolumeOpsPrice_le_cool` and
`Ttc.SamplerCost.samplePrice_le_quartic` applied at each `N`.

⚠ This bounds `Ttc.ttcComplexity` at the two **closed** prices, which
`Ttc.all_ttcPoly_cost_le_ttcComplexity` shows dominates `Ttc.ttcPoly`'s cost
coordinate almost surely.  It is not a claim that `TTC` runs in `O(m·n⁴)`; see the
module docstring. -/
theorem isBigO_ttcPolyCost_quartic {Af : ℕ → Type*}
    (atoms : ∀ N, Af N → LinAtom N) (φ : ∀ N, BForm (Af N))
    (ε δ : ℝ) (Cv volFac rf R gam Lc kap cc pf Mcool epsDraw Mwarm : ℝ) (mBound : ℕ)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hrf : 1 ≤ rf) (hR1 : 1 ≤ R) (hgam0 : 0 < gam)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcVol : ∀ N : ℕ,
      ((polyVolPrice (atoms N) (φ N) Lc kap cc pf Mcool epsDraw : ℕ) : ℝ)
        ≤ Cv * (N : ℝ) ^ 4 * volFac)
    (hcSample : ∀ N : ℕ,
      ((polySamplePrice (atoms N) (φ N) ε δ gam R Mwarm : ℕ) : ℝ)
        ≤ 2 ^ 62 * (N : ℝ) ^ 4 * rf * (R ^ 2 / gam ^ 2) * Real.log (2 * R))
    (hm : ∀ N : ℕ, (toDNFd (preprocess (atoms N) (φ N))).length ≤ mBound) :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ttcComplexity (atoms N) (φ N) ε δ
        (polyVolPrice (atoms N) (φ N) Lc kap cc pf Mcool epsDraw)
        (polySamplePrice (atoms N) (φ N) ε δ gam R Mwarm))
      (fun N : ℕ => (N : ℝ) ^ 4) :=
  PolyComplexity.isBigO_ttcComplexity_quartic (Cv := Cv) (volFac := volFac) (rfac := rf)
    (R := R) (γ := gam) atoms φ ε δ _ _ 4 mBound le_rfl hCv hvolFac hrf hR1 hgam0
    hε0 hε1 hδ0 hδ1 hcVol hcSample hm

end Asymptotic

/-! # Non-vacuity (`CLAUDE.md` §11)

Two checks, neither of which the other implies.

* `Ttc.nonempty_volumeAlgorithm` — the binder `V` ranges over a **nonempty** type, so
  the theorems above are not vacuously quantified.  The witness is
  `Ttc.VolumeAlgorithm.monteCarlo`, the development's unconditional instance; it is
  *not* the Cousins–Vempala one, and using it would of course reinstate the
  exponential price.  Which `V` is supplied changes the accuracy, never the cost
  statements — those are proved for every `V`.
* `Ttc.isProbabilityMeasure_ttcPoly` — the **measure-level** check.  A
  `MeasureTheory.Measure.bind` of a non-measurable family is the zero measure, at
  which every `All[…]` is vacuously true and every `Pr[…]` is `0`.  That instance
  rules it out at every `V`. -/

/-- The volume-algorithm binder is not vacuous. -/
theorem nonempty_volumeAlgorithm (n : ℕ) : Nonempty (VolumeAlgorithm n) :=
  ⟨VolumeAlgorithm.monteCarlo n⟩

/-! ## Axiom profile -/

end Ttc

#print axioms Ttc.polyOracles
#print axioms Ttc.polyOracles_vol
#print axioms Ttc.ttcPoly
#print axioms Ttc.toNNReal_max_zero
#print axioms Ttc.trajLaw_max_zero
#print axioms Ttc.ae_terminates_polyOracles
#print axioms Ttc.ttcPolyCost_le_ttcComplexity
#print axioms Ttc.measurable_polyVol
#print axioms Ttc.measurable_polyRates
#print axioms Ttc.polyKernel
#print axioms Ttc.countablyDetermined_polyPair
#print axioms Ttc.measurable_polyPair
#print axioms Ttc.ttcPoly_eq_map_compProd
#print axioms Ttc.isProbabilityMeasure_ttcPoly
#print axioms Ttc.all_ttcPoly_cost_le_ttcComplexity
#print axioms Ttc.all_ttcPoly_cost_le_quartic
#print axioms Ttc.pr_ttcPoly_fst_eq_lintegral
#print axioms Ttc.isBigO_ttcPolyCost_quartic
#print axioms Ttc.nonempty_volumeAlgorithm

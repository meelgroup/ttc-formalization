/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Pair
import Ttc.Process.Truncation
import Ttc.Sampler.RatesNonneg
import Ttc.Exec.Complexity

/-!
# `Monadic/Program`: `TTC`'s run, as one law on one space

`Ttc.ttc_accuracy_single_measure` (`Monadic/EventMeasurable`) states the accuracy
guarantee over the composition–product

```
MonteCarlo.coins n ⊗ₘ ttcTrajKernel …
```

— the volume oracle's coins, then the trajectory law at the rates *that* draw
produced.  This file gives that measure a name, `Ttc.ttcLaw`, so that the headline
`Ttc.ttc_volume_estimate` can state **both** of its conjuncts about a single point
`p = (c, t)` of a single space, drawn from a single law: no iterated integral, and
no pair of separately-quantified coin sequences.

`Ttc.ttcLaw` is the analogue of nfalean's `ApproxNFA.countNFAM`, with one honest
difference recorded in `Monadic/MeasurePr`'s docstring and repeated here: ours is a
`MeasureTheory.Measure`, not a `PMF`.  `Ttc.MonteCarlo.coins` is
`MeasureTheory.Measure.infinitePi` of the uniform law on a Euclidean ball — atomless
on an uncountable space — so there is no `PMF` whose `toOuterMeasure` it is, and the
`PMF` monad is simply unavailable.  What survives is the Giry-monad structure:
`Ttc.ttcTrajKernel` is a genuine Markov kernel (`Monadic/Kernel`), so `⊗ₘ` is the
monadic bind of a probability measure with it, and `Ttc.ttcLaw` is again a
probability measure (`Ttc.instIsProbabilityMeasureTtcLaw`).

Three declarations, no proof content: `Ttc.ttcLaw`, its `rfl` lemma
`Ttc.ttcLaw_def`, and the `IsProbabilityMeasure` instance.

## The paired law `Ttc.ttcPairLaw`

The second half of this file is the closest available analogue of nfalean's

```
countNFAM A n ε δ : PMF (ℝ × ℕ)
```

— a single object returning `(estimate, cost)`, so that both halves of a headline can
be read off *one* draw.  Ours is `Ttc.ttcLaw` pushed forward along the deterministic
read-off `Ttc.ttcPair`,

```
p ↦ (ttcRun … p.1 p.2, ttcCost … p.1 p.2 cVol cSample) : ℝ × ℕ
```

giving `Ttc.ttcPairLaw … cVol cSample : Measure (ℝ × ℕ)`, again a probability measure
(`Ttc.instIsProbabilityMeasureTtcPairLaw`).  Both components are countably determined
in the run — the output by `Ttc.countablyDetermined_ttcAlgOutput_joint`, the cost by
`Ttc.countablyDetermined_ttcCost_joint` (`Monadic/Pair`) — so the read-off is
measurable and the pushforward is honest.

### Why the two per-call charges stay as parameters

`Ttc.ttcCost … c t cVol cSample` takes the cost of one `Vol_ED` call and the cost of
one generated sample as arguments, because `Runtime.lean` cannot derive them: `Vol_ED`
and `GenerateSamples` are *oracles*, and the model fixes what they return, never how
they compute it.  The headline's runtime conjunct is therefore universally quantified
over `cVol` and `cSample`.  `Ttc.ttcPairLaw` keeps them as **parameters of the law**
rather than fixing them (to `1`, say): fixing them would silently replace a statement
about every charging convention by a statement about one, and there is no distinguished
convention to pick.  So there is one pair law per charging convention, and every
statement below is quantified over `cVol` and `cSample` exactly as the headline is.

### What transfers, and what does not

`Ttc.PrR_ttcPairLaw` transfers **every** event, with no measurability hypothesis at
all — `Ttc.map_apply_of_countablyDetermined` (`Monadic/Pair`) supplies what nfalean gets
for free from `PMF.toOuterMeasure`.  `Ttc.ttc_accuracy_pairLaw` is the headline's
accuracy conjunct restated over the pair law, with nothing lost.

The runtime conjunct moves across in **three** incomparable forms, and this file keeps
all three rather than picking one:

* `Ttc.ttcPairLaw_cost_le` — the bound over the image of the terminating set.  The
  guard `Ttc.ttcTerminates … p.1 p.2` is a property of the *run* `p` and is not a
  function of the pair `(estimate, cost)`, so if it is to be kept at all it can only
  survive as the set the image is taken over;
* `Ttc.ttcPairLaw_cost_le_of_terminates` — the bound over
  `Set.range (Ttc.ttcPair …)`, "every run the program can produce", under a *global*
  termination hypothesis.  No exceptional outcome, null or otherwise; this is the
  honest analogue of nfalean's `All[r ← …]` for a `PMF`, and
  `Ttc.all_ttcPairLaw_cost_le_of_terminates` is its (strictly weaker) `∀ᵐ` shadow;
* `Ttc.all_ttcPairLaw_cost_le` — **no guard at all**:
  `All[r ← ttcPairLaw …; (r.2 : ℝ) ≤ ttcComplexity …]`, with every hypothesis about
  the algorithm's *inputs* and none about its run.

The last one is not a weakening of the first two, and neither of the first two is a
weakening of it: they bound `r.2` by `m·(C_vol + C_sample·(Thresh + 1))` with
`Ttc.ttcThresh` still a `max`, whereas `Ttc.ttcComplexity` (`Exec/Complexity`) replaces
that `max` by the sum of its two branches, losing up to a factor of two on the threshold
term.  Sharper bound with a guard, or looser bound with none.

### How the guard was removed

`Ttc.ae_ttcLaw_ttcTerminates` is the seam.  `Process/Truncation` proves
`Ttc.Terminates` almost surely under `Ttc.trajLaw θ` for any `θ ≥ 0`;
`Ttc.ttcRates_nonneg` (`Sampler/RatesNonneg`) supplies `θ ≥ 0` at the run's own rate
vector **unconditionally**; and the lift through `Ttc.MonteCarlo.coins ⊗ₘ …` is done
*without* `MeasureTheory.Measure.ae_compProd_of_ae_ae`, whose `MeasurableSet {x | p x}`
hypothesis is unavailable here — `Ttc.ttcTerminates` quantifies over every
`Ttc.SketchState n`, whose `X` field is an uncountable `Multiset (Space n)`, and no
measurability of that event is known.  What replaces it is a **measurable null
superset**: `Ttc.Vanish` (`Process/Truncation`) implies termination, so the
non-terminating runs sit inside `Prod.snd ⁻¹' ⋂ Lb, (Vanish _ Lb)ᶜ`, which *is*
measurable (`Ttc.measurableSet_vanish`) and null (`Ttc.trajLaw_iInter_compl_vanish`).
`MeasureTheory.measure_mono_null` then does the rest, comparing outer measures, so the
termination event itself is never required to be measurable.

**The collapse, which is the opposite of the discrete intuition.**  One might expect a
support-based quantifier to be stronger than `∀ᵐ`, as `PMF.support ⊆ {x | E x}` is often
described.  For `Ttc.ttcPairLaw` it is **not**: `Ttc.all_ttcPairLaw_iff_atoms` proves that
`∀ᵐ` is *equivalent* to the literal `PMF`-support reading "`E` holds at every outcome of
positive mass".  The reason is structural — the pair law is a pushforward along a
**countably determined** read-off, so it is carried by the countable
`Set.range (Ttc.ttcPair …)`, and a countable carrier leaves no room for a large-but-null
exceptional set inside the range.  (That named hypothesis is where the collapse lives:
`Ttc.ae_map_iff_atoms_of_countablyDetermined` in `Monadic/Pair` states it in general, and
without it the equivalence is false.)

So dressing the runtime conjunct in a support-based quantifier buys **nothing** over
`All[…]`, and at the *same* right-hand side both are strictly weaker than
`Ttc.ttcPairLaw_cost_le_of_terminates`:
`Ttc.all_ttcPairLaw_cost_le_of_terminates` derives the a.e. form from the range form,
one way only.  `Model/Theorem.lean`'s runtime conjunct therefore stays pointwise over
runs, and keeps `Ttc.ttcThresh`'s `max`.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open Ttc.Monadic

/-! ## The measurable null set that carries the non-terminating runs

`Ttc.ttcTerminates … p.1 p.2` quantifies over every `Ttc.SketchState n`, whose `X`
field is an uncountable `Multiset (Space n)`, so `{p | ttcTerminates … p.1 p.2}` is
**not** known to be measurable — and `MeasureTheory.Measure.ae_compProd_of_ae_ae`
(and `…ae_compProd_iff`) both demand exactly that.  So the composition–product is
not entered through them.

What is used instead is that a `MeasureTheory.Measure` in Mathlib is an *outer*
measure: `μ s` is defined for every `s`, and `MeasureTheory.measure_mono_null`
needs no measurability of either set.  It therefore suffices to exhibit **one
measurable null superset** of the non-terminating runs, and `Process/Truncation`
already names it: `Ttc.Vanish L Lb` (the trajectory is empty from level `Lb` on)
implies `Ttc.BudgetMet`, hence `Ttc.Terminates` (`Ttc.budgetMet_of_vanish`,
`Ttc.terminates_of_budgetMet`), so

```
{p | ¬ ttcTerminates … p.1 p.2} ⊆ Prod.snd ⁻¹' ⋂ Lb, (Vanish L Lb)ᶜ
```

and the right-hand side *is* measurable — `Ttc.Vanish` is a countable intersection
of preimages of `{0}` under coordinate evaluations.  Its `Ttc.trajLaw`-measure is
`0` because it sits inside `(Vanish L Lb)ᶜ` for **every** `Lb`, and
`Ttc.trajLaw_compl_vanish_le` bounds that by `2Λ/2^Lb → 0`.  Only then is
`MeasureTheory.Measure.compProd_apply` applied — to the measurable superset. -/

/-- **`Ttc.Vanish` is measurable**: `{ω | ∀ j ≥ Lb, ω j = 0}` is the countable
intersection over `j ≥ Lb` of the preimages of `{0}` under `ω ↦ ω j`. -/
theorem measurableSet_vanish (L Lb : ℕ) : MeasurableSet (Vanish L Lb) := by
  have hset : Vanish L Lb
      = ⋂ j : ℕ, ⋂ _ : Lb ≤ j, (fun ω : ℕ → Fin L → ℕ => ω j) ⁻¹' {0} := by
    ext ω
    simp [Vanish, Set.mem_iInter]
  rw [hset]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    (measurable_pi_apply j) (MeasurableSet.singleton 0)

/-- **The trajectories that vanish at no level form a null set.**

`Ttc.trajLaw_compl_vanish_le` gives `trajLaw θ (Vanish L Lb)ᶜ ≤ 2Λ/2^Lb` for every
`Lb`, and the intersection over `Lb` is inside each of them, so its measure is below
a sequence tending to `0`.  The single hypothesis is the one
`Process/Truncation` asks of `θ` throughout: `0 ≤ θ s`. -/
theorem trajLaw_iInter_compl_vanish {L : ℕ} {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) :
    trajLaw θ (⋂ Lb : ℕ, (Vanish L Lb)ᶜ) = 0 := by
  refine le_antisymm ?_ bot_le
  refine ge_of_tendsto' (tendsto_geom_bound (∑ s, θ s)) fun Lb => ?_
  exact le_trans (measure_mono (Set.iInter_subset _ Lb)) (trajLaw_compl_vanish_le hθ Lb)

section Law

variable {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

/-- **The law of one run of `TTC(F, ε, δ)`**: a measure on pairs
`p = (volume coins, sample trajectory)`.

The composition–product of the volume oracle's coin law `Ttc.MonteCarlo.coins` with
the coin-indexed trajectory kernel `Ttc.ttcTrajKernel` — that is, draw the volume
coins `c`, then draw the trajectory from the coupled family at the rates `c`
produced.  Everything the algorithm reads on a run is a function of `p`: the oracle
bundle is `Ttc.ttcOracleBundle … p.1 p.2`, the output is
`Ttc.ttcAlgOutput … (that bundle)`, and the charged cost is `Ttc.ttcCost … p.1 p.2`.

This is what makes `Ttc.ttc_volume_estimate`'s two conjuncts statements about *the
same run*, and it is why that theorem has no iterated integral. -/
noncomputable def ttcLaw :
    Measure ((ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ)) :=
  MonteCarlo.coins n ⊗ₘ ttcTrajKernel atoms φ ε δ

/-- **What `Ttc.ttcLaw` is**, by `rfl`: the composition–product of the volume coins
with the coin-indexed trajectory kernel.  This is the identification that lets
`Ttc.ttc_accuracy_single_measure` be quoted verbatim as the headline's accuracy
conjunct. -/
theorem ttcLaw_def :
    ttcLaw atoms φ ε δ
      = MonteCarlo.coins n ⊗ₘ ttcTrajKernel atoms φ ε δ := rfl

/-- **A run's law is a probability measure.**  `Ttc.MonteCarlo.coins` is one
(`Ttc.MonteCarlo.instIsProbabilityMeasureCoins`) and `Ttc.ttcTrajKernel` is Markov
(`Ttc.isMarkovKernel_ttcTrajKernel`), so Mathlib's instance for `⊗ₘ` applies. -/
instance instIsProbabilityMeasureTtcLaw :
    IsProbabilityMeasure (ttcLaw atoms φ ε δ) := by
  rw [ttcLaw_def]
  infer_instance

/-! ### Termination is `Ttc.ttcLaw`-almost sure

`Process/Truncation` proves `Ttc.Terminates` almost surely under the *trajectory*
law at a fixed nonnegative rate vector.  Here that is lifted through the
composition–product, using the measurable null superset described above rather than
`MeasureTheory.Measure.ae_compProd_of_ae_ae` (which would need the termination event
itself measurable, and it is not known to be). -/

/-- **The kernel at a coin sequence is the trajectory law at the rates that sequence
produced**, by `rfl`. -/
theorem ttcTrajKernel_apply (c : ℕ → Space n) :
    ttcTrajKernel atoms φ ε δ c = trajLaw (ttcRates atoms φ ε δ c) := rfl

include hε0 hε1 hn hφ hpos in
/-- **The run's absorption loops terminate `Ttc.ttcLaw`-almost surely.**

`Ttc.ttcTerminates` is the one run hypothesis `Ttc.ttcCost_le_ttcComplexity`
(`Exec/Complexity`) still carries; this discharges it up to a null set of runs, over
the *joint* law of the volume coins and the trajectory.

Three ingredients, none of them new mathematics:

* `Ttc.ttcRates_nonneg` (`Sampler/RatesNonneg`) — the rate vector is nonnegative,
  **unconditionally**, so `Process/Truncation` applies at every coin sequence `c`;
* `Ttc.ttcThresh_nonneg` (`Exec/Api`) — `0 ≤ Thresh`, which is where `hε0`, `hε1`,
  `hn`, `hφ`, `hpos`, `hδ0` and `hδ1` are spent, and the only place they are;
* the measurable null superset `Prod.snd ⁻¹' ⋂ Lb, (Vanish _ Lb)ᶜ`, which sidesteps
  the (unknown) measurability of `{p | ttcTerminates … p.1 p.2}` entirely.

Note what is **not** assumed: nothing about the volume coins, no good event, and no
truncation of the algorithm. -/
theorem ae_ttcLaw_ttcTerminates (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᵐ p ∂(ttcLaw atoms φ ε δ), ttcTerminates atoms φ ε δ p.1 p.2 := by
  have hT : 0 ≤ (ttcBlock atoms φ ε δ).thresh :=
    ttcThresh_nonneg atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
  -- the measurable superset
  have hNmeas : MeasurableSet
      (Prod.snd ⁻¹' (⋂ Lb : ℕ, (Vanish (ttcIndex atoms φ ε δ) Lb)ᶜ) :
        Set ((ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ))) :=
    measurable_snd (MeasurableSet.iInter fun Lb => (measurableSet_vanish _ Lb).compl)
  have hNnull : ttcLaw atoms φ ε δ
      (Prod.snd ⁻¹' (⋂ Lb : ℕ, (Vanish (ttcIndex atoms φ ε δ) Lb)ᶜ)) = 0 := by
    rw [ttcLaw_def, Measure.compProd_apply hNmeas]
    have hslice : ∀ c : ℕ → Space n,
        ttcTrajKernel atoms φ ε δ c
            (Prod.mk c ⁻¹' (Prod.snd ⁻¹'
              (⋂ Lb : ℕ, (Vanish (ttcIndex atoms φ ε δ) Lb)ᶜ))) = 0 := by
      intro c
      rw [show (Prod.mk c ⁻¹' (Prod.snd ⁻¹'
            (⋂ Lb : ℕ, (Vanish (ttcIndex atoms φ ε δ) Lb)ᶜ)))
          = ⋂ Lb : ℕ, (Vanish (ttcIndex atoms φ ε δ) Lb)ᶜ from rfl,
        ttcTrajKernel_apply]
      exact trajLaw_iInter_compl_vanish (ttcRates_nonneg atoms φ ε δ c)
    simp only [hslice, lintegral_const, zero_mul]
  refine MeasureTheory.ae_iff.2 (measure_mono_null ?_ hNnull)
  intro p hp
  simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_compl_iff]
  intro Lb hv
  exact hp (terminates_of_budgetMet (P := ttcBlock atoms φ ε δ)
    (O := ttcOracleBundle atoms φ ε δ p.1 p.2) (Lb := Lb)
    (budgetMet_of_vanish
      (latticeEnum_injective (atomSet (ttcAtoms atoms φ ε δ)) (ttcInput atoms φ)
        (ttcPrec atoms φ ε δ))
      (ttcBlock atoms φ ε δ) _ _ _ hT hv)
    (toDNFd (ttcInput atoms φ)))

/-! ## The paired law: one measure on `(estimate, cost)` -/

/-- **The deterministic read-off `p ↦ (estimate, cost)`.**

`Ttc.ttcRun` is `Model/Pseudocode`'s own output on the run `p = (c, t)` — the oracle
bundle filled in from `p` itself — and `Ttc.ttcCost` is `alg:ttc`'s charged cost on the
same run, at the per-call charges `cVol` (one `Vol_ED` call) and `cSample` (one
generated sample).  No randomness: this is a function of the run. -/
noncomputable def ttcPair (cVol cSample : ℕ) :
    (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ) → ℝ × ℕ :=
  fun p =>
    (ttcRun atoms φ ε δ p.1 p.2,
      ttcCost atoms φ ε δ p.1 p.2 cVol cSample)

/-- **What `Ttc.ttcPair` is**, by `rfl`. -/
theorem ttcPair_def (cVol cSample : ℕ)
    (p : (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ)) :
    ttcPair atoms φ ε δ cVol cSample p
      = (ttcRun atoms φ ε δ p.1 p.2,
          ttcCost atoms φ ε δ p.1 p.2 cVol cSample) := rfl

/-- **The read-off is countably determined**: its first component by
`Ttc.countablyDetermined_ttcAlgOutput_joint` (`Ttc.ttcRun` is that term, by `rfl`), its
second by `Ttc.countablyDetermined_ttcCost_joint` (`Monadic/Pair`). -/
theorem countablyDetermined_ttcPair (cVol cSample : ℕ) :
    CountablyDetermined (ttcPair atoms φ ε δ cVol cSample) :=
  (countablyDetermined_ttcAlgOutput_joint atoms φ ε δ).prodMk
    (countablyDetermined_ttcCost_joint atoms φ ε δ cVol cSample)

/-- **The read-off is measurable.** -/
theorem measurable_ttcPair (cVol cSample : ℕ) :
    Measurable (ttcPair atoms φ ε δ cVol cSample) :=
  (countablyDetermined_ttcPair atoms φ ε δ cVol cSample).measurable

/-- **The law of `(estimate, cost)` on one run of `TTC(F, ε, δ)`** — `Ttc.ttcLaw` pushed
forward along `Ttc.ttcPair`.  This is the `Measure` analogue of nfalean's
`ApproxNFA.countNFAM : PMF (ℝ × ℕ)`; see the module docstring for why the two per-call
charges stay parameters and for what does and does not transfer to it. -/
noncomputable def ttcPairLaw (cVol cSample : ℕ) : Measure (ℝ × ℕ) :=
  (ttcLaw atoms φ ε δ).map
    (ttcPair atoms φ ε δ cVol cSample)

/-- **What `Ttc.ttcPairLaw` is**, by `rfl`. -/
theorem ttcPairLaw_def (cVol cSample : ℕ) :
    ttcPairLaw atoms φ ε δ cVol cSample
      = (ttcLaw atoms φ ε δ).map
          (ttcPair atoms φ ε δ cVol cSample) := rfl

/-- **`Model/Pseudocode`'s `Ttc.ttc` is the paired law.**

`Ttc.ttc` is the algorithm as written in `Model/`: a `MeasureTheory.Measure.bind` of
the volume coins with the `MeasureTheory.Measure.map` of the trajectory law along the
read-off — a definition that carries no measurability obligation, which is why it can
live in the audit surface.  This identifies it with the composition–product form
`Ttc.ttcPairLaw` that the rest of the development reasons about, so `Ttc.ttc` is not a
rename: every theorem below transfers to it verbatim.

Three Mathlib steps and nothing else: `MeasureTheory.Measure.compProd_eq_comp_prod`
turns `⊗ₘ` into a `bind`, `MeasureTheory.Measure.map_comp` pushes the read-off inside
it, and `MeasureTheory.Measure.dirac_prod` evaluates the resulting kernel at a coin
sequence.  The `Model/`-side names are definitionally the run's own
(`Ttc.algRates_eq_ttcRates`, `Ttc.algCost_eq_ttcCost`, both `rfl`), so the last step is
`rfl`. -/
theorem ttc_eq_ttcPairLaw (cVol cSample : ℕ) :
    ttc atoms φ ε δ cVol cSample = ttcPairLaw atoms φ ε δ cVol cSample := by
  have hpair : Measurable (ttcPair atoms φ ε δ cVol cSample) :=
    measurable_ttcPair atoms φ ε δ cVol cSample
  rw [ttcPairLaw_def, ttcLaw_def, Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ hpair]
  refine congrArg (Measure.bind (MonteCarlo.coins n)) ?_
  funext c
  rw [Kernel.map_apply _ hpair, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hpair measurable_prodMk_left]
  rfl

/-- **The paired law is a probability measure**, from `Ttc.instIsProbabilityMeasureTtcLaw`
and the measurability of the read-off. -/
instance instIsProbabilityMeasureTtcPairLaw (cVol cSample : ℕ) :
    IsProbabilityMeasure (ttcPairLaw atoms φ ε δ cVol cSample) := by
  rw [ttcPairLaw_def]
  exact Measure.isProbabilityMeasure_map
    (measurable_ttcPair atoms φ ε δ cVol cSample).aemeasurable

/-! ### Transfer

The pair law's mass at **any** set is the run law's mass at its preimage — no
measurability hypothesis, because `Ttc.ttcPair` has countable range
(`Ttc.map_apply_of_countablyDetermined`, `Monadic/Pair`).  This is what nfalean gets for
free from `PMF.toOuterMeasure`, whose Carathéodory σ-algebra is `⊤`. -/

/-- **The pair law at an arbitrary set** is the run law at its preimage. -/
theorem ttcPairLaw_apply (cVol cSample : ℕ) (S : Set (ℝ × ℕ)) :
    ttcPairLaw atoms φ ε δ cVol cSample S
      = ttcLaw atoms φ ε δ
          (ttcPair atoms φ ε δ cVol cSample ⁻¹' S) :=
  map_apply_of_countablyDetermined
    (countablyDetermined_ttcPair atoms φ ε δ cVol cSample) _ S

/-- **`Pr` transfers across the read-off, for every event.**  The `Measure`-level
counterpart of nfalean's `PMF.PrR_map`, and like it it needs no hypotheses. -/
theorem PrR_ttcPairLaw (cVol cSample : ℕ) (E : ℝ × ℕ → Prop) :
    Pr[r ← ttcPairLaw atoms φ ε δ cVol cSample; E r]
      = Pr[p ← ttcLaw atoms φ ε δ;
          E (ttcPair atoms φ ε δ cVol cSample p)] :=
  congrArg ENNReal.toReal
    (ttcPairLaw_apply atoms φ ε δ cVol cSample {r | E r})

/-- **The accuracy transfer.**  An event about the pair's *estimate* component is the
same event about `Model/Pseudocode`'s `Ttc.ttcRun` on the underlying run — so nothing is
lost by stating the accuracy conjunct over `Ttc.ttcPairLaw`. -/
theorem PrR_ttcPairLaw_fst (cVol cSample : ℕ) (S : Set ℝ) :
    Pr[r ← ttcPairLaw atoms φ ε δ cVol cSample; r.1 ∈ S]
      = Pr[p ← ttcLaw atoms φ ε δ;
          ttcRun atoms φ ε δ p.1 p.2 ∈ S] :=
  PrR_ttcPairLaw atoms φ ε δ cVol cSample fun r => r.1 ∈ S

include hε0 hε1 hn hφ hpos in
/-- **The headline's accuracy conjunct over the paired law.**  `Ttc.ttc_volume_estimate`'s
first half, verbatim, with the run law replaced by the law of `(estimate, cost)`: the
estimate component lands in `(1 ± ε)·Vol(F)` with probability at least `1 − δ`.  Nothing
is weakened — `Ttc.PrR_ttcPairLaw_fst` is an equality. -/
theorem ttc_accuracy_pairLaw (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ) :
    1 - δ ≤ Pr[r ← ttcPairLaw atoms φ ε δ cVol cSample;
      r.1 ∈ relErr ε (volSol (atomSet atoms) φ)] := by
  rw [PrR_ttcPairLaw_fst]
  exact ttc_accuracy_single_measure atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1

/-! ### The runtime half, and what it costs to move it

`Ttc.ttcTerminates` is a property of the *run*, not of the pair, so the faithful
statement over the pair law is about the image of the terminating set.  Under a global
termination hypothesis that image becomes all of `Set.range (Ttc.ttcPair …)` — "every
outcome the program can produce", which is what nfalean's `All[r ← …]` means for a
`PMF`.  The a.e. form is derived from it, and is strictly weaker. -/

include hε0 hε1 hn hφ hpos in
/-- **The runtime conjunct over the paired law**, faithfully: every pair produced by a
*terminating* run has cost at most `m · (C_vol + C_sample · (Thresh + 1))`.

The bound is `Ttc.ttcCost_le_thresh_add_one` (`Exec/Api`) — the real-arithmetic form,
with no integrality side condition relating a natural `thr` to the real `Ttc.ttcThresh`.
The `Ttc.ttcTerminates` guard survives as the set the image is taken over; it cannot
survive as a condition on `r`, because termination is a property of the *run* and is not
a function of the pair `(estimate, cost)`. -/
theorem ttcPairLaw_cost_le (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ) :
    ∀ r ∈ ttcPair atoms φ ε δ cVol cSample ''
        {p | ttcTerminates atoms φ ε δ p.1 p.2},
      (r.2 : ℝ) ≤ (ttcNumCubes atoms φ : ℝ)
        * ((cVol : ℝ) + (cSample : ℝ)
            * (ttcThresh atoms φ ε δ + 1)) := by
  rintro r ⟨p, hp, rfl⟩
  exact ttcCost_le_thresh_add_one atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 p.1 p.2
    cVol cSample hp

include hε0 hε1 hn hφ hpos in
/-- **Every outcome the program can produce meets the bound**, under global termination.

This is the headline-facing form of the runtime half over the paired law, and **at this
right-hand side** it is strictly stronger than both measure-theoretic quantifiers:

* stronger than `All[…]` (`∀ᵐ`), which permits a null exceptional set —
  `Ttc.all_ttcPairLaw_cost_le_of_terminates` derives that form from this one;
* stronger than any support-based quantifier, because
  `Ttc.all_ttcPairLaw_iff_atoms` shows that for `Ttc.ttcPairLaw` the `PMF`-support notion
  ("`E` holds at every outcome of positive mass") is *equivalent* to `∀ᵐ`, hence also
  permits a null exceptional set.

`Set.range (Ttc.ttcPair …)` is literally "every outcome the program can produce": the
image of the *whole* run space, with no exceptional set, null or otherwise.  This is what
nfalean's `All[r ← countNFAM …; …]` means for a `PMF`, and it is why
`Model/Theorem.lean`'s runtime conjunct stays pointwise over runs.

It is **not** comparable with `Ttc.all_ttcPairLaw_cost_le`, which drops `hterm` entirely
but at the looser right-hand side `Ttc.ttcComplexity`. -/
theorem ttcPairLaw_cost_le_of_terminates (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ)
    (hterm : ∀ p : (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ),
      ttcTerminates atoms φ ε δ p.1 p.2) :
    ∀ r ∈ Set.range (ttcPair atoms φ ε δ cVol cSample),
      (r.2 : ℝ) ≤ (ttcNumCubes atoms φ : ℝ)
        * ((cVol : ℝ) + (cSample : ℝ)
            * (ttcThresh atoms φ ε δ + 1)) := by
  rintro r ⟨p, rfl⟩
  exact ttcCost_le_thresh_add_one atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 p.1 p.2
    cVol cSample (hterm p)

include hε0 hε1 hn hφ hpos in
/-- **The a.e. form of the `max`-carrying bound, under global termination.**

`Ttc.ttcPairLaw_cost_le_of_terminates` is the theorem; this is all that survives of it if
one insists on writing the runtime conjunct with `Monadic/MeasurePr`'s `All[…]`.  It is a
corollary, never a replacement.

It is kept beside the *unconditional* `Ttc.all_ttcPairLaw_cost_le` below because the two
bounds are different: this one is `m·(C_vol + C_sample·(Thresh + 1))` with `Ttc.ttcThresh`
still a `max` of its two branches — tighter by up to a factor of two on the threshold term
than `Ttc.ttcComplexity`, which replaces that `max` by the sum
(`Ttc.ttcThresh_le_sum`, `Exec/Complexity`).  Neither statement implies the other: this one
has the sharper right-hand side, that one has no `hterm`. -/
theorem all_ttcPairLaw_cost_le_of_terminates (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ)
    (hterm : ∀ p : (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ),
      ttcTerminates atoms φ ε δ p.1 p.2) :
    All[r ← ttcPairLaw atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤ (ttcNumCubes atoms φ : ℝ)
        * ((cVol : ℝ) + (cSample : ℝ)
            * (ttcThresh atoms φ ε δ + 1))] := by
  refine MeasureTheory.ae_iff.2 ?_
  have hempty : ttcPair atoms φ ε δ cVol cSample ⁻¹'
      {r : ℝ × ℕ | ¬ ((r.2 : ℝ) ≤ (ttcNumCubes atoms φ : ℝ)
        * ((cVol : ℝ) + (cSample : ℝ)
            * (ttcThresh atoms φ ε δ + 1)))} = ∅ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact ttcPairLaw_cost_le_of_terminates atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
      cVol cSample hterm _ ⟨p, rfl⟩
  rw [ttcPairLaw_apply, hempty, measure_empty]

include hε0 hε1 hn hφ hpos in
/-- **The running-time bound over the pair law, with no termination guard at all.**

```
All[r ← ttcPairLaw atoms φ ε δ cVol cSample; (r.2 : ℝ) ≤ ttcComplexity atoms φ ε δ cVol cSample]
```

Every hypothesis is about the *inputs* — the FPRAS parameter range `0 < ε ≤ 1`,
`0 < δ ≤ 1`, the dimension `1 ≤ n`, the formula's shape `φ.IsPositive` and its
nondegeneracy `0 < volSol …`.  **Nothing is assumed about the run**: the
`Ttc.ttcTerminates` guard that `Ttc.ttcCost_le_ttcComplexity` (`Exec/Complexity`) carries
— "the intended seam", in that module's words — is discharged here by
`Ttc.ae_ttcLaw_ttcTerminates`, and it is discharged honestly, as a *null set of runs*
rather than as an empty one.

Two facts make the transfer free of measurability side conditions:

* `Ttc.ttcPairLaw_apply` (`Monadic/Pair`'s `Ttc.map_apply_of_countablyDetermined`)
  evaluates the pushforward at the — possibly non-measurable — violating set, with no
  hypothesis;
* `MeasureTheory.measure_mono_null` compares that set with the non-terminating runs as
  *outer* measures, so the termination event never has to be measurable.

The shape of the proof is the one the guarded version had — "the bad preimage is empty" —
with `= ∅` replaced by `⊆ (a null set)`.  The guarded and `Set.range`-based forms
(`Ttc.ttcPairLaw_cost_le`, `Ttc.ttcPairLaw_cost_le_of_terminates`,
`Ttc.all_ttcPairLaw_cost_le_of_terminates`) are kept: they carry the sharper
`Ttc.ttcThresh` right-hand side and admit no exceptional outcome at all, so neither they
nor this statement subsumes the other. -/
theorem all_ttcPairLaw_cost_le (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ) :
    All[r ← ttcPairLaw atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤ ttcComplexity atoms φ ε δ cVol cSample] := by
  refine MeasureTheory.ae_iff.2 ?_
  rw [ttcPairLaw_apply]
  refine measure_mono_null ?_
    (MeasureTheory.ae_iff.1
      (ae_ttcLaw_ttcTerminates atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1))
  intro p hp hterm
  exact hp (ttcCost_le_ttcComplexity atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
    p.1 p.2 cVol cSample hterm)

/-- **What the a.e. form is worth here: exactly the `PMF`-support notion — no more.**

`Ttc.ttcPairLaw` is the pushforward of a **countably determined** read-off
(`Ttc.countablyDetermined_ttcPair` — the named hypothesis of
`Ttc.ae_map_iff_atoms_of_countablyDetermined`, and the reason the collapse below holds).
So the law lives on the countable set `Set.range (Ttc.ttcPair …)`, and for such a law
"`E` holds at every outcome of positive mass" — the literal transcription of nfalean's
`PMF.support p ⊆ {x | E x}` — is *equivalent* to `∀ᵐ`, not stronger than it.

**This is the opposite of the discrete intuition**, and the difference is structural, not
incidental: a `PMF`'s support carries full mass by construction, so for nfalean the two
readings agree; here they agree for the same reason, because a countable carrier leaves no
room for a "large but null" exceptional set inside the range.  Consequently, dressing the
runtime conjunct in a support-based quantifier buys nothing over `All[…]`, and both are
strictly weaker than `Ttc.ttcPairLaw_cost_le_of_terminates`.  (`Monadic/MeasurePr`'s
`AllS[…]` is a *third*, topological, notion; its own separating examples show the three
are distinct in general — the collapse proved here is a fact about this law.) -/
theorem all_ttcPairLaw_iff_atoms (cVol cSample : ℕ) (E : ℝ × ℕ → Prop) :
    (All[r ← ttcPairLaw atoms φ ε δ cVol cSample; E r])
      ↔ ∀ r : ℝ × ℕ,
          ttcPairLaw atoms φ ε δ cVol cSample {r} ≠ 0 → E r :=
  ae_map_iff_atoms_of_countablyDetermined
    (countablyDetermined_ttcPair atoms φ ε δ cVol cSample) _ E

end Law

#print axioms ttcLaw
#print axioms ttcLaw_def
#print axioms instIsProbabilityMeasureTtcLaw
#print axioms ttcPair
#print axioms ttcPair_def
#print axioms countablyDetermined_ttcPair
#print axioms measurable_ttcPair
#print axioms ttcPairLaw
#print axioms ttcPairLaw_def
#print axioms instIsProbabilityMeasureTtcPairLaw
#print axioms ttcPairLaw_apply
#print axioms PrR_ttcPairLaw
#print axioms PrR_ttcPairLaw_fst
#print axioms ttc_accuracy_pairLaw
#print axioms measurableSet_vanish
#print axioms trajLaw_iInter_compl_vanish
#print axioms ttcTrajKernel_apply
#print axioms ae_ttcLaw_ttcTerminates
#print axioms ttcPairLaw_cost_le
#print axioms ttcPairLaw_cost_le_of_terminates
#print axioms all_ttcPairLaw_cost_le_of_terminates
#print axioms all_ttcPairLaw_cost_le
#print axioms all_ttcPairLaw_iff_atoms

end Ttc

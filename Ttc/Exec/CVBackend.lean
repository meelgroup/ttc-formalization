/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.OracleFree
import Ttc.Volume.CVInstantiate

/-!
# `Exec/CVBackend`: the pipeline entry point, generic in the volume algorithm

`Ttc.ttcProbOfInputs` (`Exec/OracleFree.lean:169`) builds the whole `Ttc.TtcProb`
from the algorithm's inputs, with the volume oracle pinned to
`Ttc.VolumeAlgorithm.monteCarlo` — hit-and-miss Monte Carlo, sample count
**exponential in `n`**. This file adds, *beside* it, the same constructor with the
volume oracle left as a parameter, and then instantiates that parameter at
Cousins–Vempala.

## This file is ADDITIVE. Nothing on the Monte-Carlo path is changed.

`Ttc.mcVol`, `Ttc.mcGood`, `Ttc.ttcProbOfInputs`, `Ttc.ttc_volume_monteCarlo` and
`Ttc.Box.bxTtcProb` are untouched — no file other than this one is edited. The
generic definitions here **specialise to them definitionally**:

* `Ttc.volOfAlg_monteCarlo : volOfAlg (monteCarlo n) … = mcVol …` — `rfl`
* `Ttc.volGoodOf_monteCarlo : volGoodOf (monteCarlo n) … = mcGood …` — `rfl`
* `Ttc.Box.bxTtcProbAlg_eq : bxTtcProbAlg … = bxTtcProb …` — `rfl`

The last one is the load-bearing check: the generic constructor at
`V = monteCarlo n` **is** the existing constructor, field for field. Swapping the
proved oracle for a conditional one *in place* would have hidden a cost the
statement cannot see (`AUDIT.md` check 7); that is why the Monte-Carlo path — the
development's only unconditional instantiation and its non-vacuity witness — stays
exactly where it was.

## What is here

| § | declaration | what it is |
| --- | --- | --- |
| 1 | `Ttc.pos_of_mem_relErr` | a two-sided relative estimate of a positive quantity is positive |
| 2 | `Ttc.volOfAlg`, `Ttc.volGoodOf` | `Ttc.mcVol` / `Ttc.mcGood` at an arbitrary `Ttc.VolumeAlgorithm` |
| 2 | `Ttc.volOfAlg_eq`, `_mem_relErr`, `_pos` | the three volume-oracle arguments `Ttc.canonicalTtcProb` consumes |
| 3 | `Ttc.exists_volGood_coin` | the good event is inhabited, for any `V` |
| 4 | `Ttc.ttcProbOfInputsAlg` | **the headline**: `Ttc.ttcProbOfInputs` with `V` a parameter |
| 4 | `Ttc.ttcProbOfInputsAlg_accuracy` | the pipeline's `1 − δ` conclusion at that `V` |
| 5 | `Ttc.cvVolAlg`, `Ttc.ttc_accuracy_cousinsVempala` | the same at Cousins–Vempala |
| 6 | `Ttc.Box.exists_ttcProbOfInputsAlg_witness`, `Ttc.Box.exists_cvVolAlg_witness` | non-vacuity |

**No binder is added** relative to `Ttc.ttcProbOfInputs`: its `(c, hc)` become
`(V, ω, hω)`, and nothing else changes. Nothing in the sampler, the rates,
`theta_eq` or `gen_mem` reads the volume oracle's identity, so the generalisation is
free.

## Where `vol_pos` comes from (`AUDIT.md` 7)

`Ttc.TtcProb.vol_pos` is **not** a new field of `Ttc.VolumeAlgorithm` and is not
asserted at every coin. It is a consequence of the *good event* `hω` together with
`0 < Vol(region M i)`, which `ball_subset` already supplies — exactly as
`Ttc.mcVol_pos` (`Exec/VolDischarge.lean:153`) derives it from `hc`. See
`Ttc.volOfAlg_pos`.

## THE COST, STATED PLAINLY — this file does NOT establish `O*(n³)`

Cousins–Vempala, *Gaussian Cooling and `O*(n³)` Algorithms for Volume and Gaussian
Volume* (arXiv:1409.6011), Theorem 1.1 is an `O*(n³)` claim. **Nothing in this
repository proves that complexity, and nothing in this file may be quoted as
establishing it.** Specifically:

* `Ttc.VolumeAlgorithm` has **no complexity field**. It asserts accuracy and
  measurability, and says nothing about running time
  (`Ttc/Volume/Oracle.lean:44-49`). So `Ttc.ttcProbOfInputsAlg` charges whatever `V`
  charges, invisibly.
* `Ttc/Volume/CVEstimator.lean`'s own accounting — `median_accuracy_of_samples`,
  `volume_accuracy_of_samples`, and `avgOf_sq_moment_le_budget`'s sample count
  `k ≥ (c−1)·m/κ` — gives `Θ(n·L⁴·log(1/p)/κ³)` samples in total, i.e. **worse than
  the paper's bound**, and bounds nothing about the cost of producing one sample.
* The sampler in this pipeline is still the lazy ball walk run for `Ttc.mixSteps`
  steps, exponential in `n`.
* The CV path is **conditional**. `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`
  discharges twelve of `cousinsVempala`'s fourteen hypotheses from `Arlib`, but
  `hphase_mean` and `hphase_var` remain, and `Ttc/Volume/CVInstantiate.lean:83` says
  of the first: "This is where the development actually stops." Both are kept as
  binders of `Ttc.ttc_accuracy_cousinsVempala`; neither is proved here.

So what `Ttc.ttc_accuracy_cousinsVempala` says is: *if* a score family meeting
Cousins–Vempala's two remaining sampler hypotheses is supplied, *then* the TTC
pipeline runs on the volume oracle it defines and delivers the accuracy guarantee.
It is a **structural** swap of the oracle, not a complexity result.

## What the `1 − δ` is conditional on

As in `Ttc.ttcProbOfInputs`, the bound is stated at one *fixed* good coin `ω`.
`Ttc.exists_volGood_coin` shows that event is inhabited and
`Ttc.measure_volGood_ge_of_length` gives it probability `≥ 1 − δ/4`; integrating the
coin out — as `Ttc.ttc_volume_monteCarlo` does for Monte Carlo — costs a further
`δ/4`, dropping the guarantee to `1 − δ − δ/4`. **That integration is not performed
here.**
-/

namespace Ttc

open MeasureTheory Pointwise

section Generic

variable {A : Type*} {n : ℕ}

/-- **A two-sided relative estimate of a positive quantity is positive.**

`Ttc.relErr ε b` is `Set.Icc ((1-ε)*b) ((1+ε)*b)`, so the lower half already gives
`(1-ε)·b ≤ x`; with `0 < b` and `ε < 1` that is a strictly positive lower bound.

This is the content of `Ttc.mcVol_pos` (`Exec/VolDischarge.lean:153`) with the
Monte-Carlo specifics removed. It is what makes `Ttc.TtcProb.vol_pos` a
*consequence* of the volume oracle's good event rather than an extra field of
`Ttc.VolumeAlgorithm`: positivity is never claimed at every coin. -/
theorem pos_of_mem_relErr {ε b x : ℝ} (h : x ∈ relErr ε b) (hb : 0 < b) (hε : ε < 1) :
    0 < x := by
  have hlo : (1 - ε) * b ≤ x := h.1
  nlinarith

/-! ## 2. `Vol_ED`'s output and its good event, for an arbitrary algorithm

`Ttc.mcVol` (`Model/Pseudocode.lean:574`) and `Ttc.mcGood` (`Exec/VolDischarge.lean:110`)
are the Monte-Carlo instances of the two definitions below — *definitionally*, as
`Ttc.volOfAlg_monteCarlo` and `Ttc.volGoodOf_monteCarlo` record by `rfl`. Nothing
about the Monte-Carlo path is changed, redefined or rewired: those two `rfl`s are
the whole compatibility statement. -/

open scoped Classical in
/-- **`Vol_ED`'s output, as a function of an arbitrary volume algorithm's coins.**

Verbatim `Ttc.mcVol` with `Ttc.MonteCarlo.est` replaced by `V.est` and the coin
space `ℕ → Space n` replaced by `V.Ω`. Off the DNF the value is `0`; the algorithm
never reads it, and totality is what avoids a proof argument. -/
noncomputable def volOfAlg (V : VolumeAlgorithm n) (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) (ω : V.Ω) (i : Cube A) : ℝ :=
  if hi : i ∈ D then
    γ ^ n * V.est (roundBody (cen ⟨i, hi⟩) γ (region M i)) ε' δ' ω
  else 0

/-- **The Monte-Carlo path is the `V = monteCarlo` case, definitionally.** So the
generalisation below is additive: `Ttc.mcVol` is not replaced, it is recovered. -/
theorem volOfAlg_monteCarlo (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) (c : ℕ → Space n) :
    volOfAlg (VolumeAlgorithm.monteCarlo n) M D cen γ ε' δ' c
      = mcVol M D cen γ ε' δ' c := rfl

/-- **`Ttc.canonicalTtcProb`'s `volED_eq`, for `Ttc.volOfAlg`.** The generic
analogue of `Ttc.mcVol_eq` (`Exec/VolDischarge.lean:97`); same proof. -/
theorem volOfAlg_eq (V : VolumeAlgorithm n) (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) (ω : V.Ω)
    (i : Cube A) (hi : i ∈ D) :
    volOfAlg V M D cen γ ε' δ' ω i =
      γ ^ n * V.est (roundBody (cen ⟨i, hi⟩) γ (region M i)) ε' δ' ω := by
  classical
  rw [volOfAlg, dif_pos hi]

/-- **The good event of the `m` `Vol_ED` calls, indexed by cube of the DNF.**
`Ttc.volGood` (`Volume/Oracle.lean:102`) reindexed along the loop of `alg:ttc`
line 23 — verbatim `Ttc.mcGood`, at an arbitrary `V`. -/
def volGoodOf (V : VolumeAlgorithm n) (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) : Set V.Ω :=
  volGood V γ ε' δ'
    (fun j : Fin D.length => cen ⟨D.get j, List.get_mem _ _⟩)
    (fun j : Fin D.length => region M (D.get j))

/-- **`Ttc.mcGood` is the `V = monteCarlo` case, definitionally.** -/
theorem volGoodOf_monteCarlo (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) :
    volGoodOf (VolumeAlgorithm.monteCarlo n) M D cen γ ε' δ' = mcGood M D cen γ ε' δ' :=
  rfl

/-- **`Ttc.canonicalTtcProb`'s `volCoins_good`, at a good coin.** The generic
analogue of `Ttc.mcVol_mem_relErr`. -/
theorem volOfAlg_mem_relErr (V : VolumeAlgorithm n) (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) {ω : V.Ω}
    (hω : ω ∈ volGoodOf V M D cen γ ε' δ') :
    ∀ i ∈ D, volOfAlg V M D cen γ ε' δ' ω i ∈ relErr ε' (volume (region M i)).toReal :=
  mem_relErr_of_mem_volGood V M D γ ε' δ' cen (volOfAlg V M D cen γ ε' δ')
    (fun ω i hi => volOfAlg_eq V M D cen γ ε' δ' ω i hi) hω

/-- **`Ttc.canonicalTtcProb`'s `vol_pos`, at a good coin.**

The generic analogue of `Ttc.mcVol_pos` (`Exec/VolDischarge.lean:153`), and it
carries the same hypothesis list: positivity is a consequence of the **good event**
`hω` together with `0 < Vol(region M i)` — which `ball_subset` supplies — and is
*not* asserted at every coin. This is why `Ttc.VolumeAlgorithm` needs no positivity
field. -/
theorem volOfAlg_pos (V : VolumeAlgorithm n) (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) {γ ε' δ' : ℝ} (hγ : 0 < γ) (hε' : ε' < 1)
    (hball : ∀ i : {c : Cube A // c ∈ D}, Metric.ball (cen i) γ ⊆ region M i.val)
    (hfin : ∀ i : {c : Cube A // c ∈ D}, volume (region M i.val) ≠ ⊤)
    {ω : V.Ω} (hω : ω ∈ volGoodOf V M D cen γ ε' δ') :
    ∀ i ∈ D, 0 < volOfAlg V M D cen γ ε' δ' ω i := by
  intro i hi
  have hvol0 : volume (region M i) ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (hball ⟨i, hi⟩)))
    exact Metric.measure_ball_pos volume (cen ⟨i, hi⟩) hγ
  exact pos_of_mem_relErr (volOfAlg_mem_relErr V M D cen γ ε' δ' hω i hi)
    (ENNReal.toReal_pos hvol0 (hfin ⟨i, hi⟩)) hε'

/-! ## 3. The good coins are inhabited, for any volume algorithm

`Ttc.exists_mcGood_coin` (`Exec/OracleFree.lean:120`) shows the Monte-Carlo good
event is nonempty because its probability is at least `1 − δ/4 ≥ 3/4 > 0`. The
argument uses nothing about Monte Carlo: `Ttc.measure_volGood_ge_of_length`
(`Coupling/Product.lean:263`) is already generic in `V`. -/

/-- **A good coin exists, for any `Ttc.VolumeAlgorithm`.**

The hypotheses are exactly the ones `Ttc.measure_volGood_ge_of_length` needs, in
the shape `Ttc.exists_mcGood_coin` states them. This is what makes the `hω` binder
of `Ttc.ttcProbOfInputsAlg` below *not* a hidden oracle: the event it names is an
explicitly constructed event of the algorithm's own coin law, and it is inhabited
from the same inputs.

It certifies inhabitation only — it says nothing about how expensive it is to *find*
a good coin. -/
theorem exists_volGood_coin (V : VolumeAlgorithm n) (atoms : A → LinAtom n)
    (φ : BForm A) {D : DNF A} (hD : IsDNFOf D φ) (P : Params) {δ : ℝ}
    (delta_eq : P.δ = δ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {gammaHat : ℝ} (hgammaHat : 0 < gammaHat)
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ))
    (cen : {c : Cube A // c ∈ D} → Space n)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (hlen : (D.length : ℝ) ≤ P.m) :
    ∃ ω : V.Ω, ω ∈ volGoodOf V (fun a => (atoms a).halfspace) D cen gammaHat
      P.epsPrime P.deltaPrime := by
  classical
  letI := V.mΩ
  have hfin : ∀ i : {c : Cube A // c ∈ D},
      volume (region (fun a => (atoms a).halfspace) i.val) ≠ ⊤ :=
    volume_region_ne_top_of_isBounded hD hbdd
  have hconv : ∀ i : {c : Cube A // c ∈ D},
      Convex ℝ (region (fun a => (atoms a).halfspace) i.val) :=
    fun i => convex_region atoms _
  have hmeas := measure_volGood_ge_of_length V (fun a => (atoms a).halfspace) D P
    delta_eq hδ0 hδ1 hgammaHat cen ball_subset hconv hfin hlen
  rcases Set.eq_empty_or_nonempty
      (volGoodOf V (fun a => (atoms a).halfspace) D cen gammaHat
        P.epsPrime P.deltaPrime) with h | h
  · have h' : volGood V gammaHat P.epsPrime P.deltaPrime
        (fun j : Fin D.length => cen ⟨D.get j, List.get_mem _ _⟩)
        (fun j : Fin D.length => region (fun a => (atoms a).halfspace) (D.get j)) = ∅ := h
    rw [h', measure_empty] at hmeas
    simp only [ENNReal.toReal_zero] at hmeas
    linarith
  · exact h

/-! ## 4. The headline: `Ttc.ttcProbOfInputs`, generic in the volume algorithm -/

/-- **`Ttc.TtcProb`, from the algorithm's inputs and an arbitrary volume algorithm.**

`Ttc.ttcProbOfInputs` (`Exec/OracleFree.lean:169`) verbatim, with the two binders
`(c : ℕ → Space n)` and `(hc : c ∈ mcGood …)` replaced by the **three**
`(V : VolumeAlgorithm n) (ω : V.Ω) (hω : ω ∈ volGoodOf V …)`, and the volume
estimates `Ttc.mcVol … c` replaced by `Ttc.volOfAlg V … ω`. Every other argument
is the same argument, supplied by the same construction.

The five volume-oracle arguments of `Ttc.canonicalTtcProb` (`Exec/Canonical.lean:118`)
go as follows.

| argument | supplied by |
| --- | --- |
| `volAlg` | the binder `V` |
| `volCoins` | the binder `ω` |
| `volED_eq` | `Ttc.volOfAlg_eq` — definitional, `dif_pos` |
| `volCoins_good` | `Ttc.volOfAlg_mem_relErr`, from `hω` |
| `vol_pos` | `Ttc.volOfAlg_pos`, from `hω` and `ball_subset` |

**No new binder is introduced** relative to `Ttc.ttcProbOfInputs`: nothing in the
sampler, the rates, `theta_eq` or `gen_mem` reads the volume oracle's identity —
`Ttc.theta_eq_rates` and `Ttc.gen_mem_of_geometry` both take the estimate function
as a parameter, and `Ttc.e2eSampD`/`Ttc.e2eSampler` never mention it.

**Costs.** `V` is a binder, so this constructor asserts *nothing* about the cost of
the volume oracle — the honest reading is that it charges whatever `V` charges, and
`Ttc.VolumeAlgorithm` has no complexity field to record it. The sampler is still the
lazy ball walk run for `Ttc.mixSteps` steps, exponential in `n`. See the module
docstring: **this file is not quotable as an `O*(n³)` result.** -/
noncomputable def ttcProbOfInputsAlg
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
    -- **the volume algorithm**, and a draw of *its* coins landing in *its* good event
    (V : VolumeAlgorithm n) (ω : V.Ω)
    (hω : ω ∈ volGoodOf V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
      P.epsPrime P.deltaPrime)
    -- the instance is in the paper's regime, at the constructed rates
    (big : (1 - P.epsPrime) * P.thresh / 8
      ≤ ∑ s, rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
          (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
            P.epsPrime rfac Am bv cen gammaHat Dm)
          (volOfAlg V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
            P.epsPrime P.deltaPrime ω) s) :
    TtcProb A n :=
  canonicalTtcProb ε δ hε0 hε1 hδ0 hδ1 atoms φ toDNF isDNF isPositive P
    (by rw [hP]; rfl) (by rw [hP]; rfl) (by rw [hP]; rfl)
    (by rw [hP]; exact ttcParams_cubes_le (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (by rw [hP]; exact ttcParams_facets_le (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (normal_ne_zero_of_coeff_ne_zero hcoeff)
    cen gammaHat hgammaHat ball_subset
    (volume_region_ne_top_of_isBounded isDNF hbdd)
    (P.precision gammaHat) rfl
    (normalisedCount (fun a => (atoms a).halfspace) φ (P.precision gammaHat)) rfl
    (latticeCount (fun a => (atoms a).halfspace) φ (P.precision gammaHat))
    (latticeEnum (fun a => (atoms a).halfspace) φ (P.precision gammaHat))
    (latticeEnum_injective _ _ _)
    (fun s => latticeEnum_mem (hasLatticeEnum_of_isBounded _ _ _ hbdd) s)
    (latticeEnum_onto (hasLatticeEnum_of_isBounded _ _ _ hbdd))
    (rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
      (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
        P.epsPrime rfac Am bv cen gammaHat Dm)
      (volOfAlg V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
        P.epsPrime P.deltaPrime ω))
    (volOfAlg V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
      P.epsPrime P.deltaPrime ω)
    (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
      P.epsPrime rfac Am bv cen gammaHat Dm)
    (e2eSampler hn
      (by
        have h0 : (0 : ℝ) < P.ε := P.hε0
        unfold Params.epsPrime; linarith)
      Jt Am bv hdil rfac hr1 hcard cen gammaHat hgammaHat ball_subset Dm hDbody)
    (fun s => theta_eq_rates isDNF (hasLatticeEnum_of_isBounded _ _ _ hbdd) _ _ s)
    (coverOfRegion (fun a => (atoms a).halfspace))
    (memPtOfRegion (fun a => (atoms a).halfspace)
      (latticeEnum (fun a => (atoms a).halfspace) φ (P.precision gammaHat)))
    (memPtOfRegion_spec _ _ _)
    (fun s i => coverOfRegion_memPtOfRegion _ _ s i)
    (fun t i j N hi => gen_mem_of_geometry atoms isDNF isPositive hbdd hcoeff P
      (by rw [hP]; rfl)
      (by rw [hP]; exact ttcParams_facets_le (toDNF φ) n ε δ hε0 hε1 hn hm hr)
      cen hgammaHat ball_subset rfl _ t i j N hi)
    -- **the volume oracle**: the binder `V` at the binder `ω`
    V ω
    (fun i hi => volOfAlg_eq V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
      P.epsPrime P.deltaPrime ω i hi)
    (volOfAlg_mem_relErr V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
      P.epsPrime P.deltaPrime hω)
    (volOfAlg_pos V (fun a => (atoms a).halfspace) (toDNF φ) cen hgammaHat
      (by
        have h0 : (0 : ℝ) < P.ε := P.hε0
        have h1 : P.ε ≤ 1 := P.hε1
        unfold Params.epsPrime; linarith)
      ball_subset (volume_region_ne_top_of_isBounded isDNF hbdd) hω)
    big

/-! ### The oracle fields read back as what was supplied

The three volume-oracle fields of the constructed bundle carry no information
beyond the binders `V`, `ω` and the construction `Ttc.volOfAlg`. All are `rfl`. -/

section ReadBack

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
  (V : VolumeAlgorithm n) (ω : V.Ω)
  (hω : ω ∈ volGoodOf V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
    P.epsPrime P.deltaPrime)
  (big : (1 - P.epsPrime) * P.thresh / 8
    ≤ ∑ s, rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
        (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
          P.epsPrime rfac Am bv cen gammaHat Dm)
        (volOfAlg V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
          P.epsPrime P.deltaPrime ω) s)

/-- Abbreviation for the constructed bundle, used by the read-back lemmas below. -/
private noncomputable abbrev TofAlg : TtcProb A n :=
  ttcProbOfInputsAlg atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP
    hbdd hcoeff cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
    V ω hω big

/-- **The volume algorithm is the supplied `V`** — not `Ttc.VolumeAlgorithm.monteCarlo`,
and not anything the constructor picked. -/
theorem ttcProbOfInputsAlg_volAlg :
    (TofAlg atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      V ω hω big).volAlg = V := rfl

/-- **The volume oracle's coins are the supplied draw.** -/
theorem ttcProbOfInputsAlg_volCoins :
    (TofAlg atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      V ω hω big).volCoins = ω := rfl

/-- **The volume estimates are `Ttc.volOfAlg`** — `V`'s own output at those coins,
not a free function. -/
theorem ttcProbOfInputsAlg_vol :
    (TofAlg atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      V ω hω big).vol
      = volOfAlg V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
          P.epsPrime P.deltaPrime ω := rfl

/-- **The rates are `Ttc.rates`** at the constructed sampler and `V`'s estimates — so
`big` cannot be met by collapsing `θ` (`Ttc.rates_pos`). -/
theorem ttcProbOfInputsAlg_theta :
    (TofAlg atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
      cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
      V ω hω big).θ
      = rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
          (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
            P.epsPrime rfac Am bv cen gammaHat Dm)
          (volOfAlg V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
            P.epsPrime P.deltaPrime ω) := rfl

include hε0 hε1 hδ0 hδ1 hn isDNF isPositive hm hr hP hbdd hcoeff hgammaHat ball_subset
  hdil hr1 hcard hDbody hω big in
/-- **THE PIPELINE'S CONCLUSION, with the volume oracle supplied by an arbitrary
`Ttc.VolumeAlgorithm`.**

`Ttc.TtcProb.volume_estimate_traj` at `Ttc.ttcProbOfInputsAlg`, written out over the
constructed data: on the trajectory space of the constructed rates, the algorithm's
output lands in `(1 ± ε)·Vol(F)` with probability at least `1 − δ`.

**What the `1 − δ` is conditional on.** The bound is stated *at the fixed good coin
`ω`*, exactly as `Ttc.ttcProbOfInputs`' is stated at the fixed good coin `c`. The
probability that a draw of `V`'s coins is good is at least `1 − δ/4`
(`Ttc.measure_volGood_ge_of_length`), and `Ttc.exists_volGood_coin` shows the event
is inhabited; integrating that failure out — as `Ttc.ttc_volume_monteCarlo` does for
Monte Carlo — drops the guarantee to `1 − δ − δ/4`. That integration is **not**
performed here; this statement fixes the coin. -/
theorem ttcProbOfInputsAlg_accuracy :
    1 - δ ≤ (trajLaw
      (rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
        (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
          P.epsPrime rfac Am bv cen gammaHat Dm)
        (volOfAlg V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
          P.epsPrime P.deltaPrime ω))
      {t : ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ
          (P.precision gammaHat)) → ℕ |
        ttcOutput P (coveredOracles (fun a => (atoms a).halfspace) φ (P.precision gammaHat)
              (volOfAlg V (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
                P.epsPrime P.deltaPrime ω))
            toDNF (P.precision gammaHat) φ t
          ∈ relErr ε (volSol (fun a => (atoms a).halfspace) φ)}).toReal :=
  (TofAlg atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr P hP hbdd hcoeff
    cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard Dm hDbody
    V ω hω big).volume_estimate_traj

end ReadBack

/-! ## 5. The Cousins–Vempala instantiation

`Ttc.VolumeAlgorithm.cousinsVempalaOfRuns` (`Volume/CVInstantiate.lean:265`) is the
§5.2 assembly with **twelve of `cousinsVempala`'s fourteen hypotheses discharged**
from `Arlib`; the two that remain, `hphase_mean` and `hphase_var`, are the sampler
debt, and `CVInstantiate.lean:83` records that this "is where the development
actually stops". Those two are kept as **binders** below — no attempt is made to
prove Cousins–Vempala Theorem 1.1.

**Why `cousinsVempalaOfRuns` and not `cousinsVempalaOfBiasedEnd`.**
`Ttc/Volume/CousinsVempala.lean:1947` says of the biased-end variant: "This
construction is retained for schedules that do end on a genuine Gaussian; it is
**not on the path to the volume oracle**." The schedule actually used ends on the
literal constant `1`, so `hchain_end` is exact and `cousinsVempalaOfSchedule` /
`cousinsVempalaOfRuns` are the live path. Using `OfBiasedEnd` would have re-opened
six hypotheses that `Arlib` already closes. -/

section CV

variable (E : Type) [MeasurableSpace E] (ν : ℕ → ℕ → MeasureTheory.Measure E)
  [∀ j i, MeasureTheory.IsProbabilityMeasure (ν j i)]
  (phases : Set (Space n) → ℝ → ℝ → ℕ)
  (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
  (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ) (B : ℝ)
  (hσ : ∀ K ε p j, 0 < σsq K ε p j)
  (hg : ∀ K ε p j i, Measurable (g K ε p j i))
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

/-- **The Cousins–Vempala volume algorithm, as a `Ttc.VolumeAlgorithm`.**

A pure abbreviation (`abbrev`, hence reducible) for
`Ttc.VolumeAlgorithm.cousinsVempalaOfRuns` at the caller's data. It introduces no
new definitional content and asserts nothing: every hypothesis of the underlying
constructor is a binder of this abbreviation, visible in its type. -/
noncomputable abbrev cvVolAlg : VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfRuns n E ν phases σsq g B hσ hg hgb
    hphase_mean hphase_var

/-- **The CV oracle has a good coin**, from the same inputs the pipeline already
carries. `Ttc.exists_volGood_coin` at `Ttc.cvVolAlg`, so the `hω` binder of the
theorem below is not a hidden oracle. It certifies inhabitation, not efficient
searchability. -/
theorem exists_volGood_coin_cv (atoms : A → LinAtom n) (φ : BForm A) {D : DNF A}
    (hD : IsDNFOf D φ) (P : Params) {δ : ℝ} (delta_eq : P.δ = δ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {gammaHat : ℝ} (hgammaHat : 0 < gammaHat)
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ))
    (cen : {c : Cube A // c ∈ D} → Space n)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (hlen : (D.length : ℝ) ≤ P.m) :
    ∃ ω : (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var).Ω,
      ω ∈ volGoodOf (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var)
        (fun a => (atoms a).halfspace) D cen gammaHat P.epsPrime P.deltaPrime :=
  exists_volGood_coin _ atoms φ hD P delta_eq hδ0 hδ1 hgammaHat hbdd cen ball_subset hlen

/-- **THE TTC PIPELINE'S CONCLUSION, WITH THE VOLUME ORACLE SUPPLIED BY
COUSINS–VEMPALA.**

`Ttc.ttcProbOfInputsAlg_accuracy` at `V := Ttc.cvVolAlg`. The volume estimates in
the conclusion are `Ttc.volOfAlg (cvVolAlg …) …`, i.e. `γ̂ⁿ` times the median-of-runs
telescoping estimator of Cousins–Vempala §5.2 on the normalised body — **not**
`Ttc.mcVol`. The hit-and-miss Monte-Carlo path (`Ttc.ttcProbOfInputs`,
`Ttc.ttc_volume_monteCarlo`) is untouched and remains the development's only
unconditional instantiation.

**What is proved and what is assumed.** Everything specific to the volume oracle
here is a *binder*: `hphase_mean` and `hphase_var` are Cousins–Vempala's two
remaining sampler hypotheses, kept exactly as `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`
states them. This theorem therefore says: *if* someone supplies a score family whose
per-phase mean is the chain ratio and whose per-phase relative second moment fits the
budget, then the pipeline runs on it and delivers `1 − δ`. It does **not** say such a
family exists.

**Cost.** Nothing here is a complexity statement, and this file must **not** be
quoted as establishing the paper's `O*(n³)`. `Ttc.VolumeAlgorithm` has no complexity
field; `Ttc/Volume/CVEstimator.lean`'s own accounting gives `Θ(n·L⁴·log(1/p)/κ³)`
samples — *worse* than the paper's bound — and bounds nothing about the cost of
producing one sample. The sampler in this pipeline is still the lazy ball walk run
for `Ttc.mixSteps` steps, exponential in `n`.

**The `1 − δ` is at the fixed good coin `ω`**, as in `Ttc.ttcProbOfInputs`; the
probability that a draw is good is `≥ 1 − δ/4` (`Ttc.measure_volGood_ge_of_length`),
and integrating it out costs a further `δ/4`. That integration is not performed
here. -/
theorem ttc_accuracy_cousinsVempala
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
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
    -- a draw of the **CV** oracle's coins, landing in **its** good event
    (ω : (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var).Ω)
    (hω : ω ∈ volGoodOf (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var)
      (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime)
    (big : (1 - P.epsPrime) * P.thresh / 8
      ≤ ∑ s, rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
          (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
            P.epsPrime rfac Am bv cen gammaHat Dm)
          (volOfAlg (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var)
            (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
            P.epsPrime P.deltaPrime ω) s) :
    1 - δ ≤ (trajLaw
      (rates (fun a => (atoms a).halfspace) φ (toDNF φ) (P.precision gammaHat)
        (e2eSampD (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat)
          P.epsPrime rfac Am bv cen gammaHat Dm)
        (volOfAlg (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var)
          (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
          P.epsPrime P.deltaPrime ω))
      {t : ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ
          (P.precision gammaHat)) → ℕ |
        ttcOutput P (coveredOracles (fun a => (atoms a).halfspace) φ (P.precision gammaHat)
              (volOfAlg (cvVolAlg E ν phases σsq g B hσ hg hgb hphase_mean hphase_var)
                (fun a => (atoms a).halfspace) (toDNF φ) cen gammaHat
                P.epsPrime P.deltaPrime ω))
            toDNF (P.precision gammaHat) φ t
          ∈ relErr ε (volSol (fun a => (atoms a).halfspace) φ)}).toReal :=
  ttcProbOfInputsAlg_accuracy atoms φ ε δ hε0 hε1 hδ0 hδ1 hn toDNF isDNF isPositive hm hr
    P hP hbdd hcoeff cen gammaHat hgammaHat ball_subset Jt Am bv hdil rfac hr1 hcard
    Dm hDbody _ ω hω big

end CV

end Generic

/-! ## 6. Non-vacuity (`CLAUDE.md` §11, `AUDIT.md` 4)

Two hypothesis bundles are introduced by this file, and each gets a witness.

**(a) `Ttc.ttcProbOfInputsAlg`'s bundle** — witnessed at the box `[0,c]ⁿ` with
`V = Ttc.VolumeAlgorithm.monteCarlo n`, an **unconditional** `Ttc.VolumeAlgorithm`.
This is the strongest available witness: every binder is discharged by a term with
no hypotheses of its own, and `Ttc.Box.bxTtcProbAlg_eq` shows the resulting bundle
is **definitionally the same `Ttc.TtcProb`** that `Ttc.ttcProbOfInputs` already
built — so the generalisation provably did not break the existing path.

*What it does not certify:* it says nothing whatever about Cousins–Vempala. It
witnesses the generic constructor, at the exponential-cost oracle.

**(b) `Ttc.cvVolAlg`'s bundle** — witnessed by
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsWitness`'s data (`CVInstantiate.lean:342`),
which is **degenerate on purpose**: zero phases, so `Fin (phases K ε p)` is empty
and `hphase_mean`/`hphase_var` hold by `Fin.elim0`. It witnesses *satisfiability of
the hypothesis bundle* and nothing more — in particular it is not evidence that the
sampler debt is dischargeable.

**What is NOT provided, honestly.** A *joint* witness for (b) — the box geometry
*and* the CV oracle *and* `big` simultaneously — is not constructed. The obstacle is
`big`: the box's regime condition is proved only against `Ttc.mcVol`
(`Ttc.Box.big_ballWalk_box`, `Ttc/Exec/EndToEnd.lean:750`, via
`Ttc.Box.sum_bxRates_ge` at line 675, whose statement names `Ttc.Box.volMC`), and
transferring it to the degenerate CV oracle would need the *value* of that oracle's
`est` — i.e. `Arlib.Probability.medianSel` of a constant family, for which
`Arlib/Probability/RunPlumbing.lean` provides `medianSel_isMedian` but no
value-computing lemma. So `Ttc.ttc_accuracy_cousinsVempala` is certified
non-vacuous only in the weaker, factored sense: bundle (a) is inhabited and bundle
(b) is inhabited, but not by a single exhibited instance. -/

namespace Box

open MeasureTheory Set

/-! ### (a) The Monte-Carlo witness for the generic constructor -/

variable (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)

/-- **The box as a `Ttc.TtcProb`, built by the *generic* constructor** at
`V = Ttc.VolumeAlgorithm.monteCarlo n`. Every argument is the same argument
`Ttc.Box.bxTtcProb` (`Exec/OracleFree.lean:480`) supplies; the coin and its goodness
travel across `Ttc.volGoodOf_monteCarlo`, and `big` across
`Ttc.volOfAlg_monteCarlo`, both `rfl`. -/
noncomputable def bxTtcProbAlg (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : TtcProb (Fin n ⊕ Fin n) n :=
  ttcProbOfInputsAlg (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn) ε δ
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
    (VolumeAlgorithm.monteCarlo n)
    (bxCoin n hn ε δ hε0 hε1 hδ0 hδ1) (bxCoin_good n hn ε δ hε0 hε1 hδ0 hδ1)
    (big_ballWalk_box n hn ε δ hε0 hε1 hδ0 hδ1 _ (bxCoin_good n hn ε δ hε0 hε1 hδ0 hδ1))

/-- **THE GENERALISATION DID NOT BREAK THE EXISTING PATH.**

`Ttc.ttcProbOfInputsAlg` at `V = Ttc.VolumeAlgorithm.monteCarlo n` is
**definitionally** `Ttc.ttcProbOfInputs` — the two bundles agree field by field,
by `rfl`. So `Ttc.mcVol`, `Ttc.mcGood` and everything downstream of
`Ttc.Box.bxTtcProb` are untouched, and this file is additive rather than a
rewiring. -/
theorem bxTtcProbAlg_eq (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    bxTtcProbAlg n hn ε δ hε0 hε1 hδ0 hδ1 = bxTtcProb n hn ε δ hε0 hε1 hδ0 hδ1 := rfl

/-- **The witness's volume algorithm is the unconditional Monte-Carlo one** — a term
with no hypotheses at all, so no binder of the generic constructor is discharged by
assumption. -/
theorem bxTtcProbAlg_volAlg (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (bxTtcProbAlg n hn ε δ hε0 hε1 hδ0 hδ1).volAlg = VolumeAlgorithm.monteCarlo n := rfl

/-- **`Ttc.ttcProbOfInputsAlg`'s hypothesis bundle is inhabited, and the instance
says something.**

The whole binder list is existentially quantified, so the claim is auditable from
the type: there is a volume algorithm, a coin of it, and a `Ttc.TtcProb` built by
the **generic** constructor at that pair, whose accuracy guarantee is a *strictly
positive* probability (`≥ 1/2` at `(ε, δ) = (1/2, 1/2)`) and whose rates are not
collapsed.

The volume algorithm exhibited is `Ttc.VolumeAlgorithm.monteCarlo n`, which assumes
nothing — hence this is a genuine inhabitation, not a conditional one. It is
**not** a witness for the Cousins–Vempala bundle; see the section docstring. -/
theorem exists_ttcProbOfInputsAlg_witness (n : ℕ) (hn : 1 ≤ n) :
    ∃ (V : VolumeAlgorithm n) (T : TtcProb (Fin n ⊕ Fin n) n) (ω : T.volAlg.Ω),
      -- the volume algorithm is the unconditional constructed one
      V = VolumeAlgorithm.monteCarlo n ∧
      -- the bundle really is the generic constructor at `(V, ω)`
      T = bxTtcProbAlg n hn (1/2) (1/2) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) ∧
      T.volAlg = V ∧ T.volCoins = ω ∧ T.ε = 1/2 ∧ T.δ = 1/2 ∧
      -- the rates are not collapsed
      (∀ s, 0 < T.θ s) ∧
      -- and the accuracy guarantee is a STRICTLY POSITIVE probability
      (1/2 : ℝ) ≤ (trajLaw T.θ
        {t | ttcOutput T.P (fun t => trajOracles T.ptE_inj T.vol T.cover T.memPt t)
               T.toDNF T.ρ T.φ t ∈ relErr T.ε (volSol T.M T.φ)}).toReal ∧
      0 < (trajLaw T.θ
        {t | ttcOutput T.P (fun t => trajOracles T.ptE_inj T.vol T.cover T.memPt t)
               T.toDNF T.ρ T.φ t ∈ relErr T.ε (volSol T.M T.φ)}).toReal := by
  have h1 := bxTtcProb_accuracy n hn (1/2) (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [← bxTtcProbAlg_eq n hn (1/2) (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)] at h1
  exact ⟨VolumeAlgorithm.monteCarlo n,
    bxTtcProbAlg n hn (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    bxCoin n hn (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    rfl, rfl, rfl, rfl, rfl, rfl,
    fun s => bxTtcProb_theta_pos n hn (1/2) (1/2) _ _ _ _ s,
    by linarith, by linarith⟩

/-! ### (b) The Cousins–Vempala bundle is inhabited -/

/-- **`Ttc.cvVolAlg`'s hypothesis bundle is inhabited.**

Every argument of `Ttc.cvVolAlg` — the coordinate space, the coordinate laws, the
schedule, the score family and its bound, and the two remaining Cousins–Vempala
hypotheses `hphase_mean`/`hphase_var` — is supplied simultaneously, so the bundle
does not contradict itself and `Ttc.ttc_accuracy_cousinsVempala` is not vacuous for
lack of a `V`.

**This witness is degenerate on purpose** and is *not* evidence that the sampler
debt is dischargeable: `phases = 0` makes `Fin (phases K ε p)` empty, so both
remaining hypotheses hold by `Fin.elim0`. It is the same data
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsWitness` (`CVInstantiate.lean:342`) uses,
and it carries the same caveat. -/
theorem exists_cvVolAlg_witness (n : ℕ) :
    ∃ V : VolumeAlgorithm n,
      V = cvVolAlg (n := n) Unit (fun _ _ => Measure.dirac ())
            (fun _ _ _ => 0) (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ => 1) 1
            (fun _ _ _ _ => one_pos) (fun _ _ _ _ _ => measurable_const)
            (fun _ _ _ _ _ _ => le_of_eq abs_one)
            (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
            (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) :=
  ⟨_, rfl⟩

end Box

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.pos_of_mem_relErr
#print axioms Ttc.volOfAlg
#print axioms Ttc.volOfAlg_monteCarlo
#print axioms Ttc.volOfAlg_eq
#print axioms Ttc.volGoodOf
#print axioms Ttc.volGoodOf_monteCarlo
#print axioms Ttc.volOfAlg_mem_relErr
#print axioms Ttc.volOfAlg_pos
#print axioms Ttc.exists_volGood_coin
#print axioms Ttc.ttcProbOfInputsAlg
#print axioms Ttc.ttcProbOfInputsAlg_volAlg
#print axioms Ttc.ttcProbOfInputsAlg_volCoins
#print axioms Ttc.ttcProbOfInputsAlg_vol
#print axioms Ttc.ttcProbOfInputsAlg_theta
#print axioms Ttc.ttcProbOfInputsAlg_accuracy
#print axioms Ttc.cvVolAlg
#print axioms Ttc.exists_volGood_coin_cv
#print axioms Ttc.ttc_accuracy_cousinsVempala
#print axioms Ttc.Box.bxTtcProbAlg
#print axioms Ttc.Box.bxTtcProbAlg_eq
#print axioms Ttc.Box.bxTtcProbAlg_volAlg
#print axioms Ttc.Box.exists_ttcProbOfInputsAlg_witness
#print axioms Ttc.Box.exists_cvVolAlg_witness

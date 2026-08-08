/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Endgoal
import Ttc.Volume.MonteCarlo
import Ttc.Witness.BoxSharp

/-!
# `Exec/VolDischarge`: the volume oracle, removed from the capstone's hypotheses

`Ttc.ttc_volume` (`Model/Endgoal.lean`) carries six binders for `Vol_ED`:

```lean
(vol : Cube A → ℝ) (volAlg : VolumeAlgorithm n) (volCoins : volAlg.Ω)
(volED_eq : ∀ i ∈ toDNF φ, vol i = gammaHat ^ n * volAlg.est (roundBody …) …)
(volCoins_good : ∀ i ∈ toDNF φ, vol i ∈ relErr P.epsPrime (volume (region M i)).toReal)
(vol_pos : ∀ i ∈ toDNF φ, 0 < vol i)
```

`Ttc.ttc_volume_monteCarlo` below has **none** of them.

## How each one goes

| binder | here |
| --- | --- |
| `volAlg` | constructed: `Ttc.VolumeAlgorithm.monteCarlo n` (`Volume/MonteCarlo.lean`), which assumes nothing |
| `vol` | constructed: `Ttc.mcVol`, the oracle's own output at the coins |
| `volED_eq` | the theorem `Ttc.mcVol_eq` |
| `volCoins` | **integrated out** — the conclusion is an integral against `Ttc.MonteCarlo.coins n` |
| `volCoins_good` | **averaged out** — it holds on `Ttc.mcGood`, of probability `≥ 1 − δ/4` (`Ttc.measure_mcGood_ge`) |
| `vol_pos` | the theorem `Ttc.mcVol_pos` |

## The price, stated plainly

`volCoins_good` is *not* true at every coin — only with probability `≥ 1 − δ/4`
(Chebyshev on `Ttc.MonteCarlo.est`, union-bounded over the `m` calls at
`δ' = δ/(4m)`).  So it cannot be supplied; it has to be paid for out of the failure
budget, and the guarantee drops from `1 − δ` to

> **`1 − δ − δ/4`**

exactly as in `Ttc.volume_estimate_joint`, whose shape this file follows.  Nothing
better is claimed: the `δ/4` is `Ttc.Params.vol_failure_eq`, the share the paper's
own budget reserves for the volume oracle, and no attempt is made to fold it back
into `δ`.

Above `δ = 4/5` the bound is not positive and the statement is uninformative.  That
is inherited from `Ttc.volume_estimate_joint`, is not patched, and is why
`Ttc.Box.exists_two_ttc_volume_monteCarlo_instances` exhibits its two witnesses at
`(1/2, 1/2)` and `(1/4, 1/4)`, where the bound reads `3/8` and `11/16`.

## What is *not* removed

* `θ` and `theta_eq`, the sampler's rates, remain binders — and they now take the
  volume oracle's coins as an argument, because `Ttc.mcVol` does.  They cannot be
  constructed here: `theta_eq` names, for each enumerated point, *which* cube of
  the decomposition it was drawn from, and that choice is the sampler's.
* `sampler`, `gen_mem`, `big`, and the geometric input conditions
  `hbdd`/`hcoeff`/`ball_subset` — untouched; this file is only about `Vol_ED`.
* One binder is **added**: `hlen`, that the main loop runs at most `P.m` times.
  `Ttc.Params.deltaPrime` is `δ/(4m)` with `m = P.m`, while the union bound runs
  over `(toDNF φ).length` calls, and `Ttc.ttcParams` sets `P.m` to the number of
  *distinct* cubes.  This is the same hypothesis `Ttc.TtcProb.volGood_prob_budget`
  already carries; it is discharged for the box by `Ttc.Box.hlen_box`.

Net: `Ttc.ttc_volume`'s **36** explicit binders become **31**, and the corollary is
a drop-in replacement — it keeps `thm:runtime` as its second conjunct, quantified
over the volume oracle's coins as well as the trajectory.

## Honest scope

`Ttc.VolumeAlgorithm.monteCarlo` is hit-and-miss Monte Carlo with a sample count
exponential in `n` — **not** Cousins–Vempala Theorem 1.1, and no running-time claim
is made or proved.  What this file removes is the *assumption* that a volume oracle
exists, not the open problem of an efficient one (`CV-ROADMAP.md`).
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Set

variable {A : Type*} {n : ℕ}

/-! ## The constructed volume estimates -/

open scoped Classical in
/-- **`Vol_ED`'s output, as a function of the volume oracle's coins.**

`Ttc.ttc_volume` carries `vol : Cube A → ℝ` together with a binder `volED_eq`
pinning it to `volAlg.est`.  With `volAlg` fixed to the *constructed* oracle
`Ttc.VolumeAlgorithm.monteCarlo`, `vol` is no longer a free function: it is this
term, and `volED_eq` becomes the theorem `Ttc.mcVol_eq`.

Off the DNF the value is `0`; the algorithm never reads it (only `i ∈ D` is ever
queried), and totality is what lets the definition avoid a proof argument. -/
noncomputable def mcVol (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ)
    (c : ℕ → Space n) (i : Cube A) : ℝ :=
  if hi : i ∈ D then
    γ ^ n * MonteCarlo.est (roundBody (cen ⟨i, hi⟩) γ (region M i)) ε' δ' c
  else 0

/-- **`Ttc.ttc_volume`'s `volED_eq`, discharged.**  At every cube of the DNF the
constructed estimate is `γ̂ⁿ` times what `Ttc.VolumeAlgorithm.monteCarlo` returns
on the normalised body — which is exactly what the binder asserted. -/
theorem mcVol_eq (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) (c : ℕ → Space n)
    (i : Cube A) (hi : i ∈ D) :
    mcVol M D cen γ ε' δ' c i =
      γ ^ n * (VolumeAlgorithm.monteCarlo n).est
        (roundBody (cen ⟨i, hi⟩) γ (region M i)) ε' δ' c := by
  classical
  rw [mcVol, dif_pos hi]
  rfl

/-- **The good event of the `m` `Vol_ED` calls, for the constructed oracle.**
`Ttc.volGood` at `Ttc.VolumeAlgorithm.monteCarlo`, on the concrete coin space
`ℕ → Space n`. -/
def mcGood (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) : Set (ℕ → Space n) :=
  volGood (VolumeAlgorithm.monteCarlo n) γ ε' δ'
    (fun j : Fin D.length => cen ⟨D.get j, List.get_mem _ _⟩)
    (fun j : Fin D.length => region M (D.get j))

/-- The good event is measurable — `Ttc.measurableSet_volGood`, at the constructed
oracle, whose σ-algebra on `ℕ → Space n` is the product one. -/
theorem measurableSet_mcGood (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) :
    MeasurableSet (mcGood M D cen γ ε' δ') :=
  measurableSet_volGood (VolumeAlgorithm.monteCarlo n) γ ε' δ' _ _

/-- **The constructed oracle's total failure probability is at most `δ/4`.**

`Ttc.measure_volGood_ge_of_length` — Chebyshev on the `Ttc.MonteCarlo` estimator,
union-bounded over the `m` calls at `δ' = δ/(4m)` — at the constructed oracle. No
hypothesis about `Vol_ED` is assumed anywhere: `Ttc.VolumeAlgorithm.monteCarlo`
has none. -/
theorem measure_mcGood_ge (M : A → Set (Space n)) (D : DNF A) (P : Params) {δ γ : ℝ}
    (delta_eq : P.δ = δ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ : 0 < γ)
    (cen : {c : Cube A // c ∈ D} → Space n)
    (hball : ∀ i : {c : Cube A // c ∈ D}, Metric.ball (cen i) γ ⊆ region M i.val)
    (hconv : ∀ i : {c : Cube A // c ∈ D}, Convex ℝ (region M i.val))
    (hfin : ∀ i : {c : Cube A // c ∈ D}, volume (region M i.val) ≠ ⊤)
    (hlen : (D.length : ℝ) ≤ P.m) :
    1 - δ / 4 ≤
      (MonteCarlo.coins n (mcGood M D cen γ P.epsPrime P.deltaPrime)).toReal :=
  measure_volGood_ge_of_length (VolumeAlgorithm.monteCarlo n) M D P delta_eq hδ0 hδ1 hγ
    cen hball hconv hfin hlen

/-- **`Ttc.ttc_volume`'s `volCoins_good`, at a good coin.** The binder said "these
coins landed well"; here it is what membership in `Ttc.mcGood` *means*. -/
theorem mcVol_mem_relErr (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) {c : ℕ → Space n}
    (hc : c ∈ mcGood M D cen γ ε' δ') :
    ∀ i ∈ D, mcVol M D cen γ ε' δ' c i ∈ relErr ε' (volume (region M i)).toReal :=
  mem_relErr_of_mem_volGood (VolumeAlgorithm.monteCarlo n) M D γ ε' δ' cen
    (mcVol M D cen γ ε' δ') (fun c i hi => mcVol_eq M D cen γ ε' δ' c i hi) hc

/-- **`Ttc.ttc_volume`'s `vol_pos`, at a good coin.** Not an extra assumption: the
two-sided estimate gives `vol ≥ (1−ε')·Vol(P(cᵢ))`, and `P(cᵢ)` has positive volume
because it contains a ball of radius `γ̂ > 0`. -/
theorem mcVol_pos (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) {γ ε' δ' : ℝ} (hγ : 0 < γ) (hε' : ε' < 1)
    (hball : ∀ i : {c : Cube A // c ∈ D}, Metric.ball (cen i) γ ⊆ region M i.val)
    (hfin : ∀ i : {c : Cube A // c ∈ D}, volume (region M i.val) ≠ ⊤)
    {c : ℕ → Space n} (hc : c ∈ mcGood M D cen γ ε' δ') :
    ∀ i ∈ D, 0 < mcVol M D cen γ ε' δ' c i := by
  intro i hi
  have hvol0 : volume (region M i) ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (hball ⟨i, hi⟩)))
    exact Metric.measure_ball_pos volume (cen ⟨i, hi⟩) hγ
  have hpos : 0 < (volume (region M i)).toReal :=
    ENNReal.toReal_pos hvol0 (hfin ⟨i, hi⟩)
  have hlo := (mcVol_mem_relErr M D cen γ ε' δ' hc i hi).1
  nlinarith

/-! ## The capstone, with the volume oracle discharged -/

/-- **`thm:volumettc` over the joint randomness of the run and the *constructed*
volume oracle.**

`Ttc.ttc_volume` carries four binders for `Vol_ED` — `volAlg`, `volCoins`,
`volED_eq`, `volCoins_good` — plus `vol` and `vol_pos`.  All six are gone here:

* `volAlg` is **constructed**, `Ttc.VolumeAlgorithm.monteCarlo n`
  (`Ttc/Volume/MonteCarlo.lean`), which has no hypotheses;
* `vol` is **constructed**, `Ttc.mcVol` — the oracle's own output at the coins;
* `volED_eq` is the theorem `Ttc.mcVol_eq`;
* `volCoins` is **integrated out**: the conclusion is the iterated integral over
  `Ttc.MonteCarlo.coins n`, the oracle's coin law, so no particular draw is fixed;
* `volCoins_good` is **averaged out**: it holds on `Ttc.mcGood`, an event of
  probability at least `1 − δ/4` (`Ttc.measure_mcGood_ge`), and the union bound
  `Ttc.toReal_lintegral_ge_of_cond` charges its failure to the budget — which is
  why the guarantee is `1 − δ − δ/4` rather than `1 − δ`;
* `vol_pos` is the theorem `Ttc.mcVol_pos`, from the two-sided estimate and
  `ball_subset`.

Everything else is `Ttc.ttc_volume`'s binder list verbatim, except that `θ` and the
rates now depend on the coins — they must, since `Ttc.mcVol` does — and one new
binder `hlen` appears (see below).

**`hlen`.** `Ttc.Params.deltaPrime` is `δ/(4m)` with `m = P.m`, while the union
bound runs over the `(toDNF φ).length` iterations of `alg:ttc`'s main loop.
`Ttc.ttcParams` sets `P.m` to the number of *distinct* cubes, so the two agree
exactly when the AllSAT call returns no duplicates; `hlen` is that condition, and
it is the same hypothesis `Ttc.TtcProb.volGood_prob_budget` already carries.

**Vacuity.** `hδ1 : δ ≤ 1` is all that is assumed, so above `δ = 4/5` the bound
`1 − δ − δ/4` is not positive and the statement is uninformative — exactly as in
`Ttc.volume_estimate_joint`.  `Ttc.Box.exists_two_ttc_volume_monteCarlo_instances`
exhibits two instances strictly inside the informative range. -/
theorem ttc_volume_monteCarlo
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
    -- the sampling oracle `GenerateSamples` (`alg:ttc` line 43); the rates depend on
    -- the volume oracle's coins, because the volume estimates do
    (θ : (ℕ → Space n) → Fin (latticeCount M φ (P.precision gammaHat)) → ℝ)
    (sampD : Cube A → Space n → ℝ)
    (sampler : KV97Sampler A n M (toDNF φ) (P.precision gammaHat) P.epsPrime sampD)
    (theta_eq : ∀ (c : ℕ → Space n) (s : Fin (latticeCount M φ (P.precision gammaHat))),
      ∃ i, i ∈ toDNF φ ∧ latticeEnum M φ (P.precision gammaHat) s ∈ region M i ∧
        θ c s = sampD i (latticeEnum M φ (P.precision gammaHat) s)
          * mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c i)
    -- `GenerateSamples` returns lattice points of the cube it was asked about
    (gen_mem : ∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ)
        (i : Cube A) (j N : ℕ), i ∈ toDNF φ →
      ∀ s ∈ (coveredOracles M φ (P.precision gammaHat)
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) t).gen i j N
              (P.precision gammaHat),
        s ∈ region M i ∩ fineLattice n (latticeScale (P.precision gammaHat)))
    -- the instance is in the paper's regime, at every coin the oracle got right
    (big : ∀ c ∈ mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime,
      (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ c s) :
    -- (accuracy) over the joint law of the run *and* the volume oracle's coins, the
    -- transcription's output is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ − δ/4`
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (θ c)
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
  refine ⟨?_, fun c t cVol cSample thr hthr hterm =>
    runCost_le P _ cVol cSample (P.precision gammaHat) (toDNF φ) thr hthr hterm⟩
  have heq : P.ε = ε := by rw [hP]; rfl
  have hdq : P.δ = δ := by rw [hP]; rfl
  have hnq : P.n = n := by rw [hP]; rfl
  have hcu : (Nat.card {c : Cube A // c ∈ toDNF φ} : ℝ) ≤ P.m := by
    rw [hP]; exact ttcParams_cubes_le (toDNF φ) n ε δ hε0 hε1 hn hm hr
  have hfa : (Nat.card (FacetIndex (toDNF φ)) : ℝ) ≤ P.r := by
    rw [hP]; exact ttcParams_facets_le (toDNF φ) n ε δ hε0 hε1 hn hm hr
  have hle : HasLatticeEnum M φ (P.precision gammaHat) :=
    hasLatticeEnum_of_isBounded _ _ _ hbdd
  have hfin : ∀ i : {c : Cube A // c ∈ toDNF φ}, volume (region M i.val) ≠ ⊤ :=
    volume_region_ne_top_of_isBounded isDNF hbdd
  have hconv : ∀ i : {c : Cube A // c ∈ toDNF φ}, Convex ℝ (region M i.val) := by
    intro i; rw [M_eq]; exact convex_region atoms _
  have heps1 : P.epsPrime < 1 := by
    have h0 : (0:ℝ) < P.ε := P.hε0
    have h1 : P.ε ≤ 1 := P.hε1
    unfold Params.epsPrime; linarith
  exact volume_estimate_joint ε δ hε0 hε1 hδ0 hδ1 atoms M M_eq φ toDNF isDNF isPositive
    P heq hdq hnq hcu hfa
    (normal_ne_zero_of_coeff_ne_zero hcoeff) cen gammaHat hgammaHat ball_subset hfin
    (P.precision gammaHat) rfl (normalisedCount M φ (P.precision gammaHat)) rfl
    (latticeCount M φ (P.precision gammaHat)) (latticeEnum M φ (P.precision gammaHat))
    (latticeEnum_injective _ _ _) (fun s => latticeEnum_mem hle s) (latticeEnum_onto hle)
    (VolumeAlgorithm.monteCarlo n) θ
    (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime) sampD sampler theta_eq
    (coverOfRegion M) (memPtOfRegion M (latticeEnum M φ (P.precision gammaHat)))
    (memPtOfRegion_spec _ _ _) (fun s i => coverOfRegion_memPtOfRegion _ _ s i)
    gen_mem
    (fun c i hi => mcVol_eq M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c i hi)
    (mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime)
    (measurableSet_mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime)
    (measure_mcGood_ge M (toDNF φ) P hdq hδ0 hδ1 hgammaHat cen ball_subset hconv hfin hlen)
    (fun c _ => mcVol_mem_relErr M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime ‹_›)
    (fun c _ => mcVol_pos M (toDNF φ) cen hgammaHat heps1 ball_subset hfin ‹_›)
    big

/-! ## Non-vacuity: the hypotheses are jointly satisfiable, at two accuracy pairs

`CLAUDE.md` §11.  The witness is `Ttc/Witness/BoxSharp.lean`'s box `[0,c]ⁿ` with
`c = max 1 Thresh(ε, δ)` — the same instance `Ttc.Box.ttc_volume_box_at` uses —
but with the **exact** volume oracle `Ttc.VolumeAlgorithm.exact` replaced by the
constructed Monte-Carlo one, which is the whole point: the estimates are now
genuinely random, and the rates `Ttc.Box.thMC` move with the coins.

The parameters are taken strictly inside `(0,1)`, so the conclusion `1 − δ − δ/4`
is a positive lower bound on a probability rather than the `0 ≤ …` of
`Ttc.Box.ttc_volume_box`. -/

namespace Box

variable (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)

/-- The inscribed-ball centre of the box's single cube. -/
noncomputable def cenMC :
    {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)} → Space n :=
  fun _ => boxCentre n (sideS n hn ε δ hε0 hε1)

/-- **The volume estimates the constructed oracle returns for the box**, at its
coins.  Unlike `Ttc.Box.vlOf`, this is not the true volume: it is
`Ttc.MonteCarlo.est` on the normalised box, rescaled by `γ̂ⁿ`. -/
noncomputable def volMC (c : ℕ → Space n) : Cube (Fin n ⊕ Fin n) → ℝ :=
  mcVol (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
    (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
    (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime c

/-- **The box's level-`0` rates, at the volume oracle's coins.**  The sampler's
mass is uniform and coin-free; the volume estimate is not, which is why the rates
depend on `c` — as they must once the oracle is randomized. -/
noncomputable def thMC (c : ℕ → Space n) :
    Fin (latticeCount (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℝ :=
  fun s => smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1) (boxCube n)
      (latticeEnum (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (boxForm n hn) (rhoS n hn ε δ hε0 hε1) s)
    * volMC n hn ε δ hε0 hε1 c (boxCube n)

theorem mem_toDNF_boxCube : boxCube n ∈ Ttc.toDNF (boxForm n hn) := by
  rw [toDNF_boxForm hn]; exact List.mem_singleton_self _

theorem length_toDNF_boxForm : (Ttc.toDNF (boxForm n hn)).length = 1 := by
  rw [toDNF_boxForm hn]; rfl

/-- **`Ttc.ttc_volume_monteCarlo`'s `hlen`, for the box** — one cube, and `P.m` is
the count of distinct cubes, which is at least one. -/
theorem hlen_box :
    ((Ttc.toDNF (boxForm n hn)).length : ℝ) ≤ ((parS n hn ε δ hε0 hε1).m : ℝ) := by
  rw [length_toDNF_boxForm n hn]
  exact_mod_cast one_le_card_cubes_box n hn

/-- **`Ttc.ttc_volume_monteCarlo`'s `theta_eq`, for the box.** -/
theorem theta_eq_MC (c : ℕ → Space n)
    (s : Fin (latticeCount (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (rhoS n hn ε δ hε0 hε1))) :
    ∃ i, i ∈ Ttc.toDNF (boxForm n hn) ∧
      latticeEnum (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (boxForm n hn) (rhoS n hn ε δ hε0 hε1) s
        ∈ region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) i ∧
      thMC n hn ε δ hε0 hε1 c s =
        smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1) i
            (latticeEnum (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
              (boxForm n hn) (rhoS n hn ε δ hε0 hε1) s)
          * volMC n hn ε δ hε0 hε1 c i := by
  refine ⟨boxCube n, mem_toDNF_boxCube n hn, ?_, rfl⟩
  rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn (mem_toDNF_boxCube n hn)]
  exact latticeEnum_mem_bxOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1) s

/-- **`Ttc.ttc_volume_monteCarlo`'s `gen_mem`, for the box** — `Ttc.Box.gen_mem_bxOf`
with the exact estimates replaced by the constructed ones; the proof never reads
them. -/
theorem gen_mem_MC (c : ℕ → Space n)
    (t : ℕ → Fin (latticeCount (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ)
    (i : Cube (Fin n ⊕ Fin n)) (j N : ℕ) (hi : i ∈ Ttc.toDNF (boxForm n hn)) :
    ∀ s ∈ (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) t).gen i j N
          (rhoS n hn ε δ hε0 hε1),
      s ∈ region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) i
        ∩ fineLattice n (latticeScale (rhoS n hn ε δ hε0 hε1)) := by
  have hmem : ∀ (cu : Cube (Fin n ⊕ Fin n))
      (s : Fin (latticeCount (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (boxForm n hn) (rhoS n hn ε δ hε0 hε1))),
      memPtOfRegion (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (latticeEnum (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) cu s = true →
      latticeEnum (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (boxForm n hn) (rhoS n hn ε δ hε0 hε1) s
        ∈ bxOf n (sideS n hn ε δ hε0 hε1)
            ∩ fineLattice n (latticeScale (rhoS n hn ε δ hε0 hε1)) :=
    fun _ s _ => ⟨latticeEnum_mem_bxOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1) s,
      (latticeEnum_mem (hasLatticeEnum_bxOf n (sideS n hn ε δ hε0 hε1) hn
        (rhoS n hn ε δ hε0 hε1)) s).2⟩
  have hne : ∃ s, memPtOfRegion (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (latticeEnum (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) i s = true :=
    ⟨⟨0, latticeCount_pos_bxOf n (sideS_pos hn hε0 hε1).le hn (rhoS n hn ε δ hε0 hε1)⟩,
      (memPtOfRegion_eq_true _ _ _ _).2
        (by
          rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn hi]
          exact latticeEnum_mem_bxOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1) _)⟩
  intro x hx
  rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn hi]
  exact gen_mem_trajOracles
    (T := fun _ => bxOf n (sideS n hn ε δ hε0 hε1)
      ∩ fineLattice n (latticeScale (rhoS n hn ε δ hε0 hε1)))
    (latticeEnum_injective _ _ _) t hmem hne j N (rhoS n hn ε δ hε0 hε1) x hx

/-- **The rates sum to the estimated volume.**  Every enumerated point carries
`est/N` and there are `N` of them — so the total rate is now a *random* quantity,
the oracle's own estimate. -/
theorem sum_thMC (c : ℕ → Space n) :
    ∑ s, thMC n hn ε δ hε0 hε1 c s = volMC n hn ε δ hε0 hε1 c (boxCube n) := by
  have hN : ((bxOf n (sideS n hn ε δ hε0 hε1)
      ∩ fineLattice n (latticeScale (rhoS n hn ε δ hε0 hε1))).ncard : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (ncard_lat_pos n (sideS_pos hn hε0 hε1).le
      (rhoS n hn ε δ hε0 hε1)).ne'
  simp only [thMC, smpOf,
    region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn (mem_toDNF_boxCube n hn),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    latticeCount_eq_ncard n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1)]
  field_simp

/-- **`Thresh/8` fits inside the box's volume**, with a factor of `7` in hand.  The
strengthening of `Ttc.Box.epsPrime_thresh_le_volumeS` that the randomized oracle
needs: the estimate is only `(1 − ε')·Vol` in the worst case, so the `(1 − ε')` on
the left has to be paid for twice. -/
theorem thresh_div_eight_le_volumeS (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal := by
  have hlat := lattice_lo_bxS (n := n) (δ := δ) hn hε0 hε1
  have hs := sideS_le_LvalS (n := n) (δ := δ) hn hε0 hε1
  have hts := thresh_le_sideS (n := n) (δ := δ) hn hε0 hε1
  have hT := parS_thresh_pos (n := n) hn hε0 hε1 hδ0 hδ1
  rw [parS_eta] at hlat
  nlinarith [hlat, hs, hts, hT, hε0, hε1,
    mul_le_mul_of_nonneg_left (le_trans hts hs) (by linarith : (0:ℝ) ≤ 1 - ε / 8)]

/-- **`Ttc.ttc_volume_monteCarlo`'s `big`, for the box**, at every coin on which the
oracle got the volume right. -/
theorem big_MC (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime) :
    (1 - (parS n hn ε δ hε0 hε1).epsPrime) * (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ ∑ s, thMC n hn ε δ hε0 hε1 c s := by
  rw [sum_thMC n hn ε δ hε0 hε1 c]
  have hlo := (mcVol_mem_relErr (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
    (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
    (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime hc
    (boxCube n) (mem_toDNF_boxCube n hn)).1
  rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn (mem_toDNF_boxCube n hn)] at hlo
  have hthr := thresh_div_eight_le_volumeS n hn ε δ hε0 hε1 hδ0 hδ1
  have heps := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1
  have hV : 0 < (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal :=
    volume_bxOf_pos n (sideS_pos hn hε0 hε1)
  have h1 : (0:ℝ) ≤ 1 - (parS n hn ε δ hε0 hε1).epsPrime := by linarith
  have h2 := mul_le_mul_of_nonneg_left hthr h1
  simp only [volMC]
  nlinarith [hlo, h2]

/-- **`Ttc.ttc_volume_monteCarlo`'s hypotheses are satisfiable, at every
`(ε, δ) ∈ (0,1]²`.**

The box `[0,c]ⁿ` with `c = max 1 Thresh(ε, δ)`, its one-cube DNF, the
Kannan–Vempala sampler of `Ttc.Box.samplerOf` — and, unlike every earlier witness
in the development, the **constructed** Monte-Carlo volume oracle rather than the
exact one `Ttc.VolumeAlgorithm.exact`.  The proof is the 31-argument application;
the conclusion is recorded so a reader can see which instance was checked. -/
theorem ttc_volume_monteCarlo_box_at (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (thMC n hn ε δ hε0 hε1 c)
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
  exact ttc_volume_monteCarlo (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn) ε δ
    hε0 hε1 hδ0 hδ1 hn
    (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) rfl Ttc.toDNF
    (toDNF_isDNFOf _) (toDNF_isPositive (boxForm_isPositive hn))
    (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)
    (parS n hn ε δ hε0 hε1) rfl (hlen_box n hn ε δ hε0 hε1)
    (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (coeff_ne_zero_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1)
    (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (thMC n hn ε δ hε0 hε1) (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
    (samplerOf n hn hcpos (rhoS n hn ε δ hε0 hε1)
      (parS_epsPrime_pos (δ := δ) hn hε0 hε1) (parS_epsPrime_le (δ := δ) hn hε0 hε1))
    (theta_eq_MC n hn ε δ hε0 hε1) (gen_mem_MC n hn ε δ hε0 hε1)
    (big_MC n hn ε δ hε0 hε1 hδ0 hδ1)

/-! ### The pair

One witness cannot tell "the hypotheses are satisfiable" from "the hypotheses force
one accuracy pair".  `Ttc.Box.AtParamsMC` packages the conclusion over the data it
is stated about, with `(ε, δ)` exposed, so two instances can be compared. -/

/-- **`Ttc.ttc_volume_monteCarlo`'s conclusion, with `(ε, δ)` exposed.**

Three of the theorem's own hypotheses travel with it — the parameter block really
is at the stated accuracy, the solution set is bounded, and `γ̂ > 0` — so that a
degenerate instance cannot satisfy it vacuously. -/
def AtParamsMC (n : ℕ) (ε δ : ℝ) : Prop :=
  ∃ (atoms : (Fin n ⊕ Fin n) → LinAtom n) (φ : BForm (Fin n ⊕ Fin n)) (P : Params)
      (gammaHat : ℝ)
      (cen : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF φ} → Space n)
      (θ : (ℕ → Space n) →
        Fin (latticeCount (fun a => (atoms a).halfspace) φ (P.precision gammaHat)) → ℝ),
    0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ P.ε = ε ∧ P.δ = δ ∧ P.n = n ∧ 0 < gammaHat ∧
    Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ) ∧
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (θ c)
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

/-- **The oracle-free capstone is instantiable at every accuracy pair in `(0,1]²`.** -/
theorem atParamsMC_of (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : AtParamsMC n ε δ := by
  obtain ⟨hacc, hrun⟩ := ttc_volume_monteCarlo_box_at n hn ε δ hε0 hε1 hδ0 hδ1
  exact ⟨boxAtoms n (sideS n hn ε δ hε0 hε1), boxForm n hn, parS n hn ε δ hε0 hε1,
    gamS n hn ε δ hε0 hε1, cenMC n hn ε δ hε0 hε1, thMC n hn ε δ hε0 hε1,
    hε0, hε1, hδ0, hδ1, rfl, rfl, rfl, gamS_pos hn hε0 hε1,
    isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn, hacc, hrun⟩

/-- **`ε` and `δ` are not forced, and both instances are informative.**

Two instances at *different* accuracy pairs, both strictly inside `(0,1)`, so both
conclusions are genuine positive lower bounds on a probability — `3/8` at
`(1/2, 1/2)` and `11/16` at `(1/4, 1/4)` — not the `0 ≤ …` that the `δ = 1` corner
of `Ttc.Box.ttc_volume_box` certifies nothing with. -/
theorem exists_two_ttc_volume_monteCarlo_instances (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε₁ δ₁ ε₂ δ₂ : ℝ,
      AtParamsMC n ε₁ δ₁ ∧ AtParamsMC n ε₂ δ₂ ∧
      ε₁ ≠ ε₂ ∧ δ₁ ≠ δ₂ ∧
      (0 < ε₁ ∧ ε₁ < 1) ∧ (0 < δ₁ ∧ δ₁ < 1) ∧
      (0 < ε₂ ∧ ε₂ < 1) ∧ (0 < δ₂ ∧ δ₂ < 1) ∧
      0 < 1 - δ₁ - δ₁ / 4 ∧ 0 < 1 - δ₂ - δ₂ / 4 :=
  ⟨1/2, 1/2, 1/4, 1/4,
    atParamsMC_of n hn (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    atParamsMC_of n hn (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    by norm_num, by norm_num, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

end Box

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms mcVol
#print axioms mcVol_eq
#print axioms mcGood
#print axioms measurableSet_mcGood
#print axioms measure_mcGood_ge
#print axioms mcVol_mem_relErr
#print axioms mcVol_pos
#print axioms ttc_volume_monteCarlo
#print axioms Box.cenMC
#print axioms Box.volMC
#print axioms Box.thMC
#print axioms Box.mem_toDNF_boxCube
#print axioms Box.length_toDNF_boxForm
#print axioms Box.hlen_box
#print axioms Box.theta_eq_MC
#print axioms Box.gen_mem_MC
#print axioms Box.sum_thMC
#print axioms Box.thresh_div_eight_le_volumeS
#print axioms Box.big_MC
#print axioms Box.ttc_volume_monteCarlo_box_at
#print axioms Box.AtParamsMC
#print axioms Box.atParamsMC_of
#print axioms Box.exists_two_ttc_volume_monteCarlo_instances

end Ttc

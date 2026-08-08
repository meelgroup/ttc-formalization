/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CanonPolytope

/-!
# `Exec/Final`: the capstone, with no oracle and no polytope description

`Ttc.ttc_volume_final` is `thm:volumettc` in the shape the end goal asks for: the
inputs are the algorithm's own inputs, no oracle is bound, no linear description of
the input polytopes is bound, and the conclusion is a clean `1 − δ`.

It is the composition of the two preceding steps, and nothing else:

* `Ttc.ttc_volume_endToEnd_canon` (`Exec/CanonPolytope`) — `Ttc.ttc_volume_endToEnd`
  with its ten polytope-description binders discharged by the canonical system read
  off `atoms`.  The key fact there is an **equality**,
  `Ttc.canon_body_eq_smul_region`, not the `⊆` the binder asked for.
* the `δ`-repricing of `Exec/Budget`, applied here directly: instantiating at the
  internal failure parameter `δ₀ = 4δ/5` turns the conclusion `1 − δ₀ − δ₀/4` into
  `1 − δ`.

## Which `δ` is which — read this before quoting the statement

`1 − δ` is in the **user's** `δ`, and `hδ0`/`hδ1` constrain the user's `δ`.  Every
other occurrence is at the **internal** `δ₀ = 4δ/5`, because `hP` ties the parameter
block to `ttcParams … ε (4 * δ / 5) …`.  So `P.δ = 4δ/5`, `P.deltaPrime = δ/(5m)`
rather than `δ/(4m)`, and `P.thresh`, the sample counts and the charged `runCost`
are all the ones at `4δ/5`.

This **reprices** the analysis; it does not improve it.  The algorithm is run at a
tighter internal failure probability and the difference is charged to the run.  What
it buys is that the statement is informative on all of `δ ∈ (0,1)` instead of only
`δ ∈ (0, 4/5)`, where `1 − δ − δ/4` was already non-positive (README finding 13a).
At `δ = 1` the bound is `0` — no longer negative, but still uninformative.

## What is bound, and what is not

**Not bound — no oracle of any kind.**  None of `volAlg`, `volCoins`, `volED_eq`,
`volCoins_good`, `vol`, `vol_pos`, `θ`, `theta_eq`, `gen_mem`, `sampD`, `sampler`
appears.  The volume estimator is `Ttc.VolumeAlgorithm.monteCarlo`, the rates are
`Ttc.rates`, and the sampler is `Ttc.e2eSampler`, a lazy ball walk whose one
quantitative field `law_tv` is a theorem
(`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`).

**Not bound — no polytope description.**  None of `Jt`, `Am`, `bv`, `hdil`, `rfac`,
`hr1`, `hcard`, `Dm`, `hDbody` appears; `Exec/CanonPolytope` builds them from
`atoms`.

**Bound, and all of it legitimate input**: the algorithm's inputs
`atoms φ ε δ M toDNF P cen γ̂`; the parameter range and definitional ties
`hε0 hε1 hδ0 hδ1 hn M_eq hP`; the input conditions
`isDNF isPositive hm hr hbdd hcoeff hgammaHat ball_subset`; the loop-length bound
`hlen`; and the regime condition `big`.

## Costs and scope, stated with the result rather than elsewhere

* **Exponential in the dimension, on both routes.**
  `Ttc.VolumeAlgorithm.monteCarlo` is hit-and-miss Monte Carlo at `Θ(Rⁿ/(ε²p))`
  samples, and the ball walk's certified step count is `2^Θ(n)·log(M·Vol(P′)/ε′)`.
  *Unconditional* and *efficient* are independent claims and only the first is
  established here.  The `runCost` conjunct is `alg:ttc`'s charged cost
  (`m·(C_vol + C_sample·Thresh)`), not a polynomial-time claim; `thm:runtime`
  stays out of scope.
* **The sampler is not proved to differ from uniform.**  `law_tv` is proved, so no
  *accuracy assumption* is made — but that the finite-time iterate is distinct from
  `Arlib.uniformOn` on the inflated body is **not** proved, and would need an
  `L²`/aperiodicity argument absent from the development.
* **`hlen` is a `Nodup` condition in disguise.**  `P.m = Nat.card {c // c ∈ toDNF φ}`
  counts *distinct* cubes and a list's length is always at least its number of
  distinct elements, so `hlen` holds exactly when `toDNF φ` repeats no cube.
* **The non-vacuity witness is a single-cube DNF.**  `Ttc.Box.length_toDNF_boxForm`
  gives `(toDNF (boxForm n hn)).length = 1`, so the witnesses below exercise the
  statement at arity one; `hlen`, the `m`-way union bound and the per-cube error
  composition are not exercised at arity two or more.  The statement is not vacuous,
  but the witness is the easiest case.
-/

namespace Ttc

open MeasureTheory Set Pointwise

variable {A : Type*} {n : ℕ}

/-- **`thm:volumettc`, end to end.**

Takes the algorithm's inputs `(atoms, φ, ε, δ)` and input conditions; binds **no
oracle** and **no linear description of the input polytopes**; concludes
`Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1 − δ` together with `alg:ttc`'s charged cost.

Read the module docstring for which `δ` is the user's and which is the internal
`4δ/5`, for the exponential cost of both constructions, and for the two live scope
caveats (the sampler is not proved distinct from uniform; the non-vacuity witness is
a single-cube DNF). -/
theorem ttc_volume_final
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε (4 * δ / 5) hε0 hε1 hn hm hr)
    (hlen : ((toDNF φ).length : ℝ) ≤ P.m)
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (big : ∀ c ∈ mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime,
      (1 - P.epsPrime) * P.thresh / 8
        ≤ ∑ s, rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime (canonRfac (toDNF φ))
              (Jt := Fin (Nat.card (FacetIndex (toDNF φ)))) (canonAm atoms (toDNF φ))
              (canonBv atoms (toDNF φ) (latticeScale (P.precision gammaHat)))
              cen gammaHat (canonDm M (toDNF φ) (P.precision gammaHat)))
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) s) :
    (1 - δ ≤
      (∫⁻ c, trajLaw (rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime (canonRfac (toDNF φ))
              (Jt := Fin (Nat.card (FacetIndex (toDNF φ)))) (canonAm atoms (toDNF φ))
              (canonBv atoms (toDNF φ) (latticeScale (P.precision gammaHat)))
              cen gammaHat (canonDm M (toDNF φ) (P.precision gammaHat)))
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
  have h0 : (0 : ℝ) < 4 * δ / 5 := by linarith
  have h1 : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  obtain ⟨hacc, hcost⟩ :=
    ttc_volume_endToEnd_canon atoms φ ε (4 * δ / 5) hε0 hε1 h0 h1 hn M M_eq toDNF
      isDNF isPositive hm hr P hP hlen hbdd hcoeff cen gammaHat hgammaHat ball_subset big
  exact ⟨by linarith, hcost⟩

end Ttc

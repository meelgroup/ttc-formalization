/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.RegimeSum
import Ttc.Exec.RegimeCube
import Ttc.Exec.RegimeInputs

/-!
# `Exec/RegimeMain`: the `big` regime condition, as a theorem

`Ttc.ttc_volume_inputs` (`Exec/Inputs`) carries a hypothesis binder

```
big : ∀ c ∈ mcGood …, (1 − ε')·Thresh/8 ≤ ∑ s, rates … (e2eSampD …) (mcVol … c) s
```

— the paper's `Λ ≥ (1 − ε')·Thresh/8` (`sections/analysis.tex:295`).  This file
**discharges that binder**: `Ttc.big_of_volume` proves the inequality, for every
coin sequence `c` in `Ttc.mcGood`, from a single transparent hypothesis about the
*input body*,

```
hvol : Thresh / 4 ≤ Vol(Sol F).
```

## The hypothesis is the paper's own, unstated

`sections/analysis.tex:284` silently assumes `j* ≥ 1`, i.e. that the very first
cooling level is already above threshold.  `Thresh/4 ≤ Vol(Sol F)` is exactly that
assumption, written out (README finding 20).  The paper never states it and never
discharges it; here it is a named hypothesis of a named theorem.

## This does **not** widen the theorem's reach

`Ttc.Box.big_not_derivable` (`Exec/Regime`) exhibits, for every `(ε, δ)` in range,
an instance on which the `big` binder is *false* — so `big` is genuinely a
restriction on the input, not a fact about the algorithm, and no proof could
remove it.  What `Ttc.big_of_volume` buys is **legibility**: the restriction stops
being a `∀` over coin sequences, quantifying over the algorithm's own randomness
and over the constructed sampler and volume estimates, and becomes one inequality
about the input body that a reader can check before running anything.  The reach
of the surrounding theorem is unchanged; only the shape of its precondition is.

## The chain

With `ε' = ε/12`, `η = ε/8`, `N = Ttc.normalisedCount`, `V = Ttc.volSol`:

```
∑ₛ θ s ≥ (1 − ε')²(1 − η)·N              -- Ttc.sum_rates_ge_of_pointwise
        ≥ (1 − ε')²(1 − η)·V/(1 + η)     -- Ttc.lattice_of_dnf, upper half
        ≥ (1 − ε')²(1 − η)/(1 + η)·Thresh/4
        ≥ (1 − ε')·Thresh/8              -- Ttc.half_le_of_eps
```

The last step is where the constants of `alg:ttc` are spent: it needs
`(1 − ε')(1 − η)/(1 + η) ≥ 1/2`, which at `ε = 1` reads `0.713 ≥ 0.5`, so the
choice `ε' = ε/12`, `η = ε/8` has real slack here.

## No positivity of `Thresh` is assumed

`Ttc.Params` carries no bounds on `δ`, so `0 ≤ P.thresh` is *not* available (both
branches of the `max` defining `Ttc.Params.thresh` go negative for large `δ`).
The arithmetic core `Ttc.sum_ge_of_volume_aux` therefore case-splits: when
`Thresh < 0` the target is negative and the sum is nonnegative, because
`Ttc.volSol` is an `ENNReal.toReal`.  So no `δ`-hypothesis is needed.
-/

namespace Ttc

variable {A : Type*} {n : ℕ}

/-! ## 1. The arithmetic

Two lemmas, both about real numbers only: the constant chase for `alg:ttc`'s
`(ε', η) = (ε/12, ε/8)`, and the four-step chain that consumes it.
-/

/-- **`2(1 − ε')(1 − η) ≥ 1 + η` for `alg:ttc`'s constants.**  With `ε' = ε/12`
and `η = ε/8` this is `1 − 13ε/24 + ε²/48 ≥ 0`, which holds on `0 ≤ ε ≤ 1` with
room to spare (at `ε = 1` the left side is `≈ 0.427 > 0`). -/
theorem two_mul_le_of_eps (P : Params) :
    (1 + P.eta) / 2 ≤ (1 - P.epsPrime) * (1 - P.eta) := by
  rw [Params.epsPrime, Params.eta]
  nlinarith [P.hε0, P.hε1, sq_nonneg P.ε]

/-- **The multiplicative slack of `alg:ttc`'s constants**, in the form the rate
chain uses: `(1 − ε')(1 − η)/(1 + η) ≥ 1/2`.  This is what lets the two-sided
`lem:lattice` error `(1 ± η)` and the sampler error `(1 − ε')` be absorbed into
the single factor `1/2` separating `Thresh/4` from `Thresh/8`. -/
theorem half_le_of_eps (P : Params) :
    (1 : ℝ) / 2 ≤ (1 - P.epsPrime) * (1 - P.eta) / (1 + P.eta) := by
  have hpos : (0 : ℝ) < 1 + P.eta := by
    rw [Params.eta]; nlinarith [P.hε0, P.hε1]
  rw [le_div_iff₀ hpos]
  have := two_mul_le_of_eps P
  linarith

/-- **The chain, over abstract reals.**  Read `e = ε'`, `h = η`, `T = Thresh`,
`V = Vol(Sol F)`, `N = |Sol(F) ∩ 𝕃ⁿ|/10^(ρn)`, `S = ∑ₛ θ s`.

The hypotheses are, in order: `e ≤ 1`; `0 ≤ h`; the constant slack
`(1 + h)/2 ≤ (1 − e)(1 − h)`; the pointwise rate bound; the upper half of
`lem:lattice`; the volume hypothesis `T/4 ≤ V`; and `0 ≤ V`.

`0 ≤ T` is *not* assumed: if `T < 0` the conclusion is negative while `S ≥ 0`
follows from `0 ≤ V` and the first two facts, so the statement is free there. -/
theorem sum_ge_of_volume_aux {e h T V N S : ℝ}
    (he1 : e ≤ 1) (hh0 : 0 ≤ h)
    (hslack : (1 + h) / 2 ≤ (1 - e) * (1 - h))
    (hsum : (1 - e) ^ 2 * (1 - h) * N ≤ S)
    (hlat : V ≤ (1 + h) * N)
    (hvol : T / 4 ≤ V) (hV : 0 ≤ V) :
    (1 - e) * T / 8 ≤ S := by
  have hpos : (0 : ℝ) < 1 + h := by linarith
  have hprod : (0 : ℝ) < (1 - e) * (1 - h) := by linarith
  have he0 : (0 : ℝ) < 1 - e := by nlinarith
  have hh1 : (0 : ℝ) < 1 - h := by nlinarith
  have hc : (0 : ℝ) ≤ (1 - e) ^ 2 * (1 - h) := by positivity
  -- `N ≥ 0`: the region has nonnegative volume and `1 + h > 0`.
  have hN : (0 : ℝ) ≤ N := by nlinarith
  rcases le_or_gt 0 T with hT | hT
  · -- The interesting case: push `T/4 ≤ V` through the two multiplicative errors.
    have hA : (1 - e) ^ 2 * (1 - h) * (T / 4) ≤ (1 + h) * S :=
      calc (1 - e) ^ 2 * (1 - h) * (T / 4)
          ≤ (1 - e) ^ 2 * (1 - h) * V := by
            exact mul_le_mul_of_nonneg_left hvol hc
        _ ≤ (1 - e) ^ 2 * (1 - h) * ((1 + h) * N) :=
            mul_le_mul_of_nonneg_left hlat hc
        _ = (1 + h) * ((1 - e) ^ 2 * (1 - h) * N) := by ring
        _ ≤ (1 + h) * S := mul_le_mul_of_nonneg_left hsum hpos.le
    have hB : (1 + h) * ((1 - e) * T / 8) ≤ (1 - e) ^ 2 * (1 - h) * (T / 4) := by
      nlinarith [mul_nonneg (mul_nonneg he0.le hT)
        (by linarith : (0 : ℝ) ≤ 2 * ((1 - e) * (1 - h)) - (1 + h))]
    exact le_of_mul_le_mul_left (by linarith) hpos
  · -- Degenerate case: the target is negative and the sum is nonnegative.
    have hS : (0 : ℝ) ≤ S := le_trans (by positivity) hsum
    nlinarith

/-! ## 2. The regime condition

Everything below is assembly: four already-proved facts, plugged into
`Ttc.sum_rates_ge_of_pointwise` and then into `Ttc.sum_ge_of_volume_aux`.
-/

/-- **`analysis.tex:295` as a theorem**, for the canonical constructed sampler
`Ttc.e2eSampD` and the Monte-Carlo volume estimate `Ttc.mcVol`, given the paper's
unstated `j* ≥ 1` in the form `Thresh/4 ≤ Vol(Sol F)`.

This is exactly the `big` binder of `Ttc.ttc_volume_inputs`, discharged.

The hypotheses are the ones the four ingredients need:

* `hD`, `hpos` — `D` is a positive DNF for `φ`;
* `hn`, `hm`, `hr1`, `hr` — the parameter block sees the instance (`hm` is the
  cube count, `hr` the facet count; `hr1` says there *is* a facet);
* `hAnz` — no facet has a zero normal;
* `hbdd` — `Sol(F)` is bounded, which supplies both `HasLatticeEnum` and the
  finiteness of every region's volume;
* `cen`, `hg`, `hball`, `hρ` — the inscribed ball and the precision it chooses;
* `hvol` — the volume hypothesis;
* `hc` — the coin sequence is good for the volume oracle.

`(1 : ℝ) ≤ P.m` is *not* a hypothesis: it is `P.hm` cast to `ℝ`.  The cube count
bound `hm` is stated as `Nat.card {c // c ∈ D} ≤ P.m` (not as `1 ≤ P.m`) because
`Ttc.lattice_of_dnf`, which supplies the upper half of `lem:lattice` for the whole
of `Sol(F)`, needs the count and not merely `1`. -/
theorem big_of_volume (atoms : A → LinAtom n) {D : DNF A} {φ : BForm A}
    (hD : IsDNFOf D φ) (hpos : DNF.IsPositive D)
    (P : Params) (hn : P.n = n)
    (hm : (Nat.card {c : Cube A // c ∈ D} : ℝ) ≤ P.m)
    (hr1 : 1 ≤ Nat.card (FacetIndex D))
    (hr : (Nat.card (FacetIndex D) : ℝ) ≤ P.r)
    (hAnz : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ))
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat)
    (hvol : P.thresh / 4 ≤ volSol (fun a => (atoms a).halfspace) φ)
    {c : ℕ → Space n}
    (hc : c ∈ mcGood (fun a => (atoms a).halfspace) D cen gammaHat
            P.epsPrime P.deltaPrime) :
    (1 - P.epsPrime) * P.thresh / 8
      ≤ ∑ s, rates (fun a => (atoms a).halfspace) φ D ρ
          (e2eSampD (fun a => (atoms a).halfspace) D ρ P.epsPrime (canonRfac D)
            (Jt := Fin (Nat.card (FacetIndex D))) (canonAm atoms D)
            (canonBv atoms D (latticeScale ρ)) cen gammaHat
            (canonDm (fun a => (atoms a).halfspace) D ρ))
          (mcVol (fun a => (atoms a).halfspace) D cen gammaHat
            P.epsPrime P.deltaPrime c) s := by
  classical
  set M : A → Set (Space n) := fun a => (atoms a).halfspace with hM
  -- `1 ≤ m` as a real, from the parameter block itself
  have hm1 : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.hm
  -- boundedness gives the enumeration and the finite volumes
  have hle : HasLatticeEnum M φ ρ := hasLatticeEnum_of_isBounded M φ ρ hbdd
  have hfin := volume_region_ne_top_of_isBounded (M := M) hD hbdd
  -- the two error parameters are at most `1`
  have hep1 : P.epsPrime ≤ 1 := by rw [Params.epsPrime]; nlinarith [P.hε0, P.hε1]
  have hη1 : P.eta ≤ 1 := by rw [Params.eta]; nlinarith [P.hε0, P.hε1]
  -- ingredient 4: per-cube `lem:lattice`, lower half, and the finiteness companion
  have hfinLat := finite_region_lattice_of_dnf atoms hpos P hn hm1 hr hAnz cen hg hball hfin hρ
  have hlatc := lattice_cube_of_dnf atoms hpos P hn hm1 hr hAnz cen hg hball hfin hρ
  -- ingredient 2: the constructed sampler is `ε'`-almost uniform on every cube
  have hAU := e2eSampD_almostUniform_of_isBounded_sol atoms hD hpos P hn hr1 hbdd cen hg hball hρ
  -- ingredient 3: the volume estimate is within `(1 − ε')` from below
  have hvolLo := fun i => mcVol_ge M D cen gammaHat P.epsPrime P.deltaPrime hc i
  -- ingredient 1: the pointwise rate bound, summed
  have hsum := sum_rates_ge_of_pointwise (M := M) hD hle _ _ hep1 hη1 hfinLat hAU hvolLo hlatc
  -- `lem:lattice` for the whole of `Sol(F)`, upper half
  have hlat := (lattice_of_dnf atoms hD hpos P hn hm hr hAnz cen hg hball hfin hρ).1.2
  exact sum_ge_of_volume_aux hep1 (by rw [Params.eta]; linarith [P.hε0])
    (two_mul_le_of_eps P) hsum hlat hvol ENNReal.toReal_nonneg

/-! ## Axiom profile (`CLAUDE.md` §4) -/

#print axioms two_mul_le_of_eps
#print axioms half_le_of_eps
#print axioms sum_ge_of_volume_aux
#print axioms big_of_volume

end Ttc

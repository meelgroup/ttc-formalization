/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.VolPriceCVAlg

/-!
# `Witness/FixedPriceTwoCube`: non-vacuity for the **fixed-price** headline

`Ttc/Witness/FullTwoCube.lean` witnesses `Ttc.ttc_volume_estimate_parametric` — the
eleven-binder, price-parametric form.  Since `Ttc.ttc_volume_estimate`'s nine binders are a
sub-list of those eleven, the same two-cube data meets them, and FullTwoCube's docstring
says so in prose.  **Prose is not a witness** (`CLAUDE.md` §11, `AUDIT.md` check #4), so
this file states the instance.

## Why it is a separate file

`Ttc/Exec/VolPriceCVAlg.lean` imports `Ttc/Witness/FullTwoCube.lean`, so the witness cannot
live there; and `Ttc.ttc` (`Model/Pseudocode`) charges `Ttc.cvVolPriceAt`/`Ttc.hrSampPriceAt`
rather than `Ttc.ttcVolPriceCVAlg`/`Ttc.ttcSampPriceHR`, because those two are
`Ttc/Exec/`-defined and `#modelClosure` tests the *defining module*.  This file is downstream
of everything, so it may name either pair; it states the witness at the `Ttc/Exec/` names,
and `Ttc.cvVolPriceAt_eq`/`Ttc.hrSampPriceAt_eq` (`Exec/VolPriceCVAlg`) are the two `rfl`
bridges.

## What this does and does not establish

It establishes that the fixed-price headline is **not vacuous**: its hypothesis list is
simultaneously satisfiable, at every `n ≥ 1` and every `(ε, δ) ∈ (0,1]²`, and the
conclusion it yields there is the same positive-probability statement FullTwoCube pins at
numerals.

It establishes **nothing about cost**.  The run is still `Ttc.mcVol` over the lazy ball
walk; the two prices named below are the Cousins–Vempala and hit-and-run numbers, which no
lemma anywhere dominates `Ttc.ttcVolCoins` or `Ttc.ttcSampleSteps` by.  See the boxed
warning at the head of `Ttc/Exec/PricedHeadline.lean`, and this repository's cost caveat in
`Ttc/Witness/FullTwoCube.lean`.
-/

namespace Ttc

namespace TwoCube

open MeasureTheory Set

/-- **Non-vacuity of `Ttc.ttc_volume_estimate` at its fixed prices.**  The two-cube data of
`Ttc/Witness/TwoCube.lean` meets all nine binders — `hφ` by
`Ttc.TwoCube.twoForm_isPositive`, `hpos` by `Ttc.TwoCube.twoVolPos`, the rest by hypothesis
— so the headline's accuracy conjunct holds there, at the Cousins–Vempala volume price and
the hit-and-run sampling price.

The prices are named here at their `Ttc/Exec/` spellings and inside `Ttc.ttc` at their
`Model/Pseudocode` ones; the two pairs are equal by `Ttc.cvVolPriceAt_eq` and
`Ttc.hrSampPriceAt_eq`.  Cost caveat as in
`Ttc/Witness/FullTwoCube.lean`: this is unconditional *correctness*, and the prices charged
are not prices this run is proved to pay. -/
theorem ttc_volume_estimate_two_cube_fixed (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ twoAccFull n hn ε δ hε0 hε1
      (ttcVolPriceCVAlg (atomsT n hn ε δ hε0 hε1) (twoForm n) ε δ)
      (ttcSampPriceHR (atomsT n hn ε δ hε0 hε1) (twoForm n) ε δ) := by
  rw [ttcVolPriceCVAlg_model, ttcSampPriceHR_model]
  exact (ttc_volume (atomsT n hn ε δ hε0 hε1) (twoForm n) ε δ
    hε0 hε1 hδ0 hδ1 hn twoForm_isPositive (twoVolPos n hn ε δ hε0 hε1)).1

/-- The same at `(ε, δ) = (1/3, 9/10)` and `(1/2, 1/4)`, with the achieved bounds proved
strictly positive **in the statement** — so neither conclusion is the vacuous
`0 ≤ (…).toReal`.  Mirrors `Ttc.TwoCube.ttc_volume_estimate_two_cube_full_at`. -/
theorem ttc_volume_estimate_two_cube_fixed_at (n : ℕ) (hn : 1 ≤ n)
    (hε₁ : (0 : ℝ) < 1/3) (hε₁' : (1/3 : ℝ) ≤ 1)
    (hε₂ : (0 : ℝ) < 1/2) (hε₂' : (1/2 : ℝ) ≤ 1) :
    ((0 : ℝ) < 1/10 ∧ (1/10 : ℝ) ≤ twoAccFull n hn (1/3) (9/10) hε₁ hε₁'
        (ttcVolPriceCVAlg (atomsT n hn (1/3) (9/10) hε₁ hε₁') (twoForm n) (1/3) (9/10))
        (ttcSampPriceHR (atomsT n hn (1/3) (9/10) hε₁ hε₁') (twoForm n) (1/3) (9/10)))
    ∧ ((0 : ℝ) < 3/4 ∧ (3/4 : ℝ) ≤ twoAccFull n hn (1/2) (1/4) hε₂ hε₂'
        (ttcVolPriceCVAlg (atomsT n hn (1/2) (1/4) hε₂ hε₂') (twoForm n) (1/2) (1/4))
        (ttcSampPriceHR (atomsT n hn (1/2) (1/4) hε₂ hε₂') (twoForm n) (1/2) (1/4))) := by
  refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩
  · have h := ttc_volume_estimate_two_cube_fixed n hn (1/3) (9/10) hε₁ hε₁'
      (by norm_num) (by norm_num)
    linarith
  · have h := ttc_volume_estimate_two_cube_fixed n hn (1/2) (1/4) hε₂ hε₂'
      (by norm_num) (by norm_num)
    linarith

end TwoCube

end Ttc

/-! ## Axiom profile

Expect `[propext, Classical.choice, Quot.sound]` throughout (`CLAUDE.md` §4). -/

#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube_fixed
#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube_fixed_at

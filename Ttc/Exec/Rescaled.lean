/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Scale
import Ttc.Exec.ScaleFactor
import Ttc.Exec.Inscribed

/-!
# `Exec/Rescaled`: the guarantee with **no volume hypothesis**

`Ttc.ttc_volume_vol` (`Exec/Inputs`) carries

```
hvol : P.thresh / 4 ≤ volSol (atomSet atoms) φ
```

and that hypothesis is **necessary for `alg:ttc` as printed**: `p` starts at `1` and
only halves (`alg:ttc` lines 21, 33, 40), so the sketch is `Poisson(Λ)` with
`Λ ≤ Vol(Sol F)`, and a Poisson count has relative standard deviation `Λ^(-1/2)`.
On a body of volume `10⁻⁶` the run draws `Pois(10⁻⁶)` points, returns `0`, and
`0 ∉ (1 ± ε)·10⁻⁶`. `Ttc.Box.big_not_derivable` (`Exec/Regime`) is the machine-checked
form of the same fact, and README finding 20 is where the paper's proof silently
assumes it away (`sections/analysis.tex:284`, the definition of `j*`).

## What this file does instead of assuming it

It **changes the algorithm**, by one preprocessing step, and then the hypothesis is
discharged rather than assumed:

1. dilate the input by `c := Ttc.scaleFactor n P gammaHat = max 1 (Thresh/(Vₙ·γ̂ⁿ))`,
   which is computable from the inscribed radius `γ̂` that `alg:prec` line 86 already
   produces, and from the dimension — **no knowledge of `Vol(Sol F)` is needed**;
2. run `TTC` on the dilated formula, whose inscribed radius is `c·γ̂`;
3. divide the estimate by `cⁿ`.

`Vol(c·S) = cⁿ·Vol(S)` exactly (`Ttc.volSol_scaleAtoms`), so step 3 undoes step 1
with no loss, and after step 1 the body clears the threshold
(`Ttc.thresh_le_scaled_ball_volume`), so `hvol` holds by construction.

**Be clear about what changed.** This is a *new line in the algorithm*, not a sharper
analysis. `alg:ttc` as printed does not dilate and really does return `0` on a small
body. What `Ttc.ttc_volume_rescaled` establishes is the guarantee for `alg:ttc`
**plus that line**, for every `(F, ε, δ)` in the parameter range and with no
condition on `Vol(F)`.

Two details that make the substitution painless, and are why the scale factor can be
defined at all:

* `Ttc.inputParams` depends only on `(toDNFd φ, n, ε, δ)` — not on `atoms` — so the
  parameter block, and hence `Thresh`, is **unchanged** by the dilation
  (`Ttc.inputParams_scaleAtoms`). There is no circularity in computing `c` from `P`.
* `φ` itself is untouched, so `Ttc.toDNFd φ` is the same list and the cube index type
  `{c // c ∈ toDNFd φ}` does not move. No dependent-type transport is needed.

`Ttc.scaleFactor` overshoots (`max 1 (…)` rather than an `n`-th root); that is
deliberate and free, since the answer is divided by `cⁿ` at the end.
-/

namespace Ttc

open MeasureTheory Set Pointwise

section Rescaled

variable {A : Type*} {n : ℕ}

/-! ## Rescaling the accuracy interval -/

/-- **`(1 ± ε)` commutes with a positive rescaling.**  An estimate of `K·V` is
within `(1 ± ε)` of it exactly when the estimate divided by `K` is within `(1 ± ε)`
of `V`. -/
theorem mem_relErr_div {ε V out K : ℝ} (hK : 0 < K) :
    out ∈ relErr ε (K * V) ↔ out / K ∈ relErr ε V := by
  simp only [relErr, Set.mem_Icc, le_div_iff₀ hK, div_le_iff₀ hK]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩

/-- The set form of `Ttc.mem_relErr_div`, for rewriting under a measure. -/
theorem setOf_mem_relErr_div {α : Type*} (f : α → ℝ) {ε V K : ℝ} (hK : 0 < K) :
    {a | f a ∈ relErr ε (K * V)} = {a | f a / K ∈ relErr ε V} := by
  ext a; exact mem_relErr_div hK

/-! ## The dilated instance -/

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
  (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
  (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))

include hε0 hε1 hn hφ hbdd in
/-- The dilation `Ttc.runScale` (`Model/Pseudocode`, line A10) is positive. -/
theorem runScale_pos (gammaHat : ℝ) : 0 < runScale atoms φ ε δ gammaHat :=
  scaleFactor_pos _ _ _

include hε0 hε1 hn hφ hbdd in
/-- `Sol` of the dilated formula is bounded, since `Sol(F)` is. -/
theorem scaledBdd (gammaHat : ℝ) :
    Bornology.IsBounded (sol (atomSet (scaledAtoms atoms φ ε δ gammaHat)) φ) :=
  isBounded_sol_scaleAtoms (runScale_pos atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) hbdd

include hε0 hε1 hn hφ hbdd in
/-- **The parameter block is unchanged by the dilation** — it is computed from
`(toDNFd φ, n, ε, δ)`, and none of those moves.  This is what makes `Ttc.runScale`
well-defined rather than circular. -/
theorem inputParams_scaleAtoms (gammaHat : ℝ) :
    inputParamsTotal (scaledAtoms atoms φ ε δ gammaHat) φ ε δ
      = inputParamsTotal atoms φ ε δ := rfl

include hε0 hε1 hn hφ hbdd in
/-- `Vol` of the dilated solution set, in terms of the original. -/
theorem volSol_scaledAtoms (gammaHat : ℝ) :
    volSol (atomSet (scaledAtoms atoms φ ε δ gammaHat)) φ
      = (runScale atoms φ ε δ gammaHat) ^ n * volSol (atomSet atoms) φ :=
  volSol_scaleAtoms (runScale_pos atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) atoms φ

include hε0 hε1 hn hφ hbdd in
/-- **The dilated body clears the threshold.**  `Vol(c·Sol F) = cⁿ·Vol(Sol F) ≥
(c·γ̂)ⁿ·Vₙ ≥ Thresh`, the middle step by the inscribed ball and the last by
`Ttc.thresh_le_scaled_ball_volume`.  This is `hvol`, discharged. -/
theorem hvol_scaled {gammaHat : ℝ} (hgammaHat : 0 < gammaHat)
    (cen : {c : Cube A // c ∈ toDNFd φ} → Space n)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region (atomSet atoms) i.val) :
    (inputParamsTotal atoms φ ε δ).thresh / 4
      ≤ volSol (atomSet (scaledAtoms atoms φ ε δ gammaHat)) φ := by
  set P := inputParamsTotal atoms φ ε δ with hP
  set c := runScale atoms φ ε δ gammaHat with hc
  have hcpos : 0 < c := runScale_pos atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat
  obtain ⟨cu, hcu⟩ := List.exists_mem_of_ne_nil _ (toDNFd_ne_nil hφ)
  -- the original body already contains a ball of radius `γ̂`
  have hball : gammaHat ^ n * unitBallVol n ≤ volSol (atomSet atoms) φ :=
    ball_volume_le_volSol_atomSet (toDNFd_isDNFOf φ) hbdd hgammaHat ball_subset ⟨cu, hcu⟩
  -- so the dilated body contains one of radius `c·γ̂`, whose volume clears `Thresh`
  have hthr : P.thresh ≤ (c * gammaHat) ^ n * unitBallVol n :=
    thresh_le_scaled_ball_volume n hn P hgammaHat
  have hscale : volSol (atomSet (scaledAtoms atoms φ ε δ gammaHat)) φ
      = c ^ n * volSol (atomSet atoms) φ := volSol_scaleAtoms hcpos atoms φ
  have hcn : (0 : ℝ) < c ^ n := pow_pos hcpos n
  have hchain : P.thresh
      ≤ volSol (atomSet (scaledAtoms atoms φ ε δ gammaHat)) φ := by
    rw [hscale]
    calc P.thresh ≤ (c * gammaHat) ^ n * unitBallVol n := hthr
      _ = c ^ n * (gammaHat ^ n * unitBallVol n) := by rw [mul_pow]; ring
      _ ≤ c ^ n * volSol (atomSet atoms) φ := by
          exact mul_le_mul_of_nonneg_left hball (le_of_lt hcn)
  have hnonneg : 0 ≤ volSol (atomSet (scaledAtoms atoms φ ε δ gammaHat)) φ :=
    ENNReal.toReal_nonneg
  linarith

/-! ## The headline, with no volume hypothesis -/

include hε0 hε1 hn hφ hbdd in
/-- **`thm:volumettc` for `alg:ttc` plus a dilation step — no condition on `Vol(F)`.**

`TTC` is run on the formula dilated by `c = Ttc.runScale …`, whose inscribed ball has
radius `c·γ̂` about `c • cen i`, and the estimate is divided by `cⁿ`.  The conclusion
is about the **original** `Vol(Sol F)`.

**16 binders** — `Ttc.ttc_volume_vol`'s seventeen minus `hvol`, which
`Ttc.hvol_scaled` now discharges.  Every remaining hypothesis is a condition on the
input, and none of them constrains the *size* of the solution set.

This is the guarantee for `alg:ttc` **with the dilation line added**; the printed
algorithm does not have it and is not covered by this statement for small bodies —
see this module's docstring and README finding 20. -/
theorem ttc_volume_rescaled
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcoeff : ∀ j : FacetIndex (toDNFd φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNFd φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region (atomSet atoms) i.val) :
    (1 - δ ≤
      (∫⁻ c, trajLaw
            (runRates (scaledAtoms atoms φ ε δ gammaHat) φ ε δ
              (fun i => runScale atoms φ ε δ gammaHat • cen i)
              (runScale atoms φ ε δ gammaHat * gammaHat) c)
          {t | ttcRunOutput (scaledAtoms atoms φ ε δ gammaHat) φ ε δ
                (fun i => runScale atoms φ ε δ gammaHat • cen i)
                (runScale atoms φ ε δ gammaHat * gammaHat) c t
              / (runScale atoms φ ε δ gammaHat) ^ n
            ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (runCount (scaledAtoms atoms φ ε δ gammaHat) φ ε δ
          (runScale atoms φ ε δ gammaHat * gammaHat)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (inputParamsTotal atoms φ ε δ).thresh →
      Terminates (inputParamsTotal atoms φ ε δ)
          (runOracles (scaledAtoms atoms φ ε δ gammaHat) φ ε δ
            (fun i => runScale atoms φ ε δ gammaHat • cen i)
            (runScale atoms φ ε δ gammaHat * gammaHat) c t) (toDNFd φ) →
      runCost (inputParamsTotal atoms φ ε δ)
          (runOracles (scaledAtoms atoms φ ε δ gammaHat) φ ε δ
            (fun i => runScale atoms φ ε δ gammaHat • cen i)
            (runScale atoms φ ε δ gammaHat * gammaHat) c t)
          cVol cSample (runPrec (scaledAtoms atoms φ ε δ gammaHat) φ ε δ
            (runScale atoms φ ε δ gammaHat * gammaHat)) (toDNFd φ)
        ≤ (toDNFd φ).length * (cVol + cSample * thr)) := by
  have hcpos : 0 < runScale atoms φ ε δ gammaHat :=
    runScale_pos atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat
  obtain ⟨hacc, hcost⟩ := ttc_volume_vol
    (scaledAtoms atoms φ ε δ gammaHat) φ ε δ
    hε0 hε1 hδ0 hδ1 hn hφ (scaledBdd atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat)
    hcoeff (fun i => runScale atoms φ ε δ gammaHat • cen i)
    (runScale atoms φ ε δ gammaHat * gammaHat) (mul_pos hcpos hgammaHat)
    (ball_subset_scaleAtoms hcpos ball_subset)
    (hvol_scaled atoms φ ε δ hε0 hε1 hn hφ hbdd hgammaHat cen ball_subset)
  refine ⟨?_, hcost⟩
  rw [volSol_scaledAtoms atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat] at hacc
  simp only [mem_relErr_div (pow_pos hcpos n)] at hacc
  exact hacc

/-! ## `GetPrecision`'s inscribed ball, constructed

`alg:prec` line 86 is `γ̂ ← MaxInscribedBall(P^i)` — the ball is *computed*, not
supplied.  `Ttc.cenOf` and `Ttc.gammaOf` (`Model/Pseudocode`, lines A8–A9) construct
one, and `Ttc.autoCen`/`Ttc.autoGamma` (`Model/Pseudocode`) are those at the input's
own cube list; `Ttc.ball_subset_cenOf` (`Exec/Inscribed`) is **unconditional** (an
empty-interior region gets radius `0`, and `Metric.ball _ 0 = ∅`).  Only positivity
needs an input condition, and it is the readable one: every cube's region has
nonempty interior. -/

include hε0 hε1 hn hφ hbdd in
/-- **`thm:volumettc` at 13 binders: no oracle, no precision, no parameter block, no
volume hypothesis and no inscribed-ball data.**

`Ttc.ttc_volume_rescaled` with `cen`, `gammaHat`, `hgammaHat` and `ball_subset`
discharged by the `GetPrecision` construction of `Exec/Inscribed`.  What replaces the
four is a single condition on the input:

```
hint : ∀ i, (interior (region (atomSet atoms) i.val)).Nonempty
```

*every polytope of the decomposition is full-dimensional* — a genuine restriction, since
a DNF cube may be empty or lower-dimensional, and exactly the condition under which
`alg:prec` line 86's LP returns a positive radius.

The ball is *some* inscribed ball, not the maximal one; non-maximality only inflates
`ρ = ⌈log₁₀(γ/γ̂)⌉`, so the guarantee is unaffected and only the precision is looser
than the paper's. -/
theorem ttc_volume_full
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcoeff : ∀ j : FacetIndex (toDNFd φ), (atoms j.2.val.atom).coeff ≠ 0)
    (hint : ∀ i : {c : Cube A // c ∈ toDNFd φ},
      (interior (region (atomSet atoms) i.val)).Nonempty) :
    (1 - δ ≤
      (∫⁻ c, trajLaw
            (runRates (scaledAtoms atoms φ ε δ (autoGamma atoms φ)) φ ε δ
              (fun i => runScale atoms φ ε δ (autoGamma atoms φ)
                • autoCen atoms φ i)
              (runScale atoms φ ε δ (autoGamma atoms φ)
                * autoGamma atoms φ) c)
          {t | ttcRunOutput (scaledAtoms atoms φ ε δ (autoGamma atoms φ)) φ ε δ
                (fun i => runScale atoms φ ε δ (autoGamma atoms φ)
                  • autoCen atoms φ i)
                (runScale atoms φ ε δ (autoGamma atoms φ)
                  * autoGamma atoms φ) c t
              / (runScale atoms φ ε δ (autoGamma atoms φ)) ^ n
            ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (runCount (scaledAtoms atoms φ ε δ (autoGamma atoms φ))
          φ ε δ
          (runScale atoms φ ε δ (autoGamma atoms φ)
            * autoGamma atoms φ)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (inputParamsTotal atoms φ ε δ).thresh →
      Terminates (inputParamsTotal atoms φ ε δ)
          (runOracles (scaledAtoms atoms φ ε δ (autoGamma atoms φ)) φ ε δ
            (fun i => runScale atoms φ ε δ (autoGamma atoms φ)
              • autoCen atoms φ i)
            (runScale atoms φ ε δ (autoGamma atoms φ)
              * autoGamma atoms φ) c t) (toDNFd φ) →
      runCost (inputParamsTotal atoms φ ε δ)
          (runOracles (scaledAtoms atoms φ ε δ (autoGamma atoms φ)) φ ε δ
            (fun i => runScale atoms φ ε δ (autoGamma atoms φ)
              • autoCen atoms φ i)
            (runScale atoms φ ε δ (autoGamma atoms φ)
              * autoGamma atoms φ) c t)
          cVol cSample
          (runPrec (scaledAtoms atoms φ ε δ (autoGamma atoms φ)) φ ε δ
            (runScale atoms φ ε δ (autoGamma atoms φ)
              * autoGamma atoms φ)) (toDNFd φ)
        ≤ (toDNFd φ).length * (cVol + cSample * thr)) :=
  ttc_volume_rescaled atoms φ ε δ hε0 hε1 hn hφ hbdd hδ0 hδ1 hcoeff
    (autoCen atoms φ) (autoGamma atoms φ)
    (gammaOf_pos_of_interior (atomSet atoms) (toDNFd_ne_nil hφ) hint)
    (ball_subset_cenOf (atomSet atoms) (toDNFd φ))

include hε0 hε1 hn hφ hbdd in
/-- **`thm:runtime` for the same run** — `alg:ttc`'s charged cost
`m · (C_vol + C_sample · Thresh)`, under `Ttc.Terminates`, on the dilated instance.
The second conjunct of `Ttc.ttc_volume_rescaled` at the constructed ball. -/
theorem ttc_volume_full_cost
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcoeff : ∀ j : FacetIndex (toDNFd φ), (atoms j.2.val.atom).coeff ≠ 0)
    (hint : ∀ i : {c : Cube A // c ∈ toDNFd φ},
      (interior (region (atomSet atoms) i.val)).Nonempty) :
    ∀ (c : ℕ → Space n)
        (t : ℕ → Fin (runCount (scaledAtoms atoms φ ε δ (autoGamma atoms φ))
          φ ε δ
          (runScale atoms φ ε δ (autoGamma atoms φ)
            * autoGamma atoms φ)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (inputParamsTotal atoms φ ε δ).thresh →
      Terminates (inputParamsTotal atoms φ ε δ)
          (runOracles (scaledAtoms atoms φ ε δ (autoGamma atoms φ)) φ ε δ
            (fun i => runScale atoms φ ε δ (autoGamma atoms φ)
              • autoCen atoms φ i)
            (runScale atoms φ ε δ (autoGamma atoms φ)
              * autoGamma atoms φ) c t) (toDNFd φ) →
      runCost (inputParamsTotal atoms φ ε δ)
          (runOracles (scaledAtoms atoms φ ε δ (autoGamma atoms φ)) φ ε δ
            (fun i => runScale atoms φ ε δ (autoGamma atoms φ)
              • autoCen atoms φ i)
            (runScale atoms φ ε δ (autoGamma atoms φ)
              * autoGamma atoms φ) c t)
          cVol cSample
          (runPrec (scaledAtoms atoms φ ε δ (autoGamma atoms φ)) φ ε δ
            (runScale atoms φ ε δ (autoGamma atoms φ)
              * autoGamma atoms φ)) (toDNFd φ)
        ≤ (toDNFd φ).length * (cVol + cSample * thr) :=
  (ttc_volume_full atoms φ ε δ hε0 hε1 hn hφ hbdd hδ0 hδ1 hcoeff hint).2

end Rescaled

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.mem_relErr_div
#print axioms Ttc.inputParams_scaleAtoms
#print axioms Ttc.hvol_scaled
#print axioms Ttc.ttc_volume_rescaled
#print axioms Ttc.ttc_volume_full
#print axioms Ttc.ttc_volume_full_cost

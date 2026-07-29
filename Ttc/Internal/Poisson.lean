/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# `lem:process`: Poisson splitting

The paper's appendix proves that two ways of populating the sketch `X` agree in
distribution:

1. draw `N ∼ Pois(λ)` and then take `N` i.i.d. samples from `S` under an
   `η`-close-to-uniform law `Pr(sᵢ) = ζᵢ/|S|`;
3. independently draw `rᵢ ∼ Pois(ζᵢ·p'/2)` for each `i` and insert `rᵢ` copies
   of `sᵢ`.

This is the classical **Poisson splitting (thinning) theorem**, proved here in
full: `Ttc.poisson_splitting`. The paper's own computation — the two long displays
in the appendix, ending with
`Pr(⋀ᵢ "sᵢ chosen rᵢ times") = ∏ᵢ (ζᵢ p'/2)^{rᵢ} e^{−ζᵢ p'/2} / rᵢ!` — is exactly
this identity, and `Ttc.poisson_splitting_paper` restates it in the paper's own
notation (`λ = |S|·p'/2`, weights `ζᵢ` with `∑ ζᵢ = |S|`, rates `ζᵢ·p'/2`).

## What the identity does and does not need

Neither the `η`-closeness of the sampling law nor the bounds `α|S| ≤ sz ≤ β|S|`
play any role in the *identity*: they only serve to locate the resulting rate
`ζᵢ p'/2` inside the interval `[(1−η)αp/2, (1+η)βp/2]` that `lem:numlattice`'s invariant
needs. The identity holds for an arbitrary probability vector `q`, which is what
is proved here — a strictly more general statement than the paper's.

The paper's own derivation of the single-coordinate case (its first display)
silently treats `ζ` as *one* scalar shared by all elements, then reintroduces
per-element `ζᵢ` for the independence computation. Only the second, per-element
computation is needed, and it is the one formalised.
-/

namespace Ttc

open Finset

/-- The Poisson probability mass function, as a real-valued function of a real
rate: `Pois(lam)(k) = e^(−lam) · lam^k / k!`. -/
noncomputable def poissonPMF (lam : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-lam) * lam ^ k / (Nat.factorial k : ℝ)

theorem poissonPMF_def (lam : ℝ) (k : ℕ) :
    poissonPMF lam k = Real.exp (-lam) * lam ^ k / (Nat.factorial k : ℝ) := rfl

/-- **Poisson splitting.** If `Pois(lam)`-many i.i.d. draws are distributed over
`l` cells according to a probability vector `q`, the resulting cell counts are
*independent* Poissons with rates `lam * q i`.

The left-hand side is the probability of the count vector `r` under procedure (1)
of the paper's `lem:process`: the multinomial probability of the pattern `r`, times the
Poisson probability of drawing `∑ᵢ rᵢ` samples in total. The right-hand side is
its probability under procedure (3): a product of independent Poissons. -/
theorem poisson_splitting {l : ℕ} (lam : ℝ) (q : Fin l → ℝ) (hq : ∑ i, q i = 1)
    (r : Fin l → ℕ) :
    (Nat.multinomial univ r : ℝ) * (∏ i, q i ^ r i) * poissonPMF lam (∑ i, r i)
      = ∏ i, poissonPMF (lam * q i) (r i) := by
  have hfac : ∀ i : Fin l, ((Nat.factorial (r i) : ℕ) : ℝ) ≠ 0 := fun i => by
    exact_mod_cast (Nat.factorial_pos (r i)).ne'
  have hprodfac : (∏ i, ((Nat.factorial (r i) : ℕ) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => hfac i
  have hKfac : ((Nat.factorial (∑ i, r i) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  -- `K! = (∏ᵢ rᵢ!) * multinomial`
  have hspec : ((Nat.factorial (∑ i, r i) : ℕ) : ℝ)
      = (∏ i, ((Nat.factorial (r i) : ℕ) : ℝ)) * (Nat.multinomial univ r : ℝ) := by
    have h := Nat.multinomial_spec (univ : Finset (Fin l)) r
    have hcast : ((∏ i, Nat.factorial (r i) : ℕ) : ℝ) * (Nat.multinomial univ r : ℝ)
        = ((Nat.factorial (∑ i, r i) : ℕ) : ℝ) := by exact_mod_cast h
    rw [← hcast, Nat.cast_prod]
  -- the exponentials collapse because `∑ q = 1`
  have hexp : ∏ i, Real.exp (-(lam * q i)) = Real.exp (-lam) := by
    rw [← Real.exp_sum]
    congr 1
    rw [show ∑ i, -(lam * q i) = -(lam * ∑ i, q i) by rw [Finset.mul_sum]; simp, hq]
    ring
  -- the powers factor into `lam^K` times `∏ qᵢ^rᵢ`
  have hpow : ∏ i, (lam * q i) ^ r i = lam ^ (∑ i, r i) * ∏ i, q i ^ r i := by
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hRHS : (∏ i, poissonPMF (lam * q i) (r i))
      = Real.exp (-lam) * (lam ^ (∑ i, r i) * ∏ i, q i ^ r i)
        / (∏ i, ((Nat.factorial (r i) : ℕ) : ℝ)) := by
    simp only [poissonPMF]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hexp, hpow]
  -- the multinomial coefficient is nonzero, so it cancels
  have hM : (Nat.multinomial univ r : ℝ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hspec
    exact hKfac hspec
  rw [hRHS, poissonPMF, hspec]
  field_simp

/-- **`lem:process`, in the paper's notation.**

With `S = {s₁,…,s_l}`, weights `ζᵢ` summing to `l = |S|`, sampling probabilities
`ζᵢ/l`, and `N ∼ Pois(l·p'/2)`, the joint law of the insertion counts is the
product of independent `Pois(ζᵢ·p'/2)` laws: procedures (1) and (3) agree.

The rate `l·(p'/2)·(ζᵢ/l) = ζᵢ·(p'/2)` is the paper's `ζᵢ p'/2`. -/
theorem poisson_splitting_paper {l : ℕ} (hl : (l : ℝ) ≠ 0) (p' : ℝ) (ζ : Fin l → ℝ)
    (hζ : ∑ i, ζ i = (l : ℝ)) (r : Fin l → ℕ) :
    (Nat.multinomial univ r : ℝ) * (∏ i, (ζ i / l) ^ r i)
        * poissonPMF ((l : ℝ) * (p' / 2)) (∑ i, r i)
      = ∏ i, poissonPMF (ζ i * (p' / 2)) (r i) := by
  have hq : ∑ i, (ζ i / (l : ℝ)) = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hζ]
    exact mul_inv_cancel₀ hl
  have h := poisson_splitting ((l : ℝ) * (p' / 2)) (fun i => ζ i / (l : ℝ)) hq r
  have hrate : ∀ i, (l : ℝ) * (p' / 2) * (ζ i / (l : ℝ)) = ζ i * (p' / 2) := fun i => by
    field_simp
  simpa only [hrate] using h

/-- The rate produced by `lem:process` sits in the interval the sketch invariant of
`lem:numlattice` requires: if `ζᵢ ∈ [1−η, 1+η]` and `α·l ≤ sz ≤ β·l` with `p' = sz·p/l`,
then `ζᵢ·p' ∈ [(1−η)·α·p, (1+η)·β·p]`. -/
theorem rate_mem_interval {l : ℕ} (hl : (0:ℝ) < l) {η α β p sz ζi : ℝ}
    (hp : 0 ≤ p) (hζlo : 1 - η ≤ ζi) (hζhi : ζi ≤ 1 + η) (hηlo : 0 ≤ 1 - η)
    (hszlo : α * l ≤ sz) (hszhi : sz ≤ β * l) (hα : 0 ≤ α) :
    (1 - η) * α * p ≤ ζi * (sz * p / l) ∧ ζi * (sz * p / l) ≤ (1 + η) * β * p := by
  have hsz0 : 0 ≤ sz := le_trans (by positivity) hszlo
  have hkey : α * p ≤ sz * p / l := by
    rw [le_div_iff₀ hl]
    nlinarith
  have hkey2 : sz * p / l ≤ β * p := by
    rw [div_le_iff₀ hl]
    nlinarith
  have hnn : 0 ≤ sz * p / l := by positivity
  constructor
  · calc (1 - η) * α * p = (1 - η) * (α * p) := by ring
      _ ≤ (1 - η) * (sz * p / l) := mul_le_mul_of_nonneg_left hkey hηlo
      _ ≤ ζi * (sz * p / l) := mul_le_mul_of_nonneg_right hζlo hnn
  · calc ζi * (sz * p / l) ≤ (1 + η) * (sz * p / l) :=
        mul_le_mul_of_nonneg_right hζhi hnn
      _ ≤ (1 + η) * (β * p) := by
        apply mul_le_mul_of_nonneg_left hkey2
        linarith
      _ = (1 + η) * β * p := by ring

end Ttc

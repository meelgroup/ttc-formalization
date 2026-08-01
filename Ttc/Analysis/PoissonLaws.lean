/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Poisson
import Ttc.Analysis.Chernoff

/-!
# `lem:process` as an identity of measures

`Ttc.poisson_splitting` (`Analysis/Poisson`) proves the paper's `lem:process` as an
identity between **probability mass functions**. That is enough to check the
combinatorics, but not to *use*: the invariant of `lem:numlattice` says the count
vector `(𝒳.count s)_{s ∈ S}` **is distributed as** a product of independent
Poissons, which is a statement about measures and about independence.

This file makes that upgrade. `Ttc.countLaw lam q` is the law of the count vector
produced by the paper's procedure (1) — draw `N ∼ Pois(lam)`, then throw the `N`
samples independently into cells with probabilities `q` — written directly by its
point masses, which is legitimate because `Fin l → ℕ` is countable. The theorem

  `Ttc.countLaw_eq_pi : countLaw lam q = Measure.pi (fun i => Po(lam * q i))`

is then exactly `Ttc.poisson_splitting` read through `Measure.ext_of_singleton`,
and *because the right-hand side is a `Measure.pi`*, it delivers independence of
the cell counts for free (`Ttc.iIndepFun_countLaw`).

Two corollaries are what the induction over the main loop actually consumes:

* **thinning** (`Ttc.poisson_thinning`) — keeping each of `Pois(lam)` items
  independently with probability `q` leaves `Pois(q·lam)`. This is the `l = 2`
  case, and it is what `halve` does to the invariant;
* **superposition** (`Ttc.poisson_add`) — independent `Pois(lam₁)` and
  `Pois(lam₂)` counts add to `Pois(lam₁+lam₂)`. This is what appending
  `GenerateSamples`' output does. Mathlib supplies it.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {l : ℕ}

/-! ## The law of the count vector -/

/-- **Procedure (1) of `lem:process`, as a measure.** Draw `N ∼ Pois(lam)` and
scatter the `N` samples independently into `l` cells with probabilities `q`; this
is the law of the resulting count vector, written by its point masses.

The mass at `r` is the multinomial probability of the pattern `r` times the
Poisson probability of drawing `∑ᵢ rᵢ` samples — the left-hand side of
`Ttc.poisson_splitting`. -/
noncomputable def countLaw (lam : ℝ) (q : Fin l → ℝ) : Measure (Fin l → ℕ) :=
  Measure.sum fun r => ENNReal.ofReal
    ((Nat.multinomial Finset.univ r : ℝ) * (∏ i, q i ^ r i)
      * poissonPMF lam (∑ i, r i)) • Measure.dirac r

@[simp] theorem countLaw_singleton (lam : ℝ) (q : Fin l → ℝ) (r : Fin l → ℕ) :
    countLaw lam q {r} = ENNReal.ofReal
      ((Nat.multinomial Finset.univ r : ℝ) * (∏ i, q i ^ r i)
        * poissonPMF lam (∑ i, r i)) := by
  rw [countLaw, Measure.sum_smul_dirac_singleton]

/-- The Poisson point masses of `Analysis/Poisson` are Mathlib's. -/
theorem poissonPMF_eq_measure_real {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) :
    poissonPMF lam k = (poissonMeasure lam.toNNReal).real {k} := by
  rw [poissonMeasure_real_singleton, poissonPMF_def, Real.coe_toNNReal lam hlam]

/-- A point mass of `Ttc.countLaw`'s intended answer: the product measure's mass
at `r` is the product of the one-dimensional Poisson masses. -/
theorem pi_poisson_singleton (f : Fin l → ℝ≥0) (r : Fin l → ℕ) :
    Measure.pi (fun i => poissonMeasure (f i)) {r}
      = ENNReal.ofReal (∏ i, poissonPMF (f i) (r i)) := by
  have hbox : ({r} : Set (Fin l → ℕ)) = Set.univ.pi (fun i => ({r i} : Set ℕ)) := by
    ext w
    constructor
    · rintro rfl; intro i _; rfl
    · intro hw; funext i; exact hw i (Set.mem_univ i)
  rw [hbox, Measure.pi_pi]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => by
    rw [poissonPMF_def]; positivity]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [poissonMeasure_singleton, poissonPMF_def]

/-- **`lem:process`, as an identity of measures.** The count vector of procedure
(1) is distributed as a product of independent `Pois(lam·qᵢ)`.

The two measures live on the countable space `Fin l → ℕ`, so they agree as soon
as they agree on singletons — and there the claim *is* `Ttc.poisson_splitting`. -/
theorem countLaw_eq_pi {lam : ℝ} (hlam : 0 ≤ lam) {q : Fin l → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) :
    countLaw lam q = Measure.pi (fun i => poissonMeasure (lam * q i).toNNReal) := by
  refine Measure.ext_of_singleton fun r => ?_
  rw [countLaw_singleton, pi_poisson_singleton]
  congr 1
  have hcoe : ∀ i, ((((lam * q i).toNNReal : ℝ≥0) : ℝ)) = lam * q i :=
    fun i => Real.coe_toNNReal _ (mul_nonneg hlam (hq0 i))
  calc (Nat.multinomial Finset.univ r : ℝ) * (∏ i, q i ^ r i) * poissonPMF lam (∑ i, r i)
      = ∏ i, poissonPMF (lam * q i) (r i) := poisson_splitting lam q hq r
    _ = ∏ i, poissonPMF (((lam * q i).toNNReal : ℝ)) (r i) := by
        exact Finset.prod_congr rfl fun i _ => by rw [hcoe i]

/-- **The cell counts are independent** — immediate from `Ttc.countLaw_eq_pi`,
since a `Measure.pi` is exactly what independence asserts. -/
theorem iIndepFun_countLaw {lam : ℝ} (hlam : 0 ≤ lam) {q : Fin l → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) :
    iIndepFun (fun (i : Fin l) (r : Fin l → ℕ) => r i) (countLaw lam q) := by
  rw [countLaw_eq_pi hlam hq0 hq]
  exact iIndepFun_pi (X := fun _ (k : ℕ) => k) fun _ => aemeasurable_id

/-- **Each cell count is `Pois(lam·qᵢ)`** — the marginal of `Ttc.countLaw_eq_pi`. -/
theorem map_countLaw_eval {lam : ℝ} (hlam : 0 ≤ lam) {q : Fin l → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) (i : Fin l) :
    (countLaw lam q).map (Function.eval i) = poissonMeasure (lam * q i).toNNReal := by
  rw [countLaw_eq_pi hlam hq0 hq]
  exact (measurePreserving_eval (fun i => poissonMeasure (lam * q i).toNNReal) i).map_eq

/-! ## The total count

Summing the cells recovers a single `Pois(lam)` — the other half of `lem:process`,
and what turns the invariant into a statement about `|𝒳|`. The proof is the
multinomial theorem: the multinomial weights over the simplex `∑ᵢ rᵢ = k` sum to
`(∑ᵢ qᵢ)^k = 1`, leaving the Poisson mass at `k`.
-/

theorem poissonPMF_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) : 0 ≤ poissonPMF lam k := by
  rw [poissonPMF_def]
  refine div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hlam k)) ?_
  exact_mod_cast (Nat.factorial_pos k).le

/-- The simplex `∑ᵢ rᵢ = k`, as a `Finset`. -/
theorem setOf_sum_eq (k : ℕ) :
    {r : Fin l → ℕ | ∑ i, r i = k} = ↑(Finset.piAntidiag (Finset.univ : Finset (Fin l)) k) := by
  ext r
  simp [Finset.mem_piAntidiag]

/-- **The total count is `Pois(lam)`.** -/
theorem countLaw_apply_sum {lam : ℝ} (hlam : 0 ≤ lam) {q : Fin l → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) (k : ℕ) :
    countLaw lam q {r : Fin l → ℕ | ∑ i, r i = k} = ENNReal.ofReal (poissonPMF lam k) := by
  classical
  rw [setOf_sum_eq, ← sum_measure_singleton]
  have hterm : ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset (Fin l)) k,
      countLaw lam q {r} = ENNReal.ofReal
        ((Nat.multinomial Finset.univ r : ℝ) * (∏ i, q i ^ r i) * poissonPMF lam k) := by
    intro r hr
    have hk : ∑ i, r i = k := by simpa using (Finset.mem_piAntidiag.1 hr).1
    rw [countLaw_singleton, hk]
  rw [Finset.sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg fun r _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (Finset.prod_nonneg fun i _ => pow_nonneg (hq0 i) _)) (poissonPMF_nonneg hlam k)]
  congr 1
  rw [← Finset.sum_mul, ← Finset.sum_pow_eq_sum_piAntidiag, hq, one_pow, one_mul]

/-- **`lem:process`, the other direction**: pushing `Ttc.countLaw` forward along
`r ↦ ∑ᵢ rᵢ` returns the `Pois(lam)` it was built from. -/
theorem map_sum_countLaw {lam : ℝ} (hlam : 0 ≤ lam) {q : Fin l → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) :
    (countLaw lam q).map (fun r => ∑ i, r i) = poissonMeasure lam.toNNReal := by
  refine Measure.ext_of_singleton fun k => ?_
  rw [Measure.map_apply (Measurable.of_discrete) (MeasurableSet.of_discrete)]
  have hpre : (fun r : Fin l → ℕ => ∑ i, r i) ⁻¹' {k} = {r : Fin l → ℕ | ∑ i, r i = k} := rfl
  rw [hpre, countLaw_apply_sum hlam hq0 hq k, poissonMeasure_singleton,
    poissonPMF_def, Real.coe_toNNReal lam hlam]

/-- **Superposition, `L`-fold.** Independent `Pois(fᵢ)` counts sum to
`Pois(∑ᵢ fᵢ)` — obtained by reading `Ttc.countLaw_eq_pi` and
`Ttc.map_sum_countLaw` at `lam = ∑ᵢ fᵢ`, `qᵢ = fᵢ/lam`. This is what makes `|𝒳|`
itself Poisson, which is what the `Err` and `Noise` branches estimate. -/
theorem map_sum_pi_poisson {f : Fin l → ℝ} (hf : ∀ i, 0 ≤ f i) (hpos : 0 < ∑ i, f i) :
    (Measure.pi fun i => poissonMeasure (f i).toNNReal).map (fun r => ∑ i, r i)
      = poissonMeasure (∑ i, f i).toNNReal := by
  set lam : ℝ := ∑ i, f i with hlamdef
  have hlam : 0 ≤ lam := hpos.le
  have hq0 : ∀ i, 0 ≤ f i / lam := fun i => div_nonneg (hf i) hlam
  have hq : ∑ i, f i / lam = 1 := by
    rw [← Finset.sum_div, ← hlamdef]
    exact div_self hpos.ne'
  have hrate : ∀ i, (lam * (f i / lam)).toNNReal = (f i).toNNReal := by
    intro i
    congr 1
    field_simp
  have hpi : Measure.pi (fun i => poissonMeasure (f i).toNNReal)
      = countLaw lam (fun i => f i / lam) := by
    rw [countLaw_eq_pi hlam hq0 hq]
    congr 1
    funext i
    rw [hrate i]
  rw [hpi, map_sum_countLaw hlam hq0 hq]

/-! ## Thinning and superposition

The two operations the main loop performs on the invariant.
-/

/-- **Poisson thinning.** Keeping each of `Pois(lam)` items independently with
probability `q` leaves `Pois(q·lam)` — the `l = 2` case of `lem:process`, and
what line 33's `halve` does (at `q = ½`).

Stated as the first marginal of the two-cell count law: cell `0` is "kept", cell
`1` is "discarded". -/
theorem poisson_thinning {lam q : ℝ} (hlam : 0 ≤ lam) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (countLaw lam ![q, 1 - q]).map (Function.eval 0)
      = poissonMeasure (lam * q).toNNReal := by
  have hq0' : ∀ i : Fin 2, 0 ≤ (![q, 1 - q] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp <;> linarith
  have hsum : ∑ i : Fin 2, (![q, 1 - q] : Fin 2 → ℝ) i = 1 := by
    simp [Fin.sum_univ_two]
  have h := map_countLaw_eval hlam hq0' hsum 0
  simpa using h

/-- **Superposition.** Independent `Pois(lam₁)` and `Pois(lam₂)` counts add to
`Pois(lam₁+lam₂)` — what appending `GenerateSamples`' fresh counts to `𝒳` does.
Supplied by Mathlib. -/
theorem poisson_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℕ} {r s : ℝ≥0}
    (hX : HasLaw X (poissonMeasure r) μ) (hY : HasLaw Y (poissonMeasure s) μ)
    (hindep : IndepFun X Y μ) :
    HasLaw (X + Y) (poissonMeasure (r + s)) μ :=
  hindep.hasLaw_add_poissonMeasure hX hY

end Ttc

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Process.PoissonLaws
import Mathlib.Probability.Distributions.Binomial

/-!
# Poisson thinning, as a kernel

`Ttc.poisson_thinning` (`Process/PoissonLaws`) gives thinning as a *marginal* of
the two-cell count law. The induction over the main loop needs it in **kernel**
form instead: the loop holds a state whose count at each point is `Pois(θ)`, then
applies one thinning, which replaces that count by a `Binomial(·, ½)` draw. So what has
to be identified is the composite

  `Pois(λ)` followed by `Binomial(·, ½)`  =  `Pois(λ/2)`.

The computation is the classical one. Reindexing `k = j + m` and using
`C(j+m,j)/(j+m)! = 1/(j!·m!)` turns

  `∑_k C(k,j)·2^(−k)·e^(−λ)·λ^k/k!`

into `[e^(−λ)(λ/2)ʲ/j!] · ∑_m (λ/2)^m/m!`, and the remaining series is `e^(λ/2)`,
leaving `e^(−λ/2)(λ/2)ʲ/j!`. Only `q = ½` is treated — that is the only thinning
the algorithm performs.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-! ## The binomial mass at `q = ½` -/

/-- The binomial point mass of `j` successes out of `k`, at `q = ½`. -/
noncomputable def binHalfPMF (k j : ℕ) : ℝ := (k.choose j : ℝ) * (1 / 2) ^ k

theorem binHalfPMF_nonneg (k j : ℕ) : 0 ≤ binHalfPMF k j := by
  rw [binHalfPMF]; positivity

/-- Below the diagonal the binomial mass vanishes. -/
theorem binHalfPMF_eq_zero {k j : ℕ} (h : k < j) : binHalfPMF k j = 0 := by
  rw [binHalfPMF, Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul]

/-- **The factorial identity** `C(j+m, j)·j!·m! = (j+m)!`. -/
theorem choose_div_factorial (j m : ℕ) :
    ((j + m).choose j : ℝ) * ((j.factorial : ℝ) * (m.factorial : ℝ))
      = ((j + m).factorial : ℝ) := by
  have hsymm : (j + m).choose j = (j + m).choose m := by
    have h := Nat.choose_symm (Nat.le_add_left m j)
    simpa using h
  have h := Nat.add_choose_mul_factorial_mul_factorial j m
  rw [hsymm]
  exact_mod_cast by rw [← h]; ring

/-! ## The thinned series -/

/-- **The thinning identity, as a series.** For each `j`, summing the binomial
mass against the `Pois(λ)` mass returns the `Pois(λ/2)` mass. -/
theorem hasSum_binHalf_poisson (lam : ℝ) (j : ℕ) :
    HasSum (fun k => binHalfPMF k j * poissonPMF lam k) (poissonPMF (lam / 2) j) := by
  have hjf : (0:ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  set c : ℝ := Real.exp (-lam) * (lam / 2) ^ j / (j.factorial : ℝ) with hc
  -- each shifted term factors as `c * (λ/2)^m/m!`
  have hterm : ∀ m : ℕ, binHalfPMF (j + m) j * poissonPMF lam (j + m)
      = c * ((lam / 2) ^ m / (m.factorial : ℝ)) := by
    intro m
    have hmf : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
    have hjmf : (0:ℝ) < ((j + m).factorial : ℝ) := by exact_mod_cast (j + m).factorial_pos
    have hch := choose_div_factorial j m
    have hpow : (lam / 2) ^ (j + m) = lam ^ (j + m) * (1 / 2) ^ (j + m) := by
      rw [div_eq_mul_inv, mul_pow]; norm_num
    have hL : binHalfPMF (j + m) j * poissonPMF lam (j + m)
        = (((j + m).choose j : ℝ) / ((j + m).factorial : ℝ))
            * (Real.exp (-lam) * (lam / 2) ^ (j + m)) := by
      rw [binHalfPMF, poissonPMF_def, hpow]
      field_simp
      try ring
    have hR : (((j + m).choose j : ℝ) / ((j + m).factorial : ℝ))
        = 1 / ((j.factorial : ℝ) * (m.factorial : ℝ)) := by
      rw [eq_div_iff (by positivity), div_mul_eq_mul_div, div_eq_iff hjmf.ne']
      linarith [hch]
    rw [hL, hR, hc, pow_add]
    field_simp
    try ring
  -- the remaining series is `exp (λ/2)`
  have hexp : HasSum (fun m : ℕ => (lam / 2) ^ m / (m.factorial : ℝ)) (Real.exp (lam / 2)) := by
    have hs := (Real.summable_pow_div_factorial (lam / 2)).hasSum
    rwa [tsum_pow_div_factorial] at hs
  have hshift : HasSum (fun m : ℕ => binHalfPMF (j + m) j * poissonPMF lam (j + m))
      (c * Real.exp (lam / 2)) := by
    simpa only [hterm] using hexp.mul_left c
  -- `c · exp(λ/2) = poissonPMF (λ/2) j`
  have hval : c * Real.exp (lam / 2) = poissonPMF (lam / 2) j := by
    rw [hc, poissonPMF_def, div_mul_eq_mul_div]
    congr 1
    rw [mul_comm (Real.exp (-lam)) _, mul_assoc, ← Real.exp_add]
    rw [show -lam + lam / 2 = -(lam / 2) by ring]
    ring
  rw [hval] at hshift
  -- terms below `j` vanish, so the shifted sum is the whole sum
  have hinj : Function.Injective (fun m : ℕ => j + m) := fun a b h => by
    simpa using h
  have hvanish : ∀ k ∉ Set.range (fun m : ℕ => j + m),
      binHalfPMF k j * poissonPMF lam k = 0 := by
    intro k hk
    have hlt : k < j := by
      by_contra hge
      exact hk ⟨k - j, by show j + (k - j) = k; omega⟩
    rw [binHalfPMF_eq_zero hlt, zero_mul]
  exact (hinj.hasSum_iff hvanish).1 hshift

/-! ## The kernel identity

Mathlib's `ProbabilityTheory.binomial` supplies the thinning kernel; matching its
point masses to `Ttc.binHalfPMF` turns the series above into an identity of
measures.
-/

/-- The fair coin, as a point of the unit interval. -/
noncomputable def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] theorem coe_half : ((half : unitInterval) : ℝ) = 1 / 2 := rfl

/-- **Mathlib's binomial mass is `Ttc.binHalfPMF`** at `q = ½`. Both sides vanish
above the diagonal, and below it `(½)ᵏ(½)^(n−k) = (½)ⁿ`. -/
theorem binomial_half_singleton (n j : ℕ) :
    binomial n half {j} = ENNReal.ofReal (binHalfPMF n j) := by
  rw [binomial_singleton, binHalfPMF]
  rcases le_or_gt j n with hj | hj
  · congr 1
    rw [coe_half]
    have : ((1:ℝ) / 2) ^ j * (1 - 1 / 2) ^ (n - j) = (1 / 2) ^ n := by
      rw [show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [mul_assoc, this]
  · rw [Nat.choose_eq_zero_of_lt hj]
    simp

/-- **Poisson thinning, in kernel form.** Drawing `N ∼ Pois(λ)` and then keeping
each of the `N` items independently with probability `½` leaves `Pois(λ/2)`.

This is the form the main loop's induction consumes: one thinning replaces the count at
each lattice point by a `Binomial(·, ½)` draw. -/
theorem poisson_bind_binomial_half {lam : ℝ} (hlam : 0 ≤ lam) :
    (poissonMeasure lam.toNNReal).bind (fun k => binomial k half)
      = poissonMeasure (lam / 2).toNNReal := by
  refine Measure.ext_of_singleton fun j => ?_
  rw [Measure.bind_apply (MeasurableSet.of_discrete) (Measurable.of_discrete).aemeasurable,
    lintegral_countable']
  have hterm : ∀ k : ℕ, binomial k half {j} * poissonMeasure lam.toNNReal {k}
      = ENNReal.ofReal (binHalfPMF k j * poissonPMF lam k) := by
    intro k
    rw [binomial_half_singleton, poissonMeasure_singleton,
      ← ENNReal.ofReal_mul (binHalfPMF_nonneg k j), poissonPMF_def,
      Real.coe_toNNReal lam hlam]
  rw [tsum_congr hterm,
    ← ENNReal.ofReal_tsum_of_nonneg
      (fun k => mul_nonneg (binHalfPMF_nonneg k j) (poissonPMF_nonneg hlam k))
      (hasSum_binHalf_poisson lam j).summable,
    (hasSum_binHalf_poisson lam j).tsum_eq, poissonMeasure_singleton, poissonPMF_def,
    Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ lam / 2)]

/-! ## Thinning a whole count vector

The loop thins every lattice point at once, so what the induction needs is the
product form. It follows from the one-dimensional identity once series and finite
products can be exchanged — which in `ℝ≥0∞`, where everything is summable, is
Tonelli. Mathlib has no such lemma for a finite index, so it is proved here by
induction on the number of coordinates.
-/

/-- **Tonelli for a finite product of series in `ℝ≥0∞`**: summing a product of
coordinate functions over `Fin L → ℕ` is the product of the individual sums. -/
theorem tsum_pi_prod : ∀ {L : ℕ} (f : Fin L → ℕ → ℝ≥0∞),
    ∑' (k : Fin L → ℕ), ∏ i, f i (k i) = ∏ i, ∑' m, f i m := by
  intro L
  induction L with
  | zero =>
      intro f
      simp
  | succ L ih =>
      intro f
      rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => ℕ)).tsum_eq
        (fun k => ∏ i, f i (k i))]
      have hterm : ∀ p : ℕ × (Fin L → ℕ),
          (∏ i, f i ((Fin.consEquiv (fun _ : Fin (L + 1) => ℕ)) p i))
            = f 0 p.1 * ∏ i : Fin L, f i.succ (p.2 i) := by
        intro p
        rw [Fin.prod_univ_succ]
        rfl
      rw [tsum_congr hterm, ENNReal.tsum_prod']
      calc ∑' (a : ℕ) (k : Fin L → ℕ), f 0 a * ∏ i : Fin L, f i.succ (k i)
          = ∑' a : ℕ, f 0 a * ∑' (k : Fin L → ℕ), ∏ i : Fin L, f i.succ (k i) := by
            exact tsum_congr fun a => ENNReal.tsum_mul_left
        _ = (∑' a : ℕ, f 0 a) * ∏ i : Fin L, ∑' m, f i.succ m := by
            rw [ih (fun i => f i.succ), ENNReal.tsum_mul_right]
        _ = ∏ i, ∑' m, f i m := (Fin.prod_univ_succ (fun i => ∑' m, f i m)).symm

/-- **Poisson thinning of a whole count vector.** Thinning every coordinate
independently with probability `½` sends a product of `Pois(θᵢ)` to a product of
`Pois(θᵢ/2)`.

This is what one execution of line 33 or line 40 does to the invariant. -/
theorem pi_poisson_bind_binomial_half {L : ℕ} {θ : Fin L → ℝ} (hθ : ∀ i, 0 ≤ θ i) :
    (Measure.pi fun i => poissonMeasure (θ i).toNNReal).bind
        (fun k => Measure.pi fun i => binomial (k i) half)
      = Measure.pi fun i => poissonMeasure (θ i / 2).toNNReal := by
  refine Measure.ext_of_singleton fun r => ?_
  have hbox : ∀ w : Fin L → ℕ,
      ({w} : Set (Fin L → ℕ)) = Set.univ.pi (fun i => ({w i} : Set ℕ)) := by
    intro w
    ext v
    constructor
    · rintro rfl; intro i _; rfl
    · intro hv; funext i; exact hv i (Set.mem_univ i)
  rw [Measure.bind_apply (MeasurableSet.of_discrete) (Measurable.of_discrete).aemeasurable,
    lintegral_countable']
  have hterm : ∀ k : Fin L → ℕ,
      (Measure.pi fun i => binomial (k i) half) {r}
          * (Measure.pi fun i => poissonMeasure (θ i).toNNReal) {k}
        = ∏ i, (binomial (k i) half {r i} * poissonMeasure (θ i).toNNReal {k i}) := by
    intro k
    rw [hbox r, hbox k, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  rw [tsum_congr hterm,
    tsum_pi_prod (fun i m => binomial m half {r i} * poissonMeasure (θ i).toNNReal {m}),
    hbox r, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := poisson_bind_binomial_half (lam := θ i) (hθ i)
  rw [Measure.ext_iff_singleton] at h
  have hi := h (r i)
  rwa [Measure.bind_apply (MeasurableSet.of_discrete)
    (Measurable.of_discrete).aemeasurable, lintegral_countable'] at hi

/-! ## Replacing a block of coordinates

The other operation the loop performs on the invariant is `dropCovered` followed
by `GenerateSamples`: every point of `P(cᵢ)` has its count **deleted** and then
redrawn. So a point's count comes from exactly *one* insertion — the last cube
containing it — and the invariant never needs Poisson superposition, only
thinning and this block replacement.
-/

/-- **Replacing a block of coordinates.** If the counts on `B` are redrawn from a
fresh, independent product of Poissons and the rest are kept, the result is again
a product of Poissons — with the rate on `B` taken from the fresh draw.

This is `dropCovered` (delete on `B`) followed by `GenerateSamples` (redraw on
`B`), with independence supplied by the level indexing. -/
theorem pi_poisson_replace {L : ℕ} (B : Finset (Fin L)) (θ θ' : Fin L → ℝ) :
    ((Measure.pi fun i => poissonMeasure (θ i).toNNReal).prod
        (Measure.pi fun i => poissonMeasure (θ' i).toNNReal)).map
        (fun p i => if i ∈ B then p.2 i else p.1 i)
      = Measure.pi fun i => poissonMeasure (if i ∈ B then θ' i else θ i).toNNReal := by
  classical
  refine Measure.ext_of_singleton fun r => ?_
  have hbox : ∀ w : Fin L → ℕ,
      ({w} : Set (Fin L → ℕ)) = Set.univ.pi (fun i => ({w i} : Set ℕ)) := by
    intro w
    ext v
    constructor
    · rintro rfl; intro i _; rfl
    · intro hv; funext i; exact hv i (Set.mem_univ i)
  -- the preimage of `{r}` is a rectangle
  have hpre : (fun (p : (Fin L → ℕ) × (Fin L → ℕ)) i => if i ∈ B then p.2 i else p.1 i) ⁻¹' {r}
      = (Set.univ.pi fun i => if i ∈ B then (Set.univ : Set ℕ) else {r i}) ×ˢ
        (Set.univ.pi fun i => if i ∈ B then ({r i} : Set ℕ) else Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_univ_pi,
      funext_iff]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i ∈ B
        · simp [hi]
        · simpa [hi] using h i
      · by_cases hi : i ∈ B
        · simpa [hi] using h i
        · simp [hi]
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ B
      · simpa [hi] using h2 i
      · simpa [hi] using h1 i
  rw [Measure.map_apply (Measurable.of_discrete) (MeasurableSet.of_discrete), hpre,
    Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, hbox r, Measure.pi_pi,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ B <;> simp [hi]

/-! ## Insertion and thinning commute

The run inserts a cube's points at whatever level `p` happens to have reached and
then thins them along with everything else; the counterfactual level-`j` process
inserts them *already at level `j`*. These agree in law, and that is what makes
the level-`j` family of finding 15 well defined — the invariant does not depend on
when the halvings fall relative to the insertions.

Both sides reduce, by the two lemmas above, to the same product of Poissons.
-/

end Ttc

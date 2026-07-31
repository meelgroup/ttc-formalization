/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.RoundLaw
import Mathlib.Probability.Independence.Basic

/-!
# The moments of the rounding law on `ℤⁿ`

`Ttc.roundLaw p` (`Analysis/RoundLaw`) is the law of `rnd p` for a **fixed** `p` —
the side `claim:cl`(b) needs, as against the fixed-`x` side of (a)/(c). To feed it
to `Ttc.rounding_tail_bound` one needs three facts about the displacement
`Y k z = p k − z k`: it is bounded by `1`, it has mean zero, and its coordinates
are independent.

All three come from the one-dimensional law, which is a **two-point law**:
`tentInt a` puts mass `1 − {a}` on `⌊a⌋` and `{a}` on `⌊a⌋ + 1`
(`Ttc.tentInt_eq_two_point`). Every integral against it is therefore a two-term
sum (`Ttc.integral_tentInt`), which makes integrability free and mean zero a
one-line computation: `(1−t)·t + t·(t−1) = 0` (`Ttc.integral_tentInt_disp`).
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## The one-dimensional law is a two-point law -/

/-- **The rounding law in one coordinate is supported on `{⌊a⌋, ⌊a⌋+1}`**, with the
tent's two nonzero values as masses. This is the presentation every statement
below is proved from: it turns integrals against `tentInt` into two-term sums. -/
theorem tentInt_eq_two_point (a : ℝ) :
    tentInt a = ENNReal.ofReal (tent (a - ⌊a⌋)) • Measure.dirac ⌊a⌋
      + ENNReal.ofReal (tent (a - (⌊a⌋ + 1 : ℤ))) • Measure.dirac (⌊a⌋ + 1) := by
  have hd : ∀ x y : ℤ, (Measure.dirac x) ({y} : Set ℤ) = if x = y then 1 else 0 := by
    intro x y
    rw [Measure.dirac_apply]
    by_cases h : x = y <;> simp [h]
  refine Measure.ext_of_singleton fun m => ?_
  rw [tentInt_singleton, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, hd, hd]
  by_cases h1 : m = ⌊a⌋
  · subst h1
    rw [if_pos rfl, if_neg (by omega), mul_one, mul_zero, add_zero]
  · by_cases h2 : m = ⌊a⌋ + 1
    · subst h2
      rw [if_neg (by omega), if_pos rfl, mul_one, mul_zero, zero_add]
    · rw [if_neg (Ne.symm h1), if_neg (Ne.symm h2), mul_zero, mul_zero, add_zero,
        tent_eq_zero_of_ne_floor a m h1 h2, ENNReal.ofReal_zero]

/-- **Everything is integrable against a two-point law.** -/
theorem integrable_tentInt (a : ℝ) (f : ℤ → ℝ) : Integrable f (tentInt a) := by
  rw [tentInt_eq_two_point]
  refine integrable_add_measure.2 ⟨?_, ?_⟩ <;>
    exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

/-- **Every integral against `tentInt a` is a two-term sum.** -/
theorem integral_tentInt (a : ℝ) (f : ℤ → ℝ) :
    ∫ m, f m ∂(tentInt a)
      = tent (a - ⌊a⌋) * f ⌊a⌋ + tent (a - (⌊a⌋ + 1 : ℤ)) * f (⌊a⌋ + 1) := by
  have hint : ∀ (x : ℝ) (z : ℤ), Integrable f (ENNReal.ofReal x • Measure.dirac z) :=
    fun x z => (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [tentInt_eq_two_point, integral_add_measure (hint _ _) (hint _ _),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (tent_nonneg _), ENNReal.toReal_ofReal (tent_nonneg _),
    smul_eq_mul, smul_eq_mul]

/-- **`hmean`, one coordinate**: the rounding displacement `a − rnd a` has mean
zero. With `t = a − ⌊a⌋` the two-term sum is `(1−t)·t + t·(t−1) = 0`. -/
theorem integral_tentInt_disp (a : ℝ) : ∫ m : ℤ, (a - (m : ℝ)) ∂(tentInt a) = 0 := by
  have h1 : (0:ℝ) ≤ a - ⌊a⌋ := by linarith [Int.floor_le a]
  have h2 : a - ⌊a⌋ < 1 := by linarith [Int.lt_floor_add_one a]
  rw [integral_tentInt a (fun m => a - (m : ℝ))]
  have e1 : tent (a - ⌊a⌋) = 1 - (a - ⌊a⌋) := by
    rw [tent_of_abs_le (by rw [abs_of_nonneg h1]; linarith), abs_of_nonneg h1]
  have e2 : tent (a - (⌊a⌋ + 1 : ℤ)) = a - ⌊a⌋ := by
    have h3 : a - ((⌊a⌋ : ℝ) + 1) ≤ 0 := by linarith
    push_cast
    rw [tent_of_abs_le (by rw [abs_of_nonpos h3]; linarith), abs_of_nonpos h3]
    ring
  rw [e1, e2]
  push_cast
  ring

/-- **`hbdd`, one coordinate**: the displacement lies in `[−1,1]` almost surely,
because the tent vanishes outside. -/
theorem tentInt_eq_zero_of_forall (a : ℝ) {s : Set ℤ} (hs : ∀ m ∈ s, tent (a - m) = 0) :
    tentInt a s = 0 := by
  rw [tentInt_eq_two_point]
  have hz : ∀ z : ℤ, ENNReal.ofReal (tent (a - z)) * Measure.dirac z s = 0 := by
    intro z
    by_cases hz : z ∈ s
    · rw [hs z hz, ENNReal.ofReal_zero, zero_mul]
    · rw [Measure.dirac_apply, Set.indicator_of_notMem hz, mul_zero]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    hz, hz, add_zero]

theorem ae_tentInt_mem_Icc (a : ℝ) :
    ∀ᵐ m : ℤ ∂(tentInt a), a - (m : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  refine tentInt_eq_zero_of_forall a fun m hm => tent_eq_zero_of_one_le ?_
  simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le] at hm
  rcases hm with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-! ## The `n`-dimensional law: the three hypotheses of the tail bound

`Ttc.roundLaw p` is a `Measure.pi`, so each of the three transfers from the
one-dimensional statements above: the marginals are the `tentInt (p k)`
(`MeasureTheory.measurePreserving_eval`), and independence is
`ProbabilityTheory.iIndepFun_pi`.
-/

variable {n : ℕ}

/-- The rounding displacement in coordinate `k`, as a measurable function. -/
theorem measurable_latDisp (p : Space n) (k : Fin n) :
    Measurable (fun z : Fin n → ℤ => p k - (z k : ℝ)) :=
  measurable_const.sub (Measurable.of_discrete.comp (measurable_pi_apply k))

/-- The `k`-th marginal of `Ttc.roundLaw p` is the one-dimensional law
`Ttc.tentInt (p k)`. -/
theorem measurePreserving_roundLaw_eval (p : Space n) (k : Fin n) :
    MeasurePreserving (Function.eval k) (roundLaw p) (tentInt (p k)) :=
  measurePreserving_eval (fun i => tentInt (p i)) k

/-- **`hbdd`**: the displacement lies in `[−1,1]` in each coordinate, almost
surely under the fixed-`p` law. -/
theorem ae_latDisp_mem_Icc (p : Space n) (k : Fin n) :
    ∀ᵐ z ∂(roundLaw p), p k - (z k : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := ae_tentInt_mem_Icc (p k)
  rw [ae_iff] at h ⊢
  have hpre : {z : Fin n → ℤ | ¬ (p k - (z k : ℝ) ∈ Set.Icc (-1 : ℝ) 1)}
      = Function.eval k ⁻¹' {m : ℤ | ¬ (p k - (m : ℝ) ∈ Set.Icc (-1 : ℝ) 1)} := rfl
  rw [hpre, (measurePreserving_roundLaw_eval p k).measure_preimage
    ((Set.to_countable _).measurableSet).nullMeasurableSet]
  exact h

/-- **`hmean`**: each coordinate of the displacement has mean zero under the
fixed-`p` law. -/
theorem integral_latDisp_eq_zero (p : Space n) (k : Fin n) :
    ∫ z, (p k - (z k : ℝ)) ∂(roundLaw p) = 0 := by
  have h := MeasureTheory.integral_comp_eval (μ := fun i => tentInt (p i)) (i := k)
    (f := fun m : ℤ => p k - (m : ℝ)) (integrable_tentInt (p k) _).aestronglyMeasurable
  rw [roundLaw, h]
  exact integral_tentInt_disp (p k)

/-- **`hindep`**: the displacement's coordinates are independent under the
fixed-`p` law — immediate, since `Ttc.roundLaw` is a product measure. -/
theorem iIndepFun_latDisp (p : Space n) (A : Fin n → ℝ) :
    iIndepFun (fun (k : Fin n) (z : Fin n → ℤ) => A k * (p k - (z k : ℝ))) (roundLaw p) :=
  iIndepFun_pi (μ := fun i => tentInt (p i)) (X := fun i (m : ℤ) => A i * (p i - (m : ℝ)))
    (fun i => (integrable_tentInt (p i) _).aemeasurable)

/-! ## The tail bound on `ℤⁿ`

`Ttc.prodKernel_tail_bound` (`Analysis/ProdLaw`) is the same estimate in the
`p`-variable; this is its companion in the `z`-variable, which is what
`claim:cl`(b) sums over.
-/

set_option maxHeartbeats 1000000 in
/-- **The facet-crossing tail bound at a fixed `p`.** -/
theorem roundLaw_tail_bound (p : Space n) (A : Fin n → ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 < ∑ k, A k ^ 2) :
    (roundLaw p).real {z | κ * coeffNorm A ≤ ∑ k, A k * (p k - (z k : ℝ))}
      ≤ Real.exp (-κ ^ 2 / 2) :=
  rounding_tail_bound (fun (k : Fin n) (z : Fin n → ℤ) => p k - (z k : ℝ)) A
    (fun k => (measurable_latDisp p k).aemeasurable) (iIndepFun_latDisp p A)
    (fun k => ae_latDisp_mem_Icc p k) (fun k => integral_latDisp_eq_zero p k) hκ hA

set_option maxHeartbeats 1000000 in
/-- **The tail bound at the paper's `κ`**: at most `η/(4r)` per facet. -/
theorem roundLaw_tail_bound_kappa (p : Space n) (A : Fin n → ℝ)
    {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r) (hA : 0 < ∑ k, A k ^ 2) :
    (roundLaw p).real
        {z | (Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r)) * coeffNorm A
              ≤ ∑ k, A k * (p k - (z k : ℝ))} ≤ η / (4 * r) :=
  rounding_tail_bound_kappa (fun (k : Fin n) (z : Fin n → ℤ) => p k - (z k : ℝ)) A
    (fun k => (measurable_latDisp p k).aemeasurable) (iIndepFun_latDisp p A)
    (fun k => ae_latDisp_mem_Icc p k) (fun k => integral_latDisp_eq_zero p k) hη hη1 hr hA

end Ttc

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Rounding.TentSum

/-!
# The rounding law on `ℤⁿ` for a fixed point

`claim:cl`(a) and (c) fix a lattice point `x` and integrate over `p`; that is the
continuous side, handled by `Ttc.RoundingKernel.dispLaw` in `Rounding/ProdLaw`.

`claim:cl`(b) goes the other way: it fixes `p` and asks for the probability that
`rnd p` lands in `Q`, a sum over **lattice points**. This file supplies that side:
`Ttc.roundLaw p` is the law of `rnd p` on `ℤⁿ`, a product of the one-dimensional
two-point laws, with point masses `∏ᵢ tent(pᵢ − zᵢ)` — the same kernel, read in
the other variable.
-/

namespace Ttc

open MeasureTheory
open scoped ENNReal

/-- The tent is supported on two integers, hence summable. -/
theorem summable_tent (a : ℝ) : Summable (fun m : ℤ => tent (a - m)) := by
  classical
  refine summable_of_ne_finset_zero (s := ({⌊a⌋, ⌊a⌋ + 1} : Finset ℤ)) ?_
  intro m hm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact tent_eq_zero_of_ne_floor a m hm.1 hm.2

/-- **The one-dimensional rounding law**: `⌊a⌋ + Bernoulli(a − ⌊a⌋)`, presented as
the tent density against counting measure. -/
noncomputable def tentInt (a : ℝ) : Measure ℤ :=
  (Measure.count : Measure ℤ).withDensity (fun m => ENNReal.ofReal (tent (a - m)))

@[simp] theorem tentInt_singleton (a : ℝ) (m : ℤ) :
    tentInt a {m} = ENNReal.ofReal (tent (a - m)) := by
  rw [tentInt, withDensity_apply _ (measurableSet_singleton m)]
  simp [Measure.restrict_singleton, lintegral_dirac]

instance isProbabilityMeasure_tentInt (a : ℝ) : IsProbabilityMeasure (tentInt a) := by
  constructor
  rw [tentInt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg (fun m => tent_nonneg _) (summable_tent a),
    tsum_tent_eq_one, ENNReal.ofReal_one]

/-- **The rounding law on `ℤⁿ`** for a fixed `p`: independent coordinates. -/
noncomputable def roundLaw {n : ℕ} (p : Space n) : Measure (Fin n → ℤ) :=
  Measure.pi (fun i => tentInt (p i))

instance isProbabilityMeasure_roundLaw {n : ℕ} (p : Space n) :
    IsProbabilityMeasure (roundLaw p) := by
  rw [roundLaw]; infer_instance

/-- **The point masses are the kernel**: `Pr[rnd p = z] = ∏ᵢ tent(pᵢ − zᵢ)`. -/
theorem roundLaw_singleton {n : ℕ} (p : Space n) (z : Fin n → ℤ) :
    roundLaw p {z} = ENNReal.ofReal (∏ i, tent (p i - z i)) := by
  have hbox : ({z} : Set (Fin n → ℤ)) = Set.univ.pi (fun i => ({z i} : Set ℤ)) := by
    ext w
    constructor
    · rintro rfl; intro i _; rfl
    · intro hw
      funext i
      exact hw i (Set.mem_univ i)
  rw [roundLaw, hbox, Measure.pi_pi]
  simp only [tentInt_singleton]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => tent_nonneg _]

end Ttc

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.MeasTree
import Mathlib.Probability.Distributions.Binomial

/-!
# The quantile draws have their laws

The program draws a Poisson number and a `Binomial(N, 1/2)` number as the quantile of a
uniform number in `[0, 1]` (`poissonQuantile`, `binomialHalfQuantile`).  This file proves
that these draws have the Poisson and the binomial law (`uniformUnit_map_poissonQuantile`,
`uniformUnit_map_binomialHalfQuantile`).

Both are an instance of one fact: for a probability measure `μ` on `ℕ`, the least `k` with
`u ≤ μ(≤ k)` has law `μ` when `u` is uniform (`uniformUnit_map_natQuantile`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology ProbabilityTheory

namespace ttc.Tape

open ttc.Model.Operations

/-- **The quantile of a law on `ℕ`**: the least `k` with `u ≤ μ(≤ k)` (and `0` when there
is none). -/
def natQuantile (μ : Measure ℕ) (u : ℝ) : ℕ := sInf {k : ℕ | u ≤ μ.real (Iic k)}

section Quantile

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

theorem monotone_real_Iic : Monotone fun k : ℕ => μ.real (Iic k) := fun _ _ h =>
  measureReal_mono (Iic_subset_Iic.mpr h)

theorem tendsto_real_Iic : Tendsto (fun k : ℕ => μ.real (Iic k)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun k : ℕ => Iic k)
    fun _ _ h => Iic_subset_Iic.mpr h
  have hU : (⋃ k : ℕ, Iic k) = univ := iUnion_Iic
  rw [hU, measure_univ] at h
  have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  simpa [Function.comp_def, measureReal_def] using this

theorem exists_lt_real_Iic {u : ℝ} (hu : u < 1) : ∃ k : ℕ, u < μ.real (Iic k) :=
  ((tendsto_real_Iic μ).eventually (lt_mem_nhds hu)).exists

/-- Below `1`, the quantile is at most `k` exactly when `u ≤ μ(≤ k)`. -/
theorem natQuantile_le_iff {u : ℝ} (hu : u < 1) (k : ℕ) :
    natQuantile μ u ≤ k ↔ u ≤ μ.real (Iic k) := by
  obtain ⟨j, hj⟩ := exists_lt_real_Iic μ hu
  have hne : ({k : ℕ | u ≤ μ.real (Iic k)} : Set ℕ).Nonempty := ⟨j, hj.le⟩
  constructor
  · intro h
    exact (Nat.sInf_mem hne).trans (monotone_real_Iic μ h)
  · intro h
    exact Nat.sInf_le h

omit [IsProbabilityMeasure μ] in
theorem measurable_natQuantile : Measurable (natQuantile μ) :=
  measurable_nat_sInf fun _ => measurableSet_le measurable_id measurable_const

/-- **Inverse transform sampling on `ℕ`**: the quantile of a uniform number in `[0, 1]` has
law `μ`. -/
theorem uniformUnit_map_natQuantile : uniformUnit.map (natQuantile μ) = μ := by
  have hq := measurable_natQuantile μ
  refine (Measure.ext_of_Iic μ _ fun k => ?_).symm
  rw [Measure.map_apply hq measurableSet_Iic,
    Measure.restrict_apply (hq measurableSet_Iic)]
  have hF1 : μ.real (Iic k) ≤ 1 := measureReal_le_one
  have hF0 : 0 ≤ μ.real (Iic k) := measureReal_nonneg
  have key : ((natQuantile μ ⁻¹' Iic k) ∩ Icc 0 1) \ {1} = Icc 0 (μ.real (Iic k)) \ {1} := by
    ext u
    simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hk, h0, h1⟩, hne⟩
      exact ⟨⟨h0, (natQuantile_le_iff μ (lt_of_le_of_ne h1 hne) k).1 hk⟩, hne⟩
    · rintro ⟨⟨h0, hu⟩, hne⟩
      have h1 : u < 1 := lt_of_le_of_ne (hu.trans hF1) hne
      exact ⟨⟨(natQuantile_le_iff μ h1 k).2 hu, h0, h1.le⟩, hne⟩
  rw [← measure_sdiff_null (s := (natQuantile μ ⁻¹' Iic k) ∩ Icc 0 1) Real.volume_singleton, key,
    measure_sdiff_null Real.volume_singleton, Real.volume_Icc, sub_zero,
    ofReal_measureReal (measure_ne_top μ _)]

end Quantile

/-! ## Poisson -/

theorem poissonQuantile_eq (r : NNReal) : poissonQuantile r = natQuantile (poissonMeasure r) :=
  rfl

/-- **A Poisson draw has the Poisson law.** -/
theorem uniformUnit_map_poissonQuantile (r : NNReal) :
    uniformUnit.map (poissonQuantile r) = poissonMeasure r := by
  rw [poissonQuantile_eq]
  exact uniformUnit_map_natQuantile _

/-! ## Binomial -/

/-- The probability `1/2`. -/
def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

@[simp] theorem coe_half : (half : ℝ) = 1 / 2 := rfl

theorem binomial_half_real_Iic (N k : ℕ) :
    (binomial N half).real (Iic k) =
      ∑ i ∈ Finset.range (k + 1), ((N.choose i : ℝ) / 2 ^ N) := by
  have hset : (Iic k : Set ℕ) = ↑(Finset.range (k + 1)) := by
    ext i; simp
  rw [hset, ← sum_measureReal_singleton]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [binomial_real_singleton, coe_half]
  rcases le_or_gt i N with hi | hi
  · have : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [this, mul_assoc, ← pow_add, Nat.add_sub_cancel' hi, one_div, inv_pow, div_eq_mul_inv]
  · simp [Nat.choose_eq_zero_of_lt hi]

theorem binomialHalfQuantile_eq (N : ℕ) :
    binomialHalfQuantile N = natQuantile (binomial N half) := by
  funext u
  simp only [binomialHalfQuantile, natQuantile, binomial_half_real_Iic]

/-- **A `Binomial(N, 1/2)` draw has the binomial law.** -/
theorem uniformUnit_map_binomialHalfQuantile (N : ℕ) :
    uniformUnit.map (binomialHalfQuantile N) = binomial N half := by
  rw [binomialHalfQuantile_eq]
  exact uniformUnit_map_natQuantile _

end ttc.Tape

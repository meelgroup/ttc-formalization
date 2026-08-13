/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Probability.TV
import Arlib.MarkovChains.Continuous.SpeedyExactOnShrunken

/-!
# Mapping the speedy law to the target: Cousins–Vempala `lem:map-speedy-to-ball` at `δ ≤ 1/(2n)`

Placeholder module docstring; replaced when the file is complete.
-/

namespace Arlib

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## 1. Total variation under conditioning -/

/-- `a⁻¹ * a ≤ 1` in `ℝ≥0∞`, including the degenerate cases `a = 0` and `a = ⊤`. -/
theorem inv_mul_self_le_one (a : ℝ≥0∞) : a⁻¹ * a ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | h0
  · simp
  rcases eq_or_ne a ⊤ with rfl | htop
  · simp
  · exact le_of_eq (ENNReal.inv_mul_cancel h0 htop)

/-- **A conditional law never exceeds `1`**, for *any* measure and *any* pair of sets — no
measurability, no finiteness.  The degenerate cases are covered by the `ℝ≥0∞` conventions
`(0)⁻¹ = ⊤`, `(⊤)⁻¹ = 0` and `⊤ * 0 = 0`. -/
theorem condOn_le_one (μ : Measure Ω) (A S : Set Ω) : condOn μ A S ≤ 1 := by
  rw [condOn_def, Measure.smul_apply, smul_eq_mul]
  calc (μ A)⁻¹ * μ.restrict A S ≤ (μ A)⁻¹ * μ.restrict A univ :=
        mul_le_mul_right (measure_mono (subset_univ _)) _
    _ = (μ A)⁻¹ * μ A := by rw [Measure.restrict_apply_univ]
    _ ≤ 1 := inv_mul_self_le_one _

/-- Two conditional laws are always within total variation distance `1`.  Used for the
degenerate branch of `Arlib.tvLe_condOn_half`, where the hypothesis `ε` is already so large
that the conclusion is vacuous. -/
theorem tvLe_condOn_one (μ ν : Measure Ω) (A : Set Ω) :
    TVLe (condOn μ A) (condOn ν A) 1 := fun S _ =>
  ⟨le_add_left (condOn_le_one μ A S), le_add_left (condOn_le_one ν A S)⟩

/-- The real-arithmetic core of `Arlib.TVLe.condOn`.

With `a ≤ b + e` (numerators close), `q ≤ p + e` (denominators close), `b ≤ q`, and both
denominators bounded below by `M > 0`,

    a / p ≤ b / q + 2 * e / M.

The proof is the exact computation
`a/p − b/q = (q(a−b) + b(q−p)) / (pq) ≤ (qe + qe)/(pq) = 2e/p ≤ 2e/M`. -/
theorem div_le_div_add_two_mul_div {a b p q e M : ℝ} (hM : 0 < M) (hMp : M ≤ p)
    (hMq : M ≤ q) (hb : 0 ≤ b) (hbq : b ≤ q) (hab : a ≤ b + e) (hqp : q ≤ p + e)
    (he : 0 ≤ e) : a / p ≤ b / q + 2 * e / M := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le hM hMq
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hM hMp
  set r : ℝ := b / q with hrdef
  have hrq : r * q = b := div_mul_cancel₀ b hq0.ne'
  have hr0 : 0 ≤ r := div_nonneg hb hq0.le
  have hr1 : r ≤ 1 := (div_le_one hq0).2 hbq
  rw [div_le_iff₀ hp0]
  have hexp : (r + 2 * e / M) * p = r * p + 2 * e / M * p := by ring
  rw [hexp]
  have h1 : r * q ≤ r * p + r * e := by nlinarith [mul_nonneg hr0 (by linarith : (0:ℝ) ≤ p + e - q)]
  have h2 : r * e ≤ e := by nlinarith
  have h3 : 2 * e / M * M = 2 * e := div_mul_cancel₀ _ hM.ne'
  have hcoef : (0 : ℝ) ≤ 2 * e / M := by positivity
  have h4 : 2 * e / M * M ≤ 2 * e / M * p := by nlinarith
  linarith

/-- One direction of `Arlib.TVLe.condOn`, isolated so that the symmetric statement can apply
it twice with the roles of the two measures exchanged. -/
theorem condOn_le_condOn_add {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A S : Set Ω} (hA : MeasurableSet A) (hS : MeasurableSet S) {ε m : ℝ≥0∞}
    (hεtop : ε ≠ ⊤) (hm : 0 < m) (hmtop : m ≠ ⊤) (hμA : m ≤ μ A) (hνA : m ≤ ν A)
    (h1 : μ (S ∩ A) ≤ ν (S ∩ A) + ε) (h2 : ν A ≤ μ A + ε) :
    condOn μ A S ≤ condOn ν A S + 2 * ε / m := by
  rw [condOn_apply μ hA hS, condOn_apply ν hA hS]
  have hpne : μ A ≠ ⊤ := measure_ne_top μ A
  have hqne : ν A ≠ ⊤ := measure_ne_top ν A
  have hane : μ (S ∩ A) ≠ ⊤ := measure_ne_top μ _
  have hbne : ν (S ∩ A) ≠ ⊤ := measure_ne_top ν _
  have hp0 : μ A ≠ 0 := (lt_of_lt_of_le hm hμA).ne'
  have hq0 : ν A ≠ 0 := (lt_of_lt_of_le hm hνA).ne'
  have hL : μ (S ∩ A) / μ A ≠ ⊤ := ENNReal.div_ne_top hane hp0
  have hquot : ν (S ∩ A) / ν A ≠ ⊤ := ENNReal.div_ne_top hbne hq0
  have hslack : 2 * ε / m ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) hεtop) hm.ne'
  have hR : ν (S ∩ A) / ν A + 2 * ε / m ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hquot, hslack⟩
  rw [← ENNReal.toReal_le_toReal hL hR, ENNReal.toReal_add hquot hslack,
    ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_mul]
  refine div_le_div_add_two_mul_div (M := m.toReal) (ENNReal.toReal_pos hm.ne' hmtop)
    (ENNReal.toReal_mono hpne hμA) (ENNReal.toReal_mono hqne hνA) ENNReal.toReal_nonneg
    (ENNReal.toReal_mono hqne (measure_mono inter_subset_right)) ?_ ?_ ENNReal.toReal_nonneg
  · have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hbne, hεtop⟩) h1
    rwa [ENNReal.toReal_add hbne hεtop] at this
  · have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hpne, hεtop⟩) h2
    rwa [ENNReal.toReal_add hpne hεtop] at this

/-- **Total variation under conditioning.**

If `μ` and `ν` are within total variation distance `ε` and both put mass at least `m > 0`
on the event `A`, then the conditional laws `condOn μ A` and `condOn ν A` are within
`2ε/m`.

The constant is sharp for this argument: the numerator error contributes `ε/m` and the
denominator error contributes another `ε/m`. -/
theorem TVLe.condOn {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ε : ℝ≥0∞}
    (h : TVLe μ ν ε) {A : Set Ω} (hA : MeasurableSet A) {m : ℝ≥0∞} (hm : 0 < m)
    (hμA : m ≤ μ A) (hνA : m ≤ ν A) :
    TVLe (Arlib.condOn μ A) (Arlib.condOn ν A) (2 * ε / m) := by
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ A) hμA
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · have : 2 * (⊤ : ℝ≥0∞) / m = ⊤ := by
      rw [ENNReal.mul_top (by simp), ENNReal.top_div_of_ne_top hmtop]
    rw [this]
    exact tvLe_top _ _
  intro S hS
  exact ⟨condOn_le_condOn_add hA hS hεtop hm hmtop hμA hνA
      (h.left (hS.inter hA)) (h.right hA),
    condOn_le_condOn_add hA hS hεtop hm hmtop hνA hμA
      (h.right (hS.inter hA)) (h.left hA)⟩

/-- **Total variation under conditioning on a `1/2`-mass event: the constant is `8ε`.**

This is step 1 of Cousins–Vempala's `lem:map-speedy-to-ball`.  If the sampler's law `μ` is
within `ε` of the target `ν` and `ν` puts at least half its mass on `A`, then conditioning
both on `A` costs a factor `8`:

    TVLe (condOn μ A) (condOn ν A) (8 * ε).

No smallness hypothesis on `ε` is needed: for `ε > 1/4` the bound `8ε > 1` is already
vacuous (`Arlib.tvLe_condOn_one`), and for `ε ≤ 1/4` the hypothesis forces
`μ A ≥ 1/2 − ε ≥ 1/4`, so `Arlib.TVLe.condOn` applies with `m = 1/4` and `2ε/(1/4) = 8ε`. -/
theorem tvLe_condOn_half {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ≥0∞} (h : TVLe μ ν ε) {A : Set Ω} (hA : MeasurableSet A)
    (hνA : ENNReal.ofReal (1 / 2) ≤ ν A) :
    TVLe (condOn μ A) (condOn ν A) (8 * ε) := by
  have hofReal4 : ENNReal.ofReal (1 / 4) = (4 : ℝ≥0∞)⁻¹ := by
    rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      show ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) by simp]
  have hofReal8 : ENNReal.ofReal (1 / 8) = (8 : ℝ≥0∞)⁻¹ := by
    rw [show (1 : ℝ) / 8 = (8 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      show ENNReal.ofReal (8 : ℝ) = (8 : ℝ≥0∞) by simp]
  have hq : ENNReal.ofReal (1 / 4) ≤ ν A :=
    le_trans (ENNReal.ofReal_le_ofReal (by norm_num)) hνA
  rcases le_or_gt ε (ENNReal.ofReal (1 / 4)) with hε | hε
  · have hp : ENNReal.ofReal (1 / 4) ≤ μ A := by
      refine ENNReal.le_of_add_le_add_right
        (show ENNReal.ofReal (1 / 4) ≠ (⊤ : ℝ≥0∞) from ENNReal.ofReal_ne_top) ?_
      calc ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4)
          = ENNReal.ofReal (1 / 2) := by
            rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
        _ ≤ ν A := hνA
        _ ≤ μ A + ε := h.right hA
        _ ≤ μ A + ENNReal.ofReal (1 / 4) := by gcongr
    have key := h.condOn hA (m := ENNReal.ofReal (1 / 4))
      (ENNReal.ofReal_pos.2 (by norm_num)) hp hq
    have hconst : 2 * ε / ENNReal.ofReal (1 / 4) = 8 * ε := by
      rw [hofReal4, ENNReal.div_eq_inv_mul, inv_inv]
      ring
    rwa [hconst] at key
  · refine (tvLe_condOn_one μ ν A).mono ?_
    calc (1 : ℝ≥0∞) = 8 * ENNReal.ofReal (1 / 8) := by
          rw [hofReal8, ENNReal.mul_inv_cancel (by simp) (by simp)]
      _ ≤ 8 * ε := by
          gcongr
          exact le_of_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by norm_num)) hε)

end Arlib

section AxiomCheck

#print axioms Arlib.condOn_le_one
#print axioms Arlib.TVLe.condOn
#print axioms Arlib.tvLe_condOn_half

end AxiomCheck

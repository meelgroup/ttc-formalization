/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Probability.PoissonMean
import Ttc.Coupling.Family

/-!
# What the thinning passes cost, in expectation

`Ttc.thinPassCost` charges one coin per copy of the sketch at each pass of `alg:ttc`'s two
`while` loops.  The pass *count* has no deterministic bound, so the charge is paid for by
the sketch shrinking instead: level `j+1`'s counts are a `Binomial(·, ½)` thinning of level
`j`'s (`Ttc.thinKernel`), so the level-`j` count at one lattice point has mean `θₛ/2ʲ` and
the sum over levels is geometric.

This file is the first half of that: the mean of one level's count.
`DnfstreamXt/Analysis/ThinMean.lean` is the corresponding file there, and carries the same
fact in the `PMF` setting.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L : ℕ}

/-- **The level-`j` count at one lattice point has mean `θₛ/2ʲ`.**

`Ttc.map_trajLaw_eval` says the level-`j` marginal is `Ttc.levelLaw θ j`, which is a product
of Poissons at rate `θᵢ/2ʲ`; the coordinate marginal of a product is the factor, and
`Ttc.lintegral_poissonMeasure_id` evaluates it. -/
theorem lintegral_trajLaw_eval_apply {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (j : ℕ)
    (s : Fin L) :
    (∫⁻ ω, ((ω j s : ℕ) : ℝ≥0∞) ∂trajLaw θ) = ENNReal.ofReal (θ s / 2 ^ j) := by
  have hmeas : Measurable fun ω : ℕ → (Fin L → ℕ) ↦ ω j := by fun_prop
  have h1 : (∫⁻ ω, ((ω j s : ℕ) : ℝ≥0∞) ∂trajLaw θ)
      = ∫⁻ k, ((k s : ℕ) : ℝ≥0∞) ∂((trajLaw θ).map fun ω ↦ ω j) := by
    rw [lintegral_map (by fun_prop) hmeas]
  rw [h1, map_trajLaw_eval hθ j]
  have h2 : (∫⁻ k, ((k s : ℕ) : ℝ≥0∞) ∂levelLaw θ j)
      = ∫⁻ m, ((m : ℕ) : ℝ≥0∞) ∂((levelLaw θ j).map (Function.eval s)) := by
    rw [lintegral_map (by fun_prop) (by fun_prop)]
  rw [h2, levelLaw,
    (measurePreserving_eval (fun i ↦ poissonMeasure (θ i / 2 ^ j).toNNReal) s).map_eq,
    lintegral_poissonMeasure_id]
  rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal]
  exact div_nonneg (hθ s) (by positivity)

/-- **What one thinning pass costs, in expectation.**

`Ttc.trajThin` keeps `min (ω j s) (count (pt s) X)` copies of each lattice point, so the
surviving sketch is no larger than the level-`j` count vector, whose mean is `θₛ/2ʲ`.  The
`min` is what makes this an inequality rather than an equality, and it is all the cost
bound needs. -/
theorem lintegral_card_trajThin_le {n : ℕ} {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (j : ℕ)
    (pt : Fin L → Space n) (X : Multiset (Space n)) :
    (∫⁻ ω, (Multiset.card (trajThin pt (ω j) X) : ℝ≥0∞) ∂trajLaw θ)
      ≤ ∑ s, ENNReal.ofReal (θ s / 2 ^ j) := by
  have hcard : ∀ ω : ℕ → (Fin L → ℕ),
      (Multiset.card (trajThin pt (ω j) X) : ℝ≥0∞) ≤ ∑ s, ((ω j s : ℕ) : ℝ≥0∞) := by
    intro ω
    rw [trajThin, card_toMultiset, Nat.cast_sum]
    exact Finset.sum_le_sum fun s _ ↦ by
      exact_mod_cast Nat.cast_le.2 (min_le_left (ω j s) (Multiset.count (pt s) X))
  refine le_trans (lintegral_mono hcard) (le_of_eq ?_)
  rw [lintegral_finsetSum _ (fun s _ ↦ by fun_prop)]
  exact Finset.sum_congr rfl fun s _ ↦ lintegral_trajLaw_eval_apply hθ j s

/-! ## The geometric sum

The exit level of the overflow loop is *random*, so the thinning charge is bounded by the
sum over **all** levels from the entry level up, which is geometric. -/

/-- `∑' k, a/2ᵏ = 2a`, in `ℝ≥0∞`. -/
theorem tsum_ofReal_geom_half {a : ℝ} (ha : 0 ≤ a) :
    (∑' k : ℕ, ENNReal.ofReal (a / 2 ^ k)) = ENNReal.ofReal (2 * a) := by
  have hgeom : HasSum (fun k : ℕ ↦ a * ((1 : ℝ) / 2) ^ k) (a * (1 - (1:ℝ)/2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left a
  have hval : a * (1 - (1:ℝ)/2)⁻¹ = 2 * a := by norm_num; ring
  rw [hval] at hgeom
  have hrw : ∀ k : ℕ, a / 2 ^ k = a * ((1 : ℝ) / 2) ^ k := by
    intro k; rw [div_pow, one_pow]; ring
  simp only [hrw]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) hgeom.summable,
    hgeom.tsum_eq]

/-- **The thinning charge of every pass from level `j₀` on, in expectation.**

Bounded by `2 · ∑ₛ θₛ/2^{j₀}` — twice the level-`j₀` rate — whatever the exit level.  This is
the geometric series that pays for the overflow loop, and the reason its pass count never
has to be bounded.  `DnfstreamXt/Analysis/GeomHalfSum.lean` is the same step there. -/
theorem lintegral_tsum_card_trajThin_le {n : ℕ} {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s)
    (j₀ : ℕ) (pt : Fin L → Space n) (X : Multiset (Space n)) :
    (∫⁻ ω, ∑' k : ℕ, (Multiset.card (trajThin pt (ω (j₀ + k)) X) : ℝ≥0∞) ∂trajLaw θ)
      ≤ ∑ s, ENNReal.ofReal (2 * (θ s / 2 ^ j₀)) := by
  have hmeas : ∀ k : ℕ, Measurable
      (fun ω : ℕ → (Fin L → ℕ) ↦
        ((Multiset.card (trajThin pt (ω (j₀ + k)) X) : ℕ) : ℝ≥0∞)) :=
    fun k ↦ (Measurable.of_discrete
      (f := fun v : Fin L → ℕ ↦ ((Multiset.card (trajThin pt v X) : ℕ) : ℝ≥0∞))).comp
      (measurable_pi_apply (j₀ + k))
  rw [lintegral_tsum (fun k ↦ (hmeas k).aemeasurable)]
  refine le_trans (ENNReal.tsum_le_tsum fun k ↦
    lintegral_card_trajThin_le hθ (j₀ + k) pt X) (le_of_eq ?_)
  have h1 : ∀ k : ℕ, (∑ s, ENNReal.ofReal (θ s / 2 ^ (j₀ + k)))
      = ∑' s : Fin L, ENNReal.ofReal (θ s / 2 ^ (j₀ + k)) := fun k ↦ (tsum_fintype _).symm
  simp only [h1]
  rw [ENNReal.tsum_comm, tsum_fintype]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hrw : ∀ k : ℕ, θ s / 2 ^ (j₀ + k) = (θ s / 2 ^ j₀) / 2 ^ k := by
    intro k; rw [pow_add]; field_simp
  simp only [hrw]
  exact tsum_ofReal_geom_half (div_nonneg (hθ s) (by positivity))

#print axioms lintegral_trajLaw_eval_apply
#print axioms lintegral_card_trajThin_le
#print axioms lintegral_tsum_card_trajThin_le

end Ttc

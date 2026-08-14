/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.InhomogeneousMarkov
import Arlib.Convexity.GaussianCooling.WarmSpeedy
import Ttc.Volume.CVCorrectedParameters

/-!
# The joint-law dependence seam for sequential cooling

The available Gaussian mixing theorems control the distribution obtained from
a specified warm *measure*.  Such a marginal TV statement does not by itself
make the next sample independent of the realized past.  This file states the
minimal joint-law hypothesis that does suffice, pushes it through an
inhomogeneous Markov trajectory, and records the exact counterexample to the
marginal-only inference.

Thus the missing operational input is now a precise theorem: the joint law of
`(history,next)` must be TV-close to `historyLaw.prod target`.  The existing
pointwise theorem in `InhomogeneousMarkov` implies this kind of control, but the
repository's warm-start mixing theorem does not currently do so.
-/

namespace Ttc.CVSequentialDependence

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.GaussianCooling
open scoped ENNReal

/-- Joint TV closeness to a product with the actual past marginal is sufficient
for the paper's event-form dependence coefficient.  Unlike the pointwise
kernel theorem, this hypothesis is only about the joint law actually used by
the algorithm. -/
theorem nuIndep_of_jointTV_product
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {τ : Measure B} [IsProbabilityMeasure τ]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    {ν : ENNReal} (hν : ν ≠ ⊤)
    (hjoint : TVLe (μ.map fun ω => (X ω, Y ω)) ((μ.map X).prod τ) ν) :
    NuIndep μ X Y ν.toReal := by
  refine nuIndep_of_approx_product (q := fun S => τ.real S) hX hY ?_
  intro S T hS hT
  let pair : Ω → A × B := fun ω => (X ω, Y ω)
  have hpair : Measurable pair := hX.prodMk hY
  have hrect : MeasurableSet (S ×ˢ T) := hS.prod hT
  have htv := hjoint.abs_measureReal_sub_le hν hrect
  have hpre : pair ⁻¹' (S ×ˢ T) = X ⁻¹' S ∩ Y ⁻¹' T := by
    ext ω
    simp [pair]
  have hmapX : (μ.map X).real S = μ.real (X ⁻¹' S) := by
    change ((μ.map X) S).toReal = (μ (X ⁻¹' S)).toReal
    rw [Measure.map_apply hX hS]
  rw [Measure.real, Measure.map_apply hpair hrect, hpre,
    measureReal_prod_prod, hmapX] at htv
  exact htv

/-- Joint-law version of the inhomogeneous Markov bridge.  This removes the
too-strong `∀ x` premise from the API: only the trajectory's actual
`(history,next)` law is constrained. -/
theorem nuIndep_history_next_of_jointTV
    {E : Type*} [MeasurableSpace E]
    (P : ℕ → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (τ : Measure E) [IsProbabilityMeasure τ] (i : ℕ) {ν : ENNReal}
    (hν : ν ≠ ⊤)
    (hjoint : TVLe
      ((inhomogeneousPathMeasure P μ).map
        (fun omega => (Preorder.frestrictLe i omega, omega (i + 1))))
      (((inhomogeneousPathMeasure P μ).map (Preorder.frestrictLe i)).prod τ) ν) :
    NuIndep (inhomogeneousPathMeasure P μ) (Preorder.frestrictLe i)
      (fun omega => omega (i + 1)) ν.toReal := by
  apply nuIndep_of_jointTV_product
    (μ := inhomogeneousPathMeasure P μ) (τ := τ)
    (X := Preorder.frestrictLe i) (Y := fun omega => omega (i + 1))
    (Preorder.measurable_frestrictLe i) (measurable_pi_apply (i + 1)) hν
  exact hjoint

/-- The exact plug-in form needed by corrected `lem:accuracy`: measurable
statistics of the realized history and next state inherit the same coefficient.
-/
theorem nuIndep_historyStatistic_nextStatistic_of_jointTV
    {E : Type*} [MeasurableSpace E]
    (P : ℕ → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (τ : Measure E) [IsProbabilityMeasure τ] (i : ℕ) {ν : ENNReal}
    (hν : ν ≠ ⊤)
    (hjoint : TVLe
      ((inhomogeneousPathMeasure P μ).map
        (fun omega => (Preorder.frestrictLe i omega, omega (i + 1))))
      (((inhomogeneousPathMeasure P μ).map (Preorder.frestrictLe i)).prod τ) ν)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (f : (Finset.Iic i → E) → A) (g : E → B)
    (hf : Measurable f) (hg : Measurable g) :
    NuIndep (inhomogeneousPathMeasure P μ)
      (fun omega => f (Preorder.frestrictLe i omega))
      (fun omega => g (omega (i + 1))) ν.toReal :=
  (nuIndep_history_next_of_jointTV P μ τ i hν hjoint).comp hf hg

/-- Exact obstruction: even equality of the next marginal with its target does
not imply independence from the past.  Taking `X=Y=id`, any event of probability
one half has dependence defect `1/4`, although `Y`'s marginal is TV distance
zero from `μ`.
-/
theorem marginalTV_zero_not_sufficient
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) (hhalf : μ.real S = 1 / 2) :
    TVLe (μ.map id) μ 0 ∧ ¬ NuIndep μ id id 0 := by
  constructor
  · rw [Measure.map_id]
    exact TVLe.refl μ
  · intro hindep
    have h := hindep S S hS hS
    change |μ.real (S ∩ S) - μ.real S * μ.real S| ≤ 0 at h
    rw [Set.inter_self, hhalf] at h
    norm_num at h

/-! ## LV2 Lemma 4.3: conditioning on a large event -/

/-- The event-conditioning core of LV2 Lemma 4.3.  It is enough to control
the conditional law for events of probability at least one half.  For a
smaller event one applies the premise to its complement; the two dependence
defects are exact negatives.

This form compares the conditional law directly to the actual next marginal,
and therefore loses no constant. -/
theorem nuIndep_of_largeEvent_conditionalMarginal
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → A} {Y : Ω → B} (hH : Measurable H) (hY : Measurable Y)
    {ν : ℝ} (hlarge : ∀ S : Set A, ∀ T : Set B,
      MeasurableSet S → MeasurableSet T →
      1 / 2 ≤ μ.real (H ⁻¹' S) →
      |μ.real (H ⁻¹' S ∩ Y ⁻¹' T) -
        μ.real (H ⁻¹' S) * μ.real (Y ⁻¹' T)| ≤ ν) :
    NuIndep μ H Y ν := by
  intro S T hS hT
  by_cases hp : 1 / 2 ≤ μ.real (H ⁻¹' S)
  · exact hlarge S T hS hT hp
  · have hHS : MeasurableSet (H ⁻¹' S) := hH hS
    have hYT : MeasurableSet (Y ⁻¹' T) := hY hT
    have hcomp : H ⁻¹' Sᶜ = (H ⁻¹' S)ᶜ := rfl
    have hpcomp : 1 / 2 ≤ μ.real (H ⁻¹' Sᶜ) := by
      rw [hcomp, measureReal_compl hHS, probReal_univ]
      linarith
    have hc := hlarge Sᶜ T hS.compl hT hpcomp
    have hsplit : μ.real (H ⁻¹' S ∩ Y ⁻¹' T) +
        μ.real ((H ⁻¹' S)ᶜ ∩ Y ⁻¹' T) = μ.real (Y ⁻¹' T) :=
      measureReal_inter_add_compl_inter hHS hYT
    rw [hcomp] at hc
    rw [measureReal_compl hHS, probReal_univ] at hc
    rw [abs_le] at hc ⊢
    constructor <;> nlinarith [hc.1, hc.2, hsplit]

/-- Source-faithful target-law form.  Suppose every event-conditioned next law
for an event of mass at least one half is `ν`-close to the target, in the
scaled rectangle form delivered by a TV bound.  The unconditioned event is one
of those events, so the actual next marginal is also `ν`-close to the target.
Consequently dependence is at most `2ν`.

To obtain a requested coefficient `δ`, run the sampler at TV accuracy `δ/2`.
-/
theorem nuIndep_of_largeEvent_approxTarget
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → A} {Y : Ω → B} (hH : Measurable H) (hY : Measurable Y)
    {ν : ℝ} {q : Set B → ℝ} (_hν : 0 ≤ ν)
    (hlarge : ∀ S : Set A, ∀ T : Set B,
      MeasurableSet S → MeasurableSet T →
      1 / 2 ≤ μ.real (H ⁻¹' S) →
      |μ.real (H ⁻¹' S ∩ Y ⁻¹' T) - μ.real (H ⁻¹' S) * q T| ≤ ν) :
    NuIndep μ H Y (2 * ν) := by
  apply nuIndep_of_largeEvent_conditionalMarginal hH hY
  intro S T hS hT hp
  have hSbound := hlarge S T hS hT hp
  have huniv := hlarge Set.univ T MeasurableSet.univ hT (by
    rw [Set.preimage_univ, probReal_univ]
    norm_num)
  have huniv' : |μ.real (Y ⁻¹' T) - q T| ≤ ν := by
    simpa [probReal_univ] using huniv
  have hp0 : 0 ≤ μ.real (H ⁻¹' S) := measureReal_nonneg
  have hp1 : μ.real (H ⁻¹' S) ≤ 1 := by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
  have hmul : μ.real (H ⁻¹' S) * |q T - μ.real (Y ⁻¹' T)| ≤ ν := by
    calc
      _ = μ.real (H ⁻¹' S) * |μ.real (Y ⁻¹' T) - q T| := by
        rw [abs_sub_comm]
      _ ≤ 1 * ν := mul_le_mul hp1 huniv' (abs_nonneg _) (by norm_num)
      _ = ν := one_mul ν
  calc
    |μ.real (H ⁻¹' S ∩ Y ⁻¹' T) -
        μ.real (H ⁻¹' S) * μ.real (Y ⁻¹' T)| =
      |(μ.real (H ⁻¹' S ∩ Y ⁻¹' T) - μ.real (H ⁻¹' S) * q T) +
        μ.real (H ⁻¹' S) * (q T - μ.real (Y ⁻¹' T))| := by ring_nf
    _ ≤ |μ.real (H ⁻¹' S ∩ Y ⁻¹' T) - μ.real (H ⁻¹' S) * q T| +
        |μ.real (H ⁻¹' S) * (q T - μ.real (Y ⁻¹' T))| := abs_add_le _ _
    _ ≤ ν + ν := by
      rw [abs_mul, abs_of_nonneg hp0]
      exact add_le_add hSbound hmul
    _ = 2 * ν := by ring

/-- History lifting of the LV2 event-conditioned argument.  This is the exact
shape required for `U_i` and `V_(i+1)`: take `H` to be the restricted history,
then use `NuIndep.comp` for the two statistics. -/
theorem nuIndep_historyStatistics_of_largeEvent_approxTarget
    {E : Type*} [MeasurableSpace E]
    (P : ℕ → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (μ : Measure E) [IsProbabilityMeasure μ] (i : ℕ)
    {ν : ℝ} {q : Set E → ℝ} (hν : 0 ≤ ν)
    (hlarge : ∀ S : Set (Finset.Iic i → E), ∀ T : Set E,
      MeasurableSet S → MeasurableSet T →
      1 / 2 ≤ (inhomogeneousPathMeasure P μ).real
        (Preorder.frestrictLe i ⁻¹' S) →
      |(inhomogeneousPathMeasure P μ).real
          (Preorder.frestrictLe i ⁻¹' S ∩ (fun omega => omega (i + 1)) ⁻¹' T) -
        (inhomogeneousPathMeasure P μ).real
          (Preorder.frestrictLe i ⁻¹' S) * q T| ≤ ν)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (f : (Finset.Iic i → E) → A) (g : E → B)
    (hf : Measurable f) (hg : Measurable g) :
    NuIndep (inhomogeneousPathMeasure P μ)
      (fun omega => f (Preorder.frestrictLe i omega))
      (fun omega => g (omega (i + 1))) (2 * ν) := by
  have hbase := nuIndep_of_largeEvent_approxTarget
    (μ := inhomogeneousPathMeasure P μ)
    (H := Preorder.frestrictLe i) (Y := fun omega => omega (i + 1))
    (Preorder.measurable_frestrictLe i) (measurable_pi_apply (i + 1)) hν hlarge
  exact hbase.comp hf hg

/-- Generic event-conditioned sampler theorem in the exact LV2 Lemma 4.3
shape. `nextGiven S` is the output law when the history start is conditioned on
`H ∈ S`; `hfactor` is the elementary conditional-probability identity.  Mixing
is required only for events with mass at least one half, precisely the events
whose conditioned starts are at most `2`-warm relative to the original start.

The resulting coefficient is `2 * eps`: one `eps` compares the conditioned
law to `tau`, and the unconditioned case `S=univ` supplies the second `eps`
between the actual next marginal and `tau`. -/
theorem nuIndep_of_largeEvent_conditionedSampler
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {τ : Measure B} [IsProbabilityMeasure τ]
    {H : Ω → A} {Y : Ω → B} (hH : Measurable H) (hY : Measurable Y)
    (nextGiven : Set A → Measure B) {eps : ENNReal} (heps : eps ≠ ⊤)
    (hprob : ∀ S : Set A, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      IsProbabilityMeasure (nextGiven S))
    (hfactor : ∀ S : Set A, ∀ T : Set B,
      MeasurableSet S → MeasurableSet T →
      1 / 2 ≤ μ.real (H ⁻¹' S) →
      μ.real (H ⁻¹' S ∩ Y ⁻¹' T) =
        μ.real (H ⁻¹' S) * (nextGiven S).real T)
    (hmix : ∀ S : Set A, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      TVLe (nextGiven S) τ eps) :
    NuIndep μ H Y (2 * eps.toReal) := by
  apply nuIndep_of_largeEvent_approxTarget hH hY (ENNReal.toReal_nonneg)
  intro S T hS hT hp
  letI : IsProbabilityMeasure (nextGiven S) := hprob S hS hp
  have htv := (hmix S hS hp).abs_measureReal_sub_le heps hT
  rw [hfactor S T hS hT hp, ← mul_sub, abs_mul,
    abs_of_nonneg measureReal_nonneg]
  have hp1 : μ.real (H ⁻¹' S) ≤ 1 := by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
  calc
    μ.real (H ⁻¹' S) * |(nextGiven S).real T - τ.real T| ≤
        1 * eps.toReal :=
      mul_le_mul hp1 htv (abs_nonneg _) (by norm_num)
    _ = eps.toReal := one_mul _

/-- History/statistic wrapper around
`nuIndep_of_largeEvent_conditionedSampler`, ready for the corrected `U_i,V_i`
recursion. -/
theorem nuIndep_statistics_of_largeEvent_conditionedSampler
    {Ω A B C D : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {τ : Measure B} [IsProbabilityMeasure τ]
    {H : Ω → A} {Y : Ω → B} (hH : Measurable H) (hY : Measurable Y)
    (f : A → C) (g : B → D) (hf : Measurable f) (hg : Measurable g)
    (nextGiven : Set A → Measure B) {eps : ENNReal} (heps : eps ≠ ⊤)
    (hprob : ∀ S : Set A, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      IsProbabilityMeasure (nextGiven S))
    (hfactor : ∀ S : Set A, ∀ T : Set B,
      MeasurableSet S → MeasurableSet T →
      1 / 2 ≤ μ.real (H ⁻¹' S) →
      μ.real (H ⁻¹' S ∩ Y ⁻¹' T) =
        μ.real (H ⁻¹' S) * (nextGiven S).real T)
    (hmix : ∀ S : Set A, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      TVLe (nextGiven S) τ eps) :
    NuIndep μ (fun ω => f (H ω)) (fun ω => g (Y ω)) (2 * eps.toReal) :=
  (nuIndep_of_largeEvent_conditionedSampler hH hY nextGiven heps hprob hfactor hmix).comp
    hf hg

/-- The elementary `2`-warm inflation used by LV2.  If `μ` is `M`-warm
relative to `π` and `A` has `μ`-probability at least one half, then the
conditioned start is `2M`-warm relative to `π`. -/
theorem isWarm_condOn_of_half
    {Ω : Type*} [MeasurableSpace Ω] {μ π : Measure Ω}
    [IsProbabilityMeasure μ] {M : ENNReal} (hwarm : IsWarm M μ π)
    {A : Set Ω} (hA : MeasurableSet A) (hhalf : 1 / 2 ≤ μ.real A) :
    IsWarm (2 * M) (condOn μ A) π := by
  have hμA0 : μ A ≠ 0 := by
    intro hz
    have : μ.real A = 0 := by simp [Measure.real, hz]
    linarith
  have hμAtop : μ A ≠ ⊤ := measure_ne_top μ A
  have hhalfENN : ENNReal.ofReal (1 / 2) ≤ μ A := by
    have hμA : (μ A).toReal = μ.real A := rfl
    rw [← hμA, ← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hhalf
    exact ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hμAtop |>.mp hhalf
  have hinv : (μ A)⁻¹ ≤ 2 := by
    have hmul : (1 : ENNReal) ≤ 2 * μ A := by
      calc
        1 = 2 * ENNReal.ofReal (1 / 2) := by
          rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        _ ≤ 2 * μ A := mul_le_mul_left' hhalfENN 2
    rw [ENNReal.inv_le_iff_le_mul (by simp) (fun _ => by norm_num)]
    simpa [mul_comm] using hmul
  have hcond := Arlib.GaussianCooling.isWarm_condOn hwarm hA
  exact hcond.mono (by
    calc
      M * (μ A)⁻¹ ≤ M * 2 := mul_le_mul_left' hinv M
      _ = 2 * M := by rw [mul_comm])

/-- The complete generic LV2 wiring from a distributional warm-start sampler
specification.  No point-start mixing premise occurs: the sampler need only mix
from every `2M`-warm *distribution*.  The only remaining joint-law obligation
is `hfactor`, identifying the algorithm's conditional next law with rerunning
the sampler from the conditioned history law. -/
theorem nuIndep_of_distributionalWarmSampler
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {π : Measure A} {τ : Measure B} [IsProbabilityMeasure τ]
    {H : Ω → A} {Y : Ω → B} (hH : Measurable H) (hY : Measurable Y)
    {M : ENNReal} (hwarm : IsWarm M (μ.map H) π)
    (sample : Measure A → Measure B) {eps : ENNReal} (heps : eps ≠ ⊤)
    (hprob : ∀ ρ : Measure A, IsWarm (2 * M) ρ π → IsProbabilityMeasure (sample ρ))
    (hmix : ∀ ρ : Measure A, IsWarm (2 * M) ρ π → TVLe (sample ρ) τ eps)
    (hfactor : ∀ S : Set A, ∀ T : Set B,
      MeasurableSet S → MeasurableSet T →
      1 / 2 ≤ μ.real (H ⁻¹' S) →
      μ.real (H ⁻¹' S ∩ Y ⁻¹' T) =
        μ.real (H ⁻¹' S) * (sample (condOn (μ.map H) S)).real T) :
    NuIndep μ H Y (2 * eps.toReal) := by
  let nextGiven : Set A → Measure B := fun S => sample (condOn (μ.map H) S)
  letI : IsProbabilityMeasure (μ.map H) :=
    Measure.isProbabilityMeasure_map hH.aemeasurable
  apply nuIndep_of_largeEvent_conditionedSampler
    (μ := μ) (τ := τ) (H := H) (Y := Y) hH hY nextGiven heps
  · intro S hS hhalf
    apply hprob
    apply isWarm_condOn_of_half hwarm hS
    simpa [Measure.real, Measure.map_apply hH hS] using hhalf
  · intro S T hS hT hhalf
    exact hfactor S T hS hT hhalf
  · intro S hS hhalf
    apply hmix
    apply isWarm_condOn_of_half hwarm hS
    simpa [Measure.real, Measure.map_apply hH hS] using hhalf

/-! Axiom audit. -/

#print axioms nuIndep_of_jointTV_product
#print axioms nuIndep_history_next_of_jointTV
#print axioms nuIndep_historyStatistic_nextStatistic_of_jointTV
#print axioms marginalTV_zero_not_sufficient
#print axioms nuIndep_of_largeEvent_conditionalMarginal
#print axioms nuIndep_of_largeEvent_approxTarget
#print axioms nuIndep_historyStatistics_of_largeEvent_approxTarget
#print axioms nuIndep_of_largeEvent_conditionedSampler
#print axioms nuIndep_statistics_of_largeEvent_conditionedSampler
#print axioms isWarm_condOn_of_half
#print axioms nuIndep_of_distributionalWarmSampler

end Ttc.CVSequentialDependence

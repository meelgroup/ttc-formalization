import Ttc.Exec.CVIndependentStreamAccuracy

/-! Bias-aware final scaling for the corrected (clipped) CV estimator. -/

namespace Ttc.CVCorrectedClippingBias

open MeasureTheory Set
open Ttc.CV Ttc.CVSourceCorrectedPathAccuracy
open Arlib.GaussianCooling

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The exact remaining estimator premise: the product of the clipped phase means is
close to the true volume.  Equality is intentionally not required. -/
def ClippedPrefixTarget (mu : Measure Ω) (V : Nat → Ω → Real) (m : Nat)
    (initialNormalizer volumeTarget beta : Real) : Prop :=
  initialNormalizer * Arlib.GaussianCooling.prefixMean mu V m ∈
    Ttc.relErr beta volumeTarget

/-- A product of operational phase means telescopes approximately.

Unlike `integral_prod_mem_relErr_of_budget`, no independence premise is needed here:
`prefixMean` is already the deterministic product of the individual expectations. -/
theorem prefixMean_mem_relErr_of_phaseMeans_budget
    {mu : Measure Ω} {Wbar : Nat → Ω → Real} {A : Nat → Real}
    {m : Nat} {eta gamma : Real} (hm : 0 < m) (heta : 0 ≤ eta)
    (hgamma : gamma ≤ 1) (hbudget : 2 * (m : Real) * eta ≤ gamma)
    (hApos : ∀ i, 0 < A i)
    (hmean : ∀ i : Fin m, ∫ omega, Wbar ((i : Nat) + 1) omega ∂mu ∈
      Set.Icc
        ((1 - eta) * (A ((i : Nat) + 1) / A (i : Nat)))
        ((1 + eta) * (A ((i : Nat) + 1) / A (i : Nat)))) :
    A 0 * prefixMean mu Wbar m ∈ Ttc.relErr gamma (A m) := by
  have heta1 : eta ≤ 1 := le_one_of_budget hm heta hgamma hbudget
  have hprod := prod_mem_Icc (ι := Fin m)
    (x := fun i => ∫ omega, Wbar ((i : Nat) + 1) omega ∂mu)
    (r := fun i => A ((i : Nat) + 1) / A (i : Nat)) heta1
    (fun i => (div_pos (hApos _) (hApos _)).le) hmean
  have htelescope := prod_fin_telescope (fun i => (hApos i).ne') m
  rw [Fintype.card_fin, htelescope] at hprod
  have hsym := two_sub_pow_one_add_le_pow_one_sub heta heta1 m
  have hbias := phaseBias_le heta hgamma hbudget
  have hratio0 : 0 ≤ A m / A 0 := (div_pos (hApos m) (hApos 0)).le
  have hprod' :
      (∏ i : Fin m, ∫ omega, Wbar ((i : Nat) + 1) omega ∂mu) ∈
        Ttc.relErr gamma (A m / A 0) := by
    constructor
    · calc
        (1 - gamma) * (A m / A 0) ≤
            (2 - (1 + eta) ^ m) * (A m / A 0) :=
          mul_le_mul_of_nonneg_right (by linarith) hratio0
        _ ≤ (1 - eta) ^ m * (A m / A 0) :=
          mul_le_mul_of_nonneg_right hsym hratio0
        _ ≤ _ := hprod.1
    · exact hprod.2.trans
        (mul_le_mul_of_nonneg_right (by linarith) hratio0)
  have hprefix : prefixMean mu Wbar m =
      ∏ i : Fin m, ∫ omega, Wbar ((i : Nat) + 1) omega ∂mu := by
    unfold prefixMean
    exact (Fin.prod_univ_eq_prod_range
      (fun j => ∫ omega, Wbar (j + 1) omega ∂mu) m).symm
  rw [hprefix]
  have hscaled := scale_mem_relErr (hApos 0).le hprod' rfl
  convert hscaled using 1 <;> field_simp [(hApos 0).ne']

/-- Per-phase clipping loss `theta` compounds to at most `m*theta` in the product of
means.  This is the quantitative core needed to prove `ClippedPrefixTarget`. -/
theorem prefixMean_clipped_mem_relErr
    {mu : Measure Ω} {V Wbar : Nat → Ω → Real} {m : Nat} {theta : Real}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hraw0 : ∀ j < m, 0 ≤ ∫ omega, Wbar (j + 1) omega ∂mu)
    (hlower : ∀ j < m,
      (1 - theta) * (∫ omega, Wbar (j + 1) omega ∂mu) ≤
        ∫ omega, V (j + 1) omega ∂mu)
    (hupper : ∀ j < m,
      (∫ omega, V (j + 1) omega ∂mu) ≤
        ∫ omega, Wbar (j + 1) omega ∂mu) :
    prefixMean mu V m ∈ Ttc.relErr ((m : Real) * theta) (prefixMean mu Wbar m) := by
  have hone : 0 ≤ 1 - theta := sub_nonneg.2 htheta1
  have hrawProd : 0 ≤ prefixMean mu Wbar m := by
    unfold prefixMean
    exact Finset.prod_nonneg fun j hj ↦ hraw0 j (Finset.mem_range.1 hj)
  have hprodLower :
      ∏ j ∈ Finset.range m,
          ((1 - theta) * ∫ omega, Wbar (j + 1) omega ∂mu) ≤
        prefixMean mu V m := by
    unfold prefixMean
    exact Finset.prod_le_prod (fun j hj ↦ mul_nonneg hone
      (hraw0 j (Finset.mem_range.1 hj)))
      (fun j hj ↦ hlower j (Finset.mem_range.1 hj))
  have hbern : 1 - (m : Real) * theta ≤ (1 - theta) ^ m := by
    have := one_add_mul_le_pow (a := -theta) (by linarith) m
    simpa [sub_eq_add_neg, mul_neg] using this
  have hlower' : (1 - (m : Real) * theta) * prefixMean mu Wbar m ≤
      prefixMean mu V m := by
    calc
      (1 - (m : Real) * theta) * prefixMean mu Wbar m ≤
          (1 - theta) ^ m * prefixMean mu Wbar m :=
        mul_le_mul_of_nonneg_right hbern hrawProd
      _ = ∏ j ∈ Finset.range m,
          ((1 - theta) * ∫ omega, Wbar (j + 1) omega ∂mu) := by
        rw [Finset.prod_mul_distrib]
        simp [prefixMean]
      _ ≤ prefixMean mu V m := hprodLower
  have hu : prefixMean mu V m ≤ prefixMean mu Wbar m := by
    unfold prefixMean
    exact Finset.prod_le_prod (fun j hj ↦ by
      have := hlower j (Finset.mem_range.1 hj)
      exact (mul_nonneg hone (hraw0 j (Finset.mem_range.1 hj))).trans this)
      (fun j hj ↦ hupper j (Finset.mem_range.1 hj))
  constructor
  · exact hlower'
  · exact hu.trans (by nlinarith [hrawProd])

/-- Concrete clipping bias from the existing second-moment truncation lemma.  The only
Gaussian-specific input is the honest raw telescoping identity. -/
theorem clippedPrefixTarget_of_rawSecondMoment
    {mu : Measure Ω} [IsProbabilityMeasure mu] {V Wbar : Nat → Ω → Real}
    {m : Nat} {k alpha initialNormalizer volumeTarget beta : Real}
    (hk : 8 ≤ k) (halpha : 0 < alpha) (halpha1 : 1 ≤ alpha)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hbeta : (m : Real) / (2 * alpha) ≤ beta)
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWm : ∀ j, Measurable (Wbar j))
    (hWint : ∀ j, Integrable (Wbar j) mu)
    (hW2int : ∀ j, Integrable (fun omega ↦ (Wbar j omega) ^ 2) mu)
    (hWEpos : ∀ j, 0 < ∫ omega, Wbar j omega ∂mu)
    (hrawSecond : ∀ j, ∫ omega, (Wbar j omega) ^ 2 ∂mu ≤
      (1 + 8 / k) * (∫ omega, Wbar j omega ∂mu) ^ 2)
    (hVdef : ∀ j omega, V j omega = min (Wbar j omega)
      (alpha * ∫ z, Wbar j z ∂mu))
    (htelescope : initialNormalizer * prefixMean mu Wbar m = volumeTarget) :
    ClippedPrefixTarget mu V m initialNormalizer volumeTarget beta := by
  let theta : Real := 1 / (2 * alpha)
  have htheta0 : 0 ≤ theta := by dsimp [theta]; positivity
  have htheta1 : theta ≤ 1 := by
    dsimp [theta]
    rw [div_le_one (by positivity)]
    linarith
  have hprefix := prefixMean_clipped_mem_relErr (mu := mu) (V := V) (Wbar := Wbar)
    (m := m) htheta0 htheta1
    (fun j _ ↦ (hWEpos (j + 1)).le)
    (fun j _ ↦ by
      have heq : (∫ omega, V (j + 1) omega ∂mu) =
          ∫ omega, min (Wbar (j + 1) omega)
            (alpha * ∫ z, Wbar (j + 1) z ∂mu) ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall (hVdef (j + 1)))
      rw [heq]
      simpa only [theta] using
        (expect_trunc_ge_half halpha (hW0 (j + 1))
        (hWm (j + 1)) (hWint (j + 1)) (hW2int (j + 1))
        (hWEpos (j + 1)) (hrawSecond (j + 1)) (by
          have hk0 : (0 : Real) < k := by linarith
          have : 8 / k ≤ 1 := (div_le_one hk0).2 hk
          linarith)))
    (fun j _ ↦ by
      have heq : (∫ omega, V (j + 1) omega ∂mu) =
          ∫ omega, min (Wbar (j + 1) omega)
            (alpha * ∫ z, Wbar (j + 1) z ∂mu) ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall (hVdef (j + 1)))
      rw [heq]
      exact expect_trunc_le (mul_nonneg halpha.le (hWEpos (j + 1)).le)
        (hW0 (j + 1)) (hWm (j + 1)) (hWint (j + 1)))
  have hscaled : initialNormalizer * prefixMean mu V m ∈
      Ttc.relErr ((m : Real) * theta) volumeTarget :=
    scale_mem_relErr hinit hprefix htelescope
  apply relErr_mono _ hvolume hscaled
  dsimp [theta]
  simpa [one_div, div_eq_mul_inv] using hbeta

/-- Operational version of `clippedPrefixTarget_of_rawSecondMoment`.

The sampled phase means need not telescope exactly.  If their raw product is within
relative error `gamma` of the target, clipping contributes `m/(2*alpha)` and the two
errors compose multiplicatively.  This is the form needed by an actual mixed Markov
execution; using an equality here would identify the sampled phase law with its ideal
cooling target. -/
theorem clippedPrefixTarget_of_rawSecondMoment_approx
    {mu : Measure Ω} [IsProbabilityMeasure mu] {V Wbar : Nat → Ω → Real}
    {m : Nat} {k alpha initialNormalizer volumeTarget beta gamma : Real}
    (hk : 8 ≤ k) (halpha : 0 < alpha) (halpha1 : 1 ≤ alpha)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hgamma : 0 ≤ gamma)
    (hbeta : (m : Real) / (2 * alpha) + gamma +
      ((m : Real) / (2 * alpha)) * gamma ≤ beta)
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWm : ∀ j, Measurable (Wbar j))
    (hWint : ∀ j, Integrable (Wbar j) mu)
    (hW2int : ∀ j, Integrable (fun omega ↦ (Wbar j omega) ^ 2) mu)
    (hWEpos : ∀ j, 0 < ∫ omega, Wbar j omega ∂mu)
    (hrawSecond : ∀ j, ∫ omega, (Wbar j omega) ^ 2 ∂mu ≤
      (1 + 8 / k) * (∫ omega, Wbar j omega ∂mu) ^ 2)
    (hVdef : ∀ j omega, V j omega = min (Wbar j omega)
      (alpha * ∫ z, Wbar j z ∂mu))
    (hrawTarget : initialNormalizer * prefixMean mu Wbar m ∈
      Ttc.relErr gamma volumeTarget) :
    ClippedPrefixTarget mu V m initialNormalizer volumeTarget beta := by
  let theta : Real := 1 / (2 * alpha)
  have htheta0 : 0 ≤ theta := by dsimp [theta]; positivity
  have htheta1 : theta ≤ 1 := by
    dsimp [theta]
    rw [div_le_one (by positivity)]
    linarith
  have hprefix := prefixMean_clipped_mem_relErr (mu := mu) (V := V) (Wbar := Wbar)
    (m := m) htheta0 htheta1
    (fun j _ ↦ (hWEpos (j + 1)).le)
    (fun j _ ↦ by
      have heq : (∫ omega, V (j + 1) omega ∂mu) =
          ∫ omega, min (Wbar (j + 1) omega)
            (alpha * ∫ z, Wbar (j + 1) z ∂mu) ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall (hVdef (j + 1)))
      rw [heq]
      simpa only [theta] using
        (expect_trunc_ge_half halpha (hW0 (j + 1))
          (hWm (j + 1)) (hWint (j + 1)) (hW2int (j + 1))
          (hWEpos (j + 1)) (hrawSecond (j + 1)) (by
            have hk0 : (0 : Real) < k := by linarith
            have : 8 / k ≤ 1 := (div_le_one hk0).2 hk
            linarith)))
    (fun j _ ↦ by
      have heq : (∫ omega, V (j + 1) omega ∂mu) =
          ∫ omega, min (Wbar (j + 1) omega)
            (alpha * ∫ z, Wbar (j + 1) z ∂mu) ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall (hVdef (j + 1)))
      rw [heq]
      exact expect_trunc_le (mul_nonneg halpha.le (hWEpos (j + 1)).le)
        (hW0 (j + 1)) (hWm (j + 1)) (hWint (j + 1)))
  have hscaled : initialNormalizer * prefixMean mu V m ∈
      Ttc.relErr ((m : Real) * theta)
        (initialNormalizer * prefixMean mu Wbar m) :=
    scale_mem_relErr hinit hprefix rfl
  have hcomposed := relErr_trans
    (mul_nonneg (Nat.cast_nonneg m) htheta0) hgamma hvolume hscaled hrawTarget
  apply relErr_mono _ hvolume hcomposed
  dsimp [theta]
  simpa [one_div, div_eq_mul_inv] using hbeta

/-- Compose the corrected estimator's concentration about its clipped proxy with the
clipping/telescoping bias.  This replaces the false exact-prefix identity in the older
public wrapper. -/
theorem four_fifths_scaled_of_clippedPrefixTarget
    {mu : Measure Ω} [IsFiniteMeasure mu] {Y : Ω → Real}
    {proxy initialNormalizer volumeTarget eta beta requested : Real}
    (hinit : 0 ≤ initialNormalizer) (heta : 0 ≤ eta) (hbeta : 0 ≤ beta)
    (hvolume : 0 ≤ volumeTarget)
    (hbudget : eta + beta + eta * beta ≤ requested)
    (hgood : 4 / 5 ≤ mu.real {omega | Y omega ∈ Ttc.relErr eta proxy})
    (hbias : initialNormalizer * proxy ∈ Ttc.relErr beta volumeTarget) :
    4 / 5 ≤ mu.real
      {omega | initialNormalizer * Y omega ∈ Ttc.relErr requested volumeTarget} := by
  apply hgood.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro omega homega
  have hscaled : initialNormalizer * Y omega ∈
      Ttc.relErr eta (initialNormalizer * proxy) :=
    scale_mem_relErr hinit homega rfl
  exact relErr_mono hbudget hvolume
    (relErr_trans heta hbeta hvolume hscaled hbias)

#print axioms four_fifths_scaled_of_clippedPrefixTarget
#print axioms prefixMean_mem_relErr_of_phaseMeans_budget
#print axioms prefixMean_clipped_mem_relErr
#print axioms clippedPrefixTarget_of_rawSecondMoment
#print axioms clippedPrefixTarget_of_rawSecondMoment_approx

end Ttc.CVCorrectedClippingBias

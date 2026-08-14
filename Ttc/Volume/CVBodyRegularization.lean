/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Volume.CousinsVempala
import Ttc.Volume.InputLawAlgorithm
import Arlib.Convexity.LocalizationClosed

/-!
# Closing an arbitrary convex volume-oracle input

`VolumeAlgorithm.correct` deliberately accepts convex sets which need not be Borel measurable
or closed.  The concrete Gaussian-cooling sampler is stated for closed bounded bodies.  This
file records the lossless bridge: replace the input by its closure.  Convexity makes the
frontier Haar-null, while the open unit ball and finite volume supply all of the concrete
sampler's geometric hypotheses.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Ttc.CV

variable {n : ℕ}

/-- The closure of a convex oracle input has exactly the same Lebesgue volume. -/
theorem volume_closure_eq_of_convex {K : Set (Space n)} (hKc : Convex ℝ K) :
    volume (closure K) = volume K :=
  Arlib.addHaar_closure_of_convex volume hKc

/-- The open unit ball contained in an arbitrary input becomes a closed unit ball after
closing the input. -/
theorem closedBall_one_subset_closure {K : Set (Space n)}
    (hball : ball (0 : Space n) 1 ⊆ K) :
    closedBall (0 : Space n) 1 ⊆ closure K := by
  rw [← closure_ball (0 : Space n) one_ne_zero]
  exact closure_mono hball

/-- Translation and nonzero rescaling preserve closedness of a normalized input body. -/
theorem isClosed_roundBody {c : Space n} {γ : ℝ} {K : Set (Space n)}
    (hγ : 0 < γ) (hK : IsClosed K) :
    IsClosed (roundBody c γ K) := by
  unfold roundBody
  exact (hK.vadd (-c)).smul_of_ne_zero (inv_ne_zero hγ.ne')

/-- Complete geometric adapter from the public `VolumeAlgorithm` assumptions to the body
assumptions used by the concrete adaptive sampler.  The source radius `cvRadius K` is used as
the sampler constant `C`; the slightly larger displayed ball `C√n` is valid in every
positive dimension.

The conjunction is intentionally ordered like the geometric arguments of
`packed_median_accuracy_concrete_adaptive`: convexity, closedness, boundedness, positive
volume, closed unit-ball inclusion, finite volume, positive radius, and outer-radius bound. -/
theorem closure_concrete_geometry (hn : 1 ≤ n) {K : Set (Space n)}
    (hKc : Convex ℝ K) (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    Convex ℝ (closure K) ∧
      IsClosed (closure K) ∧
      Bornology.IsBounded (closure K) ∧
      0 < volume (closure K) ∧
      closedBall (0 : Space n) 1 ⊆ closure K ∧
      volume (closure K) ≠ ⊤ ∧
      0 < cvRadius K ∧
      closure K ⊆ closedBall 0 (cvRadius K * Real.sqrt n) := by
  have hKR : K ⊆ closedBall (0 : Space n) (cvRadius K) :=
    subset_closedBall_cvRadius hKc hball hfin
  have hKRcl : closure K ⊆ closedBall (0 : Space n) (cvRadius K) :=
    closure_minimal hKR isClosed_closedBall
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hnreal
  have hrad : cvRadius K ≤ cvRadius K * Real.sqrt n := by
    nlinarith [cvRadius_pos K]
  have houter : closure K ⊆ closedBall 0 (cvRadius K * Real.sqrt n) :=
    hKRcl.trans (closedBall_subset_closedBall hrad)
  have hvolEq : volume (closure K) = volume K := volume_closure_eq_of_convex hKc
  have hvolpos : 0 < volume (closure K) := by
    have hballpos : 0 < volume (ball (0 : Space n) 1) :=
      measure_ball_pos volume 0 one_pos
    exact hballpos.trans_le (measure_mono (hball.trans subset_closure))
  exact ⟨hKc.closure, isClosed_closure,
    Metric.isBounded_closedBall.subset houter, hvolpos,
    closedBall_one_subset_closure hball, hvolEq.symm ▸ hfin,
    cvRadius_pos K, houter⟩

/-- The exact dimension guard of the concrete adaptive sampler immediately supplies the
regularization package. -/
theorem closure_concrete_geometry_of_twenty_one (hn : 21 ≤ n) {K : Set (Space n)}
    (hKc : Convex ℝ K) (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    Convex ℝ (closure K) ∧
      IsClosed (closure K) ∧
      Bornology.IsBounded (closure K) ∧
      0 < volume (closure K) ∧
      closedBall (0 : Space n) 1 ⊆ closure K ∧
      volume (closure K) ≠ ⊤ ∧
      0 < cvRadius K ∧
      closure K ⊆ closedBall 0 (cvRadius K * Real.sqrt n) :=
  closure_concrete_geometry (by omega) hKc hball hfin

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.volume_closure_eq_of_convex
#print axioms Ttc.CVAdaptive.closedBall_one_subset_closure
#print axioms Ttc.CVAdaptive.isClosed_roundBody
#print axioms Ttc.CVAdaptive.closure_concrete_geometry

namespace Ttc

open MeasureTheory Metric Set

/-- Package input-specific laws whose correctness theorem is stated only for closed bounded
convex bodies as a public `VolumeAlgorithm`, whose contract quantifies over arbitrary convex
sets.  On input `K` the algorithm runs the supplied construction at `closure K`.  The closure
has the same volume, so this changes neither the reported target nor the relative-error event.

This is the body-regularization adapter needed by a concrete Gaussian-cooling construction;
it adds no sampler or runtime assumption. -/
noncomputable def VolumeAlgorithm.ofClosedInputLaws
    (n : ℕ) (hn : 1 ≤ n)
    (X : (Set (Space n) × ℝ × ℝ) → Type)
    [mX : ∀ a, MeasurableSpace (X a)]
    (nu : ∀ a, Measure (X a)) [hnu : ∀ a, IsProbabilityMeasure (nu a)]
    (localEst : ∀ a, X a → ℝ)
    (hlocalMeas : ∀ a, Measurable (localEst a))
    (hlocalCorrect : ∀ (K : Set (Space n)) (eps p : ℝ),
      0 < eps → 0 < p → p < 1 →
      Convex ℝ K → IsClosed K → Bornology.IsBounded K → 0 < volume K →
      closedBall (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      1 - p ≤ (nu (K, eps, p)).real
        {omega | localEst (K, eps, p) omega ∈ relErr eps (volume K).toReal}) :
    VolumeAlgorithm n where
  Ω := InputCoinSpace n X
  mΩ := inferInstance
  μ := Measure.infinitePi nu
  isProb := by infer_instance
  est K eps p omega :=
    localEst (closure K, eps, p) (omega (closure K, eps, p))
  est_meas K eps p :=
    (hlocalMeas (closure K, eps, p)).comp (measurable_pi_apply (closure K, eps, p))
  correct K eps p heps hp hp1 hKc hball hfin := by
    let a : Set (Space n) × ℝ × ℝ := (closure K, eps, p)
    let S : Set (X a) :=
      {omega | localEst a omega ∈ relErr eps (volume K).toReal}
    have hgeom := CVAdaptive.closure_concrete_geometry hn hKc hball hfin
    have hvol : volume (closure K) = volume K :=
      CVAdaptive.volume_closure_eq_of_convex hKc
    have hS : MeasurableSet S := (hlocalMeas a) measurableSet_Icc
    have hmp := measurePreserving_inputCoord nu a
    have hEq : (Measure.infinitePi nu).real
        {omega : InputCoinSpace n X |
          localEst a (omega a) ∈ relErr eps (volume K).toReal} = (nu a).real S := by
      exact hmp.measureReal_preimage hS.nullMeasurableSet
    change 1 - p ≤ (Measure.infinitePi nu).real
      {omega : InputCoinSpace n X |
        localEst a (omega a) ∈ relErr eps (volume K).toReal}
    rw [hEq]
    have hcorrect := hlocalCorrect (closure K) eps p heps hp hp1
      hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
      hgeom.2.2.2.2.1 hgeom.2.2.2.2.2.1
    simpa only [a, S, hvol] using hcorrect

end Ttc

#print axioms Ttc.VolumeAlgorithm.ofClosedInputLaws

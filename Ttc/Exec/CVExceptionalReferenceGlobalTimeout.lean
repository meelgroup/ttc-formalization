import Ttc.Exec.CVScoreSeedExceptionalCost
import Arlib.Probability.TVTimeout

/-!
# Global timeout transfer from an exceptional reference path

The noncompounding exceptional-reference strategy has a clean final step: if the *whole
cost-recording operational path law* is within `error` of a reference costed path law,
then one Markov inequality on the reference total cost and one TV event transfer give the
desired global timeout.  This spends `error` once and introduces no per-phase
`1 / correctedNu` cutoff.

The currently available Gaussian selective theorem is weaker: it compares only the
cost-erased score/seed marginal.  The counterexample in the second section proves that
such an output comparison cannot in general be lifted to the required joint cost/output
comparison.  Thus the exact missing result is a cost-preserving path coupling (or an
equivalent joint-kernel TV theorem), not another phase-mean estimate.
-/

namespace Ttc.CVExceptionalReferenceGlobalTimeout

open MeasureTheory ProbabilityTheory Set
open Arlib
open scoped ENNReal Classical

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A single global timeout from joint path TV and a reference expected-cost bound. -/
theorem globalTimeout_le_of_jointPathTV
    {actual reference : Measure Omega}
    [IsProbabilityMeasure actual] [IsProbabilityMeasure reference]
    {error : ENNReal} (hjoint : TVLe actual reference error)
    (cost : Omega → ENNReal) (hcost : Measurable cost)
    {cutoff budget : ENNReal} (hcut0 : cutoff ≠ 0) (hcutTop : cutoff ≠ ⊤)
    (hmean : (∫⁻ omega, cost omega ∂reference) ≤ budget) :
    actual {omega | cutoff ≤ cost omega} ≤ budget / cutoff + error := by
  have hBad : MeasurableSet {omega | cutoff ≤ cost omega} :=
    measurableSet_le measurable_const hcost
  have hrefMul :
      cutoff * reference {omega | cutoff ≤ cost omega} ≤
        ∫⁻ omega, cost omega ∂reference :=
    mul_meas_ge_le_lintegral hcost cutoff
  have href : reference {omega | cutoff ≤ cost omega} ≤ budget / cutoff := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hcut0) (Or.inl hcutTop)).2
    simpa [mul_comm] using hrefMul.trans hmean
  exact hjoint.measure_le_add hBad href

/-- Multiplied form, useful before choosing a finite nonzero global cutoff. -/
theorem mul_globalTimeout_le_of_jointPathTV
    {actual reference : Measure Omega}
    [IsProbabilityMeasure actual] [IsProbabilityMeasure reference]
    {error : ENNReal} (hjoint : TVLe actual reference error)
    (cost : Omega → ENNReal) (hcost : Measurable cost)
    (cutoff budget : ENNReal)
    (hmean : (∫⁻ omega, cost omega ∂reference) ≤ budget) :
    cutoff * actual {omega | cutoff ≤ cost omega} ≤
      budget + cutoff * error := by
  have hBad : MeasurableSet {omega | cutoff ≤ cost omega} :=
    measurableSet_le measurable_const hcost
  have htransfer := hjoint.measure_le_add hBad
    (le_rfl : reference {omega | cutoff ≤ cost omega} ≤ _)
  calc
    cutoff * actual {omega | cutoff ≤ cost omega} ≤
        cutoff * (reference {omega | cutoff ≤ cost omega} + error) := by gcongr
    _ = cutoff * reference {omega | cutoff ≤ cost omega} + cutoff * error := by
      rw [mul_add]
    _ ≤ (∫⁻ omega, cost omega ∂reference) + cutoff * error := by
      gcongr
      exact mul_meas_ge_le_lintegral hcost cutoff
    _ ≤ budget + cutoff * error := by gcongr

/-- TV also transfers an expected observable bounded by a finite constant.  This is the
expected-cost counterpart of the event theorem and is useful when the operational run is
stopped at one global deadline. -/
theorem lintegral_le_add_bound_mul_of_jointTV
    {actual reference : Measure Omega} {error bound : ENNReal}
    (hjoint : TVLe actual reference error) (hbound0 : bound ≠ 0)
    (hboundTop : bound ≠ ⊤) {f : Omega → ENNReal}
    (hf : Measurable f) (hfle : ∀ omega, f omega ≤ bound) :
    (∫⁻ omega, f omega ∂actual) ≤
      (∫⁻ omega, f omega ∂reference) + bound * error := by
  let g : Omega → ENNReal := fun omega ↦ bound⁻¹ * f omega
  have hg : Measurable g := measurable_const.mul hf
  have hg1 : ∀ omega, g omega ≤ 1 := by
    intro omega
    dsimp only [g]
    calc
      bound⁻¹ * f omega ≤ bound⁻¹ * bound := by
        exact mul_le_mul_left' (hfle omega) bound⁻¹
      _ = 1 := ENNReal.inv_mul_cancel hbound0 hboundTop
  have hnormalized := Arlib.lintegral_le_of_tvLe hjoint hg hg1
  have hscale (rho : Measure Omega) :
      bound * (∫⁻ omega, g omega ∂rho) = ∫⁻ omega, f omega ∂rho := by
    rw [← lintegral_const_mul bound hg]
    apply lintegral_congr
    intro omega
    dsimp only [g]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hbound0 hboundTop, one_mul]
  rw [← hscale actual, ← hscale reference]
  calc
    bound * (∫⁻ omega, g omega ∂actual) ≤
        bound * ((∫⁻ omega, g omega ∂reference) + error) := by gcongr
    _ = bound * (∫⁻ omega, g omega ∂reference) + bound * error := by
      rw [mul_add]

/-- In particular, the expected globally stopped operational cost is the stopped
reference mean plus at most `cutoff * error`. -/
theorem lintegral_min_cost_le_of_jointPathTV
    {actual reference : Measure Omega} {error : ENNReal}
    (hjoint : TVLe actual reference error)
    (cost : Omega → ENNReal) (hcost : Measurable cost)
    {cutoff budget : ENNReal} (hcut0 : cutoff ≠ 0) (hcutTop : cutoff ≠ ⊤)
    (hmean : (∫⁻ omega, cost omega ∂reference) ≤ budget) :
    (∫⁻ omega, min (cost omega) cutoff ∂actual) ≤
      budget + cutoff * error := by
  have htransfer := lintegral_le_add_bound_mul_of_jointTV hjoint hcut0 hcutTop
    (hcost.min measurable_const) (fun omega ↦ min_le_right (cost omega) cutoff)
  calc
    (∫⁻ omega, min (cost omega) cutoff ∂actual) ≤
        (∫⁻ omega, min (cost omega) cutoff ∂reference) + cutoff * error := htransfer
    _ ≤ (∫⁻ omega, cost omega ∂reference) + cutoff * error := by
      gcongr
      exact min_le_left _ _
    _ ≤ budget + cutoff * error := by gcongr

/-! ## Why cost-erased phase TV is not enough -/

/-- Two cost/output laws can have identical output marginals while their timeout events
are maximally different. -/
theorem costErased_eq_but_timeout_differs :
    let actual : Measure (ENNReal × Unit) := Measure.dirac (1, ())
    let reference : Measure (ENNReal × Unit) := Measure.dirac (0, ())
    Measure.map Prod.snd actual = Measure.map Prod.snd reference ∧
      (∫⁻ z, z.1 ∂reference) = 0 ∧
      actual {z | (1 : ENNReal) ≤ z.1} = 1 ∧
      reference {z | (1 : ENNReal) ≤ z.1} = 0 := by
  dsimp only
  constructor
  · simp
  constructor
  · simp
  constructor <;> simp

/-- In particular, zero TV after cost erasure does not imply zero TV of the joint
cost/output laws.  This rules out deriving the premise of
`globalTimeout_le_of_jointPathTV` from the existing score/seed selective-TV theorem by
data processing alone (which only works in the opposite direction). -/
theorem not_costErasedTV_implies_jointTV :
    ¬ (∀ (actual reference : Measure (ENNReal × Unit)),
      IsProbabilityMeasure actual → IsProbabilityMeasure reference →
      TVLe (Measure.map Prod.snd actual) (Measure.map Prod.snd reference) 0 →
      TVLe actual reference 0) := by
  intro h
  let actual : Measure (ENNReal × Unit) := Measure.dirac (1, ())
  let reference : Measure (ENNReal × Unit) := Measure.dirac (0, ())
  have hactual : IsProbabilityMeasure actual := by
    dsimp only [actual]
    infer_instance
  have hreference : IsProbabilityMeasure reference := by
    dsimp only [reference]
    infer_instance
  have houtEq : Measure.map Prod.snd actual = Measure.map Prod.snd reference := by
    dsimp only [actual, reference]
    simp
  have hout : TVLe (Measure.map Prod.snd actual) (Measure.map Prod.snd reference) 0 := by
    rw [houtEq]
    exact TVLe.refl _
  have hjoint := h actual reference hactual hreference hout
  have hBad : MeasurableSet {z : ENNReal × Unit | (1 : ENNReal) ≤ z.1} := by
    exact measurableSet_le measurable_const measurable_fst
  have hle := hjoint.measure_le_add hBad
    (le_rfl : reference {z | (1 : ENNReal) ≤ z.1} ≤ _)
  have ha : actual {z | (1 : ENNReal) ≤ z.1} = 1 := by
    dsimp only [actual]
    simp
  have hr : reference {z | (1 : ENNReal) ≤ z.1} = 0 := by
    dsimp only [reference]
    simp
  rw [ha, hr] at hle
  norm_num at hle

#print axioms globalTimeout_le_of_jointPathTV
#print axioms mul_globalTimeout_le_of_jointPathTV
#print axioms lintegral_le_add_bound_mul_of_jointTV
#print axioms lintegral_min_cost_le_of_jointPathTV
#print axioms costErased_eq_but_timeout_differs
#print axioms not_costErasedTV_implies_jointTV

end Ttc.CVExceptionalReferenceGlobalTimeout

import Arlib.Probability.TVKernel
import Arlib.Probability.TVCoupling
import Ttc.Exec.CVCostedRuntimeCutoff

/-! Markov timeout under a nearby reference law. -/

namespace Ttc.CostedTVTimeoutTransfer

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.CVCostedRuntimeCutoff
open scoped ENNReal Classical

variable {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]

noncomputable def cutoffOutput (fallback : E) (L : ENNReal) (cost : Omega → ENNReal)
    (value : Omega → E) (omega : Omega) : E :=
  if cost omega < L then value omega else fallback

theorem measurable_cutoffOutput (fallback : E) (L : ENNReal)
    {cost : Omega → ENNReal} {value : Omega → E}
    (hcost : Measurable cost) (hvalue : Measurable value) :
    Measurable (cutoffOutput fallback L cost value) := by
  exact hvalue.piecewise (measurableSet_lt hcost measurable_const) measurable_const

/-- A TV perturbation of the starting/output law adds only its TV error to the reference
Markov timeout bound. -/
theorem timeout_le_reference_add_tv
    {mu nu : Measure Omega} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps B L : ENNReal} (htv : TVLe mu nu eps)
    {cost : Omega → ENNReal} (hcost : Measurable cost)
    (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ omega, cost omega ∂nu) ≤ B) :
    mu {omega | L ≤ cost omega} ≤ B / L + eps := by
  let T : Set Omega := {omega | L ≤ cost omega}
  have hT : MeasurableSet T := measurableSet_le measurable_const hcost
  have hmarkov : nu T ≤ B / L :=
    timeout_le_of_lintegral_le hcost hL0 hLtop hmean
  exact (htv T hT).1 |>.trans (by
    simpa only [add_comm] using add_le_add_right hmarkov eps)

/-- Replacing every timed-out output by a fallback changes the actual output law by at
most `reference mean / cutoff + input-law TV error`. -/
theorem tvLe_map_cutoffOutput_of_reference
    {mu nu : Measure Omega} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps B L : ENNReal} (htv : TVLe mu nu eps)
    {cost : Omega → ENNReal} (hcost : Measurable cost)
    {value : Omega → E} (hvalue : Measurable value) (fallback : E)
    (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ omega, cost omega ∂nu) ≤ B) :
    TVLe (Measure.map (cutoffOutput fallback L cost value) mu)
      (Measure.map value mu) (B / L + eps) := by
  apply tvLe_map_map_of_measure_ne_le
    (measurable_cutoffOutput fallback L hcost hvalue) hvalue
  apply (timeout_le_reference_add_tv htv hcost hL0 hLtop hmean).trans'
  apply measure_mono
  intro omega homega
  by_contra hnot
  have hlt : cost omega < L := lt_of_not_ge hnot
  exact homega (by simp [cutoffOutput, hlt])

#print axioms timeout_le_reference_add_tv
#print axioms tvLe_map_cutoffOutput_of_reference

end Ttc.CostedTVTimeoutTransfer

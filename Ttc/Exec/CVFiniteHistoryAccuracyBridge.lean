import Arlib.Probability.TVTensor
import Ttc.Volume.CVSequentialDependence
import Ttc.Exec.CVIndependentStreamDependence

/-!
# The finite-history TV seam for operational CV accuracy

A retained reference which controls only the next-state marginal is enough for expected
cost accounting, but it is not enough for the weighted estimator: the estimator reads the
whole finite score history.  This file records both sides of that distinction.

* `marginalTV_zero_not_jointHistoryProduct_zero` is the exact obstruction.  Even an exact
  next-state marginal can be maximally correlated with the past.
* `measureReal_event_ge_of_finiteHistoryTV` is the sharp conditional bridge.  Once the
  complete finite-history law is TV-close to an ideal law, every measurable accuracy event
  loses only that TV budget.
* `four_fifths_of_independentFiniteHistoryTV` tensorizes a one-stream finite-history bound
  over the `k` independent streams used by the CV estimator.

Thus the remaining analytic theorem has a precise type: a TV comparison of complete
finite histories, not another seed-marginal mixing statement.
-/

set_option autoImplicit false

namespace Ttc.CVFiniteHistoryAccuracyBridge

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Ttc.CVSequentialDependence
open Ttc.CVIndependentStreamDependence Ttc.CVIndependentStreamMoments
open Arlib.GaussianCooling
open scoped ENNReal Classical BigOperators

/-- Exact finite-history obstruction.  Equality of the current marginal with its target
does not imply that the joint `(history,current)` law is the product of the history
marginal and that target, even up to TV error zero. -/
theorem marginalTV_zero_not_jointHistoryProduct_zero
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {S : Set Omega} (hS : MeasurableSet S) (hhalf : mu.real S = 1 / 2) :
    TVLe (Measure.map id mu) mu 0 ∧
      ¬ TVLe (Measure.map (fun omega : Omega => (omega, omega)) mu)
        ((Measure.map id mu).prod mu) 0 := by
  have hmarg := marginalTV_zero_not_sufficient hS hhalf
  refine ⟨hmarg.1, ?_⟩
  intro hjoint
  have hindep : NuIndep mu id id 0 := by
    have h := nuIndep_of_jointTV_product
      (μ := mu) (τ := mu) (X := id) (Y := id)
      measurable_id measurable_id (ν := 0) (by simp) ?_
    · simpa using h
    · simpa only [Measure.map_id, id_eq] using hjoint
  exact hmarg.2 hindep

/-- Quantitative form of the same obstruction.  In the half-event graph example, every
joint-history comparison with the product reference must spend TV error at least `1/4`,
although the current marginal has error exactly zero. -/
theorem one_fourth_le_error_of_jointHistoryProduct
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {S : Set Omega} (hS : MeasurableSet S) (hhalf : mu.real S = 1 / 2)
    {error : ENNReal} (herrorTop : error ≠ ⊤)
    (hjoint : TVLe (Measure.map (fun omega : Omega => (omega, omega)) mu)
      ((Measure.map id mu).prod mu) error) :
    ENNReal.ofReal (1 / 4 : Real) ≤ error := by
  have hindep : NuIndep mu id id error.toReal := by
    have h := nuIndep_of_jointTV_product
      (μ := mu) (τ := mu) (X := id) (Y := id)
      measurable_id measurable_id herrorTop ?_
    · simpa using h
    · simpa only [Measure.map_id, id_eq] using hjoint
  have h := hindep S S hS hS
  change |mu.real (S ∩ S) - mu.real S * mu.real S| ≤ error.toReal at h
  rw [Set.inter_self, hhalf] at h
  have hreal : (1 / 4 : Real) ≤ error.toReal := by
    norm_num at h ⊢
    exact h
  apply (ENNReal.toReal_le_toReal (by simp) herrorTop).1
  simpa using hreal

/-- Sharp transfer of a measurable success event across a complete finite-history TV
comparison.  No Markov, independence, moment, or bounded-readout premise is needed. -/
theorem measureReal_event_ge_of_finiteHistoryTV
    {Omega : Type*} [MeasurableSpace Omega]
    {actual ideal : Measure Omega}
    [IsProbabilityMeasure actual] [IsProbabilityMeasure ideal]
    {error : ENNReal} (herror : error ≠ ⊤)
    (htv : TVLe actual ideal error)
    {good : Set Omega} (hgoodMeas : MeasurableSet good) {p : Real}
    (hgood : p <= ideal.real good) :
    p - error.toReal <= actual.real good := by
  have hdist := htv.abs_measureReal_sub_le herror hgoodMeas
  rw [abs_le] at hdist
  linarith [hdist.1]

/-- The constants used by the source certificate: ideal success `33/40` and complete-path
TV error at most `1/40` imply operational success at least `4/5`. -/
theorem four_fifths_of_finiteHistoryTV
    {Omega : Type*} [MeasurableSpace Omega]
    {actual ideal : Measure Omega}
    [IsProbabilityMeasure actual] [IsProbabilityMeasure ideal]
    {error : ENNReal}
    (herror : error <= ENNReal.ofReal (1 / 40 : Real))
    (htv : TVLe actual ideal error)
    {good : Set Omega} (hgoodMeas : MeasurableSet good)
    (hgood : (33 / 40 : Real) <= ideal.real good) :
    (4 / 5 : Real) <= actual.real good := by
  have herrTop : error ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) herror
  have htransfer := measureReal_event_ge_of_finiteHistoryTV
    herrTop htv hgoodMeas hgood
  have herrReal : error.toReal <= (1 / 40 : Real) := by
    have := ENNReal.toReal_mono (by simp : ENNReal.ofReal (1 / 40 : Real) ≠ ⊤) herror
    simpa using this
  linarith

/-- Complete finite-history TV tensorizes over the `k` independently restarted streams.
This is the exact bridge needed by a readout of all streams.  It deliberately assumes TV
for each *whole one-stream history*; coordinatewise next-seed TV is insufficient by
`marginalTV_zero_not_jointHistoryProduct_zero`. -/
theorem four_fifths_of_independentFiniteHistoryTV
    {k : Nat} {Omega : Fin k -> Type*}
    [forall j, MeasurableSpace (Omega j)]
    (actual ideal : forall j, Measure (Omega j))
    [forall j, IsProbabilityMeasure (actual j)]
    [forall j, IsProbabilityMeasure (ideal j)]
    {error : Fin k -> ENNReal}
    (htv : forall j, TVLe (actual j) (ideal j) (error j))
    (herror : (∑ j, error j) <= ENNReal.ofReal (1 / 40 : Real))
    {good : Set (forall j, Omega j)} (hgoodMeas : MeasurableSet good)
    (hgood : (33 / 40 : Real) <= (Measure.pi ideal).real good) :
    (4 / 5 : Real) <= (Measure.pi actual).real good := by
  exact four_fifths_of_finiteHistoryTV herror (TVLe.pi htv) hgoodMeas hgood

/-- Constant one-stream error form of
`four_fifths_of_independentFiniteHistoryTV`. -/
theorem four_fifths_of_independentFiniteHistoryTV_const
    {k : Nat} {Omega : Type*} [MeasurableSpace Omega]
    (actual ideal : Measure Omega)
    [IsProbabilityMeasure actual] [IsProbabilityMeasure ideal]
    {error : ENNReal} (htv : TVLe actual ideal error)
    (herror : (k : ENNReal) * error <= ENNReal.ofReal (1 / 40 : Real))
    {good : Set (Fin k -> Omega)} (hgoodMeas : MeasurableSet good)
    (hgood : (33 / 40 : Real) <=
      (Measure.pi (fun _ : Fin k => ideal)).real good) :
    (4 / 5 : Real) <=
      (Measure.pi (fun _ : Fin k => actual)).real good := by
  apply four_fifths_of_independentFiniteHistoryTV
    (actual := fun _ : Fin k => actual) (ideal := fun _ : Fin k => ideal)
    (error := fun _ : Fin k => error) (fun _ => htv)
  · simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using herror
  · exact hgoodMeas
  · exact hgood

/-- Direct operational-path form.  A one-stream TV theorem for the complete Markov path,
followed by the exact-law accuracy theorem for the product of ideal paths, discharges the
`haccuracy` field expected by the slow retained-reference certificate. -/
theorem four_fifths_of_independentPathLawTV
    {k : Nat} {X : Type*} [MeasurableSpace X]
    (P : Nat -> Kernel X X) [forall i, IsMarkovKernel (P i)]
    (mu0 : Measure X) [IsProbabilityMeasure mu0]
    (idealPath : Measure (Nat -> X)) [IsProbabilityMeasure idealPath]
    {error : ENNReal}
    (htv : TVLe (inhomogeneousPathMeasure P mu0) idealPath error)
    (herror : (k : ENNReal) * error <= ENNReal.ofReal (1 / 40 : Real))
    (readout : (Fin k -> Nat -> X) -> Real) (hreadout : Measurable readout)
    {lo hi : Real}
    (hideal : (33 / 40 : Real) <=
      (Measure.pi (fun _ : Fin k => idealPath)).real
        {omega | readout omega ∈ Set.Icc lo hi}) :
    (4 / 5 : Real) <= (independentPathLaw k P mu0).real
      {omega | readout omega ∈ Set.Icc lo hi} := by
  have hmeas : MeasurableSet {omega | readout omega ∈ Set.Icc lo hi} :=
    measurableSet_Icc.preimage hreadout
  have h := four_fifths_of_independentFiniteHistoryTV_const
    (k := k) (actual := inhomogeneousPathMeasure P mu0) (ideal := idealPath)
    htv herror hmeas hideal
  simpa only [independentPathLaw, independentStreamLaw] using h

#print axioms marginalTV_zero_not_jointHistoryProduct_zero
#print axioms one_fourth_le_error_of_jointHistoryProduct
#print axioms measureReal_event_ge_of_finiteHistoryTV
#print axioms four_fifths_of_finiteHistoryTV
#print axioms four_fifths_of_independentFiniteHistoryTV
#print axioms four_fifths_of_independentFiniteHistoryTV_const
#print axioms four_fifths_of_independentPathLawTV

end Ttc.CVFiniteHistoryAccuracyBridge

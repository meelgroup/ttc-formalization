import Ttc.Exec.CVHistoryReferenceAdapter
import Ttc.Exec.CVGaussianCappedCostEnvelope
import Ttc.Exec.CVGaussianSourceSharpCost
import Ttc.Exec.CVIndependentHistoryReference
import Ttc.Exec.CVSourceReferenceTVCapstone

set_option maxHeartbeats 100000

/-!
# Gaussian specialization of the retained-history reference induction

This file applies the history adapter to the actual cost-increment Gaussian cooling
schedule.  The operational mixing field supplies every phase-TV estimate, and the
Gaussian reference-envelope theorem supplies every phase-cost estimate.  The only new
analytic premise is warmth of the exact reference seed marginal at the entrance to each
phase.  Thus the previously law-quantified reference obligations are reduced to the
source's adjacent-Gaussian warmth statement.
-/

namespace Ttc.CVGaussianHistoryReferenceSpecialization

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVGaussianCappedCostEnvelope
open Ttc.CVGaussianSourceSharpCost
open Ttc.CVSeedProjectedDependence
open Ttc.CVHistoryCostedKernel
open Ttc.CVHistoryReferenceAdapter
open Ttc.CVRetainedHistoryReferenceInduction
open Ttc.CVIndependentHistoryReference
open Ttc.CVSourceReferenceTVCapstone
open scoped ENNReal Classical BigOperators

variable {X Seed Score : Type*} [MeasurableSpace X] [MeasurableSpace Seed]
  [MeasurableSpace Score]

/-- Put an initial state into the cumulative-cost/full-history representation.  The
constant tail is harmless: phase `i` overwrites coordinate `i+1` before it is read. -/
def initialHistoryState (x : X) : HistoryState X :=
  ((0, fun _ ↦ x), x)

theorem measurable_initialHistoryState :
    Measurable (initialHistoryState : X → HistoryState X) := by
  unfold initialHistoryState
  fun_prop

noncomputable def initialHistoryLaw (mu : Measure X) : Measure (HistoryState X) :=
  Measure.map initialHistoryState mu

instance initialHistoryLaw.instIsProbabilityMeasure
    (mu : Measure X) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (initialHistoryLaw mu) :=
  Measure.isProbabilityMeasure_map measurable_initialHistoryState.aemeasurable

theorem map_snd_initialHistoryLaw (mu : Measure X) [SFinite mu] :
    Measure.map Prod.snd (initialHistoryLaw mu) = mu := by
  unfold initialHistoryLaw
  rw [Measure.map_map measurable_snd measurable_initialHistoryState]
  convert Measure.map_id
  funext x
  rfl

theorem lintegral_initialHistoryCost (mu : Measure X) :
    (∫⁻ z, z.1.1 ∂initialHistoryLaw mu) = 0 := by
  unfold initialHistoryLaw
  change (∫⁻ z, (Prod.fst ∘ Prod.fst) z ∂Measure.map initialHistoryState mu) = 0
  rw [lintegral_map (measurable_fst.comp measurable_fst)
    measurable_initialHistoryState]
  simp [initialHistoryState]

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev GaussianScoreSeed (n : Nat) := State n × State n

/-- The source adjacent-Gaussian reference is uniformly `2e`-warm.  Keeping this
constant separate from the operational mixing warmth prevents phase-by-phase warmth
budgets from entering the reference expected-cost sum. -/
noncomputable def gaussianReferenceWarm : ENNReal :=
  ENNReal.ofReal (2 * Real.exp 1)

theorem gaussianReferenceWarm_ne_top : gaussianReferenceWarm ≠ ⊤ := by
  unfold gaussianReferenceWarm
  exact ENNReal.ofReal_ne_top

/-- The source adjacent-Gaussian lemma supplies exactly the active successor case of
`hrefWarm`; a larger operational warmth budget is harmless. -/
theorem isWarm_scoreSeedReference_active_of_twoE_le
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {M : ENNReal} (hM : ENNReal.ofReal (2 * Real.exp 1) ≤ M) :
    IsWarm M
      (Measure.map Prod.snd
        (Ttc.CVGaussianScoreSeedPhaseKernel.scoreSeedReference
          (1 - 1 / (2 * (n : Real))) (coolLaw m sigmaSq K i)))
      (ellGaussianProb K delta (sigmaSq (i + 1))) :=
  (Ttc.CVGaussianScoreSeedPhaseKernel.isWarm_snd_scoreSeedReference_standard
    hn hsigma hK hKc hball hfin hi hcc1 hcc hsched hdelta hdeltan).mono hM

/-- On the exact reference tail, the required input warmth follows just from the
declared tail seed marginal and `1 ≤ M`. -/
theorem isWarm_exactTail_of_map_snd_eq
    (rho : Measure (Score × Seed)) (pi : Measure Seed) {M : ENNReal}
    (hmap : Measure.map Prod.snd rho = pi) (hM : 1 ≤ M) :
    IsWarm M (Measure.map Prod.snd rho) pi := by
  rw [hmap]
  exact (IsWarm.refl pi).mono hM

/-- The exact input reference used by the reset induction: the operational initial law
at time zero, then the phase-output reference from the preceding phase. -/
noncomputable def referenceInputFamily
    (mu0 : Measure X) (target : Nat → Measure X) : Nat → Measure X
  | 0 => mu0
  | i + 1 => target i

instance referenceInputFamily.instIsProbabilityMeasure
    (mu0 : Measure X) [IsProbabilityMeasure mu0]
    (target : Nat → Measure X) [∀ i, IsProbabilityMeasure (target i)] (i : Nat) :
    IsProbabilityMeasure (referenceInputFamily mu0 target i) := by
  cases i <;> simp only [referenceInputFamily] <;> infer_instance

/-- Assemble the sole `hrefWarm` binder from its initial, active-successor, and exact-tail
pieces.  The two successor premises are precisely discharged by
`isWarm_scoreSeedReference_active_of_twoE_le` and
`isWarm_exactTail_of_map_snd_eq` in the concrete score-aware construction. -/
theorem referenceInputFamily_warm
    (mu0 : Measure (Score × Seed)) (target : Nat → Measure (Score × Seed))
    (pi : Nat → Measure Seed) (M : Nat → ENNReal) (m : Nat)
    (hstart : IsWarm (M 0) (Measure.map Prod.snd mu0) (pi 0))
    (hactive : ∀ i, i + 1 < m → IsWarm (M (i + 1))
      (Measure.map Prod.snd (target i)) (pi (i + 1)))
    (htail : ∀ i, ¬ i + 1 < m → IsWarm (M (i + 1))
      (Measure.map Prod.snd (target i)) (pi (i + 1))) :
    ∀ i, IsWarm (M i)
      (Measure.map Prod.snd (referenceInputFamily mu0 target i)) (pi i) := by
  intro i
  cases i with
  | zero => simpa only [referenceInputFamily] using hstart
  | succ i =>
      simp only [referenceInputFamily]
      by_cases hi : i + 1 < m
      · exact hactive i hi
      · exact htail i hi

/-! ## Independent-stream and source-certificate packaging -/

/-- Tensor one scalar retained-history reference across all corrected-estimator streams
and immediately package the complete joint TV/expected-cost certificate consumed by the
source global cutoff.  No independence or cost bookkeeping remains downstream.

For the Gaussian specialization, instantiate `Omega` with `HistoryState
(GaussianScoreSeed n)`, `actual` with the terminal retained law above, and `cost z =
z.1.1`. -/
theorem exists_sourceReferenceTVOneRunCertificate_of_scalarHistory
    {Omega : Type*} [MeasurableSpace Omega]
    (k : Nat) (actual : Measure Omega) [IsProbabilityMeasure actual]
    (cost : Omega → ENNReal) (hcost : Measurable cost)
    (value : (Fin k → Omega) → Real) (hvalue : Measurable value)
    {scalarError scalarBudget : ENNReal}
    (hscalar : ∃ reference : Measure Omega,
      IsProbabilityMeasure reference ∧
      TVLe actual reference scalarError ∧
      (∫⁻ omega, cost omega ∂reference) ≤ scalarBudget)
    {runtimeConstant R eps lo hi : Real} {dim : Nat}
    (herror : (k : ENNReal) * scalarError ≤ ENNReal.ofReal (1 / 40 : Real))
    (hbudget : (k : ENNReal) * scalarBudget ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant dim R eps)
    (haccuracy : 4 / 5 ≤ (Measure.pi (fun _ : Fin k ↦ actual)).real
      {omega | value omega ∈ Icc lo hi}) :
    ∃ reference : Measure (Fin k → Omega),
      SourceReferenceTVOneRunCertificate
        (Measure.pi (fun _ : Fin k ↦ actual)) reference
        (totalHistoryCost cost) value runtimeConstant dim R eps lo hi := by
  obtain ⟨scalarReference, hscalarProb, hscalarTV, hscalarMean⟩ := hscalar
  letI : IsProbabilityMeasure scalarReference := hscalarProb
  obtain ⟨reference, hrefProb, hrefTV, hrefMean⟩ :=
    exists_product_historyReference cost hcost
      (fun _ : Fin k ↦ actual) (fun _ : Fin k ↦ scalarError)
      (fun _ : Fin k ↦ scalarBudget)
      (fun _ ↦ ⟨scalarReference, hscalarProb, hscalarTV, hscalarMean⟩)
  refine ⟨reference,
    { actual_probability := inferInstance
      reference_probability := hrefProb
      cost_measurable := measurable_totalHistoryCost hcost
      value_measurable := hvalue
      path_tv := ?_
      reference_expected_queries := ?_
      accuracy := haccuracy }⟩
  · exact hrefTV.mono (by
      simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using herror)
  · exact hrefMean.trans (by
      simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using hbudget)

#print axioms exists_sourceReferenceTVOneRunCertificate_of_scalarHistory

end Ttc.CVGaussianHistoryReferenceSpecialization

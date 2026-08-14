import Ttc.Exec.CVHistoryReferenceAdapter
import Ttc.Exec.CVGaussianCappedCostEnvelope
import Ttc.Exec.CVGaussianSourceSharpCost
import Ttc.Exec.CVIndependentHistoryReference
import Ttc.Exec.CVSourceReferenceTVCapstone

set_option maxHeartbeats 800000

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
  simp [gaussianReferenceWarm]

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
    (mu0 : Measure X) (target : Nat → Measure X)
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

/-- Concrete scalar history-reference theorem for the uncapped Gaussian execution.

All law-quantified hypotheses of `exists_exactHistoryReference_terminal` have
disappeared.  `hrefWarm` is the exact remaining analytic bridge: the seed marginal of
the reference entering phase `i` is warm for the phase-`i` Gaussian target. -/
theorem exists_gaussianHistoryReference
    (hn : 2 ≤ n) (m : Nat)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (q radius : Real) (hq : 1 < q) (hR : 0 ≤ radius)
    (delta sigma shrink : Nat → Real)
    (hdelta : ∀ j, 0 < delta j) (hsigma : ∀ j, 0 < sigma j)
    (hshrink : ∀ j, shrink j ≠ 0)
    (hdeltan : ∀ j, delta j ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ j, j + 1 < m →
      delta j ≤ sigma j / (max 8 (2 * q) * Real.sqrt n))
    (hRsigma : ∀ j, j + 1 < m → radius ≤ q * sigma j * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ radius)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback tail : Nat → Measure (GaussianScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    [∀ j, IsProbabilityMeasure (tail j)]
    [∀ j, IsProbabilityMeasure
      (ellGaussianProb K (delta j) ((sigma j) ^ 2))]
    (mu0 : Measure (GaussianScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → GaussianScoreSeed n) → Real) (eta : Real)
    (hop : SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
          hdelta hshrink steps retries fallback) tail)
      Prod.snd Prod.fst mu0 V m eta)
    (hpi : ∀ j, hop.pi j = ellGaussianProb K (delta j) ((sigma j) ^ 2))
    (referenceWarm : Nat → ENNReal)
    (hReferenceTop : ∀ j, referenceWarm j ≠ ⊤)
    (tauRef : Nat → Measure (GaussianScoreSeed n))
    [∀ i, IsProbabilityMeasure (tauRef i)]
    (htau0 : tauRef 0 = mu0)
    (htauSucc : ∀ i, tauRef (i + 1) = hop.tau i)
    (hrefWarm : ∀ i, IsWarm (referenceWarm i)
      (Measure.map Prod.snd (tauRef i)) (hop.pi i))
    (hReferenceLeOperational : ∀ i,
      referenceWarm i ≤ 2 * hop.warmConst i) :
    ∃ reference : Measure (HistoryState (GaussianScoreSeed n)),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.snd reference = tauRef m ∧
      TVLe
        (retainedPathLaw
          (fun i ↦ historyCostedKernel
            (costedStateScheduleFromSeed
              (costedActiveReferenceTailSchedule m
                (warmFallbackCostedSchedule K hK delta
                  (fun j ↦ (sigma j) ^ 2) shrink hdelta hshrink steps retries fallback)
                tail) i) i)
          (initialHistoryLaw mu0) m)
        reference (∑ i ∈ range m, hop.mixError i) ∧
      (∫⁻ z, z.1.1 ∂reference) ≤
        ∑ i ∈ range m,
          gaussianActiveMeanEnvelope m referenceWarm steps retries i := by
  let S := activeReferenceTailSchedule m
    (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
      hdelta hshrink steps retries fallback) tail
  let QR := costedStateScheduleFromSeed
    (costedActiveReferenceTailSchedule m
      (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback) tail)
  have hforget : ∀ i z, Measure.map Prod.snd (QR i z) =
      stateScheduleFromSeed S i z := by
    intro i z
    exact map_snd_costedStateActiveReferenceTailSchedule m
      (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback)
      (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback) tail
      (fun j x ↦ map_snd_gaussianWarmFallbackCostedPhaseKernel hK
        (delta j) ((sigma j) ^ 2) (shrink j) (hdelta j) (hshrink j)
        (steps j) (retries j) (fallback j) x) i z
  have hphaseTV : ∀ i,
      TVLe ((tauRef i).bind (Kernel.map (QR i) Prod.snd))
        (tauRef (i + 1)) (hop.mixError i) := by
    intro i
    have hk : Kernel.map (QR i) Prod.snd = stateScheduleFromSeed S i := by
      ext z A hA
      rw [Kernel.map_apply _ measurable_snd]
      exact congrArg (fun mu : Measure (GaussianScoreSeed n) ↦ mu A) (hforget i z)
    rw [hk, htauSucc i]
    letI : IsProbabilityMeasure (Measure.map Prod.snd (tauRef i)) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    have hwarm2 : IsWarm (2 * hop.warmConst i)
        (Measure.map Prod.snd (tauRef i)) (hop.pi i) :=
      (hrefWarm i).mono (hReferenceLeOperational i)
    have hm := hop.distributional_mixing i
      (Measure.map Prod.snd (tauRef i)) hwarm2 inferInstance
    change TVLe ((tauRef i).bind
      (Kernel.comap (S i) Prod.snd measurable_snd)) (hop.tau i) (hop.mixError i)
    rw [Arlib.MarkovChains.bind_comap]
    exact hm
  have hphaseCost : ∀ i,
      (∫⁻ x, Ttc.SequentialCost.stepMean (fun _ ↦ QR i) 0 x ∂tauRef i) ≤
        gaussianActiveMeanEnvelope m referenceWarm steps retries i := by
    intro i
    by_cases hi : i + 1 < m
    · rw [gaussianActiveMeanEnvelope, if_pos hi]
      have hwarm : IsWarm (referenceWarm i)
          (Measure.map Prod.snd (tauRef i))
          (ellGaussianProb K (delta i) ((sigma i) ^ 2)) := by
        rw [← hpi i]
        exact hrefWarm i
      simpa only [QR, Ttc.SequentialCost.stepMean] using
        (lintegral_stepMean_costedActive_gaussian_le_referenceEnvelope
          hn m i hi hK hKc hball hq (hdelta i) (hsigma i) (hshrink i)
          (hdeltan i) (hdeltaq i hi) hR (hRsigma i hi) hKR
          (steps i) (retries i) (fallback i) tail (tauRef i)
          (hReferenceTop i) hwarm)
    · rw [gaussianActiveMeanEnvelope, if_neg hi]
      exact le_of_eq (by
        simpa only [QR, Ttc.SequentialCost.stepMean] using
        (lintegral_stepMean_costedStateActiveReferenceTailSchedule_inactive
          m
          (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback)
          tail (tauRef i) i hi))
  have hinitState : Measure.map Prod.snd (initialHistoryLaw mu0) = tauRef 0 := by
    rw [map_snd_initialHistoryLaw, htau0]
  have hmain := exists_historyReference_of_incrementKernels QR
    (initialHistoryLaw mu0) (initialHistoryLaw mu0) tauRef
    hop.mixError (gaussianActiveMeanEnvelope m referenceWarm steps retries)
    (d := 0) (initialBudget := 0) (TVLe.refl _)
    hinitState (by simp [lintegral_initialHistoryCost]) hphaseTV hphaseCost m
  simpa only [QR, zero_add] using hmain

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

/-- Input-indexed version of the independent retained-history packaging.  This produces
the exact `SourcePublicReferenceTVCertificates` object required by the source-sharp
Theorem 1.1 arithmetic.  Consequently, after a concrete scalar history reference and
retained-history accuracy are supplied for each input, no further measure/product/cost
glue remains. -/
theorem exists_sourcePublicReferenceTVCertificates_of_scalarHistory
    (dim : Nat) (runtimeConstant : Real)
    (radialR : Set (Ttc.Space dim) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput dim → Type*)
    [∀ a, MeasurableSpace (Omega a)]
    (k : Ttc.CVAdaptive.VolumeInput dim → Nat)
    (actualScalar : ∀ a, Measure (Omega a))
    [∀ a, IsProbabilityMeasure (actualScalar a)]
    (scalarCost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, (Fin (k a) → Omega a) → Real)
    (scalarError scalarBudget : Ttc.CVAdaptive.VolumeInput dim → ENNReal)
    (hcost : ∀ a, Measurable (scalarCost a))
    (hvalue : ∀ a, Measurable (value a))
    (hscalar : ∀ a, ∃ reference : Measure (Omega a),
      IsProbabilityMeasure reference ∧
      TVLe (actualScalar a) reference (scalarError a) ∧
      (∫⁻ omega, scalarCost a omega ∂reference) ≤ scalarBudget a)
    (herror : ∀ a, (k a : ENNReal) * scalarError a ≤
      ENNReal.ofReal (1 / 40 : Real))
    (hbudget : ∀ a, (k a : ENNReal) * scalarBudget a ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant dim (radialR a.1) a.2.1)
    (haccuracy : ∀ (K : Set (Ttc.Space dim)) (eps p : Real),
      0 < eps → 0 < p → p < 1 → Convex Real K →
      ball (0 : Ttc.Space dim) 1 ⊆ K → volume K ≠ ⊤ →
      4 / 5 ≤ (Measure.pi
        (fun _ : Fin (k (K, eps, p)) ↦ actualScalar (K, eps, p))).real
        {omega | value (K, eps, p) omega ∈
          Icc ((1 - eps) * (volume K).toReal)
            ((1 + eps) * (volume K).toReal)}) :
    ∃ reference : ∀ a, Measure (Fin (k a) → Omega a),
      SourcePublicReferenceTVCertificates dim runtimeConstant radialR
        (fun a ↦ Fin (k a) → Omega a)
        (fun a ↦ Measure.pi (fun _ : Fin (k a) ↦ actualScalar a))
        reference
        (fun a ↦ totalHistoryCost (scalarCost a)) value := by
  choose scalarReference hscalarProb hscalarTV hscalarMean using hscalar
  letI : ∀ a, IsProbabilityMeasure (scalarReference a) := hscalarProb
  let reference : ∀ a, Measure (Fin (k a) → Omega a) := fun a ↦
    Measure.pi (fun _ : Fin (k a) ↦ scalarReference a)
  refine ⟨reference,
    { actual_probability := fun _ ↦ inferInstance
      reference_probability := fun _ ↦ inferInstance
      cost_measurable := fun a ↦ measurable_totalHistoryCost (hcost a)
      value_measurable := hvalue
      path_tv := ?_
      reference_expected_queries := ?_
      accuracy := haccuracy }⟩
  · intro a
    have htv := (product_historyReference (scalarCost a) (hcost a)
      (fun _ : Fin (k a) ↦ actualScalar a)
      (fun _ : Fin (k a) ↦ scalarReference a)
      (fun _ : Fin (k a) ↦ scalarError a)
      (fun _ : Fin (k a) ↦ scalarBudget a)
      (fun _ ↦ hscalarTV a) (fun _ ↦ hscalarMean a)).1
    exact htv.mono (by
      simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using herror a)
  · intro a
    have hmean := (product_historyReference (scalarCost a) (hcost a)
      (fun _ : Fin (k a) ↦ actualScalar a)
      (fun _ : Fin (k a) ↦ scalarReference a)
      (fun _ : Fin (k a) ↦ scalarError a)
      (fun _ : Fin (k a) ↦ scalarBudget a)
      (fun _ ↦ hscalarTV a) (fun _ ↦ hscalarMean a)).2
    exact hmean.trans (by
      simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using hbudget a)

#print axioms exists_gaussianHistoryReference
#print axioms exists_sourceReferenceTVOneRunCertificate_of_scalarHistory
#print axioms exists_sourcePublicReferenceTVCertificates_of_scalarHistory

end Ttc.CVGaussianHistoryReferenceSpecialization

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CVCorrectedFixedBlockCost
import Ttc.Exec.CostedPackedJointLaw
import Ttc.Volume.AdaptiveTerminalWarmLawAdjustable

/-!
# Corrected source-hybrid runtime assembly

This file discharges the two abstract warm-cost premises in
`CVCorrectedFixedBlockCost` with the adjustable-radius traced warm-phase theorem.  The
step counts remain `Nat` values obtained by rounding the deadline in the source figure.
It also gives the joint state projection needed to apply the `4/5 -> 3/4` runtime cutoff
to the independent fixed/adaptive block execution.
-/

namespace Ttc.CVCorrectedHybridRuntimeAssembly

open MeasureTheory ProbabilityTheory Metric Set Function
open Arlib Arlib.Probability Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.CVCorrectedFixedBlockCost Ttc.CostedWarmPhaseRejection
open Ttc.CostedPackedWarmSchedule Ttc.CostedPackedJointLaw
open Ttc.CVCostedRuntimeCutoff
open scoped ENNReal Classical Pointwise

variable {n r k m : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-! ## Rounded source deadline -/

/-- The source figure's displayed proper-step deadline, rounded up to a positive `Nat`. -/
noncomputable def sourceFigureSteps (n : Nat) (sigmaSq nu : Real) : Nat :=
  ⌈sourceFigureProperSteps n sigmaSq nu⌉₊ + 1

theorem sourceFigureProperSteps_le_steps (n : Nat) (sigmaSq nu : Real) :
    sourceFigureProperSteps n sigmaSq nu ≤
      (sourceFigureSteps n sigmaSq nu : Real) := by
  have h := Nat.le_ceil (sourceFigureProperSteps n sigmaSq nu)
  rw [sourceFigureSteps]
  push_cast
  linarith

theorem sourceFigureSteps_pos (n : Nat) (sigmaSq nu : Real) :
    0 < sourceFigureSteps n sigmaSq nu := by
  simp [sourceFigureSteps]

/-- The adaptive block already uses the same honest `ceil + 1` conversion. -/
theorem adaptiveDeadline_le_terminalSteps
    (q N s0 eps : Real) (i : Fin (m + 1)) :
    Ttc.CVAdaptive.adaptiveTerminalDeadlineQ (n := n) q N s0 eps i ≤
      (Ttc.CVAdaptive.adaptiveTerminalStepsQ (n := n) (m := m) q N s0 eps i : Real) :=
  Ttc.CVAdaptive.adaptiveTerminalStepsQ_spec q N s0 eps i

/-! ## Discharging the fixed-block `hpost` premise -/

/-- The post-ambient fixed coordinates satisfy the exact `hpost` interface once the
adjustable-radius geometry, warmness and two restart-acceptance bounds are supplied. -/
theorem fixed_hpost_of_adjustable
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {s0 : Real} (hs0 : 0 < s0)
    (q delta R : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Real)
    (hq : ∀ i, 1 < q i) (hdelta : ∀ i, 0 < delta i)
    (hdeltan : ∀ i, delta i ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ i, delta i ≤ Real.sqrt (fixedSigmaSq n s0 i) /
      (max 8 (2 * q i) * Real.sqrt n))
    (hR : ∀ i, 0 ≤ R i)
    (hRsigma : ∀ i, R i ≤ q i * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hKR : ∀ i x, x ∈ K → ‖x‖ ≤ R i)
    (M : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → ENNReal)
    (mu0 : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (hwarm : ∀ i, IsWarm (M i) (mu0 i)
      (ellGaussianProb K (delta i) (fixedSigmaSq n s0 i)))
    (steps : Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Nat)
    (hhalf : ∀ i, ENNReal.ofReal (1 / 2 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian K (delta i) (fixedSigmaSq n s0 i)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) • K))
    (hquarter : ∀ i, ENNReal.ofReal (1 / 4 : Real) ≤
      ((Ttc.SpeedyRejection.phasePointProposal K (delta i) (fixedSigmaSq n s0 i)
        (mu0 i) (steps i)).withDensity (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (fixedSigmaSq n s0 i) x))) univ)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    ∀ i : Fin (Ttc.CVHybridSchedule.coldPhases n s0),
      ¬ ambientEligible n (fixedSigmaSq n s0 i) →
      6 * (∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK (delta i) (fixedSigmaSq n s0 i)
        (hdelta i) (mu0 i) (steps i))) ≤ 80 * ((steps i : ENNReal) * M i) := by
  intro i _hi
  have hs : 0 < fixedSigmaSq n s0 i :=
    geomSchedule_pos hs0 (by positivity) i
  have hsq : Real.sqrt (fixedSigmaSq n s0 i) ^ 2 = fixedSigmaSq n s0 i :=
    Real.sq_sqrt hs.le
  simpa only [hsq] using
    (six_mul_lintegral_warmPhaseCostLaw_le_eighty_mul_adjustable
      hn hK hKc hball (hq i) (hdelta i) (Real.sqrt_pos.2 hs) (hdeltan i)
      (hdeltaq i) (hR i) (hRsigma i) (hKR i) (by simpa only [hsq] using hwarm i)
      (steps i) (by simpa only [hsq] using hhalf i)
      (by simpa only [hsq] using hquarter i) hc2)

/-! ## A phase-dependent adaptive warm family -/

/-- Traced warm-phase laws where the truncated body and every numerical parameter may
depend on the accelerated phase. -/
noncomputable def varyingWarmCoordinateLaw
    (K : Fin m → Set (State n)) (hK : ∀ i, MeasurableSet (K i))
    (delta sigma : Fin m → Real) (hdelta : ∀ i, 0 < delta i)
    (mu0 : Fin m → Measure (State n)) (steps : Fin m → Nat)
    (_j : Fin r) (i : Fin m) (_l : Fin k) : Measure (ENNReal × State n) :=
  warmPhaseCostLaw (K i) (hK i) (delta i) ((sigma i) ^ 2)
    (hdelta i) (mu0 i) (steps i)

instance (K : Fin m → Set (State n)) (hK : ∀ i, MeasurableSet (K i))
    (delta sigma : Fin m → Real) (hdelta : ∀ i, 0 < delta i)
    (mu0 : Fin m → Measure (State n)) [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin m → Nat) (j : Fin r) (i : Fin m) (l : Fin k) :
    IsProbabilityMeasure (varyingWarmCoordinateLaw K hK delta sigma hdelta mu0 steps j i l) := by
  unfold varyingWarmCoordinateLaw
  infer_instance

/-- The accelerated per-coordinate cost premise, fully reduced to the existing adjustable
warm-phase theorem. -/
theorem varyingWarmCoordinateCost_le_adjustable
    (hn : 2 ≤ n)
    (K : Fin m → Set (State n)) (hK : ∀ i, MeasurableSet (K i))
    (hKc : ∀ i, Convex Real (K i))
    (hball : ∀ i, ball (0 : State n) 1 ⊆ K i)
    (q delta sigma R : Fin m → Real)
    (hq : ∀ i, 1 < q i) (hdelta : ∀ i, 0 < delta i)
    (hsigma : ∀ i, 0 < sigma i)
    (hdeltan : ∀ i, delta i ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ i, delta i ≤ sigma i / (max 8 (2 * q i) * Real.sqrt n))
    (hR : ∀ i, 0 ≤ R i) (hRsigma : ∀ i, R i ≤ q i * sigma i * Real.sqrt n)
    (hKR : ∀ i x, x ∈ K i → ‖x‖ ≤ R i)
    (M : Fin m → ENNReal) (mu0 : Fin m → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (hwarm : ∀ i, IsWarm (M i) (mu0 i)
      (ellGaussianProb (K i) (delta i) ((sigma i) ^ 2)))
    (steps : Fin m → Nat)
    (hhalf : ∀ i, ENNReal.ofReal (1 / 2 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian (K i) (delta i) ((sigma i) ^ 2)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) • K i))
    (hquarter : ∀ i, ENNReal.ofReal (1 / 4 : Real) ≤
      ((Ttc.SpeedyRejection.phasePointProposal (K i) (delta i) ((sigma i) ^ 2)
        (mu0 i) (steps i)).withDensity (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) ((sigma i) ^ 2) x))) univ)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    ∀ (j : Fin r) (i : Fin m) (l : Fin k),
      6 * (∫⁻ z, z.1 ∂(varyingWarmCoordinateLaw K hK delta sigma hdelta
      mu0 steps j i l)) ≤ 80 * ((steps i : ENNReal) * M i) := by
  intro j i l
  exact six_mul_lintegral_warmPhaseCostLaw_le_eighty_mul_adjustable
    hn (hK i) (hKc i) (hball i) (hq i) (hdelta i) (hsigma i) (hdeltan i)
    (hdeltaq i) (hR i) (hRsigma i) (hKR i) (hwarm i) (steps i)
    (hhalf i) (hquarter i) hc2

/-! ## Joint law and runtime cutoff for the two-block execution -/

abbrev HybridStateSpace (n r k c m : Nat) :=
  RunSpace (Fin k → State n) r c × RunSpace (Fin k → State n) r m

/-- Forget all recorded query counts while retaining both fixed and accelerated blocks. -/
def hybridStateProjection {c m : Nat}
    (omega : CostedPackedSpace n r c k × CostedPackedSpace n r m k) :
    HybridStateSpace n r k c m :=
  (stateProjection omega.1, stateProjection omega.2)

theorem measurable_hybridStateProjection {c m : Nat} :
    Measurable (hybridStateProjection (n := n) (r := r) (k := k) (c := c) (m := m)) := by
  exact (measurable_stateProjection.comp measurable_fst).prodMk
    (measurable_stateProjection.comp measurable_snd)

/-- Full state-law identity for the independently executed fixed and accelerated blocks. -/
theorem map_hybridBlockCostLaw_stateProjection
    {s0 : Real}
    (rhoFixed : Fin r → Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Fin k →
      Measure (ENNReal × State n))
    (rhoAdaptive : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rhoFixed j i l)]
    [∀ j i l, IsProbabilityMeasure (rhoAdaptive j i l)] :
    Measure.map hybridStateProjection (hybridBlockCostLaw rhoFixed rhoAdaptive) =
      (runMeasure (packedPhaseLaw
        (fun j i l => Measure.map Prod.snd (rhoFixed j i l)))).prod
      (runMeasure (packedPhaseLaw
        (fun j i l => Measure.map Prod.snd (rhoAdaptive j i l)))) := by
  unfold hybridStateProjection hybridBlockCostLaw
  change Measure.map (Prod.map stateProjection stateProjection)
    ((costedPackedLaw rhoFixed).prod (costedPackedLaw rhoAdaptive)) = _
  rw [← Measure.map_prod_map _ _ measurable_stateProjection measurable_stateProjection,
    map_costedPackedLaw_stateProjection, map_costedPackedLaw_stateProjection]

/-- Accuracy events for an arbitrary measurable two-block estimator transport to the same
law that records actual membership queries. -/
theorem measureReal_hybridEstimator_event
    {s0 : Real}
    (rhoFixed : Fin r → Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Fin k →
      Measure (ENNReal × State n))
    (rhoAdaptive : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rhoFixed j i l)]
    [∀ j i l, IsProbabilityMeasure (rhoAdaptive j i l)]
    (est : HybridStateSpace n r k (Ttc.CVHybridSchedule.coldPhases n s0) m → Real)
    (hest : Measurable est) {S : Set Real} (hS : MeasurableSet S) :
    (hybridBlockCostLaw rhoFixed rhoAdaptive).real
        {omega | est (hybridStateProjection omega) ∈ S} =
      ((runMeasure (packedPhaseLaw
        (fun j i l => Measure.map Prod.snd (rhoFixed j i l)))).prod
        (runMeasure (packedPhaseLaw
          (fun j i l => Measure.map Prod.snd (rhoAdaptive j i l))))).real
        {omega | est omega ∈ S} := by
  have hmap := map_hybridBlockCostLaw_stateProjection rhoFixed rhoAdaptive
  have hleft :
      Measure.map (est ∘ hybridStateProjection)
          (hybridBlockCostLaw rhoFixed rhoAdaptive) S =
        hybridBlockCostLaw rhoFixed rhoAdaptive
          {omega | est (hybridStateProjection omega) ∈ S} := by
    rw [Measure.map_apply (hest.comp measurable_hybridStateProjection) hS]
    rfl
  have hright :
      Measure.map est
        ((runMeasure (packedPhaseLaw
          (fun j i l => Measure.map Prod.snd (rhoFixed j i l)))).prod
          (runMeasure (packedPhaseLaw
            (fun j i l => Measure.map Prod.snd (rhoAdaptive j i l))))) S =
        ((runMeasure (packedPhaseLaw
          (fun j i l => Measure.map Prod.snd (rhoFixed j i l)))).prod
          (runMeasure (packedPhaseLaw
            (fun j i l => Measure.map Prod.snd (rhoAdaptive j i l)))))
          {omega | est omega ∈ S} := by
    rw [Measure.map_apply hest hS]
    rfl
  change ((hybridBlockCostLaw rhoFixed rhoAdaptive)
    {omega | est (hybridStateProjection omega) ∈ S}).toReal = _
  rw [← hleft, ← Measure.map_map hest measurable_hybridStateProjection,
    hmap, hright]
  rfl

/-- The source's `4/5 -> 3/4` runtime-cutoff calculation on the corrected two-block law.
The expected-cost hypothesis is now about the actual sum of recorded membership queries. -/
theorem cutoff_success_correctedHybridBlock
    {s0 : Real}
    (rhoFixed : Fin r → Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Fin k →
      Measure (ENNReal × State n))
    (rhoAdaptive : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rhoFixed j i l)]
    [∀ j i l, IsProbabilityMeasure (rhoAdaptive j i l)]
    (est : HybridStateSpace n r k (Ttc.CVHybridSchedule.coldPhases n s0) m → Real)
    (hest : Measurable est) {B L : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ omega, totalHybridMembershipQueries omega
      ∂(hybridBlockCostLaw rhoFixed rhoAdaptive)) ≤ B)
    (hratio : B / L ≤ ENNReal.ofReal (1 / 20 : Real))
    {fallback lo hi : Real}
    (haccuracy : 4 / 5 ≤
      ((runMeasure (packedPhaseLaw
        (fun j i l => Measure.map Prod.snd (rhoFixed j i l)))).prod
        (runMeasure (packedPhaseLaw
          (fun j i l => Measure.map Prod.snd (rhoAdaptive j i l))))).real
        {omega | est omega ∈ Icc lo hi}) :
    3 / 4 ≤ (hybridBlockCostLaw rhoFixed rhoAdaptive).real
      {omega | cutoffValue L fallback totalHybridMembershipQueries
        (est ∘ hybridStateProjection) omega ∈ Icc lo hi} := by
  letI : IsProbabilityMeasure (hybridBlockCostLaw rhoFixed rhoAdaptive) := by
    unfold hybridBlockCostLaw
    infer_instance
  apply cutoff_success_three_quarters measurable_totalHybridMembershipQueries
    (hest.comp measurable_hybridStateProjection) hL0 hLtop hmean hratio
  change 4 / 5 ≤ (hybridBlockCostLaw rhoFixed rhoAdaptive).real
    {omega | est (hybridStateProjection omega) ∈ Icc lo hi}
  rw [measureReal_hybridEstimator_event rhoFixed rhoAdaptive est hest measurableSet_Icc]
  exact haccuracy

/-- Remove the common factor six from a corrected operational accounting theorem. -/
theorem expectedQueries_le_of_six_mul_le {α : Type*} [MeasurableSpace α]
    {mu : Measure α}
    {cost : α → ENNReal} {B : ENNReal}
    (h : 6 * (∫⁻ omega, cost omega ∂mu) ≤ B) :
    (∫⁻ omega, cost omega ∂mu) ≤ B := by
  exact (by
    calc
      (∫⁻ omega, cost omega ∂mu) = 1 * (∫⁻ omega, cost omega ∂mu) := by simp
      _ ≤ 6 * (∫⁻ omega, cost omega ∂mu) :=
        mul_le_mul_right' (by norm_num : (1 : ENNReal) ≤ 6) _
      _ ≤ B := h)

/-- Direct adapter from the factor-six corrected hybrid accounting theorem to the runtime
cutoff.  This is the form consumed after applying
`six_mul_lintegral_correctedHybridBlock_le`. -/
theorem cutoff_success_correctedHybridBlock_of_six
    {s0 : Real}
    (rhoFixed : Fin r → Fin (Ttc.CVHybridSchedule.coldPhases n s0) → Fin k →
      Measure (ENNReal × State n))
    (rhoAdaptive : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rhoFixed j i l)]
    [∀ j i l, IsProbabilityMeasure (rhoAdaptive j i l)]
    (est : HybridStateSpace n r k (Ttc.CVHybridSchedule.coldPhases n s0) m → Real)
    (hest : Measurable est) {B L : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hsix : 6 * (∫⁻ omega, totalHybridMembershipQueries omega
      ∂(hybridBlockCostLaw rhoFixed rhoAdaptive)) ≤ B)
    (hratio : B / L ≤ ENNReal.ofReal (1 / 20 : Real))
    {fallback lo hi : Real}
    (haccuracy : 4 / 5 ≤
      ((runMeasure (packedPhaseLaw
        (fun j i l => Measure.map Prod.snd (rhoFixed j i l)))).prod
        (runMeasure (packedPhaseLaw
          (fun j i l => Measure.map Prod.snd (rhoAdaptive j i l))))).real
        {omega | est omega ∈ Icc lo hi}) :
    3 / 4 ≤ (hybridBlockCostLaw rhoFixed rhoAdaptive).real
      {omega | cutoffValue L fallback totalHybridMembershipQueries
        (est ∘ hybridStateProjection) omega ∈ Icc lo hi} := by
  exact cutoff_success_correctedHybridBlock rhoFixed rhoAdaptive est hest hL0 hLtop
    (expectedQueries_le_of_six_mul_le hsix) hratio haccuracy

/-! ## Independent cutoff-run amplification -/

/-- IID copies of any one-run cost/output law, specialized to the paper's cutoff followed
by a median.  Applied with `oneLaw = hybridBlockCostLaw ...`, this turns the preceding
`3/4` one-run theorem into confidence `1-p` without charging the repetition index inside
the one-run execution. -/
theorem median_cutoff_success_iid
    {Ω : Type*} [MeasurableSpace Ω] (oneLaw : Measure Ω)
    [IsProbabilityMeasure oneLaw]
    {r : Nat} (hr : 0 < r)
    {cost : Ω → ENNReal} {value : Ω → Real}
    (hcost : Measurable cost) (hvalue : Measurable value)
    {B L : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ omega, cost omega ∂oneLaw) ≤ B)
    (hratio : B / L ≤ ENNReal.ofReal (1 / 20 : Real))
    {fallback lo hi p : Real}
    (haccuracy : 4 / 5 ≤ oneLaw.real {omega | value omega ∈ Icc lo hi})
    (hp : 0 < p)
    (hreps : Real.log (1 / p) / (2 * (3 / 4 - 1 / 2) ^ 2) ≤ (r : Real)) :
    1 - p ≤ (Measure.pi (fun _ : Fin r => oneLaw)).real
      {omega | medianSel (fun i => cutoffValue L fallback cost value (omega i)) ∈
        Icc lo hi} := by
  let mu : Measure (Fin r → Ω) := Measure.pi (fun _ : Fin r => oneLaw)
  let costRun : Fin r → (Fin r → Ω) → ENNReal := fun i omega => cost (omega i)
  let valueRun : Fin r → (Fin r → Ω) → Real := fun i omega => value (omega i)
  let med : (Fin r → Ω) → Real :=
    fun omega => medianSel (fun i => cutoffValue L fallback cost value (omega i))
  letI : IsProbabilityMeasure mu := by
    dsimp only [mu]
    infer_instance
  have hcostRun : ∀ i, Measurable (costRun i) :=
    fun i => hcost.comp (measurable_pi_apply i)
  have hvalueRun : ∀ i, Measurable (valueRun i) :=
    fun i => hvalue.comp (measurable_pi_apply i)
  have hmeanRun : ∀ i, (∫⁻ omega, costRun i omega ∂mu) ≤ B := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin r => oneLaw) i
    rw [show (∫⁻ omega, costRun i omega ∂mu) = ∫⁻ x, cost x ∂oneLaw by
      exact hmp.lintegral_comp hcost]
    exact hmean
  have haccuracyRun : ∀ i, 4 / 5 ≤ mu.real
      {omega | valueRun i omega ∈ Icc lo hi} := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin r => oneLaw) i
    let G : Set Ω := value ⁻¹' Icc lo hi
    have hG : MeasurableSet G := measurableSet_Icc.preimage hvalue
    have heq : mu.real {omega | valueRun i omega ∈ Icc lo hi} =
        oneLaw.real {omega | value omega ∈ Icc lo hi} := by
      change (mu ((fun omega : Fin r → Ω => omega i) ⁻¹' G)).toReal =
        (oneLaw G).toReal
      rw [← Measure.map_apply (measurable_pi_apply i) hG, hmp.map_eq]
    rw [heq]
    exact haccuracy
  have hindep : iIndepFun
      (fun i omega => cutoffValue L fallback (costRun i) (valueRun i) omega) mu := by
    dsimp only [mu, costRun, valueRun]
    exact iIndepFun_pi fun _ =>
      (measurable_cutoffValue hcost hvalue).aemeasurable
  have hmedian : ∀ omega, IsMedian
      (fun i => cutoffValue L fallback (costRun i) (valueRun i) omega) (med omega) := by
    intro omega
    exact medianSel_isMedian _
  have hmain := median_cutoff_success (mu := mu) hr hcostRun hvalueRun
    hL0 hLtop hmeanRun hratio haccuracyRun hindep hmedian hp hreps
  simpa only [mu, costRun, valueRun, med] using hmain

end Ttc.CVCorrectedHybridRuntimeAssembly

#print axioms Ttc.CVCorrectedHybridRuntimeAssembly.fixed_hpost_of_adjustable
#print axioms Ttc.CVCorrectedHybridRuntimeAssembly.varyingWarmCoordinateCost_le_adjustable
#print axioms Ttc.CVCorrectedHybridRuntimeAssembly.cutoff_success_correctedHybridBlock
#print axioms Ttc.CVCorrectedHybridRuntimeAssembly.median_cutoff_success_iid

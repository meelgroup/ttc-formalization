import Ttc.Exec.CVCostedAdjustablePublicEstimator
import Ttc.Exec.CVCorrectedHybridRuntimeAssembly
import Ttc.Volume.ExpectedQueryBodyRegularization

/-! Independent cutoff amplification of the complete costed adjustable estimator. -/

namespace Ttc.CVCostedAdjustableOuterMedian

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVAdaptive Ttc.CVCostedAdjustablePublicEstimator
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def outerCutoffReps (p : Real) : Nat :=
  ⌈Real.log (1 / p) / (2 * (3 / 4 - 1 / 2) ^ 2)⌉₊ + 1

theorem outerCutoffReps_pos (p : Real) : 0 < outerCutoffReps p := by
  unfold outerCutoffReps
  omega

theorem outerCutoffReps_spec (p : Real) :
    Real.log (1 / p) / (2 * (3 / 4 - 1 / 2) ^ 2) ≤ (outerCutoffReps p : Real) := by
  have h := Nat.le_ceil (Real.log (1 / p) / (2 * (3 / 4 - 1 / 2) ^ 2))
  unfold outerCutoffReps
  push_cast
  linarith

noncomputable def baseInput (a : VolumeInput n) : VolumeInput n :=
  (a.1, a.2.1, (1 : Real) / 5)

abbrev BaseCostCoin (n : Nat) (a : VolumeInput n) :=
  Ttc.CostedPackedWarmSchedule.CostedPackedSpace n
    (guardedR (baseInput a)) (guardedM (baseInput a) + 1) (guardedK (baseInput a))

abbrev OuterCostCoin (n : Nat) (a : VolumeInput n) :=
  Fin (outerCutoffReps a.2.2) → BaseCostCoin n a

noncomputable def baseCostLaw (hn : 21 ≤ n) (a : VolumeInput n) :
    Measure (BaseCostCoin n a) := by
  classical
  exact if h : 0 < a.2.1 ∧ MeasurableSet a.1 then
    let b := baseInput a
    let hN : 0 < guardedC b ^ 2 * (n : Real) := by
      have hC : 0 < guardedC b := Ttc.CV.cvRadius_pos b.1
      positivity
    let hs0 : 0 < guardedS0 b := polynomialEndpointSigmaSq_pos (by omega)
      (by
        unfold guardedEta
        have hb : b.2.1 = a.2.1 := rfl
        have : 0 < guardedAccuracy b := by
          unfold guardedAccuracy
          rw [hb]
          exact lt_min h.1 zero_lt_one
        positivity)
    publicTerminalCostLaw (by omega) b h.2 hN hs0
  else Measure.dirac (fun _ _ _ => (0, 0))

instance isProbabilityMeasure_baseCostLaw (hn : 21 ≤ n) (a : VolumeInput n) :
    IsProbabilityMeasure (baseCostLaw hn a) := by
  classical
  unfold baseCostLaw
  split_ifs with h
  · dsimp only
    let b := baseInput a
    have hN : 0 < guardedC b ^ 2 * (n : Real) := by
      have hC : 0 < guardedC b := Ttc.CV.cvRadius_pos b.1
      positivity
    have heta : 0 < guardedEta b := by
      unfold guardedEta
      have hb : b.2.1 = a.2.1 := rfl
      have : 0 < guardedAccuracy b := by
        unfold guardedAccuracy
        rw [hb]
        exact lt_min h.1 zero_lt_one
      positivity
    have hs0 : 0 < guardedS0 b := polynomialEndpointSigmaSq_pos (by omega) heta
    let rhoCost := publicTerminalCostFamily (by omega : 1 ≤ n) b h.2 hN hs0
    letI : ∀ j i l, IsProbabilityMeasure (rhoCost j i l) := by
      intro j i l
      exact Ttc.CostedAdaptiveTerminalPhaseAssembly.isProbabilityMeasure_terminalCoordinateCostLaw
        (r := guardedR b) (m := guardedM b) (k := guardedK b) (by omega)
        hN hs0 endpointRho_pos h.2 j i l
    change IsProbabilityMeasure (Ttc.CostedPackedWarmSchedule.costedPackedLaw rhoCost)
    infer_instance
  · infer_instance

noncomputable def outerCostLaw (hn : 21 ≤ n) (a : VolumeInput n) :
    Measure (OuterCostCoin n a) := Measure.pi fun _ => baseCostLaw hn a

instance isProbabilityMeasure_outerCostLaw (hn : 21 ≤ n) (a : VolumeInput n) :
    IsProbabilityMeasure (outerCostLaw hn a) := by
  unfold outerCostLaw
  infer_instance

noncomputable def baseValue (a : VolumeInput n) (omega : BaseCostCoin n a) : Real :=
  adjustablePublicRawEstimator (baseInput a)
    (Ttc.CostedPackedJointLaw.stateProjection omega)

noncomputable def baseQueryCost (a : VolumeInput n) (omega : BaseCostCoin n a) : ENNReal :=
  Ttc.CostedPackedWarmSchedule.totalMembershipQueries omega

noncomputable def outerEstimator (a : VolumeInput n) (omega : OuterCostCoin n a) : Real :=
  medianSel fun t => Ttc.CVCostedRuntimeCutoff.cutoffValue
    (publicTerminalCutoff (baseInput a)) 0 (baseQueryCost a) (baseValue a) (omega t)

/-- Actual stopped cost: each independent copy is charged only up to its deterministic
deadline. -/
noncomputable def outerQueryCost (a : VolumeInput n) (omega : OuterCostCoin n a) : ENNReal :=
  ∑ t, min (baseQueryCost a (omega t)) (publicTerminalCutoff (baseInput a))

theorem measurable_baseQueryCost (a : VolumeInput n) : Measurable (baseQueryCost a) :=
  Ttc.CostedPackedWarmSchedule.measurable_totalMembershipQueries

theorem measurable_baseValue (a : VolumeInput n) (hK : MeasurableSet a.1) :
    Measurable (baseValue a) := by
  exact (measurable_adjustablePublicRawEstimator (baseInput a) (by simpa [baseInput] using hK)).comp
    Ttc.CostedPackedJointLaw.measurable_stateProjection

theorem measurable_outerEstimator (a : VolumeInput n) (hK : MeasurableSet a.1) :
    Measurable (outerEstimator a) := by
  unfold outerEstimator
  apply measurable_medianSel
  intro t
  exact (Ttc.CVCostedRuntimeCutoff.measurable_cutoffValue (measurable_baseQueryCost a)
    (measurable_baseValue a hK)).comp (measurable_pi_apply t)

theorem measurable_outerQueryCost (a : VolumeInput n) : Measurable (outerQueryCost a) := by
  unfold outerQueryCost
  apply Finset.measurable_fun_sum
  intro t ht
  exact ((measurable_baseQueryCost a).comp (measurable_pi_apply t)).min measurable_const

theorem baseCostLaw_eq_raw (hn : 21 ≤ n) (a : VolumeInput n)
    (heps : 0 < a.2.1) (hK : MeasurableSet a.1)
    (hN : 0 < guardedC (baseInput a) ^ 2 * (n : Real))
    (hs0 : 0 < guardedS0 (baseInput a)) :
    baseCostLaw hn a = publicTerminalCostLaw (by omega) (baseInput a) hK hN hs0 := by
  classical
  unfold baseCostLaw
  rw [dif_pos ⟨heps, hK⟩]

/-- Arbitrary-confidence cutoff accuracy from genuinely independent copies of the complete
costed public estimator. -/
theorem outerMedian_accuracy
    (hn : 21 ≤ n) (a : VolumeInput n)
    (heps : 0 < a.2.1) (hp : 0 < a.2.2) (hp1 : a.2.2 < 1)
    (hKc : Convex Real a.1) (hKcl : IsClosed a.1) (hKb : Bornology.IsBounded a.1)
    (hvol : 0 < volume a.1)
    (hclosedBall : closedBall (0 : State n) 1 ⊆ a.1) (hfin : volume a.1 ≠ ⊤) :
    1 - a.2.2 ≤ (outerCostLaw hn a).real
      {omega | outerEstimator a omega ∈ Ttc.relErr a.2.1 (volume a.1).toReal} := by
  let b := baseInput a
  have hbK : b.1 = a.1 := rfl
  have hbE : b.2.1 = a.2.1 := rfl
  have hbeps : 0 < b.2.1 := by simpa [hbE] using heps
  have hN : 0 < guardedC b ^ 2 * (n : Real) := by
    have hC : 0 < guardedC b := Ttc.CV.cvRadius_pos b.1
    positivity
  have heta : 0 < guardedEta b := by
    unfold b baseInput guardedEta guardedAccuracy
    positivity
  have hs0 : 0 < guardedS0 b := polynomialEndpointSigmaSq_pos (by omega) heta
  have hlaw : baseCostLaw hn a =
      publicTerminalCostLaw (by omega) b hKcl.measurableSet hN hs0 := by
    exact baseCostLaw_eq_raw hn a heps hKcl.measurableSet hN hs0
  have hmean : (∫⁻ omega, baseQueryCost a omega ∂(baseCostLaw hn a)) ≤
      publicTerminalQueryEnvelope b := by
    rw [hlaw]
    exact publicTerminal_expected_queries hn b hbeps
      (by simpa [hbK] using hKc) (by simpa [hbK] using hKcl)
      (by simpa [hbK] using hclosedBall)
  have hacc : (4 : Real) / 5 ≤ (baseCostLaw hn a).real
      {omega | baseValue a omega ∈
        Ttc.relErr (guardedAccuracy b) (volume a.1).toReal} := by
    rw [hlaw]
    have hbp : b.2.2 = (1 : Real) / 5 := rfl
    have h := publicTerminal_costed_accuracy hn b hbeps
      (by rw [hbp]; norm_num) (by rw [hbp]; norm_num)
      (by simpa [hbK] using hKc) (by simpa [hbK] using hKcl)
      (by simpa [hbK] using hKb) (by simpa [hbK] using hvol)
      (by simpa [hbK] using hclosedBall) (by simpa [hbK] using hfin)
    convert h using 1 <;> norm_num [b, baseInput, baseValue]
  have hmain := Ttc.CVCorrectedHybridRuntimeAssembly.median_cutoff_success_iid
    (oneLaw := baseCostLaw hn a) (r := outerCutoffReps a.2.2)
    (outerCutoffReps_pos a.2.2) (measurable_baseQueryCost a)
    (measurable_baseValue a hKcl.measurableSet)
    (B := publicTerminalQueryEnvelope b) (L := publicTerminalCutoff b)
    (publicTerminalCutoff_ne_zero b) (publicTerminalCutoff_ne_top b)
    hmean (publicTerminalCutoff_ratio b) (fallback := 0)
    (lo := (1 - guardedAccuracy b) * (volume a.1).toReal)
    (hi := (1 + guardedAccuracy b) * (volume a.1).toReal)
    hacc hp (outerCutoffReps_spec a.2.2)
  have hmono : Ttc.relErr (guardedAccuracy b) (volume a.1).toReal ⊆
      Ttc.relErr a.2.1 (volume a.1).toReal := by
    apply Ttc.CV.relErr_mono
    · unfold b baseInput guardedAccuracy
      exact min_le_left _ _
    · exact ENNReal.toReal_nonneg
  refine hmain.trans (measureReal_mono ?_ (measure_ne_top _ _))
  intro omega homega
  exact hmono homega

noncomputable def totalOuterEstimator (a : VolumeInput n) (omega : OuterCostCoin n a) : Real :=
  if MeasurableSet a.1 then outerEstimator a omega else 0

theorem measurable_totalOuterEstimator (a : VolumeInput n) :
    Measurable (totalOuterEstimator a) := by
  classical
  by_cases hK : MeasurableSet a.1
  · unfold totalOuterEstimator
    simpa only [if_pos hK] using measurable_outerEstimator a hK
  · unfold totalOuterEstimator
    simpa only [if_neg hK] using
      (measurable_const : Measurable (fun _ : OuterCostCoin n a => (0 : Real)))

theorem totalOuterEstimator_eq (a : VolumeInput n) (hK : MeasurableSet a.1) :
    totalOuterEstimator a = outerEstimator a := by
  funext omega
  unfold totalOuterEstimator
  simp only [if_pos hK]

/-- Deterministic actual-query bound for the outer cutoff execution.  The exact inner
envelope remains visible through `publicTerminalCutoff = 20 * (envelope + 1)`. -/
noncomputable def outerExpectedBound (a : VolumeInput n) : ENNReal :=
  (outerCutoffReps a.2.2 : ENNReal) * publicTerminalCutoff (baseInput a)

theorem outerQueryCost_le (a : VolumeInput n) (omega : OuterCostCoin n a) :
    outerQueryCost a omega ≤ outerExpectedBound a := by
  unfold outerQueryCost outerExpectedBound
  calc
    ∑ t, min (baseQueryCost a (omega t)) (publicTerminalCutoff (baseInput a)) ≤
        ∑ _t : Fin (outerCutoffReps a.2.2), publicTerminalCutoff (baseInput a) := by
      apply Finset.sum_le_sum
      intro t ht
      exact min_le_right _ _
    _ = (outerCutoffReps a.2.2 : ENNReal) *
        publicTerminalCutoff (baseInput a) := by simp

theorem outer_expectedQueryCost_le (hn : 21 ≤ n) (a : VolumeInput n) :
    (∫⁻ omega, outerQueryCost a omega ∂(outerCostLaw hn a)) ≤ outerExpectedBound a := by
  calc
    _ ≤ ∫⁻ _omega, outerExpectedBound a ∂(outerCostLaw hn a) :=
      lintegral_mono (outerQueryCost_le a)
    _ = outerExpectedBound a := by simp

/-- Public arbitrary-confidence expected-query volume algorithm.  This theorem makes no
polynomial claim: its bound contains `publicTerminalQueryEnvelope` literally. -/
noncomputable def costedAdjustableVolumeAlgorithm (n : Nat) (hn : 21 ≤ n) :
    Ttc.ExpectedQueryVolumeAlgorithm n :=
  Ttc.ExpectedQueryVolumeAlgorithm.ofClosedInputCostedLaws n (by omega)
    (OuterCostCoin n) (outerCostLaw hn) totalOuterEstimator outerQueryCost
    measurable_totalOuterEstimator measurable_outerQueryCost outerExpectedBound
    (outer_expectedQueryCost_le hn)
    (fun K eps p heps hp hp1 hKc hKcl hKb hvol hclosedBall hfin => by
      let a : VolumeInput n := (K, eps, p)
      have hacc := outerMedian_accuracy hn a heps hp hp1 hKc hKcl hKb hvol
        hclosedBall hfin
      rw [totalOuterEstimator_eq a hKcl.measurableSet]
      exact hacc)

#print axioms outer_expectedQueryCost_le
#print axioms costedAdjustableVolumeAlgorithm

#print axioms outerMedian_accuracy

end Ttc.CVCostedAdjustableOuterMedian

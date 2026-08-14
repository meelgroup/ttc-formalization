import Ttc.Exec.CostedAdaptiveTerminalPhaseAssembly
import Ttc.Volume.CVAdjustableVolumeAlgorithm

/-! Recorded-query counterpart of the public fixed-q adjustable CV estimator. -/

namespace Ttc.CVCostedAdjustablePublicEstimator

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVAdaptive Ttc.CostedAdaptiveTerminalPhaseAssembly
open Ttc.CV.Adaptive
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def publicTerminalQueryEnvelope (a : VolumeInput n) : ENNReal :=
  (guardedR a : ENNReal) * (guardedK a : ENNReal) *
    ∑ i : Fin (guardedM a + 1),
      terminalPhaseQueryBound (n := n) (adjustablePublicQ a)
        (guardedC a ^ 2 * n) (guardedS0 a) (guardedMix a)
        (fun i => ENNReal.ofReal (adaptiveRestartWarmConst n i)) i

/-- A deterministic cutoff with enough slack to be nonzero even when the exact envelope
vanishes. -/
noncomputable def publicTerminalCutoff (a : VolumeInput n) : ENNReal :=
  20 * (publicTerminalQueryEnvelope a + 1)

/-- The exact remaining arithmetic obligation for any claimed polynomial runtime bound.
No operational or probabilistic premise is hidden in this predicate. -/
def PublicTerminalRuntimeCertificate (a : VolumeInput n) (P : ENNReal) : Prop :=
  publicTerminalQueryEnvelope a ≤ P

theorem publicTerminalCutoff_le_of_runtimeCertificate {a : VolumeInput n} {P : ENNReal}
    (hP : PublicTerminalRuntimeCertificate a P) :
    publicTerminalCutoff a ≤ 20 * (P + 1) := by
  unfold PublicTerminalRuntimeCertificate at hP
  unfold publicTerminalCutoff
  gcongr

noncomputable def publicTerminalCostFamily
    (hn : 1 ≤ n) (a : VolumeInput n) (hK : MeasurableSet a.1)
    (hN : 0 < guardedC a ^ 2 * (n : Real)) (hs0 : 0 < guardedS0 a) :
    Fin (guardedR a) → Fin (guardedM a + 1) → Fin (guardedK a) →
      Measure (ENNReal × State n) :=
  terminalCoordinateCostLaw hn (adjustablePublicQ a)
    (guardedC a ^ 2 * n) (guardedS0 a) endpointRho (guardedMix a)
    a.1 hK hN hs0

noncomputable def publicTerminalCostLaw
    (hn : 1 ≤ n) (a : VolumeInput n) (hK : MeasurableSet a.1)
    (hN : 0 < guardedC a ^ 2 * (n : Real)) (hs0 : 0 < guardedS0 a) :=
  Ttc.CostedPackedWarmSchedule.costedPackedLaw
    (publicTerminalCostFamily hn a hK hN hs0)

/-- The fully concrete operational law has the public raw sampler as state projection and
is charged by the exact phasewise finite sum. -/
theorem publicTerminal_cost_and_state
    (hn : 21 ≤ n) (a : VolumeInput n) (heps : 0 < a.2.1)
    (hKc : Convex Real a.1) (hKcl : IsClosed a.1)
    (hclosedBall : closedBall (0 : State n) 1 ⊆ a.1) :
    let hN : 0 < guardedC a ^ 2 * (n : Real) := by
      have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
      positivity
    let hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos (by omega)
      (by unfold guardedEta guardedAccuracy; positivity)
    Measure.map Ttc.CostedPackedJointLaw.stateProjection
        (publicTerminalCostLaw (by omega) a hKcl.measurableSet hN hs0) =
      adjustablePublicRawRunLaw a ∧
    6 * (∫⁻ omega, Ttc.CostedPackedWarmSchedule.totalMembershipQueries omega
        ∂(publicTerminalCostLaw (by omega) a hKcl.measurableSet hN hs0)) ≤
      publicTerminalQueryEnvelope a := by
  dsimp only
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hacc : 0 < guardedAccuracy a := by unfold guardedAccuracy; positivity
  have heta : 0 < guardedEta a := by unfold guardedEta; positivity
  have heta1 : guardedEta a ≤ 1 := by
    unfold guardedEta
    have hacc1 : guardedAccuracy a ≤ 1 := min_le_right _ _
    linarith
  have hN : 0 < guardedC a ^ 2 * (n : Real) := by
    have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
    positivity
  have hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos hn1 heta
  have hk : 0 < guardedK a :=
    concreteEstimatorSamples_pos (guardedJ a) (guardedAccuracy a / 4)
  have hA : 0 < runwiseSamplerCalls (guardedM a) (guardedK a) :=
    runwiseSamplerCalls_pos (guardedM a) hk
  have hq := (adjustablePublicQ_spec a hn1 hA).1
  have hmix0 : 0 < guardedMix a := runwiseChosenMixError_pos (guardedM a) hk
  have hmix32 : guardedMix a ≤ 1 / 32 :=
    runwiseChosenMixError_le_one_div_32 (guardedM a) hk
  have hbelow : ∀ j, j + 1 < guardedM a + 1 →
      adaptiveChunkStart (guardedC a ^ 2 * n) (guardedS0 a)
        (adaptivePhaseChunk (guardedC a ^ 2 * n) (guardedS0 a) j) ≤
          guardedC a ^ 2 * n := by
    intro j hj
    have hjm : j < guardedM a := by omega
    have hchunk : adaptivePhaseChunk (guardedC a ^ 2 * n) (guardedS0 a) j < guardedJ a :=
      adaptivePhaseChunk_lt_of_lt_offset hN hs0 hjm
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs0 hchunk).le
  have hcold : 4 * (n : Real) * guardedS0 a ≤ endpointRho ^ 2 :=
    polynomialEndpointSigmaSq_coldBall hn1 heta heta1
  have hmain := packedTerminal_cost_and_state_concrete
    (r := guardedR a) (m := guardedM a) (k := guardedK a)
    hn hq hN hs0 hKcl.measurableSet hKc hclosedBall endpointRho_pos
    (endpointRho_lt_shrink hn2) hcold hbelow hmix0 hmix32
  constructor
  · convert hmain.1 using 1 <;>
      simp only [publicTerminalCostLaw, publicTerminalCostFamily,
        adjustablePublicRawRunLaw, adjustablePublicPhaseLaw,
        Ttc.CVRunwise.iidRunFamily, adaptiveTerminalWarmLawFamilyQ] <;> rfl
  · simpa only [publicTerminalCostLaw, publicTerminalCostFamily,
      publicTerminalQueryEnvelope] using hmain.2

/-- Accuracy of the public estimator on the same probability space that records every
membership query. -/
theorem publicTerminal_costed_accuracy
    (hn : 21 ≤ n) (a : VolumeInput n)
    (heps : 0 < a.2.1) (hp : 0 < a.2.2) (hp1 : a.2.2 < 1)
    (hKc : Convex Real a.1) (hKcl : IsClosed a.1) (hKb : Bornology.IsBounded a.1)
    (hvol : 0 < volume a.1)
    (hclosedBall : closedBall (0 : State n) 1 ⊆ a.1) (hfin : volume a.1 ≠ ⊤) :
    let hN : 0 < guardedC a ^ 2 * (n : Real) := by
      have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
      positivity
    let hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos (by omega)
      (by unfold guardedEta guardedAccuracy; positivity)
    1 - a.2.2 ≤
      (publicTerminalCostLaw (by omega) a hKcl.measurableSet hN hs0).real
        {omega | adjustablePublicRawEstimator a
          (Ttc.CostedPackedJointLaw.stateProjection omega) ∈
            Ttc.relErr (guardedAccuracy a) (volume a.1).toReal} := by
  dsimp only
  have hn1 : 1 ≤ n := by omega
  have hacc : 0 < guardedAccuracy a := by unfold guardedAccuracy; positivity
  have hacc1 : guardedAccuracy a ≤ 1 := min_le_right _ _
  have hN : 0 < guardedC a ^ 2 * (n : Real) := by
    have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
    positivity
  have heta : 0 < guardedEta a := by unfold guardedEta; positivity
  have hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos hn1 heta
  have hk : 0 < guardedK a :=
    concreteEstimatorSamples_pos (guardedJ a) (guardedAccuracy a / 4)
  have hA : 0 < runwiseSamplerCalls (guardedM a) (guardedK a) :=
    runwiseSamplerCalls_pos (guardedM a) hk
  have hqspec := adjustablePublicQ_spec a hn1 hA
  have hgeom := closure_concrete_geometry (n := n) hn1 hKc
    (Metric.ball_subset_closedBall.trans hclosedBall) hfin
  have hKR : a.1 ⊆ closedBall 0 (guardedC a * Real.sqrt n) := by
    simpa [guardedC, hKcl.closure_eq] using hgeom.2.2.2.2.2.2.2
  have hmain := concrete_adaptive_runwise_volume_accuracy_q hn hqspec.1 hKc hKcl hKb
    hvol hclosedBall hfin (Ttc.CV.cvRadius_pos a.1) hacc hacc1 hp hp1 hKR
    (by
      simpa only [guardedAccuracy, guardedEta, guardedC, guardedS0, guardedJ,
        guardedM, guardedK] using hqspec.2)
  have hraw : 1 - a.2.2 ≤ (adjustablePublicRawRunLaw a).real
      {omega | adjustablePublicRawEstimator a omega ∈
        Ttc.relErr (guardedAccuracy a) (volume a.1).toReal} := by
    convert hmain using 1 <;>
      simp only [guardedAccuracy, guardedEta, guardedC, guardedS0, guardedJ,
        guardedM, guardedK, guardedR, adjustablePublicRawRunLaw,
        adjustablePublicRawEstimator] <;> rfl
  have hmap := (publicTerminal_cost_and_state hn a heps hKc hKcl hclosedBall).1
  have hevent : MeasurableSet
      {omega | adjustablePublicRawEstimator a omega ∈
        Ttc.relErr (guardedAccuracy a) (volume a.1).toReal} :=
    MeasurableSet.preimage measurableSet_Icc
      (measurable_adjustablePublicRawEstimator a hKcl.measurableSet)
  have happly := Measure.map_apply
    (μ := publicTerminalCostLaw (by omega) a hKcl.measurableSet hN hs0)
    Ttc.CostedPackedJointLaw.measurable_stateProjection hevent
  change 1 - a.2.2 ≤
    ((publicTerminalCostLaw (by omega) a hKcl.measurableSet hN hs0)
      (Ttc.CostedPackedJointLaw.stateProjection ⁻¹'
        {omega | adjustablePublicRawEstimator a omega ∈
          Ttc.relErr (guardedAccuracy a) (volume a.1).toReal})).toReal
  rw [← happly, hmap]
  exact hraw

theorem publicTerminalQueryEnvelope_ne_top (a : VolumeInput n) :
    publicTerminalQueryEnvelope a ≠ ⊤ := by
  unfold publicTerminalQueryEnvelope
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top (by simp) (by simp)
  · rw [ENNReal.sum_ne_top]
    intro i hi
    unfold terminalPhaseQueryBound
    split_ifs
    · norm_num
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)

theorem publicTerminalCutoff_ne_zero (a : VolumeInput n) :
    publicTerminalCutoff a ≠ 0 := by
  simp [publicTerminalCutoff]

theorem publicTerminalCutoff_ne_top (a : VolumeInput n) :
    publicTerminalCutoff a ≠ ⊤ := by
  unfold publicTerminalCutoff
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.add_ne_top.mpr ⟨publicTerminalQueryEnvelope_ne_top a, by simp⟩)

theorem publicTerminalCutoff_ratio (a : VolumeInput n) :
    publicTerminalQueryEnvelope a / publicTerminalCutoff a ≤
      ENNReal.ofReal (1 / 20 : Real) := by
  rw [ENNReal.div_le_iff_le_mul
    (Or.inl (publicTerminalCutoff_ne_zero a))
    (Or.inl (publicTerminalCutoff_ne_top a))]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 20)]
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  unfold publicTerminalCutoff
  calc
    publicTerminalQueryEnvelope a ≤ publicTerminalQueryEnvelope a + 1 := le_add_right le_rfl
    _ = (1 / 20 : ENNReal) * (20 * (publicTerminalQueryEnvelope a + 1)) := by
      rw [← mul_assoc, ENNReal.div_eq_inv_mul, mul_one,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- Expected membership queries, without the harmless factor six used by the raw walk
accounting theorem. -/
theorem publicTerminal_expected_queries
    (hn : 21 ≤ n) (a : VolumeInput n) (heps : 0 < a.2.1)
    (hKc : Convex Real a.1) (hKcl : IsClosed a.1)
    (hclosedBall : closedBall (0 : State n) 1 ⊆ a.1) :
    let hN : 0 < guardedC a ^ 2 * (n : Real) := by
      have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
      positivity
    let hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos (by omega)
      (by unfold guardedEta guardedAccuracy; positivity)
    (∫⁻ omega, Ttc.CostedPackedWarmSchedule.totalMembershipQueries omega
      ∂(publicTerminalCostLaw (by omega) a hKcl.measurableSet hN hs0)) ≤
      publicTerminalQueryEnvelope a := by
  dsimp only
  have hsix := (publicTerminal_cost_and_state hn a heps hKc hKcl hclosedBall).2
  calc
    (∫⁻ omega, Ttc.CostedPackedWarmSchedule.totalMembershipQueries omega
      ∂(publicTerminalCostLaw (by omega) a hKcl.measurableSet _ _)) ≤
        6 * (∫⁻ omega, Ttc.CostedPackedWarmSchedule.totalMembershipQueries omega
          ∂(publicTerminalCostLaw (by omega) a hKcl.measurableSet _ _)) := by
      exact le_mul_of_one_le_left (by simp) (by norm_num)
    _ ≤ publicTerminalQueryEnvelope a := hsix

theorem publicTerminal_expected_queries_le_of_runtimeCertificate
    (hn : 21 ≤ n) (a : VolumeInput n) (heps : 0 < a.2.1)
    (hKc : Convex Real a.1) (hKcl : IsClosed a.1)
    (hclosedBall : closedBall (0 : State n) 1 ⊆ a.1) {P : ENNReal}
    (hP : PublicTerminalRuntimeCertificate a P) :
    let hN : 0 < guardedC a ^ 2 * (n : Real) := by
      have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
      positivity
    let hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos (by omega)
      (by unfold guardedEta guardedAccuracy; positivity)
    (∫⁻ omega, Ttc.CostedPackedWarmSchedule.totalMembershipQueries omega
      ∂(publicTerminalCostLaw (by omega) a hKcl.measurableSet hN hs0)) ≤ P := by
  exact (publicTerminal_expected_queries hn a heps hKc hKcl hclosedBall).trans hP

/-- Deterministically cutting off the complete public estimator at twenty times its exact
query envelope (with unit slack) leaves success probability at least `3/4`.  This uses the
already median-amplified public estimator with requested failure at most `1/5`. -/
theorem publicTerminal_cutoff_accuracy_three_quarters
    (hn : 21 ≤ n) (a : VolumeInput n)
    (heps : 0 < a.2.1) (hp : 0 < a.2.2) (hp1 : a.2.2 < 1)
    (hp5 : a.2.2 ≤ 1 / 5)
    (hKc : Convex Real a.1) (hKcl : IsClosed a.1) (hKb : Bornology.IsBounded a.1)
    (hvol : 0 < volume a.1)
    (hclosedBall : closedBall (0 : State n) 1 ⊆ a.1) (hfin : volume a.1 ≠ ⊤)
    (fallback : Real) :
    let hN : 0 < guardedC a ^ 2 * (n : Real) := by
      have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
      positivity
    let hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos (by omega)
      (by unfold guardedEta guardedAccuracy; positivity)
    3 / 4 ≤
      (publicTerminalCostLaw (by omega) a hKcl.measurableSet hN hs0).real
        {omega | Ttc.CVCostedRuntimeCutoff.cutoffValue (publicTerminalCutoff a) fallback
          Ttc.CostedPackedWarmSchedule.totalMembershipQueries
          (adjustablePublicRawEstimator a ∘
            Ttc.CostedPackedJointLaw.stateProjection) omega ∈
              Ttc.relErr (guardedAccuracy a) (volume a.1).toReal} := by
  dsimp only
  have hN : 0 < guardedC a ^ 2 * (n : Real) := by
    have hC : 0 < guardedC a := Ttc.CV.cvRadius_pos a.1
    positivity
  have heta : 0 < guardedEta a := by unfold guardedEta guardedAccuracy; positivity
  have hs0 : 0 < guardedS0 a := polynomialEndpointSigmaSq_pos (by omega) heta
  let rhoCost := publicTerminalCostFamily (by omega : 1 ≤ n) a
    hKcl.measurableSet hN hs0
  letI : ∀ j i l, IsProbabilityMeasure (rhoCost j i l) := by
    intro j i l
    exact isProbabilityMeasure_terminalCoordinateCostLaw (r := guardedR a)
      (m := guardedM a) (k := guardedK a) (by omega) hN hs0 endpointRho_pos
      hKcl.measurableSet j i l
  letI : IsProbabilityMeasure
      (publicTerminalCostLaw (by omega) a hKcl.measurableSet hN hs0) := by
    unfold publicTerminalCostLaw
    change IsProbabilityMeasure (Ttc.CostedPackedWarmSchedule.costedPackedLaw rhoCost)
    infer_instance
  have hmean := publicTerminal_expected_queries hn a heps hKc hKcl hclosedBall
  have hacc := publicTerminal_costed_accuracy hn a heps hp hp1 hKc hKcl hKb hvol
    hclosedBall hfin
  apply Ttc.CVCostedRuntimeCutoff.cutoff_success_three_quarters
    Ttc.CostedPackedWarmSchedule.measurable_totalMembershipQueries
    ((measurable_adjustablePublicRawEstimator a hKcl.measurableSet).comp
      Ttc.CostedPackedJointLaw.measurable_stateProjection)
    (publicTerminalCutoff_ne_zero a) (publicTerminalCutoff_ne_top a)
    hmean (publicTerminalCutoff_ratio a)
  exact (by linarith : (4 : Real) / 5 ≤ 1 - a.2.2).trans hacc

#print axioms publicTerminal_cost_and_state
#print axioms publicTerminal_costed_accuracy
#print axioms publicTerminal_expected_queries
#print axioms publicTerminal_expected_queries_le_of_runtimeCertificate
#print axioms publicTerminal_cutoff_accuracy_three_quarters

end Ttc.CVCostedAdjustablePublicEstimator

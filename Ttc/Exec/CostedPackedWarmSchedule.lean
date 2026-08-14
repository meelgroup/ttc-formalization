/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CostedWarmPhaseRejection
import Ttc.Volume.CVHybridRuntimeAccounting
import Ttc.Volume.CVCorrectedExplicitRadiusRuntime

/-!
# Independently restarted packed warm-phase query cost

The accuracy development uses a product law with one independently restarted sample for
every `(run, phase, sample)` coordinate.  This file gives that exact product construction a
recorded `ENNReal` membership-query count and sums its expectation.  It does not reinterpret
the product law as a single stateful trajectory through the phases.

The ambient-Gaussian cold branch is deliberately an input family below: its costed kernel is
implemented separately.  Thus the final hybrid adapter only needs its marginal and expected
cost certificates, rather than silently assigning it warm-walk cost.
-/

namespace Ttc.CostedPackedWarmSchedule

open MeasureTheory ProbabilityTheory Function Set
open Arlib Arlib.Probability Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.CostedWarmPhaseRejection Ttc.RawGaussianLazyStoppedExecution
open Ttc.SpeedyRejection
open scoped ENNReal Classical Pointwise

variable {n r m k : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

abbrev CostedPackedSpace (n r m k : Nat) :=
  Arlib.Probability.RunSpace (Fin k → ENNReal × State n) r m

/-- Product law of independently restarted costed elementary coordinates. -/
noncomputable def costedPackedLaw
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n)) :
    Measure (CostedPackedSpace n r m k) :=
  runMeasure (packedPhaseLaw rho)

instance (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)] :
    IsProbabilityMeasure (costedPackedLaw rho) := by
  unfold costedPackedLaw
  infer_instance

/-- Actual membership queries recorded across every independently restarted coordinate. -/
noncomputable def totalMembershipQueries
    (omega : CostedPackedSpace n r m k) : ENNReal :=
  ∑ j : Fin r, ∑ i : Fin m, ∑ l : Fin k, (omega j i l).1

theorem measurable_totalMembershipQueries :
    Measurable (totalMembershipQueries (n := n) (r := r) (m := m) (k := k)) := by
  unfold totalMembershipQueries
  exact Finset.measurable_fun_sum _ fun j _ =>
    Finset.measurable_fun_sum _ fun i _ =>
      Finset.measurable_fun_sum _ fun l _ =>
        measurable_fst.comp ((measurable_pi_apply l).comp
          ((measurable_pi_apply i).comp (measurable_pi_apply j)))

/-- Each costed elementary coordinate has its declared joint cost/state marginal. -/
theorem map_costedPackedLaw_coordinate
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)] (j : Fin r) (i : Fin m) (l : Fin k) :
    Measure.map (fun omega : CostedPackedSpace n r m k => omega j i l)
        (costedPackedLaw rho) = rho j i l :=
  (Ttc.CVPacked.measurePreserving_sampleCoord rho j i l).map_eq

/-- Forgetting the cost at one coordinate recovers its advertised state law. -/
theorem map_costedPackedLaw_stateCoordinate
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    (nu : Fin r → Fin m → Fin k → Measure (State n))
    (hstate : ∀ j i l, Measure.map Prod.snd (rho j i l) = nu j i l)
    (j : Fin r) (i : Fin m) (l : Fin k) :
    Measure.map (fun omega : CostedPackedSpace n r m k => (omega j i l).2)
        (costedPackedLaw rho) = nu j i l := by
  rw [show (fun omega : CostedPackedSpace n r m k => (omega j i l).2) =
      Prod.snd ∘ (fun omega => omega j i l) from rfl,
    ← Measure.map_map measurable_snd (by fun_prop),
    map_costedPackedLaw_coordinate rho j i l, hstate j i l]

/-- Scores of the state components retain the exact two-level independence contract used
by the packed CV estimator.  Costs are carried jointly but do not compromise independent
restarts. -/
theorem coordinateIndep_stateScore
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    {g : Fin r → Fin m → Fin k → State n → Real}
    (hg : ∀ j i l, Measurable (g j i l)) (j : Fin r) :
    Ttc.CVEst.CoordinateIndep
      (fun i l (omega : CostedPackedSpace n r m k) => g j i l (omega j i l).2)
      (costedPackedLaw rho) := by
  let gCost : Fin r → Fin m → Fin k → (ENNReal × State n) → Real :=
    fun j i l z => g j i l z.2
  have hgCost : ∀ j i l, Measurable (gCost j i l) :=
    fun j i l => (hg j i l).comp measurable_snd
  change Ttc.CVEst.CoordinateIndep
    (fun i l => Ttc.CVPacked.sampleScore gCost j i l)
    (runMeasure (packedPhaseLaw rho))
  exact Ttc.CVPacked.coordinateIndep_sampleScore rho hgCost j

/-- Tonelli for the finite packed product: total expected queries are exactly the sum of
the elementary expected recorded costs. -/
theorem lintegral_totalMembershipQueries
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)] :
    ∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rho) =
      ∑ j : Fin r, ∑ i : Fin m, ∑ l : Fin k, ∫⁻ z, z.1 ∂(rho j i l) := by
  unfold totalMembershipQueries
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro l hl
        exact (Ttc.CVPacked.measurePreserving_sampleCoord rho j i l).lintegral_comp
          measurable_fst
      · intro l hl
        exact measurable_fst.comp ((measurable_pi_apply l).comp
          ((measurable_pi_apply i).comp (measurable_pi_apply j)))
    · intro i hi
      exact Finset.measurable_fun_sum _ fun l _ =>
        measurable_fst.comp ((measurable_pi_apply l).comp
          ((measurable_pi_apply i).comp (measurable_pi_apply j)))
  · intro j hj
    exact Finset.measurable_fun_sum _ fun i _ =>
      Finset.measurable_fun_sum _ fun l _ =>
        measurable_fst.comp ((measurable_pi_apply l).comp
          ((measurable_pi_apply i).comp (measurable_pi_apply j)))

/-- Sum any coordinatewise expected-query certificates.  This is the basic one-run and
repetition composition theorem; no independence assumption is hidden in the inequality,
while independence is supplied by `costedPackedLaw` itself. -/
theorem six_mul_lintegral_totalMembershipQueries_le
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    (B : Fin r → Fin m → Fin k → ENNReal)
    (hB : ∀ j i l, 6 * (∫⁻ z, z.1 ∂(rho j i l)) ≤ B j i l) :
    6 * (∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rho)) ≤
      ∑ j : Fin r, ∑ i : Fin m, ∑ l : Fin k, B j i l := by
  rw [lintegral_totalMembershipQueries]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun l _ => hB j i l

/-- If all runs and samples at phase `i` share a bound `B i`, repetitions and sample count
appear as the exact multiplicative factors `r*k`. -/
theorem six_mul_lintegral_totalMembershipQueries_le_phaseBounds
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    (B : Fin m → ENNReal)
    (hB : ∀ j i l, 6 * (∫⁻ z, z.1 ∂(rho j i l)) ≤ B i) :
    6 * (∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rho)) ≤
      (r : ENNReal) * (k : ENNReal) * ∑ i : Fin m, B i := by
  calc
    _ ≤ ∑ _j : Fin r, ∑ i : Fin m, ∑ _l : Fin k, B i :=
      six_mul_lintegral_totalMembershipQueries_le rho (fun _ i _ => B i) hB
    _ = (r : ENNReal) * (k : ENNReal) * ∑ i : Fin m, B i := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fin]
      rw [← Finset.mul_sum, mul_assoc]

/-! ## Warm phase family -/

/-- One independently restarted costed warm phase for every phase index, copied across
runs and elementary samples. -/
noncomputable def warmCoordinateLaw
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq : Fin m → Real) (hdelta : ∀ i, 0 < delta i)
    (mu0 : Fin m → Measure (State n)) (steps : Fin m → Nat)
    (j : Fin r) (i : Fin m) (l : Fin k) : Measure (ENNReal × State n) :=
  warmPhaseCostLaw K hK (delta i) (sigmaSq i) (hdelta i) (mu0 i) (steps i)

instance (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq : Fin m → Real) (hdelta : ∀ i, 0 < delta i)
    (mu0 : Fin m → Measure (State n)) [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin m → Nat) (j : Fin r) (i : Fin m) (l : Fin k) :
    IsProbabilityMeasure (warmCoordinateLaw K hK delta sigmaSq hdelta mu0 steps j i l) := by
  unfold warmCoordinateLaw
  infer_instance

/-- State marginal of every independently restarted packed warm coordinate. -/
theorem map_warmCoordinateLaw_state
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq : Fin m → Real) (hdelta : ∀ i, 0 < delta i)
    (mu0 : Fin m → Measure (State n)) [∀ i, IsProbabilityMeasure (mu0 i)]
    (steps : Fin m → Nat)
    (hshrink : ∀ i, 0 <
      (iterate (lazy (speedyMetropolisGaussian K (delta i) (sigmaSq i)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) • K))
    (hsigma : ∀ i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (hmass : ∀ i, ((phasePointProposal K (delta i) (sigmaSq i) (mu0 i) (steps i)).withDensity
      (fun x => ENNReal.ofReal
        (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (sigmaSq i) x))) Set.univ ≠ 0)
    (j : Fin r) (i : Fin m) (l : Fin k) :
    Measure.map Prod.snd
        (warmCoordinateLaw K hK delta sigmaSq hdelta mu0 steps j i l) =
      Ttc.CVSampler.phaseLaw K (delta i) (sigmaSq i) (mu0 i) (steps i) := by
  exact map_snd_warmPhaseCostLaw_eq_phaseLaw hK (delta i) (hdelta i) (mu0 i)
    (steps i) (hshrink i) (hsigma i) hc2 (hmass i)

/-- Packed independently restarted adjustable-radius warm cost.  The right side exposes
the exact phase-dependent mixing-step/warmness sum; repetitions and samples factor out. -/
theorem six_mul_lintegral_packedWarm_le_adjustable
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : Metric.ball (0 : State n) 1 ⊆ K)
    (q delta sigma R : Fin m → Real)
    (hq : ∀ i, 1 < q i) (hdelta : ∀ i, 0 < delta i)
    (hsigma : ∀ i, 0 < sigma i)
    (hdeltan : ∀ i, delta i ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ i, delta i ≤ sigma i / (max 8 (2 * q i) * Real.sqrt n))
    (hR : ∀ i, 0 ≤ R i) (hRsigma : ∀ i, R i ≤ q i * sigma i * Real.sqrt n)
    (hKR : ∀ i x, x ∈ K → ‖x‖ ≤ R i)
    (M : Fin m → ENNReal) (mu0 : Fin m → Measure (State n))
    [∀ i, IsProbabilityMeasure (mu0 i)]
    (hwarm : ∀ i, IsWarm (M i) (mu0 i)
      (ellGaussianProb K (delta i) ((sigma i) ^ 2)))
    (steps : Fin m → Nat)
    (hhalf : ∀ i, ENNReal.ofReal (1 / 2 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian K (delta i) ((sigma i) ^ 2)))
        (mu0 i) (steps i)) ((1 - 1 / (2 * (n : Real))) • K))
    (hquarter : ∀ i, ENNReal.ofReal (1 / 4 : Real) ≤
      ((phasePointProposal K (delta i) ((sigma i) ^ 2) (mu0 i) (steps i)).withDensity
        (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) ((sigma i) ^ 2) x))) Set.univ)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    6 * (∫⁻ omega, totalMembershipQueries omega
      ∂(costedPackedLaw
        (warmCoordinateLaw K hK delta (fun i => (sigma i) ^ 2) hdelta mu0 steps :
          Fin r → Fin m → Fin k → Measure (ENNReal × State n)))) ≤
      (r : ENNReal) * (k : ENNReal) *
        ∑ i : Fin m, 80 * ((steps i : ENNReal) * M i) := by
  apply six_mul_lintegral_totalMembershipQueries_le_phaseBounds
  intro j i l
  exact six_mul_lintegral_warmPhaseCostLaw_le_eighty_mul_adjustable hn hK hKc hball
    (hq i) (hdelta i) (hsigma i) (hdeltan i) (hdeltaq i) (hR i) (hRsigma i)
    (hKR i) (hwarm i) (steps i) (hhalf i) (hquarter i) hc2

/-! ## Hybrid seam -/

/-- Honest hybrid cost premise.  The warm coordinates can be discharged by the theorem
above.  `coldCost` is intentionally separate until the ambient-Gaussian traced kernel is
connected: it must certify both its state marginal and its expected recorded queries. -/
def HybridCoordinateCostCertificate
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    (nu : Fin r → Fin m → Fin k → Measure (State n))
    (B : Fin r → Fin m → Fin k → ENNReal) : Prop :=
  (∀ j i l, IsProbabilityMeasure (rho j i l)) ∧
  (∀ j i l, Measure.map Prod.snd (rho j i l) = nu j i l) ∧
  (∀ j i l, 6 * (∫⁻ z, z.1 ∂(rho j i l)) ≤ B j i l)

/-- A complete hybrid coordinate certificate immediately yields the honest total expected
membership-query bound for all estimator repetitions. -/
theorem hybrid_total_expected_queries
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    (nu : Fin r → Fin m → Fin k → Measure (State n))
    (B : Fin r → Fin m → Fin k → ENNReal)
    (h : HybridCoordinateCostCertificate rho nu B) :
    6 * (∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rho)) ≤
      ∑ j : Fin r, ∑ i : Fin m, ∑ l : Fin k, B j i l := by
  letI : ∀ j i l, IsProbabilityMeasure (rho j i l) := h.1
  exact six_mul_lintegral_totalMembershipQueries_le rho B h.2.2

/-- The same hybrid certificate identifies every estimator state coordinate with the
declared hybrid sampler marginal. -/
theorem hybrid_stateCoordinate_marginal
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    (nu : Fin r → Fin m → Fin k → Measure (State n))
    (B : Fin r → Fin m → Fin k → ENNReal)
    (h : HybridCoordinateCostCertificate rho nu B)
    (j : Fin r) (i : Fin m) (l : Fin k) :
    Measure.map (fun omega : CostedPackedSpace n r m k => (omega j i l).2)
        (costedPackedLaw rho) = nu j i l := by
  letI : ∀ j i l, IsProbabilityMeasure (rho j i l) := h.1
  exact map_costedPackedLaw_stateCoordinate rho nu h.2.1 j i l

/-! ## Connection to the corrected deterministic envelope -/

/-- The remaining comparison between operational queries and the source's deterministic
proposal accounting.  It is intentionally a proposition rather than a definitionally true
claim: warm coordinates are discharged by `six_mul_lintegral_packedWarm_le_adjustable`,
whereas cold coordinates require the separately developed ambient rejection kernel. -/
def OperationalCostFitsSourceAccounting
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    (N s0 : Real) (J : Nat) (q : Real) : Prop :=
  6 * (∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rho)) ≤
    ENNReal.ofReal
      (Ttc.CVCorrectedRuntime.adaptiveSourceProposalAccounting n N s0 J k r q)

/-- Once actual recorded membership queries are shown to fit the source accounting, the
already-proved corrected arithmetic yields the public polynomial envelope.  This theorem
does not assume or require a sequential dependence fiction: `rho` is precisely the packed
independently restarted coordinate family. -/
theorem operational_queries_le_correctedSourceProposalEnvelope
    {J : Nat}
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    {C eps p q : Real} (hn : 1 ≤ n) (hC : 0 < C)
    (heps : 0 < eps) (hp : 0 < p) (hp1 : p < 1)
    (hsource : (1 / 2 : Real) ^ n ≤ eps / 4)
    (hJ : J = Ttc.CV.Adaptive.adaptiveTerminalChunk
      (C ^ 2 * n) (Ttc.CVAdaptive.polynomialEndpointSigmaSq n (eps / 4)))
    (hk : k = Ttc.CVCorrectedRuntime.correctedRuntimeSamples
      (Ttc.CVAdaptive.terminalPhaseCount n C
        (Ttc.CVAdaptive.polynomialEndpointSigmaSq n (eps / 4))) eps)
    (hr : r = Ttc.CVAdaptive.concreteRunwiseReps p)
    (hfits : OperationalCostFitsSourceAccounting rho (C ^ 2 * n)
      (Ttc.CVAdaptive.polynomialEndpointSigmaSq n (eps / 4)) J q) :
    6 * (∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rho)) ≤
      ENNReal.ofReal (Ttc.CVCorrectedRuntime.correctedSourceProposalEnvelope
        n C eps p q) := by
  have haccount := Ttc.CVCorrectedRuntime.corrected_adaptive_source_accounting_le_envelope
    (n := n) (C := C) (eps := eps) (p := p) (q := q)
    hn hC heps hp hp1 hsource
  dsimp only at haccount
  rw [← hJ, ← hk, ← hr] at haccount
  exact hfits.trans (ENNReal.ofReal_le_ofReal haccount)

/-- Fully explicit radius specialization of the previous adapter.  The only operational
premise left is `OperationalCostFitsSourceAccounting`; all phase/sample/repetition/radius
arithmetic is discharged by `CVCorrectedExplicitRadiusRuntime`. -/
theorem operational_queries_le_correctedExplicitSourceProposalEnvelope
    {J : Nat}
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    {C eps p : Real} (hn : 1 ≤ n) (hC : 0 < C)
    (heps : 0 < eps) (hp : 0 < p) (hp1 : p < 1)
    (hsource : (1 / 2 : Real) ^ n ≤ eps / 4)
    (hJ : J = Ttc.CV.Adaptive.adaptiveTerminalChunk
      (C ^ 2 * n) (Ttc.CVAdaptive.polynomialEndpointSigmaSq n (eps / 4)))
    (hk : k = Ttc.CVCorrectedRuntime.correctedRuntimeSamples
      (Ttc.CVAdaptive.terminalPhaseCount n C
        (Ttc.CVAdaptive.polynomialEndpointSigmaSq n (eps / 4))) eps)
    (hr : r = Ttc.CVAdaptive.concreteRunwiseReps p)
    (hfits : OperationalCostFitsSourceAccounting rho (C ^ 2 * n)
      (Ttc.CVAdaptive.polynomialEndpointSigmaSq n (eps / 4)) J
      (Ttc.CVCorrectedRuntime.correctedExplicitQPoly n C eps)) :
    6 * (∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rho)) ≤
      ENNReal.ofReal
        (Ttc.CVCorrectedRuntime.correctedExplicitSourceProposalEnvelope n C eps p) := by
  simpa only [Ttc.CVCorrectedRuntime.correctedExplicitSourceProposalEnvelope] using
    operational_queries_le_correctedSourceProposalEnvelope rho hn hC heps hp hp1 hsource
      hJ hk hr hfits

end Ttc.CostedPackedWarmSchedule

#print axioms Ttc.CostedPackedWarmSchedule.lintegral_totalMembershipQueries
#print axioms Ttc.CostedPackedWarmSchedule.coordinateIndep_stateScore
#print axioms Ttc.CostedPackedWarmSchedule.map_warmCoordinateLaw_state
#print axioms Ttc.CostedPackedWarmSchedule.six_mul_lintegral_packedWarm_le_adjustable
#print axioms Ttc.CostedPackedWarmSchedule.hybrid_total_expected_queries
#print axioms Ttc.CostedPackedWarmSchedule.operational_queries_le_correctedExplicitSourceProposalEnvelope

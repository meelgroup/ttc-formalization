import Ttc.Exec.TTCUnconditionalExplicitRuntime
import Ttc.Exec.CVRadialLogEnvelope

/-!
# TTC driven directly by an honest CV expected-query implementation

`CVTheorem11ExpectedImplementation` already packages a dimension-indexed volume
algorithm, its actual random membership-query counter, and the corrected Theorem 1.1
expected-query bound.  This file plugs that interface directly into the operational TTC
law.  In particular, the public theorem below has no
`SourcePublicOneRunCertificates` argument: that certificate is one possible way to build
the supplied CV implementation, not a condition on TTC once the implementation exists.

The bound is intentionally stated as the finite sum over the rounded bodies on which TTC
actually calls the volume oracle.  Each summand uses that body's exact second moment, so
no radial comparison hypothesis is hidden in the adapter.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.TTCCVExpectedImplementation

open MeasureTheory ProbabilityTheory Metric Set
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem
open Ttc.CanonicalOwnerRateCutoff
open Ttc.KV97RoundedEndpointBridge
open Ttc.CVRadialLogEnvelope
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}

/-- The exact normalized body used by TTC's `j`th volume call. -/
noncomputable def callBody
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (j : Fin (toDNFd (preprocess atoms phi)).length) : Set (Space n) :=
  roundBody
    (algCen atoms phi eps delta
      ⟨(toDNFd (preprocess atoms phi)).get j,
        List.get_mem (toDNFd (preprocess atoms phi)) j⟩)
    (algGamma atoms phi eps delta)
    (region (atomSet (algAtoms atoms phi eps delta))
      ((toDNFd (preprocess atoms phi)).get j))

/-- A nonnegative second-moment parameter for one actual TTC volume call. -/
noncomputable def callSecondMoment
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (j : Fin (toDNFd (preprocess atoms phi)).length) : Real :=
  max 0 (cvSecondMoment (callBody atoms phi eps delta j))

/-- Every volume body passed by TTC to CV satisfies the public geometric input contract.
The moment parameter is its own (nonnegatively clipped) exact second moment. -/
theorem callBody_admissible
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    CVAdmissible (callBody atoms phi eps delta j)
      (callSecondMoment atoms phi eps delta j) := by
  let K := region (atomSet (algAtoms atoms phi eps delta))
    ((toDNFd (preprocess atoms phi)).get j)
  let c := algCen atoms phi eps delta
    ⟨(toDNFd (preprocess atoms phi)).get j,
      List.get_mem (toDNFd (preprocess atoms phi)) j⟩
  let gamma := algGamma atoms phi eps delta
  have hgamma : 0 < gamma :=
    algGamma_pos_of_isPositive atoms phi eps delta hphi hvol
  have hballK : ball c gamma ⊆ K := by
    exact ball_subset_algCen atoms phi eps delta
      ⟨(toDNFd (preprocess atoms phi)).get j,
        List.get_mem (toDNFd (preprocess atoms phi)) j⟩
  have hball : ball (0 : Space n) 1 ⊆ roundBody c gamma K :=
    ball_subset_roundBody hgamma hballK
  have hconv : Convex Real (roundBody c gamma K) :=
    convex_roundBody (convex_region (algAtoms atoms phi eps delta) _)
  have hbdd : Bornology.IsBounded
      (sol (atomSet (algAtoms atoms phi eps delta)) (preprocess atoms phi)) :=
    algAtoms_bdd atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hfinK : volume K ≠ ⊤ :=
    volume_region_ne_top_of_isBounded (toDNFd_isDNFOf _) hbdd
      ⟨(toDNFd (preprocess atoms phi)).get j,
        List.get_mem (toDNFd (preprocess atoms phi)) j⟩
  have hfin : volume (roundBody c gamma K) ≠ ⊤ :=
    volume_roundBody_ne_top hgamma hfinK
  have hzero : volume (roundBody c gamma K) ≠ 0 :=
    Arlib.MarkovChains.volume_ne_zero_of_ball_subset one_pos hball
  refine ⟨hconv, hball, hzero, hfin, ?_⟩
  exact le_max_right 0 (cvSecondMoment (roundBody c gamma K))

/-- The sum of the honest CV Theorem 1.1 bounds over precisely the volume calls made by
TTC.  There is no worst-case radial parameter or certificate-level cutoff in this sum. -/
noncomputable def volumeQueryEnvelope
    (I : CVTheorem11ExpectedImplementation)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : ENNReal :=
  ∑ j : Fin (toDNFd (preprocess atoms phi)).length,
    ENNReal.ofReal
      (I.runtimeConstant *
        cvComplexityShapeClipped n
          (callSecondMoment atoms phi eps delta j)
          (algBlock atoms phi eps delta).epsPrime
          (algBlock atoms phi eps delta).deltaPrime)

/-- The actual input-wise TTC volume budget of the supplied implementation is bounded by
the finite Theorem 1.1 sum above. -/
theorem ttcPolyVolumeQueryBound_le_volumeQueryEnvelope
    (I : CVTheorem11ExpectedImplementation)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    ttcPolyVolumeQueryBound atoms phi eps delta (I.algorithm n) ≤
      volumeQueryEnvelope I atoms phi eps delta := by
  have heps0 : 0 < (algBlock atoms phi eps delta).epsPrime :=
    algBlock_epsPrime_pos atoms phi eps delta
  have heps1 : (algBlock atoms phi eps delta).epsPrime < 1 := by
    rw [algBlock_epsPrime_eq atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol]
    linarith
  have hp0 : 0 < (algBlock atoms phi eps delta).deltaPrime :=
    algBlock_deltaPrime_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
      h_delta_pos
  have hp1 : (algBlock atoms phi eps delta).deltaPrime < 1 :=
    lt_of_le_of_lt
      (algBlock_deltaPrime_le_half atoms phi eps delta h_eps_pos h_eps_le hn
        hphi hvol h_delta_le)
      (by norm_num)
  unfold ttcPolyVolumeQueryBound volOfExpectedAlgQueryBound volumeQueryEnvelope
  apply Finset.sum_le_sum
  intro j hj
  exact I.expectedBound_le n (callBody atoms phi eps delta j)
    (algBlock atoms phi eps delta).epsPrime
    (algBlock atoms phi eps delta).deltaPrime
    (callSecondMoment atoms phi eps delta j)
    hn heps0 heps1 hp0 hp1
    (callBody_admissible atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j)

/-- The exact TTC call sum for the literal CV hybrid schedule.  Compared with
`volumeQueryEnvelope`, this honest intermediate interface retains the extra squared
radial logarithm currently required by the machine-checked source accounting. -/
noncomputable def radialVolumeQueryEnvelope
    (I : CVRadialLogExpectedImplementation)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : ENNReal :=
  ∑ j : Fin (toDNFd (preprocess atoms phi)).length,
    ENNReal.ofReal
      (I.runtimeConstant *
        cvRadialLogComplexityShapeClipped n
          (callSecondMoment atoms phi eps delta j)
          (algBlock atoms phi eps delta).epsPrime
          (algBlock atoms phi eps delta).deltaPrime)

/-- The actual TTC volume-query budget of a radial-log CV implementation is bounded by
the corresponding finite sum over TTC's exact rounded call bodies. -/
theorem ttcPolyVolumeQueryBound_le_radialVolumeQueryEnvelope
    (I : CVRadialLogExpectedImplementation)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    ttcPolyVolumeQueryBound atoms phi eps delta (I.algorithm n) ≤
      radialVolumeQueryEnvelope I atoms phi eps delta := by
  have heps0 : 0 < (algBlock atoms phi eps delta).epsPrime :=
    algBlock_epsPrime_pos atoms phi eps delta
  have heps1 : (algBlock atoms phi eps delta).epsPrime < 1 := by
    rw [algBlock_epsPrime_eq atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol]
    linarith
  have hp0 : 0 < (algBlock atoms phi eps delta).deltaPrime :=
    algBlock_deltaPrime_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
      h_delta_pos
  have hp1 : (algBlock atoms phi eps delta).deltaPrime < 1 :=
    lt_of_le_of_lt
      (algBlock_deltaPrime_le_half atoms phi eps delta h_eps_pos h_eps_le hn
        hphi hvol h_delta_le)
      (by norm_num)
  unfold ttcPolyVolumeQueryBound volOfExpectedAlgQueryBound radialVolumeQueryEnvelope
  apply Finset.sum_le_sum
  intro j hj
  exact I.expectedBound_le n (callBody atoms phi eps delta j)
    (algBlock atoms phi eps delta).epsPrime
    (algBlock atoms phi eps delta).deltaPrime
    (callSecondMoment atoms phi eps delta j)
    hn heps0 heps1 hp0 hp1
    (callBody_admissible atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j)

/-- Generic same-law capped TTC result for an arbitrary expected-query volume oracle.
This separates the TTC adapter from every particular proof of the volume oracle. -/
theorem cappedTTC_fullTrajectory
    (V : ExpectedQueryVolumeAlgorithm n)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      ttcPolyVolumeQueryBound atoms phi eps deltaRun V +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  let deltaRun := 4 * delta / 5
  have hd0 : 0 < deltaRun := by dsimp [deltaRun]; linarith
  have hd1 : deltaRun ≤ 1 := by dsimp [deltaRun]; linarith
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI := V.mΩ
  let rawP :=
    Ttc.ConcreteHybridCanonicalOwnerMeasurable.polyHybridTrajectoryPluginMeasurable
      atoms phi eps deltaRun V
      (hasLatticeEnum_polyHybridCanonical atoms phi eps deltaRun
        h_eps_pos h_eps_le hn hphi hvol)
      (canonicalHybridInnerRadius atoms phi eps deltaRun)
      (canonicalHybridOuterRadius atoms phi eps deltaRun)
      (canonicalHybridStep atoms phi eps deltaRun)
      (canonicalHybridWarm atoms phi eps deltaRun)
      (canonicalHybridStart atoms phi eps deltaRun)
      (fun i ↦ Arlib.isProbabilityMeasure_uniformOn_ball volume _
        (ttcSampInradius_pos atoms phi eps deltaRun
          h_eps_pos h_eps_le hn hphi hvol))
      (isBounded_polyHybridCanonical atoms phi eps deltaRun
        h_eps_pos h_eps_le hn hphi hvol)
      (fun _ ↦ by
        unfold canonicalHybridStep
        have hr := ttcSampInradius_pos atoms phi eps deltaRun
          h_eps_pos h_eps_le hn hphi hvol
        linarith)
      (one_eighth_le_roundedMeasure_polyHybridCanonical atoms phi eps deltaRun
        h_eps_pos h_eps_le hn hphi hvol)
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn hphi hvol
  have hraw := polyHybridCanonicalFinal_accuracy_and_expectedQueries
    atoms phi eps deltaRun h_eps_pos h_eps_le hd0 hd1 hn hphi hvol V
      (J := 1) (by decide)
  let good := polyGood atoms phi eps deltaRun V.toVolumeAlgorithm
  have hgoodMeas : MeasurableSet good :=
    measurableSet_volGood V.toVolumeAlgorithm _ _ _ _ _
  have hk : ∀ omega ∈ good,
      rawP.trajectoryKernel omega = P.trajectoryKernel omega := by
    intro omega homega
    have hcap := polyGood_subset_ratesWithinCap atoms phi eps deltaRun
      V.toVolumeAlgorithm homega
    symm
    simpa only [P, canonicalCappedPolyHybridPlugin,
      polyHybridCappedTrajectoryPluginMeasurable, rawP,
      Ttc.ConcreteHybridCanonicalOwnerMeasurable.polyHybridTrajectoryPluginMeasurable,
      Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin.ofMeasurableRates] using
      (clippedPlugin_trajectoryKernel_eq_of_mem
        (q := (rawP.family omega).q)
        (hq0 := (rawP.family omega).q_nonneg)
        (hqsum := (rawP.family omega).q_sum)
        (S := (rawP.family omega).sampler) (owner := rawP.owner)
        (lam := fun omega i ↦
          (polyVol atoms phi eps deltaRun V.toVolumeAlgorithm omega i.val).toNNReal)
        (hlam := measurable_pi_lambda _ fun i ↦ measurable_real_toNNReal.comp
          (measurable_polyVol atoms phi eps deltaRun V.toVolumeAlgorithm i.val))
        (cap := polyGoodRateCap atoms phi eps deltaRun) hcap)
  have hacc := canonicalCappedJoint_accuracy_of_raw atoms phi eps deltaRun
    (deltaRun / 5) V rawP P good hgoodMeas hk hraw.1
    (measure_polyGood_compl_le_one_fifth atoms phi eps deltaRun V.toVolumeAlgorithm
      h_eps_pos h_eps_le hd0 hd1 hn hphi hvol)
  have hcost := lintegral_canonicalFullPolyQueryCost_le V P
  have hsample := lintegral_canonicalCapped_expectedSampleQueries_le
    atoms phi eps deltaRun V h_eps_pos h_eps_le hn hphi hvol
  have hcost' :
      (∫⁻ z, canonicalFullPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P z
        ∂canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P) ≤
        ttcPolyVolumeQueryBound atoms phi eps deltaRun V +
          canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun := by
    exact hcost.trans (add_le_add (le_refl _) (by
      simpa only [P, canonicalCappedPolyHybridPlugin] using hsample))
  apply canonicalFullOperationalLaw_accuracy_and_expectedQueries V P
  · exact le_trans (by dsimp [deltaRun]; linarith) hacc
  · exact hcost'

/-- TTC integrated with a supplied honest CV Theorem 1.1 implementation.

The only assumptions are TTC's ordinary input conditions and the implementation object
itself.  In particular there is no source-certificate, radial, per-call, rate-cap, or
sampler-price premise. -/
theorem ttc_volume_estimate_of_cvExpectedImplementation
    (I : CVTheorem11ExpectedImplementation)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      volumeQueryEnvelope I atoms phi eps deltaRun +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  let deltaRun := 4 * delta / 5
  have hd0 : 0 < deltaRun := by dsimp [deltaRun]; linarith
  have hd1 : deltaRun ≤ 1 := by dsimp [deltaRun]; linarith
  let V := I.algorithm n
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn hphi hvol
  have hmain := cappedTTC_fullTrajectory V atoms phi eps delta
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact add_le_add
    (ttcPolyVolumeQueryBound_le_volumeQueryEnvelope I atoms phi eps deltaRun
      h_eps_pos h_eps_le hd0 hd1 hn hphi hvol)
    (le_refl (canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun))

/-- TTC integrated with the honest radial-log CV implementation interface currently
provided by the literal cold/hot hybrid source accounting.

This removes the source-certificate premise from TTC itself: the caller supplies one
`CVRadialLogExpectedImplementation`, whose algorithm, accuracy, and expected-query
bound are bundled together.  It deliberately does not assert that such an object has
already been constructed unconditionally. -/
theorem ttc_volume_estimate_of_cvRadialLogExpectedImplementation
    (I : CVRadialLogExpectedImplementation)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      radialVolumeQueryEnvelope I atoms phi eps deltaRun +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  let deltaRun := 4 * delta / 5
  have hd0 : 0 < deltaRun := by dsimp [deltaRun]; linarith
  have hd1 : deltaRun ≤ 1 := by dsimp [deltaRun]; linarith
  let V := I.algorithm n
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn hphi hvol
  have hmain := cappedTTC_fullTrajectory V atoms phi eps delta
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact add_le_add
    (ttcPolyVolumeQueryBound_le_radialVolumeQueryEnvelope I atoms phi eps deltaRun
      h_eps_pos h_eps_le hd0 hd1 hn hphi hvol)
    (le_refl (canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun))

#print axioms callBody_admissible
#print axioms ttcPolyVolumeQueryBound_le_volumeQueryEnvelope
#print axioms cappedTTC_fullTrajectory
#print axioms ttc_volume_estimate_of_cvExpectedImplementation
#print axioms ttcPolyVolumeQueryBound_le_radialVolumeQueryEnvelope
#print axioms ttc_volume_estimate_of_cvRadialLogExpectedImplementation

end Ttc.TTCCVExpectedImplementation

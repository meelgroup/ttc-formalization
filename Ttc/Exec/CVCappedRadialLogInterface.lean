import Ttc.Exec.CVCappedRadialLogExpectedImplementation
import Ttc.Exec.TTCCVExpectedImplementation

/-!
# Public interface for the honestly capped radial-log CV runtime

The operational `delta ≤ 1/(2n)` branch costs one clipped dimension factor beyond the
previous radial-log interface.  This file exposes that corrected runtime all the way to
the TTC adapter.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.CVCappedRadialLogInterface

open MeasureTheory ProbabilityTheory Metric Set
open Ttc.CVHotRefreshHonestRuntime
open Ttc.CVRadialLogEnvelope
open Ttc.TTCCVExpectedImplementation
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem
open Ttc.CanonicalOwnerRateCutoff
open Ttc.KV97RoundedEndpointBridge
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}

/-- Exact sum of corrected CV volume-oracle bounds over TTC's rounded call bodies. -/
noncomputable def cappedRadialVolumeQueryEnvelope
    (I : CVCappedRadialLogExpectedImplementation)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : ENNReal :=
  ∑ j : Fin (toDNFd (preprocess atoms phi)).length,
    ENNReal.ofReal
      (I.runtimeConstant *
        cvCappedRadialLogComplexityShapeClipped n
          (callSecondMoment atoms phi eps delta j)
          (algBlock atoms phi eps delta).epsPrime
          (algBlock atoms phi eps delta).deltaPrime)

theorem ttcPolyVolumeQueryBound_le_cappedRadialVolumeQueryEnvelope
    (I : CVCappedRadialLogExpectedImplementation)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    ttcPolyVolumeQueryBound atoms phi eps delta (I.algorithm n) ≤
      cappedRadialVolumeQueryEnvelope I atoms phi eps delta := by
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
        hphi hvol h_delta_le) (by norm_num)
  unfold ttcPolyVolumeQueryBound volOfExpectedAlgQueryBound
    cappedRadialVolumeQueryEnvelope
  apply Finset.sum_le_sum
  intro j hj
  exact I.expectedBound_le n (callBody atoms phi eps delta j)
    (algBlock atoms phi eps delta).epsPrime
    (algBlock atoms phi eps delta).deltaPrime
    (callSecondMoment atoms phi eps delta j)
    hn heps0 heps1 hp0 hp1
    (callBody_admissible atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j)

/-- TTC compatibility theorem for the corrected capped-radial CV interface in the
dimension range of the operational Gaussian cooling implementation.  The explicit
`21 ≤ n` premise prevents this public theorem from silently routing lower dimensions
through the non-operational exact-volume semantic witness. -/
theorem ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation
    (I : CVCappedRadialLogExpectedImplementation)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      cappedRadialVolumeQueryEnvelope I atoms phi eps deltaRun +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  let deltaRun := 4 * delta / 5
  let hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hd0 : 0 < deltaRun := by dsimp [deltaRun]; linarith
  have hd1 : deltaRun ≤ 1 := by dsimp [deltaRun]; linarith
  let V := I.algorithm n
  letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn1 hphi hvol
  have hmain := cappedTTC_fullTrajectory V atoms phi eps delta
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn1 hphi hvol
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact add_le_add
    (ttcPolyVolumeQueryBound_le_cappedRadialVolumeQueryEnvelope I atoms phi eps deltaRun
      h_eps_pos h_eps_le hd0 hd1 hn1 hphi hvol)
    (le_refl (canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun))

#print axioms CVCappedRadialLogExpectedImplementation.ofRadial
#print axioms cvCappedRadialLogExpectedImplementationOfReferenceTVFamily
#print axioms ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation

end Ttc.CVCappedRadialLogInterface

import Ttc.Exec.TTCFullTrajectoryQueryCost
import Ttc.Exec.TTCRuntimePaperArithmetic

/-!
# From operational TTC counters to the runtime display in `analysis.tex`

The operational theorem records two `ENNReal` counters: the source-CV volume calls and
the membership/facet inspections made by the complete canonical-owner sampling
trajectory.  This file reduces comparison with the paper's real-valued runtime display
to local, per-cube inequalities.

The remaining hypotheses are intentionally local.  They are not bookkeeping gaps:
`analysis.tex` uses big-O and suppresses the CV logarithms, confidence amplification,
warm-start costs, and universal implementation constants.  Those suppressed factors
cannot be bounded by the paper's coefficient-one expression for arbitrary parameters.
-/

namespace Ttc.TTCOperationalPaperBridge

open MeasureTheory ProbabilityTheory Set
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem
open Ttc.TTCRuntimePaperArithmetic
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}

/-- The canonical operational cube index has exactly the DNF length used as `m` in
the paper.  Thus summing the per-cube operational prices introduces no extra index
factor. -/
theorem card_cubeIndex_eq_length
    (atoms : A → LinAtom n) (phi : BForm A) :
    Fintype.card (CubeIndex atoms phi) =
      (toDNFd (preprocess atoms phi)).length := by
  rw [← Nat.card_eq_fintype_card]
  exact card_toDNFd (preprocess atoms phi)

/-- The facet count used by every concrete hybrid endpoint is exactly the facet field
of TTC's computed parameter block. -/
theorem canonicalFacetCount_eq_algBlock
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi) :
    (Nat.card (FacetIndex (D atoms phi)) : Real) =
      (algBlock atoms phi eps delta).r := by
  exact (ttcBlock_r atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol).symm

/-- Radius ratio of the actual canonical hybrid endpoint geometry. -/
noncomputable def canonicalHybridRadiusRatio
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi) : Real :=
  canonicalHybridOuterRadius atoms phi eps delta i /
    canonicalHybridInnerRadius atoms phi eps delta i

theorem canonicalHybridRadiusRatio_eq
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi)
    (hinner : ttcSampInradius atoms phi eps delta ≠ 0) :
    canonicalHybridRadiusRatio atoms phi eps delta i =
      2 * ttcSampDiam atoms phi eps delta i /
        ttcSampInradius atoms phi eps delta := by
  unfold canonicalHybridRadiusRatio canonicalHybridOuterRadius
    canonicalHybridInnerRadius
  field_simp

theorem canonicalHybridRadiusRatio_pos
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (i : CubeIndex atoms phi) :
    0 < canonicalHybridRadiusRatio atoms phi eps delta i := by
  unfold canonicalHybridRadiusRatio canonicalHybridOuterRadius
    canonicalHybridInnerRadius
  exact div_pos
    (ttcSampDiam_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i)
    (by
      have h := ttcSampInradius_pos atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol
      linarith)

/-- TTC's canonical `Threshold` is already a closed expression in `eps`, `delta`, and
the exact cube count.  No radius or facet datum occurs in it. -/
theorem canonicalThreshold_eq
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi) :
    ttcThresh atoms phi eps delta =
      max (24 * Real.log (24 / (4 * delta / 5)) /
          ((1 - eps / 12) * (eps / 12) ^ 2))
        (15 * (Real.log (6 / (4 * delta / 5)) +
          Real.log (ttcNumCubes atoms phi))) := by
  exact ttcThresh_eq atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol

theorem canonicalThreshold_nonneg
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1) :
    0 ≤ ttcThresh atoms phi eps delta :=
  ttcThresh_nonneg atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
    h_delta_pos h_delta_le

/-- A local comparison for each actual source-CV call implies the paper's total
volume term.  This is the smallest exact interface at which the big-O-suppressed CV
constants and logarithms must be supplied. -/
theorem ttcSourceVolumeQueryEnvelope_le_paperVolume_of_call
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (rho rMax : Real)
    (hcall : ∀ j : Fin (toDNFd (preprocess atoms phi)).length,
      ENNReal.ofReal
          (sourceAmplifiedQueryEnvelope runtimeConstant n
            (radialR
              (roundBody
                (algCen atoms phi eps delta
                  ⟨(toDNFd (preprocess atoms phi)).get j,
                    List.get_mem (toDNFd (preprocess atoms phi)) j⟩)
                (algGamma atoms phi eps delta)
                (region (atomSet (algAtoms atoms phi eps delta))
                  ((toDNFd (preprocess atoms phi)).get j))))
            (algBlock atoms phi eps delta).epsPrime
            (algBlock atoms phi eps delta).deltaPrime) ≤
        ENNReal.ofReal (rMax * paperVolumeFactor n rho eps)) :
    ttcSourceVolumeQueryEnvelope atoms phi eps delta runtimeConstant radialR ≤
      ENNReal.ofReal
        (((toDNFd (preprocess atoms phi)).length : Real) * rMax *
          paperVolumeFactor n rho eps) := by
  unfold ttcSourceVolumeQueryEnvelope
  calc
    _ ≤ ∑ _j : Fin (toDNFd (preprocess atoms phi)).length,
          ENNReal.ofReal (rMax * paperVolumeFactor n rho eps) := by
      exact Finset.sum_le_sum fun j _hj ↦ hcall j
    _ = ((toDNFd (preprocess atoms phi)).length : ENNReal) *
          ENNReal.ofReal (rMax * paperVolumeFactor n rho eps) := by simp
    _ = ENNReal.ofReal
        (((toDNFd (preprocess atoms phi)).length : Real) * rMax *
          paperVolumeFactor n rho eps) := by
      rw [← ENNReal.ofReal_natCast]
      rw [show
        ((toDNFd (preprocess atoms phi)).length : Real) * rMax *
            paperVolumeFactor n rho eps =
          ((toDNFd (preprocess atoms phi)).length : Real) *
            (rMax * paperVolumeFactor n rho eps) by ring]
      rw [ENNReal.ofReal_mul (by positivity :
        (0 : Real) ≤ (toDNFd (preprocess atoms phi)).length)]

/-- The concrete clipping intensity and concrete endpoint inspection bound imply the
paper's sampling term if (i) every clipped intensity is at most `threshold`, and
(ii) one endpoint costs at most `rMax*n^5*rho^2` inspections.  These are exactly the
two operational meanings of the two factors in the sampling line of `analysis.tex`. -/
theorem canonicalCappedSampleQueryEnvelope_le_paperSampling_of_cube
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (rho rMax threshold : Real)
    (_hrMax : 0 ≤ rMax)
    (hthreshold : 0 ≤ threshold)
    (hcap : ∀ i : CubeIndex atoms phi,
      (polyGoodRateCap atoms phi eps delta i : ENNReal) ≤
        ENNReal.ofReal threshold)
    (hprice : ∀ i : CubeIndex atoms phi,
      canonicalHybridSamplerQueryBound atoms phi eps delta i ≤
        ENNReal.ofReal (rMax * (n : Real) ^ 5 * rho ^ 2)) :
    canonicalCappedSampleQueryEnvelope atoms phi eps delta ≤
      ENNReal.ofReal
        (((toDNFd (preprocess atoms phi)).length : Real) * rMax *
          paperSamplingFactor n rho threshold) := by
  unfold canonicalCappedSampleQueryEnvelope
  calc
    _ ≤ ∑ _i : CubeIndex atoms phi,
          ENNReal.ofReal threshold *
            ENNReal.ofReal (rMax * (n : Real) ^ 5 * rho ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (hcap i) (hprice i) bot_le bot_le
    _ = (Fintype.card (CubeIndex atoms phi) : ENNReal) *
          (ENNReal.ofReal threshold *
            ENNReal.ofReal (rMax * (n : Real) ^ 5 * rho ^ 2)) := by simp
    _ = ENNReal.ofReal
        (((toDNFd (preprocess atoms phi)).length : Real) * rMax *
          paperSamplingFactor n rho threshold) := by
      rw [card_cubeIndex_eq_length]
      rw [← ENNReal.ofReal_natCast]
      rw [show
        ((toDNFd (preprocess atoms phi)).length : Real) * rMax *
            paperSamplingFactor n rho threshold =
          ((toDNFd (preprocess atoms phi)).length : Real) *
            (threshold * (rMax * (n : Real) ^ 5 * rho ^ 2)) by
        unfold paperSamplingFactor
        ring]
      rw [ENNReal.ofReal_mul (by positivity :
        (0 : Real) ≤ (toDNFd (preprocess atoms phi)).length)]
      rw [ENNReal.ofReal_mul hthreshold]

/-- The two local operational comparisons assemble to the exact unsuppressed runtime
envelope immediately preceding the final big-O statement in `analysis.tex`. -/
theorem operationalEnvelopes_le_paperRuntime_of_local
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (rho rMax threshold : Real)
    (hrMax : 0 ≤ rMax)
    (hthreshold : 0 ≤ threshold)
    (hvolumeCall : ∀ j : Fin (toDNFd (preprocess atoms phi)).length,
      ENNReal.ofReal
          (sourceAmplifiedQueryEnvelope runtimeConstant n
            (radialR
              (roundBody
                (algCen atoms phi eps delta
                  ⟨(toDNFd (preprocess atoms phi)).get j,
                    List.get_mem (toDNFd (preprocess atoms phi)) j⟩)
                (algGamma atoms phi eps delta)
                (region (atomSet (algAtoms atoms phi eps delta))
                  ((toDNFd (preprocess atoms phi)).get j))))
            (algBlock atoms phi eps delta).epsPrime
            (algBlock atoms phi eps delta).deltaPrime) ≤
        ENNReal.ofReal (rMax * paperVolumeFactor n rho eps))
    (hcap : ∀ i : CubeIndex atoms phi,
      (polyGoodRateCap atoms phi eps delta i : ENNReal) ≤
        ENNReal.ofReal threshold)
    (hprice : ∀ i : CubeIndex atoms phi,
      canonicalHybridSamplerQueryBound atoms phi eps delta i ≤
        ENNReal.ofReal (rMax * (n : Real) ^ 5 * rho ^ 2)) :
    ttcSourceVolumeQueryEnvelope atoms phi eps delta runtimeConstant radialR +
        canonicalCappedSampleQueryEnvelope atoms phi eps delta ≤
      ENNReal.ofReal
        (paperRuntimeEnvelope (toDNFd (preprocess atoms phi)).length n
          rho rMax eps threshold) := by
  apply operationalEnvelopes_le_paperRuntime _ _ _ _ _ _ hrMax hthreshold
  · exact ttcSourceVolumeQueryEnvelope_le_paperVolume_of_call
      atoms phi eps delta runtimeConstant radialR rho rMax hvolumeCall
  · exact canonicalCappedSampleQueryEnvelope_le_paperSampling_of_cube
      atoms phi eps delta rho rMax threshold hrMax hthreshold hcap hprice

/-- Public J-free operational TTC theorem with the exact unsuppressed paper envelope.
The conclusion is still an expected membership/facet-inspection bound; it does not
claim exact-real bit complexity.  The three local hypotheses are the explicit
implementation-to-paper comparisons isolated above. -/
theorem ttc_volume_estimate_operational_sourceSharp_fullTrajectory_paperRuntime
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (rho rMax threshold : Real)
    (hrMax : 0 ≤ rMax) (hthreshold : 0 ≤ threshold)
    (hvolumeCall : ∀ j : Fin (toDNFd (preprocess atoms phi)).length,
      ENNReal.ofReal
          (sourceAmplifiedQueryEnvelope runtimeConstant n
            (radialR
              (roundBody
                (algCen atoms phi eps (4 * delta / 5)
                  ⟨(toDNFd (preprocess atoms phi)).get j,
                    List.get_mem (toDNFd (preprocess atoms phi)) j⟩)
                (algGamma atoms phi eps (4 * delta / 5))
                (region (atomSet (algAtoms atoms phi eps (4 * delta / 5)))
                  ((toDNFd (preprocess atoms phi)).get j))))
            (algBlock atoms phi eps (4 * delta / 5)).epsPrime
            (algBlock atoms phi eps (4 * delta / 5)).deltaPrime) ≤
        ENNReal.ofReal (rMax * paperVolumeFactor n rho eps))
    (hcap : ∀ i : CubeIndex atoms phi,
      (polyGoodRateCap atoms phi eps (4 * delta / 5) i : ENNReal) ≤
        ENNReal.ofReal threshold)
    (hprice : ∀ i : CubeIndex atoms phi,
      canonicalHybridSamplerQueryBound atoms phi eps (4 * delta / 5) i ≤
        ENNReal.ofReal (rMax * (n : Real) ^ 5 * rho ^ 2)) :
    let deltaRun := 4 * delta / 5
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    letI := V.mΩ
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      ENNReal.ofReal
        (paperRuntimeEnvelope (toDNFd (preprocess atoms phi)).length n
          rho rMax eps threshold)) := by
  let deltaRun := 4 * delta / 5
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn hphi hvol
  have hmain :=
    ttc_volume_estimate_operational_sourceSharp_fullTrajectory atoms phi eps delta
      runtimeConstant radialR Omega oneLaw cost value hcert hconstant h_eps_pos
      h_eps_le h_delta_pos h_delta_le hn hphi hvol
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact operationalEnvelopes_le_paperRuntime_of_local atoms phi eps deltaRun
    runtimeConstant radialR rho rMax threshold hrMax hthreshold hvolumeCall hcap hprice

/-!
The local volume premise above cannot be deleted from a coefficient-one inequality.
Already one amplified CV call has a positive cutoff slack when the runtime constant is
zero.  More generally its explicit runtime constant and logarithmic amplification are
precisely factors which `analysis.tex` places under big-O suppression.
-/

theorem sourceAmplifiedQueryEnvelope_counterexample :
    4 < sourceAmplifiedQueryEnvelope 1000 1 0 (1 / 2) (1 / 2) := by
  have hlog : 0 ≤ Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  unfold sourceAmplifiedQueryEnvelope sourceOneRunQueryEnvelope
  norm_num
  nlinarith [hlog]

#print axioms card_cubeIndex_eq_length
#print axioms canonicalFacetCount_eq_algBlock
#print axioms canonicalHybridRadiusRatio_eq
#print axioms canonicalHybridRadiusRatio_pos
#print axioms canonicalThreshold_eq
#print axioms canonicalThreshold_nonneg
#print axioms ttcSourceVolumeQueryEnvelope_le_paperVolume_of_call
#print axioms canonicalCappedSampleQueryEnvelope_le_paperSampling_of_cube
#print axioms operationalEnvelopes_le_paperRuntime_of_local
#print axioms ttc_volume_estimate_operational_sourceSharp_fullTrajectory_paperRuntime
#print axioms sourceAmplifiedQueryEnvelope_counterexample

end Ttc.TTCOperationalPaperBridge

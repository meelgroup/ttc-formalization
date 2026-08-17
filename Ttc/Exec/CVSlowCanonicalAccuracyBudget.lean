import Ttc.Exec.CVGaussianScoreAwareMeanBudget

/-! # Discharging the accuracy binders of the slow canonical certificate

The frontier certificate constructor
`exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData` carries
three scalar accuracy binders: `hbeta : 0 ≤ beta`, `hbetaDef` (which pins `beta` to
the score-aware accuracy allowance) and `haccuracyBudget : eps + beta + eps * beta ≤
requested`.  This file supplies the canonical witnesses: `beta` is instantiated by
`scoreAwareAccuracyBeta`, `requested` by `slowAccuracyRequested`, and both binders
become `le_refl`.  The substantive content is that at the canonical stream count
`correctedRuntimeSamples m eps` the allowance is negligible, so the canonical request
is at most `2 * eps`; running the construction at internal accuracy `eps / 2` therefore
meets any externally requested accuracy `eps`.
-/

namespace Ttc.CVSlowCanonicalAccuracyBudget

set_option autoImplicit false

open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVCorrectedClippingArithmetic

/-- The score-aware accuracy allowance is nonnegative; this discharges the `hbeta`
binder of the slow canonical certificate. -/
theorem scoreAwareAccuracyBeta_nonneg (m k : Nat) {eps : Real} (heps : 0 < eps) :
    0 ≤ scoreAwareAccuracyBeta m k eps := by
  have halpha : 0 < correctedAlpha m eps := correctedAlpha_pos heps
  have htheta : 0 ≤ (m : Real) / (2 * correctedAlpha m eps) :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hgamma : 0 ≤ scoreAwareMeanGamma m k eps := scoreAwareMeanGamma_nonneg m k eps
  unfold scoreAwareAccuracyBeta
  exact add_nonneg (add_nonneg htheta hgamma) (mul_nonneg htheta hgamma)

/-- The canonical instantiation of the certificate's `requested` binder. -/
noncomputable def slowAccuracyRequested (m k : Nat) (eps : Real) : Real :=
  eps + scoreAwareAccuracyBeta m k eps + eps * scoreAwareAccuracyBeta m k eps

/-- The `haccuracyBudget` binder at the canonical witnesses; definitionally `le_refl`,
named so that callers can cite a single lemma. -/
theorem slowAccuracyBudget_le (m k : Nat) (eps : Real) :
    eps + scoreAwareAccuracyBeta m k eps + eps * scoreAwareAccuracyBeta m k eps ≤
      slowAccuracyRequested m k eps := le_refl _

/-- The clipping contribution to the allowance is quadratically small. -/
theorem phase_div_two_correctedAlpha_le (m : Nat) {eps : Real} (heps : 0 < eps) :
    (m : Real) / (2 * correctedAlpha m eps) ≤ eps ^ 2 / 200000 := by
  have h := phase_div_correctedAlpha_le (m := m) (ε := eps) heps
  calc
    (m : Real) / (2 * correctedAlpha m eps) =
        ((m : Real) / correctedAlpha m eps) / 2 := by ring
    _ ≤ (eps ^ 2 / 100000) / 2 := by gcongr
    _ = eps ^ 2 / 200000 := by ring

/-- The aggregate mean bias at the canonical stream count is negligible. -/
theorem scoreAwareMeanGamma_canonical_le
    (m : Nat) {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m (correctedRuntimeSamples m eps) eps ≤ eps / 8 :=
  (scoreAwareMeanGamma_corrected_le_div_hundred (m := m) heps heps1).trans
    (by linarith)

/-- At the canonical stream count the whole score-aware allowance costs at most a
quarter of the accuracy. -/
theorem scoreAwareAccuracyBeta_canonical_le
    (m : Nat) {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareAccuracyBeta m (correctedRuntimeSamples m eps) eps ≤ eps / 4 := by
  set k : Nat := correctedRuntimeSamples m eps with hk
  have htheta : (m : Real) / (2 * correctedAlpha m eps) ≤ eps ^ 2 / 200000 :=
    phase_div_two_correctedAlpha_le m heps
  have halpha : 0 < correctedAlpha m eps := correctedAlpha_pos heps
  have htheta0 : 0 ≤ (m : Real) / (2 * correctedAlpha m eps) :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hgamma : scoreAwareMeanGamma m k eps ≤ eps / 8 :=
    scoreAwareMeanGamma_canonical_le m heps heps1
  have hgamma0 : 0 ≤ scoreAwareMeanGamma m k eps := scoreAwareMeanGamma_nonneg m k eps
  have hprod : ((m : Real) / (2 * correctedAlpha m eps)) * scoreAwareMeanGamma m k eps ≤
      (eps ^ 2 / 200000) * (eps / 8) :=
    mul_le_mul htheta hgamma hgamma0 (by positivity)
  have hsq : eps ^ 2 ≤ eps := by nlinarith
  have hcube : eps ^ 2 * eps ≤ eps := by nlinarith
  unfold scoreAwareAccuracyBeta
  calc
    (m : Real) / (2 * correctedAlpha m eps) + scoreAwareMeanGamma m k eps +
        ((m : Real) / (2 * correctedAlpha m eps)) * scoreAwareMeanGamma m k eps ≤
        eps ^ 2 / 200000 + eps / 8 + (eps ^ 2 / 200000) * (eps / 8) := by
      gcongr
    _ ≤ eps / 4 := by nlinarith

/-- The canonical request at the canonical stream count. -/
theorem slowAccuracyRequested_canonical_le
    (m : Nat) {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    slowAccuracyRequested m (correctedRuntimeSamples m eps) eps ≤
      eps + eps / 4 + eps * (eps / 4) := by
  have hbeta := scoreAwareAccuracyBeta_canonical_le m heps heps1
  unfold slowAccuracyRequested
  gcongr

/-- Hence the canonical request never exceeds twice the internal accuracy. -/
theorem slowAccuracyRequested_canonical_le_two
    (m : Nat) {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    slowAccuracyRequested m (correctedRuntimeSamples m eps) eps ≤ 2 * eps := by
  have h := slowAccuracyRequested_canonical_le m heps heps1
  nlinarith

/-- Consumer-facing form: running the construction at internal accuracy `epsIn / 2`
meets the externally requested accuracy `epsIn`. -/
theorem slowAccuracyRequested_le_of_half
    (m : Nat) {epsIn : Real} (heps : 0 < epsIn) (heps1 : epsIn ≤ 1) :
    slowAccuracyRequested m (correctedRuntimeSamples m (epsIn / 2)) (epsIn / 2) ≤
      epsIn := by
  have h := slowAccuracyRequested_canonical_le_two m
    (eps := epsIn / 2) (by positivity) (by linarith)
  linarith

#print axioms scoreAwareAccuracyBeta_nonneg
#print axioms slowAccuracyBudget_le
#print axioms phase_div_two_correctedAlpha_le
#print axioms scoreAwareMeanGamma_canonical_le
#print axioms scoreAwareAccuracyBeta_canonical_le
#print axioms slowAccuracyRequested_canonical_le
#print axioms slowAccuracyRequested_canonical_le_two
#print axioms slowAccuracyRequested_le_of_half

end Ttc.CVSlowCanonicalAccuracyBudget

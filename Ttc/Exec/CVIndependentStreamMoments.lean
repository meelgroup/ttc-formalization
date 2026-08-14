import Ttc.Volume.CVEstimator
import Arlib.Probability.RunPlumbing

/-!
# Empirical phase moments on independent scalar cooling streams

The operational `k`-sample state is represented honestly as a finite product of complete
scalar stream laws.  Each stream retains its own raw seed.  The phase estimator reads one
score from each stream and averages them.  This file discharges the exact mean, `L²`, and
relative second-moment binders without making any independence claim about draws that
share a seed.
-/

namespace Ttc.CVIndependentStreamMoments

open MeasureTheory ProbabilityTheory
open scoped Classical

variable {k : Nat} {Path : Type*} [MeasurableSpace Path]

/-- Product law of `k` independently executed scalar paths. -/
noncomputable def independentStreamLaw (mu : Measure Path) : Measure (Fin k → Path) :=
  Measure.pi (fun _ : Fin k ↦ mu)

instance independentStreamLaw.isProbabilityMeasure
    (mu : Measure Path) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (independentStreamLaw (k := k) mu) := by
  unfold independentStreamLaw
  infer_instance

/-- One phase score read from scalar stream `l`. -/
noncomputable def streamScore (g : Path → Real) (l : Fin k)
    (omega : Fin k → Path) : Real :=
  g (omega l)

/-- Empirical phase average across the independent scalar streams. -/
noncomputable def streamAverage (g : Path → Real) (omega : Fin k → Path) : Real :=
  Ttc.CVEst.avgOf k (streamScore g) omega

theorem measurable_streamScore {g : Path → Real} (hg : Measurable g) (l : Fin k) :
    Measurable (streamScore g l) :=
  hg.comp (measurable_pi_apply l)

theorem measurable_streamAverage {g : Path → Real} (hg : Measurable g) :
    Measurable (streamAverage (k := k) g) := by
  unfold streamAverage Ttc.CVEst.avgOf
  exact (Finset.measurable_fun_sum _ fun l _ ↦ measurable_streamScore hg l).div
    measurable_const

theorem measurePreserving_streamCoord
    (mu : Measure Path) [IsProbabilityMeasure mu] (l : Fin k) :
    MeasurePreserving (fun omega : Fin k → Path ↦ omega l)
      (independentStreamLaw mu) mu := by
  unfold independentStreamLaw
  exact measurePreserving_eval (fun _ : Fin k ↦ mu) l

/-- The coordinate scores are genuinely independent because the complete scalar streams,
not merely their final draws, are product coordinates. -/
theorem iIndepFun_streamScore
    (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) :
    iIndepFun (streamScore (k := k) g) (independentStreamLaw mu) := by
  unfold streamScore independentStreamLaw
  exact iIndepFun_pi fun _ ↦ hg.aemeasurable

theorem integral_streamScore
    (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (l : Fin k) :
    ∫ omega, streamScore g l omega ∂(independentStreamLaw mu) = ∫ x, g x ∂mu := by
  have hmp := measurePreserving_streamCoord (k := k) mu l
  calc
    ∫ omega, streamScore g l omega ∂(independentStreamLaw mu) =
        ∫ x, g x ∂Measure.map (fun omega : Fin k → Path ↦ omega l)
          (independentStreamLaw mu) := by
            symm
            exact integral_map hmp.measurable.aemeasurable (by
              rw [hmp.map_eq]
              exact hg.aestronglyMeasurable)
    _ = ∫ x, g x ∂mu := by rw [hmp.map_eq]

theorem memLp_streamScore
    (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hL2 : MemLp g 2 mu) (l : Fin k) :
    MemLp (streamScore g l) 2 (independentStreamLaw mu) :=
  hL2.comp_measurePreserving (measurePreserving_streamCoord (k := k) mu l)

/-- The empirical score on independent complete streams is square-integrable whenever
the scalar score is. -/
theorem memLp_streamAverage
    (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hL2 : MemLp g 2 mu) :
    MemLp (streamAverage (k := k) g) 2 (independentStreamLaw mu) := by
  unfold streamAverage
  exact Ttc.CVEst.memLp_avgOf (fun l ↦ memLp_streamScore mu hL2 l)

theorem integrable_streamAverage_sq
    (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hL2 : MemLp g 2 mu) :
    Integrable (fun omega ↦ (streamAverage (k := k) g omega) ^ 2)
      (independentStreamLaw mu) :=
  (memLp_streamAverage (k := k) mu hL2).integrable_sq

/-- Exact empirical mean on the independent-stream law. -/
theorem integral_streamAverage
    (hk : 0 < k) (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hgInt : Integrable g mu) :
    ∫ omega, streamAverage (k := k) g omega ∂(independentStreamLaw mu) =
      ∫ x, g x ∂mu := by
  apply Ttc.CVEst.integral_avgOf hk
  · intro l
    change Integrable (fun omega : Fin k → Path ↦ g (omega l)) (independentStreamLaw mu)
    exact (measurePreserving_streamCoord (k := k) mu l).integrable_comp_of_integrable hgInt
  · intro l
    exact integral_streamScore mu hg l

/-- The exact averaged relative-second-moment factor on `k` independent operational
streams.  If a scalar phase score has factor `rawFactor`, its empirical mean has factor
`1 + (rawFactor-1)/k`. -/
theorem integral_streamAverage_sq_le
    (hk : 0 < k) (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hL2 : MemLp g 2 mu)
    {rawFactor mean : Real} (hmean : ∫ x, g x ∂mu = mean)
    (hsq : ∫ x, (g x) ^ 2 ∂mu ≤ rawFactor * mean ^ 2) :
    ∫ omega, (streamAverage (k := k) g omega) ^ 2
        ∂(independentStreamLaw mu) ≤
      (1 + (rawFactor - 1) / (k : Real)) * mean ^ 2 := by
  apply Ttc.CVEst.avgOf_sq_moment_le hk
  · exact fun l ↦ memLp_streamScore mu hL2 l
  · intro l l' hne
    exact (iIndepFun_streamScore (k := k) mu hg).indepFun hne
  · intro l
    rw [integral_streamScore mu hg l]
    exact hmean
  · intro l
    have hmp := measurePreserving_streamCoord (k := k) mu l
    calc
      ∫ omega, (streamScore g l omega) ^ 2 ∂(independentStreamLaw mu) =
          ∫ x, (g x) ^ 2 ∂Measure.map (fun omega : Fin k → Path ↦ omega l)
            (independentStreamLaw mu) := by
              symm
              exact integral_map hmp.measurable.aemeasurable (by
                rw [hmp.map_eq]
                exact (hg.pow_const 2).aestronglyMeasurable)
      _ = ∫ x, (g x) ^ 2 ∂mu := by rw [hmp.map_eq]
      _ ≤ rawFactor * mean ^ 2 := hsq

/-- The factor used by the corrected CV estimator: a scalar relative second moment at
most `9` becomes `1 + 8/k` after averaging `k` independent complete streams. -/
theorem integral_streamAverage_sq_le_nine
    (hk : 0 < k) (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hL2 : MemLp g 2 mu)
    {mean : Real} (hmean : ∫ x, g x ∂mu = mean)
    (hsq : ∫ x, (g x) ^ 2 ∂mu ≤ 9 * mean ^ 2) :
    ∫ omega, (streamAverage (k := k) g omega) ^ 2
        ∂(independentStreamLaw mu) ≤
      (1 + 8 / (k : Real)) * mean ^ 2 := by
  simpa only [show (9 : Real) - 1 = 8 by norm_num] using
    integral_streamAverage_sq_le hk mu hg hL2 hmean hsq

#print axioms measurePreserving_streamCoord
#print axioms iIndepFun_streamScore
#print axioms integral_streamAverage
#print axioms integral_streamAverage_sq_le
#print axioms integral_streamAverage_sq_le_nine

end Ttc.CVIndependentStreamMoments

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVCombinedContinuingRetryPhaseTV
import Ttc.Volume.CVDirectMetropolisPhase

/-!
# Distributional warmness of a Gaussian combined-accept retry

Finite lazy walks retain a point mass at a deterministic starting state.  Therefore the
pointwise local domination premise of `FiniteContinuingRetrySelfWarm` cannot hold against
the atomless Gaussian target.  The correct statement is distributional: a warm incoming
law stays warm under the stationary lazy speedy walk; adding the independent coin keeps
the same warmness; and an actual acceptance probability at least `1/16` costs a factor
`16` when the accepted law is normalized.
-/

namespace Ttc.CVGaussianAcceptedWarm

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler Ttc.SpeedyRejection
open Ttc.CVCombinedContinuingAccept Ttc.FiniteContinuingRetryGaussian
open Ttc.CVCombinedContinuingRetryPhaseTV
open scoped ENNReal Classical Pointwise

variable {E C : Type*} [MeasurableSpace E] [MeasurableSpace C]

/-- Tensoring both laws with the same finite measure preserves a warmness constant. -/
theorem IsWarm.prod_right_same {mu nu : Measure E} {xi : Measure C} [SFinite xi]
    {M : ENNReal} (h : IsWarm M mu nu) :
    IsWarm M (mu.prod xi) (nu.prod xi) := by
  have hle : mu ≤ M • nu := by
    apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.smul_apply]
    simpa only [smul_eq_mul] using h S hS
  have hp : mu.prod xi ≤ (M • nu).prod xi := Measure.prod_mono hle le_rfl
  rw [Measure.prod_smul_left] at hp
  intro S hS
  have := hp S
  rw [Measure.smul_apply] at this
  simpa only [smul_eq_mul] using this

/-- Conditioning an `M`-warm proposal on an event of actual mass at least `1/16`
costs at most a factor `16`.  No TV-to-warm conversion is used here. -/
theorem isWarm_condOn_sixteenth
    {nu tau : Measure E} [IsProbabilityMeasure nu] [IsProbabilityMeasure tau]
    {A : Set E} (hA : MeasurableSet A) {M : ENNReal}
    (hwarm : IsWarm M nu tau)
    (hnu : ENNReal.ofReal (1 / 16 : Real) ≤ nu A) :
    IsWarm (16 * M) (Arlib.condOn nu A) (Arlib.condOn tau A) := by
  have hnuInv : (nu A)⁻¹ ≤ (16 : ENNReal) := by
    rw [ENNReal.inv_le_iff_inv_le]
    have h16 : (16 : ENNReal) = ENNReal.ofReal (16 : Real) := by norm_num
    rw [h16]
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 16)]
    convert hnu using 1 <;> norm_num
  have htauInv : (1 : ENNReal) ≤ (tau A)⁻¹ :=
    ENNReal.one_le_inv.mpr prob_le_one
  intro T hT
  rw [Arlib.condOn_apply nu hA hT, Arlib.condOn_apply tau hA hT]
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  calc
    (nu A)⁻¹ * nu (T ∩ A) ≤ (nu A)⁻¹ * (M * tau (T ∩ A)) := by
      gcongr
      exact hwarm (T ∩ A) (hT.inter hA)
    _ ≤ 16 * (M * tau (T ∩ A)) := by gcongr
    _ ≤ 16 * (M * ((tau A)⁻¹ * tau (T ∩ A))) := by
      gcongr
      calc
        tau (T ∩ A) = 1 * tau (T ∩ A) := by rw [one_mul]
        _ ≤ (tau A)⁻¹ * tau (T ∩ A) := by gcongr
    _ = (16 * M) * ((tau A)⁻¹ * tau (T ∩ A)) := by ac_rfl

/-- An ideal acceptance floor `1/8` and TV error at most `1/16` imply actual acceptance
at least `1/16`. -/
theorem sixteenth_le_acceptance_of_tvLe_eighth
    {nu tau : Measure E} {zeta : ENNReal} (htv : TVLe nu tau zeta)
    {A : Set E} (hA : MeasurableSet A)
    (heighth : ENNReal.ofReal (1 / 8 : Real) ≤ tau A)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    ENNReal.ofReal (1 / 16 : Real) ≤ nu A := by
  refine ENNReal.le_of_add_le_add_right
    (show ENNReal.ofReal (1 / 16 : Real) ≠ (⊤ : ENNReal) from ENNReal.ofReal_ne_top) ?_
  calc
    ENNReal.ofReal (1 / 16 : Real) + ENNReal.ofReal (1 / 16 : Real) =
        ENNReal.ofReal (1 / 8 : Real) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    _ ≤ tau A := heighth
    _ ≤ nu A + zeta := htv.right hA
    _ ≤ nu A + ENNReal.ofReal (1 / 16 : Real) := by gcongr

/-- Warmness plus the source acceptance floor gives multiplicative warmness of the
normalized combined-accepted output.  This is the honest distributional replacement for
the false pointwise local premise. -/
theorem isWarm_combinedAccepted_of_warm_tv
    {n : Nat} {nu tau : Measure (EuclideanSpace Real (Fin n) × Real)}
    [IsProbabilityMeasure nu] [IsProbabilityMeasure tau]
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {c s : Real} (hc : c ≠ 0) {M zeta : ENNReal}
    (hwarm : IsWarm M nu tau)
    (htv : TVLe nu tau zeta)
    (heighth : ENNReal.ofReal (1 / 8 : Real) ≤ tau (combinedAccept K c s))
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    IsWarm (16 * M)
      (Measure.map (combinedOutput c)
        (Arlib.condOn nu (combinedAccept K c s)))
      (Measure.map (combinedOutput c)
        (Arlib.condOn tau (combinedAccept K c s))) := by
  have hacc := sixteenth_le_acceptance_of_tvLe_eighth htv
    (measurableSet_combinedAccept hK hc) heighth hzeta
  intro T hT
  rw [Measure.map_apply (measurable_combinedOutput c) hT,
    Measure.map_apply (measurable_combinedOutput c) hT]
  exact isWarm_condOn_sixteenth (measurableSet_combinedAccept hK hc) hwarm hacc
    _ (hT.preimage (measurable_combinedOutput c))

/-- A warm distributional start remains warm after the actual cost-recording lazy-speedy
round once cost is erased and the independent coin is added. -/
theorem isWarm_costErased_combinedRound
    {n : Nat} {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta s : Real} (hdelta : 0 < delta) {rho : Measure (EuclideanSpace Real (Fin n))}
    [IsProbabilityMeasure rho]
    (hell : IsProbabilityMeasure (ellGaussianProb K delta s))
    {M : ENNReal} (hwarm : IsWarm M rho (ellGaussianProb K delta s)) (t : Nat) :
    IsWarm M
      (Measure.map Prod.snd
        (sampleFromKernel (combinedRoundCostedKernel K hK delta s hdelta t) rho))
      (proposal (ellGaussianProb K delta s)) := by
  letI : IsProbabilityMeasure (ellGaussianProb K delta s) := hell
  rw [map_snd_sampleFrom_combinedRoundCostedKernel hK delta s hdelta]
  apply IsWarm.prod_right_same
  rw [← Ttc.CVSequentialPhaseSampler.iterate_eq_sampleFrom_iteratedKernel]
  exact isWarm_iterate_of_invariant hwarm
    ((isReversible_lazy
      (isReversible_speedyMetropolisGaussian_prob hK delta s)).invariant) t

/-- Fully Gaussian form: a warm distributional retry proposal has a `16 M`-warm
combined-accepted output, provided its additive mixing error is small enough to retain the
source `1/8` acceptance floor. -/
theorem isWarm_costedCombinedAccepted
    {n : Nat} {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    {rho : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure rho]
    (hell : IsProbabilityMeasure (ellGaussianProb K delta s))
    {M zeta : ENNReal} (hwarm : IsWarm M rho (ellGaussianProb K delta s))
    (t : Nat)
    (htv : TVLe
      (Measure.map Prod.snd
        (sampleFromKernel (combinedRoundCostedKernel K hK delta s hdelta t) rho))
      (proposal (ellGaussianProb K delta s)) zeta)
    (heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      proposal (ellGaussianProb K delta s) (combinedAccept K c s))
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    IsWarm (16 * M)
      (Measure.map (acceptedOutput c)
        (Arlib.condOn
          (sampleFromKernel (combinedRoundCostedKernel K hK delta s hdelta t) rho)
          (costedCombinedAccept K c s)))
      (Measure.map (combinedOutput c)
        (Arlib.condOn (proposal (ellGaussianProb K delta s))
          (combinedAccept K c s))) := by
  letI : IsProbabilityMeasure (ellGaussianProb K delta s) := hell
  letI : IsProbabilityMeasure
      (sampleFromKernel (combinedRoundCostedKernel K hK delta s hdelta t) rho) := by
    infer_instance
  letI : IsProbabilityMeasure
      (Measure.map Prod.snd
        (sampleFromKernel (combinedRoundCostedKernel K hK delta s hdelta t) rho)) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hwarmPair := isWarm_costErased_combinedRound hK hdelta hell hwarm t
  have h := isWarm_combinedAccepted_of_warm_tv hK hc hwarmPair htv heighth hzeta
  rw [map_acceptedOutput_condOn_costedCombinedAccept
    (nu := sampleFromKernel (combinedRoundCostedKernel K hK delta s hdelta t) rho)
    (K := K) (c := c) (s := s) hK hc]
  exact h

end Ttc.CVGaussianAcceptedWarm

#print axioms Ttc.CVGaussianAcceptedWarm.isWarm_condOn_sixteenth
#print axioms Ttc.CVGaussianAcceptedWarm.isWarm_combinedAccepted_of_warm_tv
#print axioms Ttc.CVGaussianAcceptedWarm.isWarm_costErased_combinedRound
#print axioms Ttc.CVGaussianAcceptedWarm.isWarm_costedCombinedAccepted

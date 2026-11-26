/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.FuelStep
import ttc.Analysis.PrecisionChoice
import ttc.Analysis.ScaledVolumeBridge
import ttc.Analysis.ConcreteComponentStep
import ttc.Analysis.OriginCertifiedRun

/-!
# The certified components

On a component of the decomposition, at the precision of `GetPrecision`, the old step is the
`gvGen` form with the conditioned point law (`step_eq_gvGen`), and the sealed sampler with fuel
approximates that law (`approx_samplerLaw`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ttc.Tape

open ArlibCommunity.Algorithms.CV18 (measurable_some)
open ttc (TTCState)

variable {d k : ℕ} {F : ttc.LRAFormula d k}

/-- The point law `GenerateSamples` draws from on a component: the rounded proposal
conditioned on acceptance. -/
def condLaw (P : ttc.PolytopeData d) (b : ℕ) (eta : ℝ) : Measure (Fin d → ℤ) :=
  ArlibCommunity.Foundations.Convex.condOn
    (ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw P b eta))
    (ttc.acceptedIntegers P b)

section Certified

variable (hn : 21 ≤ d) (D : ttc.Decomposition F) (p : ttc.ApproxParams) (i : Fin D.componentCount)

include hn in
theorem route_certified :
    ttc.samplerRadiusRequirement (D.component i) p.ε' ≤
        ttc.decimalScale (ttc.GetPrecision D p.precisionEta) * (D.component i).inradius ∧
      0 < p.ε' ∧ p.ε' ≤ 1 ∧
      (ttc.codedLatticePoints (D.component i) (ttc.GetPrecision D p.precisionEta)).Finite ∧
      (ttc.codedLatticePoints (D.component i) (ttc.GetPrecision D p.precisionEta)).Nonempty := by
  have hn0 : 0 < d := by omega
  have hadq := (ttc.getPrecisionChoice D p).adequate
  have hset := ttc.coded_lattice_points_finite_nonempty hn0 D p
    (ttc.GetPrecision D p.precisionEta) hadq i
  have hunit : ttc.samplerRadiusRequirement (D.component i) p.ε' ≤
      ttc.decimalScale (ttc.GetPrecision D p.precisionEta) * (D.component i).inradius :=
    (le_max_right _ _).trans (hadq.split i)
  refine ⟨hunit, div_pos p.epsilon_pos (by norm_num), ?_, hset.1, hset.2⟩
  dsimp only [ttc.ApproxParams.ε']
  linarith [p.epsilon_le_one]

include hn in
theorem acceptance_pos :
    ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw (D.component i)
        (ttc.GetPrecision D p.precisionEta) p.ε')
      (ttc.acceptedIntegers (D.component i) (ttc.GetPrecision D p.precisionEta)) ≠ 0 := by
  have hn0 : 0 < d := by omega
  have := ttc.normalizedHitAndRunContinuousLaw_isProbabilityMeasure hn0 (D.component i)
    (ttc.GetPrecision D p.precisionEta) p.ε'
  have := Arlib.KV97.isProbabilityMeasure_roundedMeasureLaw
    (ttc.normalizedHitAndRunContinuousLaw (D.component i) (ttc.GetPrecision D p.precisionEta) p.ε')
  have h := ttc.certified_normalizedHitAndRun_acceptance_ge_half hn D p
    (ttc.GetPrecision D p.precisionEta) (ttc.getPrecisionChoice D p).adequate i
  rw [ttc.roundedAcceptanceProbability_val_eq] at h
  intro h0
  rw [Measure.real, h0, ENNReal.toReal_zero] at h
  norm_num at h

end Certified

/-- **The old step, on a certified component, in the `gvGen` form.** -/
theorem step_eq_gvGen (hn : 21 ≤ d) (prep : ttc.TTCPreprocessor d k) (P : ttc.PolytopeData d)
    (b : ℕ) (eta delta Th : ℝ)
    (hroute : ttc.samplerRadiusRequirement P eta ≤ ttc.decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧ (ttc.codedLatticePoints P b).Finite ∧
      (ttc.codedLatticePoints P b).Nonempty) (y : TTCState d) :
    ttcPseudocode.step (ttc.ttcSubroutines hn prep) b eta delta Th P y =
      (ttc.communityCV18VolumeLaw (by omega) P eta delta).bind fun vol =>
        gvGen P Th (oldInner Th (condLaw P b eta) b) y (ttcPseudocode.t b d vol.2) := by
  simp only [ttcPseudocode.step, gvGen, oldInner, appendLaw,
    ttc.community_generateSamples_eq_iid hn prep P _ b eta delta hroute]
  rfl

theorem body_eq (P : ttc.PolytopeData d) (b : ℕ) (eta : ℝ) :
    ttc.HitAndRunLaw.body (P.hitAndRunPresentation b eta) = P.normalizedHitAndRunBody b eta := by
  simp only [ttc.HitAndRunLaw.body, ttc.PolytopeData.hitAndRunPresentation,
    ttc.PolytopeData.hitAndRunOffsetsProg_value]
  rfl

/-- **The sealed sampler with fuel approximates the conditioned point law.** -/
theorem approx_samplerLaw (hn : 21 ≤ d) (D : ttc.Decomposition F) (p : ttc.ApproxParams)
    (i : Fin D.componentCount) (b' : ℕ) :
    Approx (fun f => samplerLaw (paramsOf D p) f b' (D.component i))
      (condLaw (D.component i) (ttc.GetPrecision D p.precisionEta) p.ε') := by
  have hm : 0 < D.componentCount := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hdimN, hdim, he, -, -, hs, -⟩ := paramsProg_val D p hm
  set P := D.component i
  set bP := ttc.GetPrecision D p.precisionEta
  have hcont := ttc.normalizedHitAndRunContinuousLaw_isProbabilityMeasure (by omega) P bP p.ε'
  have := Arlib.KV97.isProbabilityMeasure_roundedMeasureLaw
    (ttc.normalizedHitAndRunContinuousLaw P bP p.ε')
  have hK : Bornology.IsBounded (ttc.HitAndRunLaw.body (P.hitAndRunPresentation bP p.ε')) := by
    rw [body_eq]; exact P.normalizedHitAndRun_bounded bP p.ε'
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆
      ttc.HitAndRunLaw.body (P.hitAndRunPresentation bP p.ε') := by
    rw [body_eq]
    exact Metric.ball_subset_closedBall.trans (P.normalizedHitAndRun_unitBall bP p.ε')
  have heq : (fun f => samplerLaw (paramsOf D p) f b' P) = fun f =>
      (∑ j ∈ Finset.range f, ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw P bP p.ε')
          (ttc.acceptedIntegers P bP)ᶜ ^ j) •
        ((ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw P bP p.ε')).restrict
          (ttc.acceptedIntegers P bP)).map some +
      ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw P bP p.ε')
          (ttc.acceptedIntegers P bP)ᶜ ^ f • Measure.dirac none := by
    funext f
    exact sampler_eq_old P bP p.ε' _ _ _ hs he hdim _ hdimN hK hball b' f
  rw [heq]
  exact approx_retry _ _ (Set.to_countable _).measurableSet (acceptance_pos hn D p i)

end ttc.Tape

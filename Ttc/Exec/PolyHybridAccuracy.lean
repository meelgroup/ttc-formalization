import Ttc.Exec.PolySamplerAccuracyGeneric
import Ttc.Exec.ConcreteHybridCanonicalOwnerPoly

/-!
# Accuracy of the honest hybrid TTC sampling law

This instantiates the sampler-parametric TTC proof at the operational lazy
hit-and-run/ball-walk hybrid law.  It does not identify that law with legacy
`polySampD`.
-/

namespace Ttc.ConcreteHybridCanonicalOwnerPoly

open MeasureTheory ProbabilityTheory Set
open Ttc.CostedTTCPlugin
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}
variable (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)

theorem polyRatesWith_polyHybridSampD
    (V : VolumeAlgorithm n) (omega : V.Ω)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n)) :
    Ttc.polyRatesWith atoms phi eps delta V omega
        (polyHybridSampD atoms phi eps delta rin Rout step Mw sigma) =
      polyHybridRates atoms phi eps delta V omega rin Rout step Mw sigma := rfl

/-- The semantic iterated-integral accuracy theorem for the distinct hybrid
rates.  The regime premise is discharged by `big_polyRatesWith`. -/
theorem lintegral_ttcPolyRun_ge_polyHybrid
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (V : VolumeAlgorithm n)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (sampler : KV97Sampler A n (M atoms phi eps delta) (D atoms phi)
      (rho atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
      (polyHybridSampD atoms phi eps delta rin Rout step Mw sigma)) :
    1 - delta ≤
      letI := V.mΩ
      (∫⁻ omega,
        trajLaw (polyHybridRates atoms phi eps delta V omega rin Rout step Mw sigma)
          {t | ttcPolyRun atoms phi eps delta V omega t ∈
            relErr eps (volSol (atomSet atoms) phi)} ∂V.μ).toReal := by
  simpa only [polyRatesWith_polyHybridSampD] using
    Ttc.lintegral_ttcPolyRun_ge_withSampler_closedBig atoms phi eps delta
      h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol V
      (polyHybridSampD atoms phi eps delta rin Rout step Mw sigma) sampler

/-- Joint-law form consumed by the canonical-owner operational capstone. -/
theorem polyHybridKernel_accuracy
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (V : VolumeAlgorithm n)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (sampler : KV97Sampler A n (M atoms phi eps delta) (D atoms phi)
      (rho atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
      (polyHybridSampD atoms phi eps delta rin Rout step Mw sigma)) :
    letI := V.mΩ
    1 - delta ≤
      ((V.μ.compProd (polyHybridKernel atoms phi eps delta V rin Rout step Mw sigma))
        (idealPolyAccuracyEvent (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V)).toReal := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel
      (polyHybridKernel atoms phi eps delta V rin Rout step Mw sigma) :=
    isMarkovKernel_polyHybridKernel atoms phi eps delta V rin Rout step Mw sigma
  let S := idealPolyAccuracyEvent (atoms := atoms) (phi := phi)
    (eps := eps) (delta := delta) V
  have hS : MeasurableSet S := measurableSet_idealPolyAccuracyEvent V
  rw [Measure.compProd_apply hS]
  change 1 - delta ≤
    (∫⁻ omega,
      trajLaw (polyHybridRates atoms phi eps delta V omega rin Rout step Mw sigma)
        {t | ttcPolyRun atoms phi eps delta V omega t ∈
          relErr eps (volSol (atomSet atoms) phi)} ∂V.μ).toReal
  exact lintegral_ttcPolyRun_ge_polyHybrid atoms phi eps delta h_eps_pos h_eps_le
    h_delta_pos h_delta_le hn hphi hvol V rin Rout step Mw sigma sampler

/-- The existing canonical-owner correctness/cost theorem with its semantic
accuracy premise discharged for the honest hybrid sampler. -/
theorem polyHybridCanonicalJoint_accuracy_and_expectedQueries
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (V : ExpectedQueryVolumeAlgorithm n)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (sampler : KV97Sampler A n (M atoms phi eps delta) (D atoms phi)
      (rho atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
      (polyHybridSampD atoms phi eps delta rin Rout step Mw sigma))
    (P : @Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
      (CubeIndex atoms phi) _ (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega s, (P.family omega).lam (P.owner s) *
          (P.family omega).q (P.owner s) s.castSucc =
        max (polyHybridRates atoms phi eps delta V.toVolumeAlgorithm omega
          rin Rout step Mw sigma s) 0)
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    (1 - delta ≤
      ((Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
        (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)).toReal) ∧
    ((∫⁻ z, Ttc.CostedCanonicalOwnerTTCPlugin.canonicalActualPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P J z
        ∂Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) ≤
      Ttc.ttcPolyVolumeQueryBound atoms phi eps delta V +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ) := by
  letI := V.mΩ
  exact polyHybridCanonicalJoint_accuracy_and_expectedQueries_of_semantic
    atoms phi eps delta V rin Rout step Mw sigma P hrate
    (polyHybridKernel_accuracy atoms phi eps delta h_eps_pos h_eps_le
      h_delta_pos h_delta_le hn hphi hvol V.toVolumeAlgorithm rin Rout step Mw sigma
      sampler) hJ

#print axioms polyRatesWith_polyHybridSampD
#print axioms lintegral_ttcPolyRun_ge_polyHybrid
#print axioms polyHybridKernel_accuracy
#print axioms polyHybridCanonicalJoint_accuracy_and_expectedQueries

end Ttc.ConcreteHybridCanonicalOwnerPoly

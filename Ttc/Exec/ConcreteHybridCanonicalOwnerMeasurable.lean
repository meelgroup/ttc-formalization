import Ttc.Exec.CanonicalOwnerMeasurableKernel
import Ttc.Exec.PolyHybridAccuracy

/-!
# Measurable canonical-owner plug-in for the concrete hybrid sampler

This file removes the outer `Kernel` and fiber-equality binders from the
concrete hybrid canonical-owner construction.  The cube samplers and their
finite mark laws are fixed; only the nonnegative Poisson rate vector varies
with the volume-oracle coin.
-/

namespace Ttc.ConcreteHybridCanonicalOwnerMeasurable

open MeasureTheory ProbabilityTheory Set Pointwise
open Ttc.KV97RoundedEndpointBridge
open Ttc.CostedMarkedPoisson
open Ttc.CostedMarkedPoissonTrajectory
open Ttc.CanonicalOwnerPoissonAssembler
open Ttc.ConcreteHybridCanonicalOwnerSampler
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open scoped ENNReal BigOperators Classical NNReal

variable {A : Type*} {n : Nat}
variable (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)

/-- The canonical-owner plug-in whose outer kernel is constructed by Giry
measurability of the complete marked-Poisson/thinning trajectory. -/
noncomputable def polyHybridTrajectoryPluginMeasurable
    (V : ExpectedQueryVolumeAlgorithm n)
    (hle : HasLatticeEnum
      (Ttc.ConcreteHybridCanonicalOwnerPoly.M atoms phi eps delta)
      (preprocess atoms phi)
      (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta))
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi)
          (latticeScale
            (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance
          (Ttc.ConcreteHybridCanonicalOwnerPoly.M atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta) i.val)) :
    letI := V.mΩ
    CanonicalOwnerTrajectoryPlugin (CubeIndex atoms phi)
      (algIndex atoms phi eps delta) V.Ω := by
  letI := V.mΩ
  let target := polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
  let fine := polyHybridFineSampler atoms phi eps delta rin Rout step Mw sigma hsigma
    hbounded hstep heighth
  let base : CubeMarkedFamily (CubeIndex atoms phi) (algIndex atoms phi eps delta) :=
    canonicalMarkedFamily (Ttc.ConcreteHybridCanonicalOwnerPoly.pt atoms phi eps delta)
      target
      (isProbabilityMeasure_polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
        hsigma hbounded hstep heighth)
      fine (fun _ => 0) (fun _ => le_rfl)
  let lam : V.Ω → CubeIndex atoms phi → NNReal := fun omega i =>
    (polyVol atoms phi eps delta V.toVolumeAlgorithm omega i.val).toNNReal
  have hlam : Measurable lam := by
    exact measurable_pi_lambda _ fun i => measurable_real_toNNReal.comp
      (measurable_polyVol atoms phi eps delta V.toVolumeAlgorithm i.val)
  exact CanonicalOwnerTrajectoryPlugin.ofMeasurableRates
    base.q base.q_nonneg base.q_sum base.sampler
    (polyOwner atoms phi eps delta hle) lam hlam

/-! The following rate identity is the interface consumed by the generic
costed TTC plug-in. -/

theorem polyHybridTrajectoryPluginMeasurable_rate
    (V : ExpectedQueryVolumeAlgorithm n)
    (hle : HasLatticeEnum
      (Ttc.ConcreteHybridCanonicalOwnerPoly.M atoms phi eps delta)
      (preprocess atoms phi)
      (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta))
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi)
          (latticeScale
            (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance
          (Ttc.ConcreteHybridCanonicalOwnerPoly.M atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta) i.val))
    (omega : V.Ω) (s : Fin (algIndex atoms phi eps delta)) :
    letI := V.mΩ
    let P := polyHybridTrajectoryPluginMeasurable atoms phi eps delta V hle
      rin Rout step Mw sigma hsigma hbounded hstep heighth
    (P.family omega).lam (P.owner s) *
        (P.family omega).q (P.owner s) s.castSucc =
      max (polyHybridRates atoms phi eps delta V.toVolumeAlgorithm omega
        rin Rout step Mw sigma s) 0 := by
  letI := V.mΩ
  unfold polyHybridTrajectoryPluginMeasurable
  dsimp only [CanonicalOwnerTrajectoryPlugin.ofMeasurableRates]
  rw [Real.coe_toNNReal']
  exact polyHybridMarkedFamily_selectedRate atoms phi eps delta V.toVolumeAlgorithm
    omega hle rin Rout step Mw sigma hsigma hbounded hstep heighth s

/-- Concrete hybrid TTC accuracy and recorded-query bound with the outer
trajectory kernel and its fiber identity discharged by measurability.  The
only probabilistic premise left at this layer is the sampler-generic TTC
semantic accuracy statement. -/
theorem polyHybridCanonicalMeasurable_accuracy_and_expectedQueries_of_semantic
    (V : ExpectedQueryVolumeAlgorithm n)
    (hle : HasLatticeEnum
      (Ttc.ConcreteHybridCanonicalOwnerPoly.M atoms phi eps delta)
      (preprocess atoms phi)
      (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta))
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi)
          (latticeScale
            (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance
          (Ttc.ConcreteHybridCanonicalOwnerPoly.M atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta) i.val))
    (hsemantic : letI := V.mΩ
      1 - delta ≤
        ((V.μ.compProd (polyHybridKernel atoms phi eps delta V.toVolumeAlgorithm
          rin Rout step Mw sigma))
          (Ttc.CostedTTCPlugin.idealPolyAccuracyEvent
            (atoms := atoms) (phi := phi) (eps := eps) (delta := delta)
            V.toVolumeAlgorithm)).toReal)
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    let P := polyHybridTrajectoryPluginMeasurable atoms phi eps delta V hle
      rin Rout step Mw sigma hsigma hbounded hstep heighth
    (1 - delta ≤
      ((canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
        (canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)).toReal) ∧
    ((∫⁻ z, canonicalActualPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P J z
        ∂canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) ≤
      Ttc.ttcPolyVolumeQueryBound atoms phi eps delta V +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ) := by
  letI := V.mΩ
  let P := polyHybridTrajectoryPluginMeasurable atoms phi eps delta V hle
    rin Rout step Mw sigma hsigma hbounded hstep heighth
  exact polyHybridCanonicalJoint_accuracy_and_expectedQueries_of_semantic
    atoms phi eps delta V rin Rout step Mw sigma P
      (polyHybridTrajectoryPluginMeasurable_rate atoms phi eps delta V hle
        rin Rout step Mw sigma hsigma hbounded hstep heighth)
      hsemantic hJ

/-- Final measurable canonical-owner TTC theorem for the honest hybrid
sampler.  Both the outer trajectory-kernel seam and the semantic-accuracy seam
are discharged. -/
theorem polyHybridCanonicalMeasurable_accuracy_and_expectedQueries
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (V : ExpectedQueryVolumeAlgorithm n)
    (hle : HasLatticeEnum
      (Ttc.ConcreteHybridCanonicalOwnerPoly.M atoms phi eps delta)
      (preprocess atoms phi)
      (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta))
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi)
          (latticeScale
            (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance
          (Ttc.ConcreteHybridCanonicalOwnerPoly.M atoms phi eps delta)
          (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta) i.val))
    (sampler : KV97Sampler A n
      (Ttc.ConcreteHybridCanonicalOwnerPoly.M atoms phi eps delta)
      (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi)
      (Ttc.ConcreteHybridCanonicalOwnerPoly.rho atoms phi eps delta)
      (algBlock atoms phi eps delta).epsPrime
      (polyHybridSampD atoms phi eps delta rin Rout step Mw sigma))
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    let P := polyHybridTrajectoryPluginMeasurable atoms phi eps delta V hle
      rin Rout step Mw sigma hsigma hbounded hstep heighth
    (1 - delta ≤
      ((canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
        (canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)).toReal) ∧
    ((∫⁻ z, canonicalActualPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P J z
        ∂canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) ≤
      Ttc.ttcPolyVolumeQueryBound atoms phi eps delta V +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ) := by
  letI := V.mΩ
  exact polyHybridCanonicalMeasurable_accuracy_and_expectedQueries_of_semantic
    atoms phi eps delta V hle rin Rout step Mw sigma hsigma hbounded hstep heighth
    (polyHybridKernel_accuracy atoms phi eps delta h_eps_pos h_eps_le
      h_delta_pos h_delta_le hn hphi hvol V.toVolumeAlgorithm rin Rout step Mw sigma
      sampler) hJ

#print axioms polyHybridTrajectoryPluginMeasurable
#print axioms polyHybridTrajectoryPluginMeasurable_rate
#print axioms polyHybridCanonicalMeasurable_accuracy_and_expectedQueries_of_semantic
#print axioms polyHybridCanonicalMeasurable_accuracy_and_expectedQueries

end Ttc.ConcreteHybridCanonicalOwnerMeasurable

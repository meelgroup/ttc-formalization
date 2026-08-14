import Ttc.Exec.PolyHybridCanonicalCertificate
import Ttc.Exec.ConcreteHybridCanonicalOwnerMeasurable

/-!
# Fully instantiated measurable hybrid TTC sampler

This is the operational accuracy/query capstone at the canonical TTC data.
The hybrid sampler certificate, rejection probability, boundedness, lattice
enumeration, and outer Giry measurability are all constructed.
-/

namespace Ttc.ConcreteHybridCanonicalOwnerPoly

open MeasureTheory ProbabilityTheory Set Pointwise
open Ttc.KV97RoundedEndpointBridge
open Ttc.ConcreteHybridCanonicalOwnerMeasurable
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}
variable (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)

theorem isBounded_polyHybridCanonical
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (i : CubeIndex atoms phi) :
    Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
          (latticeScale (rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r) := by
  apply Metric.isBounded_closedBall.subset
  intro y hy
  have hcard : (algBlock atoms phi eps delta).r =
      (Nat.card (FacetIndex (D atoms phi)) : Real) :=
    ttcBlock_r atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hPr : (algBlock atoms phi eps delta).r = canonRfac (D atoms phi) := by
    rw [hcard, canonRfac]
  rw [hPr] at hy
  change y ∈ Metric.closedBall (canonicalHybridCenter atoms phi eps delta i)
    (canonicalHybridOuterRadius atoms phi eps delta i)
  unfold canonicalHybridCenter canonicalHybridOuterRadius
  rw [Metric.mem_closedBall, dist_comm]
  apply dist_le_ttcSampDiam atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i
  · exact (ball_subset_ttcSampBody atoms phi eps delta
      h_eps_pos h_eps_le hn hphi hvol i)
      (Metric.mem_ball_self
        (ttcSampInradius_pos atoms phi eps delta
          h_eps_pos h_eps_le hn hphi hvol))
  · exact hy

theorem hasLatticeEnum_polyHybridCanonical
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi) :
    HasLatticeEnum (M atoms phi eps delta) (preprocess atoms phi)
      (rho atoms phi eps delta) :=
  hasLatticeEnum_of_isBounded _ _ _
    (algAtoms_bdd atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol)

/-- Final measurable canonical-owner TTC result for the explicit hybrid
sampler.  No `KV97Sampler`, `1/8` acceptance, boundedness, lattice-enumeration,
or outer-kernel premise remains. -/
theorem polyHybridCanonicalFinal_accuracy_and_expectedQueries
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (V : ExpectedQueryVolumeAlgorithm n) {J : Nat} (hJ : 0 < J) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    letI := V.mΩ
    let P := Ttc.ConcreteHybridCanonicalOwnerMeasurable.polyHybridTrajectoryPluginMeasurable
      atoms phi eps delta V
      (hasLatticeEnum_polyHybridCanonical atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol)
      (canonicalHybridInnerRadius atoms phi eps delta)
      (canonicalHybridOuterRadius atoms phi eps delta)
      (canonicalHybridStep atoms phi eps delta)
      (canonicalHybridWarm atoms phi eps delta)
      (canonicalHybridStart atoms phi eps delta)
      (fun i ↦ Arlib.isProbabilityMeasure_uniformOn_ball volume _
        (ttcSampInradius_pos atoms phi eps delta
          h_eps_pos h_eps_le hn hphi hvol))
      (isBounded_polyHybridCanonical atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol)
      (fun _ ↦ by
        unfold canonicalHybridStep
        have hr := ttcSampInradius_pos atoms phi eps delta
          h_eps_pos h_eps_le hn hphi hvol
        linarith)
      (one_eighth_le_roundedMeasure_polyHybridCanonical atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol)
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
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact Ttc.ConcreteHybridCanonicalOwnerMeasurable.polyHybridCanonicalMeasurable_accuracy_and_expectedQueries
      atoms phi eps delta h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol V
      (hasLatticeEnum_polyHybridCanonical atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol)
      (canonicalHybridInnerRadius atoms phi eps delta)
      (canonicalHybridOuterRadius atoms phi eps delta)
      (canonicalHybridStep atoms phi eps delta)
      (canonicalHybridWarm atoms phi eps delta)
      (canonicalHybridStart atoms phi eps delta)
      (fun i ↦ Arlib.isProbabilityMeasure_uniformOn_ball volume _
        (ttcSampInradius_pos atoms phi eps delta
          h_eps_pos h_eps_le hn hphi hvol))
      (isBounded_polyHybridCanonical atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol)
      (fun _ ↦ by
        unfold canonicalHybridStep
        have hr := ttcSampInradius_pos atoms phi eps delta
          h_eps_pos h_eps_le hn hphi hvol
        linarith)
      (one_eighth_le_roundedMeasure_polyHybridCanonical atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol)
      (kv97Sampler_polyHybridCanonical atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol) hJ

#print axioms isBounded_polyHybridCanonical
#print axioms hasLatticeEnum_polyHybridCanonical
#print axioms polyHybridCanonicalFinal_accuracy_and_expectedQueries

end Ttc.ConcreteHybridCanonicalOwnerPoly

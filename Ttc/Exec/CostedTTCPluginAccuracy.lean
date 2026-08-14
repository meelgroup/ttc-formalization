import Ttc.Exec.CostedTTCPlugin

/-!
# Accuracy capstone for an operational costed TTC plug-in

This transfers the existing semantic TTC accuracy theorem to the genuine marked-Poisson
execution from `CostedTTCPlugin`.  The proof uses equality of the entire joint
volume-coin/trajectory law, not an independence approximation.
-/

namespace Ttc.CostedTTCPlugin

open MeasureTheory ProbabilityTheory Set
open Ttc.SequentialCostedPathLumping
open scoped ENNReal Classical

variable {A : Type*} {n : Nat}
variable {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}

def idealPolyAccuracyEvent (V : VolumeAlgorithm n) :
    Set (V.Ω × CountPath (algIndex atoms phi eps delta)) :=
  {z | ttcPolyRun atoms phi eps delta V z.1 z.2 ∈
    relErr eps (volSol (atomSet atoms) phi)}

theorem measurableSet_idealPolyAccuracyEvent (V : VolumeAlgorithm n) :
    letI := V.mΩ
    MeasurableSet (idealPolyAccuracyEvent (atoms := atoms) (phi := phi)
      (eps := eps) (delta := delta) V) := by
  letI := V.mΩ
  have hout : Measurable
      (fun z : V.Ω × CountPath (algIndex atoms phi eps delta) =>
        ttcPolyRun atoms phi eps delta V z.1 z.2) :=
    measurable_fst.comp (measurable_polyPair atoms phi eps delta V 0 0)
  exact measurableSet_Icc.preimage hout

def costedPolyAccuracyEvent
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    Set (V.Ω × CostedCountPath (algIndex atoms phi eps delta)) :=
  {z | ttcPolyRun atoms phi eps delta V.toVolumeAlgorithm z.1
      (pathMap Prod.snd z.2) ∈ relErr eps (volSol (atomSet atoms) phi)}

/-- The operational marked-Poisson execution has TTC's advertised accuracy whenever the
existing KV97 sampler certificate holds.  `V` is a genuine expected-query volume oracle;
the cost conclusion is supplied separately by `lintegral_actualPolyQueryCost_le`. -/
theorem costedPolyJoint_accuracy
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (V : ExpectedQueryVolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)} → Real)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)} →
      Measure (Ttc.Space n))
    (sampler : KV97Sampler A n (atomSet (algAtoms atoms phi eps delta))
      (toDNFd (preprocess atoms phi)) (algPrec atoms phi eps delta)
      (algBlock atoms phi eps delta).epsPrime
      (polySampD atoms phi eps delta rin Rout Mw sigma))
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega a, P.lam omega * P.q omega a =
        polyRates atoms phi eps delta V.toVolumeAlgorithm omega rin Rout Mw sigma a) :
    letI := V.mΩ
    1 - delta ≤
      ((costedPolyJoint (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
        (costedPolyAccuracyEvent (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P)).toReal := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  let stateMap :
    V.Ω × CostedCountPath (algIndex atoms phi eps delta) →
      V.Ω × CountPath (algIndex atoms phi eps delta) :=
    Prod.map id (pathMap Prod.snd)
  let idealEvent := idealPolyAccuracyEvent (atoms := atoms) (phi := phi)
    (eps := eps) (delta := delta) V.toVolumeAlgorithm
  have hstate : Measurable stateMap :=
    measurable_id.prodMap (measurable_pathMap measurable_snd)
  have hideal : MeasurableSet idealEvent :=
    measurableSet_idealPolyAccuracyEvent V.toVolumeAlgorithm
  have hevent : costedPolyAccuracyEvent (atoms := atoms) (phi := phi)
      (eps := eps) (delta := delta) V P = stateMap ⁻¹' idealEvent := rfl
  have hjoint := map_forgetCost_costedPolyJoint V rin Rout Mw sigma P hrate
  have heq :
      (costedPolyJoint (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
          (costedPolyAccuracyEvent (atoms := atoms) (phi := phi)
            (eps := eps) (delta := delta) V P) =
        (V.μ.compProd
          (polyKernel atoms phi eps delta V.toVolumeAlgorithm rin Rout Mw sigma))
          idealEvent := by
    rw [hevent, ← Measure.map_apply hstate hideal, hjoint]
  rw [heq, Measure.compProd_apply hideal]
  have hacc := lintegral_ttcPolyRun_ge atoms phi eps delta
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol V.toVolumeAlgorithm
    rin Rout Mw sigma sampler
    (big_polyRates atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
      V.toVolumeAlgorithm rin Rout Mw sigma sampler)
  simpa only [idealEvent, idealPolyAccuracyEvent, polyKernel_apply,
    Set.preimage_setOf_eq] using hacc

/-- Combined semantic/cost capstone.  The query bound is exact up to the displayed
outer average of the per-call sampler mean; no deterministic Poisson cap is asserted. -/
theorem costedPolyJoint_accuracy_and_expectedQueries
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (V : ExpectedQueryVolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)} → Real)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)} →
      Measure (Ttc.Space n))
    (sampler : KV97Sampler A n (atomSet (algAtoms atoms phi eps delta))
      (toDNFd (preprocess atoms phi)) (algPrec atoms phi eps delta)
      (algBlock atoms phi eps delta).epsPrime
      (polySampD atoms phi eps delta rin Rout Mw sigma))
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega a, P.lam omega * P.q omega a =
        polyRates atoms phi eps delta V.toVolumeAlgorithm omega rin Rout Mw sigma a)
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    (1 - delta ≤
      ((costedPolyJoint (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
        (costedPolyAccuracyEvent (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P)).toReal) ∧
    ((∫⁻ z, actualPolyQueryCost (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P J z
        ∂costedPolyJoint (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P) ≤
      ttcPolyVolumeQueryBound atoms phi eps delta V +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ) := by
  letI := V.mΩ
  exact ⟨costedPolyJoint_accuracy h_eps_pos h_eps_le h_delta_pos h_delta_le hn
      hphi hvol V rin Rout Mw sigma sampler P hrate,
    lintegral_actualPolyQueryCost_le V P hJ⟩

#print axioms costedPolyJoint_accuracy
#print axioms costedPolyJoint_accuracy_and_expectedQueries

end Ttc.CostedTTCPlugin

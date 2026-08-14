import Ttc.Exec.CanonicalOwnerPoissonAssembler
import Ttc.Exec.CostedTTCPluginAccuracy

/-!
# TTC plug-in for canonical-owner per-cube Poisson streams

Unlike the single-mixture marked sampler, this construction runs one independent
Poisson stream per cube.  Samples not canonically owned by that cube are sent to
an explicit null mark and dropped.  Thus there is no assignment-cell rejection
and the exact expected sampling cost is `sum_i lambda_i * B_i`.
-/

namespace Ttc.CostedCanonicalOwnerTTCPlugin

open MeasureTheory ProbabilityTheory Set
open Ttc.CanonicalOwnerPoissonAssembler
open Ttc.CostedInitialThinningTrajectory
open Ttc.SequentialCostedPathLumping
open Ttc.CostedTTCPlugin
open scoped ENNReal BigOperators Classical NNReal

variable {I : Type*} [Fintype I] {L n : Nat}
variable {Omega : Type*} [MeasurableSpace Omega]

abbrev CostedCountPath (L : Nat) := Nat → ENNReal × (Fin L → Nat)
abbrev CountPath (L : Nat) := Nat → (Fin L → Nat)

/-- The only outer measurability seam: a Markov kernel whose fibers are the
already-constructed independent canonical-owner trajectories. -/
structure CanonicalOwnerTrajectoryPlugin
    (I : Type*) [Fintype I] (L : Nat) (Omega : Type*)
    [MeasurableSpace Omega] where
  family : Omega → CubeMarkedFamily I L
  owner : Fin L → I
  trajectoryKernel : Kernel Omega (CostedCountPath L)
  trajectoryKernel_markov : IsMarkovKernel trajectoryKernel
  trajectoryKernel_apply : ∀ omega,
    trajectoryKernel omega = (family omega).assembledTrajectoryLaw owner

namespace CanonicalOwnerTrajectoryPlugin

variable (P : CanonicalOwnerTrajectoryPlugin I L Omega)

noncomputable def expectedSampleQueries (omega : Omega) : ENNReal :=
  ∑ i, (((P.family omega).lam i).toNNReal : ENNReal) *
    ((P.family omega).sampler i).expectedQueries

theorem map_forgetCost_trajectoryKernel (omega : Omega) :
    Measure.map (pathMap Prod.snd) (P.trajectoryKernel omega) =
      Ttc.trajLaw (fun s =>
        (P.family omega).lam (P.owner s) *
          (P.family omega).q (P.owner s) s.castSucc) := by
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  rw [P.trajectoryKernel_apply]
  exact (P.family omega).map_forgetCost_assembledTrajectoryLaw P.owner

theorem lintegral_prefixQueryCost_trajectoryKernel (omega : Omega)
    {J : Nat} (hJ : 0 < J) :
    (∫⁻ path, finitePrefixQueryCost J path ∂P.trajectoryKernel omega) =
      P.expectedSampleQueries omega := by
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  rw [P.trajectoryKernel_apply]
  exact (P.family omega).lintegral_finitePrefixQueryCost_assembledTrajectoryLaw
    P.owner hJ

end CanonicalOwnerTrajectoryPlugin

variable {A : Type*} {atoms : A → LinAtom n} {phi : BForm A}
variable {eps delta : Real}

/-- Joint volume-coin and canonical-owner costed trajectory law. -/
noncomputable def canonicalCostedPolyJoint
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    @Measure (V.Ω × CostedCountPath (algIndex atoms phi eps delta))
      (@Prod.instMeasurableSpace _ _ V.mΩ _) := by
  letI := V.mΩ
  exact V.μ.compProd P.trajectoryKernel

instance (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    letI := V.mΩ
    IsProbabilityMeasure (canonicalCostedPolyJoint
      (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  unfold canonicalCostedPolyJoint
  infer_instance

/-- Exact joint-law identification with TTC's ordinary polynomial kernel. -/
theorem map_forgetCost_canonicalCostedPolyJoint
    (V : ExpectedQueryVolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)} → Real)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)} →
      Measure (Ttc.Space n))
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega s,
        (P.family omega).lam (P.owner s) *
            (P.family omega).q (P.owner s) s.castSucc =
          max (polyRates atoms phi eps delta V.toVolumeAlgorithm omega
            rin Rout Mw sigma s) 0) :
    letI := V.mΩ
    Measure.map (Prod.map id (pathMap Prod.snd))
        (canonicalCostedPolyJoint (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P) =
      V.μ.compProd
        (polyKernel atoms phi eps delta V.toVolumeAlgorithm rin Rout Mw sigma) := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  have hpoint : ∀ omega,
      Measure.map (pathMap Prod.snd) (P.trajectoryKernel omega) =
        polyKernel atoms phi eps delta V.toVolumeAlgorithm rin Rout Mw sigma omega := by
    intro omega
    rw [P.map_forgetCost_trajectoryKernel, polyKernel_apply]
    calc
      Ttc.trajLaw (fun s =>
          (P.family omega).lam (P.owner s) *
            (P.family omega).q (P.owner s) s.castSucc) =
          Ttc.trajLaw (fun s => max
            (polyRates atoms phi eps delta V.toVolumeAlgorithm omega
              rin Rout Mw sigma s) 0) := by
            congr 1
            funext s
            exact hrate omega s
      _ = Ttc.trajLaw
          (polyRates atoms phi eps delta V.toVolumeAlgorithm omega
            rin Rout Mw sigma) :=
        (Ttc.trajLaw_max_zero _).symm
  simpa only [canonicalCostedPolyJoint, Measure.map_id] using
    (map_compProd_prodMap_of_pointwise V.μ P.trajectoryKernel
      (polyKernel atoms phi eps delta V.toVolumeAlgorithm rin Rout Mw sigma)
      measurable_id (measurable_pathMap measurable_snd) hpoint)

/-- Volume queries plus all independently generated cube-stream queries. -/
noncomputable def canonicalActualPolyQueryCost
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (J : Nat) :
    V.Ω × CostedCountPath (algIndex atoms phi eps delta) → ENNReal :=
  fun z => ttcPolyVolumeQueryCost atoms phi eps delta V z.1 +
    finitePrefixQueryCost J z.2

theorem lintegral_canonicalActualPolyQueryCost
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    (∫⁻ z, canonicalActualPolyQueryCost (atoms := atoms) (phi := phi)
        (eps := eps) (delta := delta) V P J z
      ∂canonicalCostedPolyJoint (atoms := atoms) (phi := phi)
        (eps := eps) (delta := delta) V P) =
      (∫⁻ omega, ttcPolyVolumeQueryCost atoms phi eps delta V omega ∂V.μ) +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  unfold canonicalActualPolyQueryCost
  rw [lintegral_add_left]
  congr 1
  · change (∫⁻ z, (ttcPolyVolumeQueryCost atoms phi eps delta V ∘ Prod.fst) z
        ∂V.μ.compProd P.trajectoryKernel) = _
    rw [Measure.lintegral_compProd
      ((measurable_ttcPolyVolumeQueryCost atoms phi eps delta V).comp measurable_fst)]
    simp
  · change (∫⁻ z, (finitePrefixQueryCost J ∘ Prod.snd) z
        ∂V.μ.compProd P.trajectoryKernel) = _
    rw [Measure.lintegral_compProd
      ((measurable_finitePrefixQueryCost J).comp measurable_snd)]
    apply lintegral_congr
    intro omega
    exact P.lintegral_prefixQueryCost_trajectoryKernel omega hJ
  · exact (measurable_ttcPolyVolumeQueryCost atoms phi eps delta V).comp measurable_fst

theorem lintegral_canonicalActualPolyQueryCost_le
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    (∫⁻ z, canonicalActualPolyQueryCost (atoms := atoms) (phi := phi)
        (eps := eps) (delta := delta) V P J z
      ∂canonicalCostedPolyJoint (atoms := atoms) (phi := phi)
        (eps := eps) (delta := delta) V P) ≤
      ttcPolyVolumeQueryBound atoms phi eps delta V +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ := by
  letI := V.mΩ
  rw [lintegral_canonicalActualPolyQueryCost V P hJ]
  exact add_le_add (lintegral_ttcPolyVolumeQueryCost_le atoms phi eps delta V) le_rfl

/-- The TTC accuracy event on the cost-erased canonical-owner execution. -/
def canonicalCostedPolyAccuracyEvent
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    Set (V.Ω × CostedCountPath (algIndex atoms phi eps delta)) :=
  {z | ttcPolyRun atoms phi eps delta V.toVolumeAlgorithm z.1
      (pathMap Prod.snd z.2) ∈ relErr eps (volSol (atomSet atoms) phi)}

/-- Semantic TTC accuracy transferred through the exact canonical-owner joint
law.  The only sampling premise is the repository's existing `KV97Sampler`
certificate; all operational query accounting is separate and exact. -/
theorem canonicalCostedPolyJoint_accuracy
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
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega s,
        (P.family omega).lam (P.owner s) *
            (P.family omega).q (P.owner s) s.castSucc =
          max (polyRates atoms phi eps delta V.toVolumeAlgorithm omega
            rin Rout Mw sigma s) 0) :
    letI := V.mΩ
    1 - delta ≤
      ((canonicalCostedPolyJoint (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P)
        (canonicalCostedPolyAccuracyEvent (atoms := atoms) (phi := phi)
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
  have hevent : canonicalCostedPolyAccuracyEvent (atoms := atoms) (phi := phi)
      (eps := eps) (delta := delta) V P = stateMap ⁻¹' idealEvent := rfl
  have hjoint := map_forgetCost_canonicalCostedPolyJoint V rin Rout Mw sigma P hrate
  have heq :
      (canonicalCostedPolyJoint (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P)
          (canonicalCostedPolyAccuracyEvent (atoms := atoms) (phi := phi)
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

/-- Final generic plug-in capstone: TTC accuracy and the honest expected sum of
volume-query cost plus all independent cube-stream costs. -/
theorem canonicalCostedPolyJoint_accuracy_and_expectedQueries
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
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega s,
        (P.family omega).lam (P.owner s) *
            (P.family omega).q (P.owner s) s.castSucc =
          max (polyRates atoms phi eps delta V.toVolumeAlgorithm omega
            rin Rout Mw sigma s) 0)
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    (1 - delta ≤
      ((canonicalCostedPolyJoint (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P)
        (canonicalCostedPolyAccuracyEvent (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P)).toReal) ∧
    ((∫⁻ z, canonicalActualPolyQueryCost (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P J z
        ∂canonicalCostedPolyJoint (atoms := atoms) (phi := phi)
          (eps := eps) (delta := delta) V P) ≤
      ttcPolyVolumeQueryBound atoms phi eps delta V +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ) := by
  letI := V.mΩ
  exact ⟨canonicalCostedPolyJoint_accuracy h_eps_pos h_eps_le h_delta_pos
      h_delta_le hn hphi hvol V rin Rout Mw sigma sampler P hrate,
    lintegral_canonicalActualPolyQueryCost_le V P hJ⟩

#print axioms map_forgetCost_canonicalCostedPolyJoint
#print axioms lintegral_canonicalActualPolyQueryCost
#print axioms lintegral_canonicalActualPolyQueryCost_le
#print axioms canonicalCostedPolyJoint_accuracy
#print axioms canonicalCostedPolyJoint_accuracy_and_expectedQueries

end Ttc.CostedCanonicalOwnerTTCPlugin

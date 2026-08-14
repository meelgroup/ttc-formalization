import Ttc.Exec.CostedMarkedPoissonTrajectory
import Ttc.Exec.ExpectedQueryPolyVolume

/-!
# A costed marked-Poisson plug-in for TTC

The pointwise `ExpectedQueryFineSampler` interface does not assert measurable dependence
on an outer volume coin.  This file therefore asks for the missing object explicitly: a
Markov kernel whose fiber is the costed marked-Poisson trajectory constructed from the
pointwise sampler.  Under that narrow interface, forgetting recorded costs gives the
ordinary TTC trajectory jointly with the volume coin, and the expected actual query
cost is the sum of the volume-oracle cost and the exact Poisson marking mean.
-/

namespace Ttc.CostedTTCPlugin

open MeasureTheory ProbabilityTheory
open Ttc.CostedMarkedPoisson
open Ttc.CostedMarkedPoissonIdentified
open Ttc.CostedMarkedPoissonTrajectory
open Ttc.CostedInitialThinningTrajectory
open Ttc.SequentialCostedPathLumping
open scoped ENNReal BigOperators Classical NNReal

variable {n L : Nat} {Omega : Type*} [MeasurableSpace Omega]

abbrev CostedCountPath (L : Nat) := Nat → ENNReal × (Fin L → Nat)
abbrev CountPath (L : Nat) := Nat → (Fin L → Nat)

/-- A measurably coin-indexed family of genuine fine samplers, normalized into one
categorical marked-Poisson trajectory.  All analytic sampling work is confined to the
pointwise `fineSampler`; `trajectoryKernel` is precisely the measurability seam needed
to compose these pointwise laws with an outer random coin. -/
structure MarkedTrajectoryPlugin (n L : Nat) (Omega : Type*)
    [MeasurableSpace Omega] where
  target : Omega → Measure (Ttc.Space n)
  fineSampler : ∀ omega, Ttc.KV97RoundedEndpointBridge.ExpectedQueryFineSampler (target omega)
  encode : Omega → Ttc.Space n → Fin L
  encode_measurable : ∀ omega, Measurable (encode omega)
  q : Omega → Fin L → Real
  lam : Omega → Real
  lam_nonneg : ∀ omega, 0 ≤ lam omega
  q_nonneg : ∀ omega a, 0 ≤ q omega a
  q_sum : ∀ omega, ∑ a, q omega a = 1
  encoded : ∀ omega,
    Measure.map (encode omega) (target omega) = categoricalLaw (q omega)
  trajectoryKernel : Kernel Omega (CostedCountPath L)
  trajectoryKernel_markov : IsMarkovKernel trajectoryKernel
  trajectoryKernel_apply : ∀ omega,
    trajectoryKernel omega = trajectoryLaw
      (finiteSamplerOfFine (fineSampler omega) (encode omega) (q omega)
        (encode_measurable omega) (encoded omega))
      (lam omega)

namespace MarkedTrajectoryPlugin

variable (P : MarkedTrajectoryPlugin n L Omega)

noncomputable def finiteSampler (omega : Omega) :
    ExpectedQueryFiniteSampler (P.q omega) :=
  finiteSamplerOfFine (P.fineSampler omega) (P.encode omega) (P.q omega)
    (P.encode_measurable omega) (P.encoded omega)

noncomputable def expectedSampleQueries (omega : Omega) : ENNReal :=
  ((P.lam omega).toNNReal : ENNReal) * (P.fineSampler omega).expectedQueries

theorem map_forgetCost_trajectoryKernel (omega : Omega) :
    Measure.map (pathMap Prod.snd) (P.trajectoryKernel omega) =
      Ttc.trajLaw (fun a => P.lam omega * P.q omega a) := by
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  rw [P.trajectoryKernel_apply]
  exact map_forgetCost_trajectoryLaw_eq_trajLaw
    (P.lam_nonneg omega) (P.q_nonneg omega) (P.q_sum omega) (P.finiteSampler omega)

theorem lintegral_prefixQueryCost_trajectoryKernel (omega : Omega)
    {J : Nat} (hJ : 0 < J) :
    (∫⁻ path, finitePrefixQueryCost J path ∂P.trajectoryKernel omega) =
      P.expectedSampleQueries omega := by
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  rw [P.trajectoryKernel_apply]
  simpa only [finiteSampler, finiteSamplerOfFine, expectedSampleQueries] using
    (lintegral_finitePrefixQueryCost_trajectoryLaw
      (finiteSamplerOfFine (P.fineSampler omega) (P.encode omega) (P.q omega)
        (P.encode_measurable omega) (P.encoded omega)) (P.lam omega) hJ)

end MarkedTrajectoryPlugin

variable {A : Type*} {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}

/-- The joint operational law of the volume coin and its costed thinning trajectory. -/
noncomputable def costedPolyJoint
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    @Measure (V.Ω × CostedCountPath (algIndex atoms phi eps delta))
      (@Prod.instMeasurableSpace _ _ V.mΩ _) := by
  letI := V.mΩ
  exact V.μ.compProd P.trajectoryKernel

instance (V : ExpectedQueryVolumeAlgorithm n)
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    letI := V.mΩ
    IsProbabilityMeasure (costedPolyJoint (atoms := atoms) (phi := phi)
      (eps := eps) (delta := delta) V P) := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  unfold costedPolyJoint
  infer_instance

/-- If the plug-in rates are the rates read by TTC, then erasing recorded costs from
the whole joint law gives exactly TTC's ordinary coin/trajectory joint law. -/
theorem map_forgetCost_costedPolyJoint
    (V : ExpectedQueryVolumeAlgorithm n)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)} → Real)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)} →
      Measure (Ttc.Space n))
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega a, P.lam omega * P.q omega a =
        polyRates atoms phi eps delta V.toVolumeAlgorithm omega rin Rout Mw sigma a) :
    letI := V.mΩ
    Measure.map (Prod.map id (pathMap Prod.snd))
        (costedPolyJoint (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) =
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
    congr 1
    funext a
    exact hrate omega a
  simpa only [costedPolyJoint, Measure.map_id] using
    (map_compProd_prodMap_of_pointwise V.μ P.trajectoryKernel
      (polyKernel atoms phi eps delta V.toVolumeAlgorithm rin Rout Mw sigma)
      measurable_id (measurable_pathMap measurable_snd) hpoint)

/-- Actual recorded membership-query cost: all volume calls made by TTC plus the
single level-zero marked-Poisson execution.  Thinning after level zero is query-free. -/
noncomputable def actualPolyQueryCost
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (J : Nat) :
    V.Ω × CostedCountPath (algIndex atoms phi eps delta) → ENNReal :=
  fun z => ttcPolyVolumeQueryCost atoms phi eps delta V z.1 +
    finitePrefixQueryCost J z.2

theorem measurable_actualPolyQueryCost
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (J : Nat) :
    letI := V.mΩ
    Measurable (actualPolyQueryCost (atoms := atoms) (phi := phi)
      (eps := eps) (delta := delta) V P J) := by
  letI := V.mΩ
  exact (measurable_ttcPolyVolumeQueryCost atoms phi eps delta V).comp measurable_fst |>.add
    ((measurable_finitePrefixQueryCost J).comp measurable_snd)

/-- Exact expected actual query decomposition. -/
theorem lintegral_actualPolyQueryCost
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ)
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    (∫⁻ z, actualPolyQueryCost (atoms := atoms) (phi := phi)
        (eps := eps) (delta := delta) V P J z
      ∂costedPolyJoint (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) =
      (∫⁻ omega, ttcPolyVolumeQueryCost atoms phi eps delta V omega ∂V.μ) +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  unfold actualPolyQueryCost
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

/-- Honest expected query bound.  The only residual arithmetic term is the outer average
of `lambda *` the one-call sampler mean. -/
theorem lintegral_actualPolyQueryCost_le
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @MarkedTrajectoryPlugin n (algIndex atoms phi eps delta) V.Ω V.mΩ)
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    (∫⁻ z, actualPolyQueryCost (atoms := atoms) (phi := phi)
        (eps := eps) (delta := delta) V P J z
      ∂costedPolyJoint (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) ≤
      ttcPolyVolumeQueryBound atoms phi eps delta V +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ := by
  letI := V.mΩ
  rw [lintegral_actualPolyQueryCost V P hJ]
  exact add_le_add (lintegral_ttcPolyVolumeQueryCost_le atoms phi eps delta V) le_rfl

#print axioms MarkedTrajectoryPlugin.map_forgetCost_trajectoryKernel
#print axioms map_forgetCost_costedPolyJoint
#print axioms lintegral_actualPolyQueryCost
#print axioms lintegral_actualPolyQueryCost_le

end Ttc.CostedTTCPlugin

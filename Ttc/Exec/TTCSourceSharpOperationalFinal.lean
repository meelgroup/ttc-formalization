import Ttc.Exec.CanonicalOwnerRateCutoff
import Ttc.Exec.CVSourcePolynomialCutoffCapstone
import Ttc.Exec.VolPriceCVAlg

set_option maxHeartbeats 8000000

/-!
# Source-sharp volume costs in the operational TTC law

This file instantiates the operational canonical-owner TTC theorem with the
expected-query volume oracle obtained from the source-shaped Cousins--Vempala
one-run certificate.  Accuracy and both query counters consequently refer to
one and the same joint law.

The theorem is conditional only on the genuinely operational common-law
certificate required by `SourcePublicOneRunCertificates`; it does not identify
the result with the legacy price-parametric `Ttc.ttc` measure.
-/

namespace Ttc.TTCSourceSharpOperationalFinal

open MeasureTheory ProbabilityTheory Set
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CanonicalOwnerRateCutoff
open Ttc.KV97RoundedEndpointBridge
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}

/-- A deterministic cap for the raw per-cube Poisson intensity.  On the volume
oracle's ordinary good event this cap is never active. -/
noncomputable def polyGoodRateCap
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) :
    CubeIndex atoms phi → NNReal :=
  fun i ↦ ((1 + (algBlock atoms phi eps delta).epsPrime) *
    (volume
      (region (atomSet (algAtoms atoms phi eps delta)) i.val)).toReal).toNNReal

/-- The concrete cap event is closed: every coin on which all TTC volume calls
meet their advertised relative error lies below the corresponding deterministic
Poisson-rate cap. -/
theorem polyGood_subset_ratesWithinCap
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (V : VolumeAlgorithm n) :
    polyGood atoms phi eps delta V ⊆
      ratesWithinCap (polyGoodRateCap atoms phi eps delta)
        (fun omega i ↦
          (polyVol atoms phi eps delta V omega i.val).toNNReal) := by
  intro omega homega i
  apply Real.toNNReal_mono
  exact (volOfAlg_mem_relErr V
    (atomSet (algAtoms atoms phi eps delta))
    (toDNFd (preprocess atoms phi)) (algCen atoms phi eps delta)
    (algGamma atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
    (algBlock atoms phi eps delta).deltaPrime homega i.val i.property).2

/-- The measurable hybrid canonical-owner plug-in with its raw per-cube
intensities clipped at `polyGoodRateCap`. -/
noncomputable def polyHybridCappedTrajectoryPluginMeasurable
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
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
    Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
      (CubeIndex atoms phi) (algIndex atoms phi eps delta) V.Ω := by
  letI := V.mΩ
  let target := polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
  let fine := polyHybridFineSampler atoms phi eps delta rin Rout step Mw sigma hsigma
    hbounded hstep heighth
  let base : Ttc.CanonicalOwnerPoissonAssembler.CubeMarkedFamily
      (CubeIndex atoms phi) (algIndex atoms phi eps delta) :=
    Ttc.ConcreteHybridCanonicalOwnerSampler.canonicalMarkedFamily
      (Ttc.ConcreteHybridCanonicalOwnerPoly.pt atoms phi eps delta) target
      (isProbabilityMeasure_polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
        hsigma hbounded hstep heighth)
      fine (fun _ ↦ 0) (fun _ ↦ le_rfl)
  let lam : V.Ω → CubeIndex atoms phi → NNReal := fun omega i ↦
    (polyVol atoms phi eps delta V.toVolumeAlgorithm omega i.val).toNNReal
  have hlam : Measurable lam := measurable_pi_lambda _ fun i ↦
    measurable_real_toNNReal.comp
      (measurable_polyVol atoms phi eps delta V.toVolumeAlgorithm i.val)
  exact clippedPlugin base.q base.q_nonneg base.q_sum base.sampler
    (polyOwner atoms phi eps delta hle) lam hlam
    (polyGoodRateCap atoms phi eps delta)

/-- The clipped hybrid sampler has a deterministic, coin-independent expected
query envelope.  Every factor on the right is concrete: a geometric intensity
cap and the expected cost of the constructed finite hybrid endpoint sampler. -/
theorem lintegral_polyHybridCapped_expectedSampleQueries_le
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
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
    let P := polyHybridCappedTrajectoryPluginMeasurable atoms phi eps delta V hle
      rin Rout step Mw sigma hsigma hbounded hstep heighth
    (∫⁻ omega, P.expectedSampleQueries omega ∂V.μ) ≤
      ∑ i : CubeIndex atoms phi,
        (polyGoodRateCap atoms phi eps delta i : ENNReal) *
          ((Ttc.ConcreteHybridCanonicalOwnerSampler.canonicalMarkedFamily
            (Ttc.ConcreteHybridCanonicalOwnerPoly.pt atoms phi eps delta)
            (polyHybridTarget atoms phi eps delta rin Rout step Mw sigma)
            (isProbabilityMeasure_polyHybridTarget atoms phi eps delta
              rin Rout step Mw sigma hsigma hbounded hstep heighth)
            (polyHybridFineSampler atoms phi eps delta rin Rout step Mw sigma hsigma
              hbounded hstep heighth)
            (fun _ ↦ 0) (fun _ ↦ le_rfl)).sampler i).expectedQueries := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  unfold polyHybridCappedTrajectoryPluginMeasurable
  dsimp only
  exact lintegral_clippedPlugin_expectedSampleQueries_le
      (Ttc.ConcreteHybridCanonicalOwnerSampler.canonicalMarkedFamily
        (Ttc.ConcreteHybridCanonicalOwnerPoly.pt atoms phi eps delta)
        (polyHybridTarget atoms phi eps delta rin Rout step Mw sigma)
        (isProbabilityMeasure_polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
          hsigma hbounded hstep heighth)
        (polyHybridFineSampler atoms phi eps delta rin Rout step Mw sigma hsigma
          hbounded hstep heighth)
        (fun _ ↦ 0) (fun _ ↦ le_rfl)).q
      (Ttc.ConcreteHybridCanonicalOwnerSampler.canonicalMarkedFamily
        (Ttc.ConcreteHybridCanonicalOwnerPoly.pt atoms phi eps delta)
        (polyHybridTarget atoms phi eps delta rin Rout step Mw sigma)
        (isProbabilityMeasure_polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
          hsigma hbounded hstep heighth)
        (polyHybridFineSampler atoms phi eps delta rin Rout step Mw sigma hsigma
          hbounded hstep heighth)
        (fun _ ↦ 0) (fun _ ↦ le_rfl)).q_nonneg
      (Ttc.ConcreteHybridCanonicalOwnerSampler.canonicalMarkedFamily
        (Ttc.ConcreteHybridCanonicalOwnerPoly.pt atoms phi eps delta)
        (polyHybridTarget atoms phi eps delta rin Rout step Mw sigma)
        (isProbabilityMeasure_polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
          hsigma hbounded hstep heighth)
        (polyHybridFineSampler atoms phi eps delta rin Rout step Mw sigma hsigma
          hbounded hstep heighth)
        (fun _ ↦ 0) (fun _ ↦ le_rfl)).q_sum
      (Ttc.ConcreteHybridCanonicalOwnerSampler.canonicalMarkedFamily
        (Ttc.ConcreteHybridCanonicalOwnerPoly.pt atoms phi eps delta)
        (polyHybridTarget atoms phi eps delta rin Rout step Mw sigma)
        (isProbabilityMeasure_polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
          hsigma hbounded hstep heighth)
        (polyHybridFineSampler atoms phi eps delta rin Rout step Mw sigma hsigma
          hbounded hstep heighth)
        (fun _ ↦ 0) (fun _ ↦ le_rfl)).sampler
      (polyOwner atoms phi eps delta hle)
      (fun omega i ↦
        (polyVol atoms phi eps delta V.toVolumeAlgorithm omega i.val).toNNReal)
      (measurable_pi_lambda _ fun i ↦ measurable_real_toNNReal.comp
        (measurable_polyVol atoms phi eps delta V.toVolumeAlgorithm i.val))
      (polyGoodRateCap atoms phi eps delta) V.μ

theorem measurableSet_canonicalCostedPolyAccuracyEvent
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
      (CubeIndex atoms phi) _ (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    letI := V.mΩ
    MeasurableSet
      (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
        (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) := by
  letI := V.mΩ
  change MeasurableSet
    ((Prod.map id (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)) ⁻¹'
      Ttc.CostedTTCPlugin.idealPolyAccuracyEvent
        (atoms := atoms) (phi := phi) (eps := eps) (delta := delta)
        V.toVolumeAlgorithm)
  exact (Ttc.CostedTTCPlugin.measurableSet_idealPolyAccuracyEvent
    V.toVolumeAlgorithm).preimage
      (measurable_id.prodMap
        (Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd))

/-- Generic same-law accuracy transfer used by the concrete clipped hybrid
implementation.  The loss is exactly the outer mass `beta` outside `good`. -/
theorem canonicalCappedJoint_accuracy_of_raw
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta beta : Real)
    (V : ExpectedQueryVolumeAlgorithm n)
    (rawP capP : @Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
      (CubeIndex atoms phi) _ (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (good : Set V.Ω) (hgoodMeas : MeasurableSet[V.mΩ] good)
    (hk : letI := V.mΩ
      ∀ omega ∈ good,
        rawP.trajectoryKernel omega = capP.trajectoryKernel omega)
    (hraw : letI := V.mΩ
      1 - delta ≤
        ((Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
            (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V rawP)
          (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
            (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V rawP)).toReal)
    (hbad : letI := V.mΩ
      (V.μ goodᶜ).toReal ≤ beta) :
    letI := V.mΩ
    1 - (delta + beta) ≤
      ((Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V capP)
        (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V capP)).toReal := by
  letI := V.mΩ
  let rawMu := Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
    (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V rawP
  let capMu := Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
    (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V capP
  let accuracy := Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
    (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V capP
  let jointGood : Set
      (V.Ω × Ttc.CostedCanonicalOwnerTTCPlugin.CostedCountPath
        (algIndex atoms phi eps delta)) := Prod.fst ⁻¹' good
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel rawP.trajectoryKernel := rawP.trajectoryKernel_markov
  letI : IsMarkovKernel capP.trajectoryKernel := capP.trajectoryKernel_markov
  have haccMeas : MeasurableSet accuracy :=
    measurableSet_canonicalCostedPolyAccuracyEvent atoms phi eps delta V capP
  have hagree : rawMu (accuracy ∩ jointGood) = capMu (accuracy ∩ jointGood) := by
    exact compProd_inter_fst_preimage_eq_of_kernel_eq_on V.μ
      rawP.trajectoryKernel capP.trajectoryKernel accuracy good haccMeas hgoodMeas hk
  have hbadJoint : (rawMu jointGoodᶜ).toReal ≤ beta := by
    have hmap : Measure.map Prod.fst rawMu = V.μ := by
      exact Measure.fst_compProd V.μ rawP.trajectoryKernel
    have heq : rawMu jointGoodᶜ = V.μ goodᶜ := by
      rw [show jointGoodᶜ = Prod.fst ⁻¹' goodᶜ by
        simp only [jointGood, preimage_compl]]
      rw [← Measure.map_apply measurable_fst hgoodMeas.compl, hmap]
    rw [heq]
    exact hbad
  have hraw' : 1 - delta ≤ (rawMu accuracy).toReal := by
    exact hraw
  have htransfer := probability_accuracy_transfer_of_agree_on_good
    rawMu capMu accuracy jointGood hraw' hbadJoint hagree
  simpa only [capMu, accuracy] using htransfer

/-- The exact failure budget of the concrete cap event.  TTC runs its volume
block at internal confidence `4*delta/5`, and the union bound spends one
quarter of that amount, hence `delta/5`. -/
theorem measure_polyGood_compl_le_one_fifth
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (V : VolumeAlgorithm n)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    letI := V.mΩ
    (V.μ (polyGood atoms phi eps delta V)ᶜ).toReal ≤ delta / 5 := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  have hbdd : Bornology.IsBounded
      (sol (atomSet (algAtoms atoms phi eps delta)) (preprocess atoms phi)) :=
    algAtoms_bdd atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hisD : IsDNFOf (toDNFd (preprocess atoms phi)) (preprocess atoms phi) :=
    toDNFd_isDNFOf _
  have hg : 0 < algGamma atoms phi eps delta :=
    algGamma_pos_of_isPositive atoms phi eps delta hphi hvol
  have hball := ball_subset_algCen atoms phi eps delta
  have hfin : ∀ i : CubeIndex atoms phi,
      volume (region (atomSet (algAtoms atoms phi eps delta)) i.val) ≠ ⊤ :=
    volume_region_ne_top_of_isBounded hisD hbdd
  have hconv : ∀ i : CubeIndex atoms phi,
      Convex Real (region (atomSet (algAtoms atoms phi eps delta)) i.val) :=
    fun i ↦ convex_region (algAtoms atoms phi eps delta) _
  have hPm : (algBlock atoms phi eps delta).m = ttcNumCubes atoms phi :=
    ttcBlock_m atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hmlen : ((toDNFd (preprocess atoms phi)).length : Real) ≤
      (algBlock atoms phi eps delta).m := by
    rw [hPm, ttcNumCubes_eq]
  have hd0 : (0 : Real) < 4 * delta / 5 := by linarith
  have hd1 : (4 : Real) * delta / 5 ≤ 1 := by linarith
  have hgood : 1 - delta / 5 ≤
      (V.μ (polyGood atoms phi eps delta V)).toReal := by
    have h := measure_volGood_ge_of_length V
      (atomSet (algAtoms atoms phi eps delta))
      (toDNFd (preprocess atoms phi)) (algBlock atoms phi eps delta)
      (ttcBlock_delta atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol)
      hd0 hd1 hg (algCen atoms phi eps delta) hball hconv hfin hmlen
    change 1 - delta / 5 ≤
      (V.μ (volGoodOf V (atomSet (algAtoms atoms phi eps delta))
        (toDNFd (preprocess atoms phi)) (algCen atoms phi eps delta)
        (algGamma atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
        (algBlock atoms phi eps delta).deltaPrime)).toReal
    rw [show 1 - delta / 5 = 1 - (4 * delta / 5) / 4 by ring]
    exact h
  have hmeas : MeasurableSet (polyGood atoms phi eps delta V) :=
    measurableSet_volGood V _ _ _ _ _
  change V.μ.real (polyGood atoms phi eps delta V)ᶜ ≤ delta / 5
  rw [measureReal_compl hmeas]
  simp only [measureReal_univ_eq_one]
  change 1 - delta / 5 ≤ V.μ.real (polyGood atoms phi eps delta V) at hgood
  linarith

/-- The explicit polynomial facet/membership-inspection envelope for one
canonical hybrid endpoint draw, including KV97 rejection at acceptance `1/8`. -/
noncomputable def canonicalHybridSamplerQueryBound
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi) : ENNReal :=
  let K := Arlib.KV97.inflated
    (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
    (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
      (latticeScale (rho atoms phi eps delta)) i)
    (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
    (algBlock atoms phi eps delta).r
  8 * (ENNReal.ofReal
      (Ttc.hybridTransitionBound n
        (canonicalHybridInnerRadius atoms phi eps delta i)
        (canonicalHybridOuterRadius atoms phi eps delta i)
        (canonicalHybridStep atoms phi eps delta i)
        (canonicalHybridWarm atoms phi eps delta i)
        ((algBlock atoms phi eps delta).epsPrime /
          (4 * (volume K).toReal))) *
      Ttc.ConcreteHybridExpectedQuerySampler.hybridStepInspectionBound n
        (Nat.card (FacetIndex (D atoms phi))) + 1)

/-- The expected query field of the concrete hybrid fine sampler is bounded by
the displayed polynomial inspection envelope. -/
theorem polyHybridFineSampler_expectedQueries_le_canonicalBound
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (i : CubeIndex atoms phi) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    (polyHybridFineSampler atoms phi eps delta
      (canonicalHybridInnerRadius atoms phi eps delta)
      (canonicalHybridOuterRadius atoms phi eps delta)
      (canonicalHybridStep atoms phi eps delta)
      (canonicalHybridWarm atoms phi eps delta)
      (canonicalHybridStart atoms phi eps delta)
      (fun j ↦ Arlib.isProbabilityMeasure_uniformOn_ball volume _
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
        h_eps_pos h_eps_le hn hphi hvol) i).expectedQueries ≤
      canonicalHybridSamplerQueryBound atoms phi eps delta i := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let hsigma : ∀ j : CubeIndex atoms phi,
      IsProbabilityMeasure (canonicalHybridStart atoms phi eps delta j) := fun j ↦
    Arlib.isProbabilityMeasure_uniformOn_ball volume _
    (ttcSampInradius_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol)
  let hbounded := isBounded_polyHybridCanonical atoms phi eps delta
    h_eps_pos h_eps_le hn hphi hvol
  let hstep : ∀ _i : CubeIndex atoms phi,
      0 < canonicalHybridStep atoms phi eps delta _i := fun _ ↦ by
    unfold canonicalHybridStep
    have hr := ttcSampInradius_pos atoms phi eps delta
      h_eps_pos h_eps_le hn hphi hvol
    linarith
  let heighth := one_eighth_le_roundedMeasure_polyHybridCanonical
    atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  let S := polyHybridFineSampler atoms phi eps delta
    (canonicalHybridInnerRadius atoms phi eps delta)
    (canonicalHybridOuterRadius atoms phi eps delta)
    (canonicalHybridStep atoms phi eps delta)
    (canonicalHybridWarm atoms phi eps delta)
    (canonicalHybridStart atoms phi eps delta)
    hsigma hbounded hstep heighth i
  change S.expectedQueries ≤ _
  rw [← S.expectedQueries_eq]
  simpa only [S, polyHybridFineSampler,
    Ttc.ConcreteHybridAcceptanceCost.expectedQueryKV97HybridConcreteOfEighth,
    Ttc.ConcreteHybridExpectedQuerySampler.expectedQueryKV97HybridConcrete,
    Ttc.CostedLazyHitAndRunAdapter.expectedQueryKV97SamplerOfRealization,
    Ttc.KV97RoundedEndpointBridge.expectedQueryKV97Sampler,
    Ttc.KV97RoundedEndpointBridge.expectedQueryFineSampler,
    canonicalHybridSamplerQueryBound, Nat.card_eq_fintype_card,
    Fintype.card_fin] using
    (Ttc.ConcreteHybridAcceptanceCost.expected_inspections_kv97HybridConcrete_le_polynomial hn
      (algBlock atoms phi eps delta).epsPrime (algBlock atoms phi eps delta).r
      (canonAm (algAtoms atoms phi eps delta) (D atoms phi))
      (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
        (latticeScale (rho atoms phi eps delta)))
      (canonicalHybridInnerRadius atoms phi eps delta)
      (canonicalHybridOuterRadius atoms phi eps delta)
      (canonicalHybridStep atoms phi eps delta)
      (canonicalHybridWarm atoms phi eps delta)
      (canonicalHybridStart atoms phi eps delta) hsigma hbounded hstep
      (M atoms phi eps delta) (rho atoms phi eps delta) i
      (by
        unfold canonicalHybridInnerRadius
        have hr := ttcSampInradius_pos atoms phi eps delta
          h_eps_pos h_eps_le hn hphi hvol
        linarith)
      (by
        unfold canonicalHybridOuterRadius
        exact ttcSampDiam_pos atoms phi eps delta
          h_eps_pos h_eps_le hn hphi hvol i)
      (by
        unfold canonicalHybridWarm
        exact one_le_ttcSampWarm atoms phi eps delta
          h_eps_pos h_eps_le hn hphi hvol i)
          (by
            have hPr : (algBlock atoms phi eps delta).r =
                (Nat.card (FacetIndex (D atoms phi)) : Real) :=
              ttcBlock_r atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
            have hrf : (algBlock atoms phi eps delta).r =
                canonRfac (D atoms phi) := by
              rw [hPr, canonRfac]
            rw [hrf]
            change 0 < ttcSampTol atoms phi eps delta i
            exact ttcSampTol_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i)
          (by
            have hPr : (algBlock atoms phi eps delta).r =
                (Nat.card (FacetIndex (D atoms phi)) : Real) :=
              ttcBlock_r atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
            have hrf : (algBlock atoms phi eps delta).r =
                canonRfac (D atoms phi) := by
              rw [hPr, canonRfac]
            rw [hrf]
            change ttcSampTol atoms phi eps delta i ≤ 1
            exact ttcSampTol_le_one atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i)
      (heighth i))

/-- Total deterministic sampling-query envelope after clipping all canonical
cube streams. -/
noncomputable def canonicalCappedSampleQueryEnvelope
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : ENNReal :=
  ∑ i : CubeIndex atoms phi,
    (polyGoodRateCap atoms phi eps delta i : ENNReal) *
      canonicalHybridSamplerQueryBound atoms phi eps delta i

/-- The concrete clipped canonical hybrid plug-in has expected sampling cost
bounded by `canonicalCappedSampleQueryEnvelope`. -/
theorem lintegral_canonicalCapped_expectedSampleQueries_le
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (V : ExpectedQueryVolumeAlgorithm n)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let P := polyHybridCappedTrajectoryPluginMeasurable atoms phi eps delta V
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
    letI := V.mΩ
    (∫⁻ omega, P.expectedSampleQueries omega ∂V.μ) ≤
      canonicalCappedSampleQueryEnvelope atoms phi eps delta := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let hle := hasLatticeEnum_polyHybridCanonical atoms phi eps delta
    h_eps_pos h_eps_le hn hphi hvol
  let hsigma : ∀ i : CubeIndex atoms phi,
      IsProbabilityMeasure (canonicalHybridStart atoms phi eps delta i) := fun i ↦
    Arlib.isProbabilityMeasure_uniformOn_ball volume _
    (ttcSampInradius_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol)
  let hbounded := isBounded_polyHybridCanonical atoms phi eps delta
    h_eps_pos h_eps_le hn hphi hvol
  let hstep : ∀ _i : CubeIndex atoms phi,
      0 < canonicalHybridStep atoms phi eps delta _i := fun _ ↦ by
    unfold canonicalHybridStep
    have hr := ttcSampInradius_pos atoms phi eps delta
      h_eps_pos h_eps_le hn hphi hvol
    linarith
  let heighth := one_eighth_le_roundedMeasure_polyHybridCanonical atoms phi eps delta
    h_eps_pos h_eps_le hn hphi hvol
  letI := V.mΩ
  have hbase := lintegral_polyHybridCapped_expectedSampleQueries_le
    atoms phi eps delta V hle
    (canonicalHybridInnerRadius atoms phi eps delta)
    (canonicalHybridOuterRadius atoms phi eps delta)
    (canonicalHybridStep atoms phi eps delta)
    (canonicalHybridWarm atoms phi eps delta)
    (canonicalHybridStart atoms phi eps delta)
    hsigma hbounded hstep heighth
  refine hbase.trans ?_
  unfold canonicalCappedSampleQueryEnvelope
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_left'
  change (polyHybridFineSampler atoms phi eps delta
    (canonicalHybridInnerRadius atoms phi eps delta)
    (canonicalHybridOuterRadius atoms phi eps delta)
    (canonicalHybridStep atoms phi eps delta)
    (canonicalHybridWarm atoms phi eps delta)
    (canonicalHybridStart atoms phi eps delta)
    hsigma hbounded hstep heighth i).expectedQueries ≤ _
  exact polyHybridFineSampler_expectedQueries_le_canonicalBound atoms phi eps delta
    h_eps_pos h_eps_le hn hphi hvol i

/-- The explicit sum of the source-shaped CV envelopes over exactly the volume
calls made by TTC.  Its dependence on each call's accuracy is quadratic through
`sourceAmplifiedQueryEnvelope`. -/
noncomputable def ttcSourceVolumeQueryEnvelope
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real) : ENNReal :=
  ∑ j : Fin (toDNFd (preprocess atoms phi)).length,
    ENNReal.ofReal
      (sourceAmplifiedQueryEnvelope runtimeConstant n
        (radialR
          (roundBody
            (algCen atoms phi eps delta
              ⟨(toDNFd (preprocess atoms phi)).get j,
                List.get_mem (toDNFd (preprocess atoms phi)) j⟩)
            (algGamma atoms phi eps delta)
            (region (atomSet (algAtoms atoms phi eps delta))
              ((toDNFd (preprocess atoms phi)).get j))))
        (algBlock atoms phi eps delta).epsPrime
        (algBlock atoms phi eps delta).deltaPrime)

/-- The public source-shaped oracle's TTC volume budget is bounded by the
explicit sum of its per-call polynomial envelopes. -/
theorem ttcPolyVolumeQueryBound_source_le
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    ttcPolyVolumeQueryBound atoms phi eps delta V ≤
      ttcSourceVolumeQueryEnvelope atoms phi eps delta runtimeConstant radialR := by
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  have hp : 0 < (algBlock atoms phi eps delta).deltaPrime :=
    algBlock_deltaPrime_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
      h_delta_pos
  have hp1 : (algBlock atoms phi eps delta).deltaPrime < 1 :=
    lt_of_le_of_lt
      (algBlock_deltaPrime_le_half atoms phi eps delta h_eps_pos h_eps_le hn
        hphi hvol h_delta_le)
      (by norm_num)
  unfold ttcPolyVolumeQueryBound volOfExpectedAlgQueryBound
    ttcSourceVolumeQueryEnvelope
  apply Finset.sum_le_sum
  intro j hj
  change sourcePublicExpectedBound runtimeConstant n radialR _
      (algBlock atoms phi eps delta).epsPrime
      (algBlock atoms phi eps delta).deltaPrime ≤ _
  exact sourcePublicExpectedBound_le_polynomial hconstant radialR _ hp hp1

/-- Operational TTC with the concrete hybrid sampler and the source-shaped
expected-query volume oracle.  The first conjunct is accuracy of the same law
whose actual volume and sampling queries are integrated in the second. -/
theorem sourceSharpPolyHybridTTC_accuracy_and_expectedQueries
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) {J : Nat} (hJ : 0 < J) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    letI := V.mΩ
    let P :=
      Ttc.ConcreteHybridCanonicalOwnerMeasurable.polyHybridTrajectoryPluginMeasurable
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
      ttcSourceVolumeQueryEnvelope atoms phi eps delta runtimeConstant radialR +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  letI := V.mΩ
  let P :=
    Ttc.ConcreteHybridCanonicalOwnerMeasurable.polyHybridTrajectoryPluginMeasurable
      atoms phi eps delta V
      (hasLatticeEnum_polyHybridCanonical atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol)
      (canonicalHybridInnerRadius atoms phi eps delta)
      (canonicalHybridOuterRadius atoms phi eps delta)
      (canonicalHybridStep atoms phi eps delta)
      (canonicalHybridWarm atoms phi eps delta)
      (canonicalHybridStart atoms phi eps delta)
      (fun i : CubeIndex atoms phi ↦ Arlib.isProbabilityMeasure_uniformOn_ball volume _
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
  have hmain := polyHybridCanonicalFinal_accuracy_and_expectedQueries
    atoms phi eps delta h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol V hJ
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  have hv := ttcPolyVolumeQueryBound_source_le atoms phi eps delta
    runtimeConstant radialR Omega oneLaw cost value hcert hconstant h_eps_pos
    h_eps_le h_delta_pos h_delta_le hn hphi hvol
  have hadd := add_le_add_right hv
    (∫⁻ omega, P.expectedSampleQueries omega ∂V.μ)
  simpa only [add_comm] using hadd

/-- Fully instantiated clipped canonical hybrid plug-in. -/
noncomputable def canonicalCappedPolyHybridPlugin
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (V : ExpectedQueryVolumeAlgorithm n)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    letI := V.mΩ
    Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
      (CubeIndex atoms phi) (algIndex atoms phi eps delta) V.Ω := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI := V.mΩ
  exact polyHybridCappedTrajectoryPluginMeasurable atoms phi eps delta V
    (hasLatticeEnum_polyHybridCanonical atoms phi eps delta
      h_eps_pos h_eps_le hn hphi hvol)
    (canonicalHybridInnerRadius atoms phi eps delta)
    (canonicalHybridOuterRadius atoms phi eps delta)
    (canonicalHybridStep atoms phi eps delta)
    (canonicalHybridWarm atoms phi eps delta)
    (canonicalHybridStart atoms phi eps delta)
    (fun i : CubeIndex atoms phi ↦ Arlib.isProbabilityMeasure_uniformOn_ball volume _
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

/-- Same-law operational TTC theorem with both oracle sides bounded explicitly.
The volume summand has the source CV `eps^-2` shape; the sampling summand is the
deterministic polynomial hybrid-transition envelope after rate clipping. -/
theorem sourceSharpCappedPolyHybridTTC_accuracy_and_expectedQueries
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) {J : Nat} (hJ : 0 < J) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    letI := V.mΩ
    let P := canonicalCappedPolyHybridPlugin atoms phi eps delta V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - (delta + delta / 5) ≤
      ((Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
        (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)).toReal) ∧
    ((∫⁻ z, Ttc.CostedCanonicalOwnerTTCPlugin.canonicalActualPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P J z
        ∂Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) ≤
      ttcSourceVolumeQueryEnvelope atoms phi eps delta runtimeConstant radialR +
        canonicalCappedSampleQueryEnvelope atoms phi eps delta) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  letI := V.mΩ
  let rawP := Ttc.ConcreteHybridCanonicalOwnerMeasurable.polyHybridTrajectoryPluginMeasurable
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
  let P := canonicalCappedPolyHybridPlugin atoms phi eps delta V
    h_eps_pos h_eps_le hn hphi hvol
  have hrawMain := polyHybridCanonicalFinal_accuracy_and_expectedQueries
    atoms phi eps delta h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol V hJ
  let good := polyGood atoms phi eps delta V.toVolumeAlgorithm
  have hgoodMeas : MeasurableSet good :=
    measurableSet_volGood V.toVolumeAlgorithm _ _ _ _ _
  have hk : ∀ omega ∈ good,
      rawP.trajectoryKernel omega = P.trajectoryKernel omega := by
    intro omega homega
    have hcap := polyGood_subset_ratesWithinCap atoms phi eps delta
      V.toVolumeAlgorithm homega
    symm
    simpa only [P, canonicalCappedPolyHybridPlugin,
      polyHybridCappedTrajectoryPluginMeasurable, rawP,
      Ttc.ConcreteHybridCanonicalOwnerMeasurable.polyHybridTrajectoryPluginMeasurable,
      Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin.ofMeasurableRates] using
      (clippedPlugin_trajectoryKernel_eq_of_mem
        (q := (rawP.family omega).q)
        (hq0 := (rawP.family omega).q_nonneg)
        (hqsum := (rawP.family omega).q_sum)
        (S := (rawP.family omega).sampler) (owner := rawP.owner)
        (lam := fun omega i ↦
          (polyVol atoms phi eps delta V.toVolumeAlgorithm omega i.val).toNNReal)
        (hlam := measurable_pi_lambda _ fun i ↦ measurable_real_toNNReal.comp
          (measurable_polyVol atoms phi eps delta V.toVolumeAlgorithm i.val))
        (cap := polyGoodRateCap atoms phi eps delta) hcap)
  have hacc := canonicalCappedJoint_accuracy_of_raw atoms phi eps delta
    (delta / 5) V rawP P good hgoodMeas hk hrawMain.1
    (measure_polyGood_compl_le_one_fifth atoms phi eps delta V.toVolumeAlgorithm
      h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol)
  refine ⟨?_, ?_⟩
  · simpa only [P, canonicalCappedPolyHybridPlugin] using hacc
  have hcost := Ttc.CostedCanonicalOwnerTTCPlugin.lintegral_canonicalActualPolyQueryCost_le
    V P hJ
  refine hcost.trans ?_
  have hsum := add_le_add
    (ttcPolyVolumeQueryBound_source_le atoms phi eps delta runtimeConstant radialR
      Omega oneLaw cost value hcert hconstant h_eps_pos h_eps_le h_delta_pos
      h_delta_le hn hphi hvol)
    (lintegral_canonicalCapped_expectedSampleQueries_le atoms phi eps delta V
      h_eps_pos h_eps_le hn hphi hvol)
  simpa only [P, canonicalCappedPolyHybridPlugin] using hsum

/-- Final re-budgeted headline.  The operational run uses confidence
`deltaRun = 4*delta/5`; its raw TTC proof spends `deltaRun`, clipping spends
`deltaRun/5`, and their sum is at most the user's `delta`.  Thus the displayed
same-law accuracy remains exactly `1-delta`, while the second conjunct records
the actual expected volume-plus-sampling queries of that law. -/
theorem sourceSharpCappedPolyHybridTTC_final
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) {J : Nat} (hJ : 0 < J) :
    let deltaRun := 4 * delta / 5
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    letI := V.mΩ
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤
      ((Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P)
        (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P)).toReal) ∧
    ((∫⁻ z, Ttc.CostedCanonicalOwnerTTCPlugin.canonicalActualPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P J z
        ∂Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P) ≤
      ttcSourceVolumeQueryEnvelope atoms phi eps deltaRun runtimeConstant radialR +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  let deltaRun := 4 * delta / 5
  have hd0 : 0 < deltaRun := by dsimp [deltaRun]; linarith
  have hd1 : deltaRun ≤ 1 := by dsimp [deltaRun]; linarith
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  letI := V.mΩ
  have hmain := sourceSharpCappedPolyHybridTTC_accuracy_and_expectedQueries
    atoms phi eps deltaRun runtimeConstant radialR Omega oneLaw cost value hcert
    hconstant h_eps_pos h_eps_le hd0 hd1 hn hphi hvol hJ
  constructor
  · exact le_trans (by dsimp [deltaRun]; linarith) hmain.1
  · exact hmain.2

#print axioms polyGood_subset_ratesWithinCap
#print axioms canonicalCappedJoint_accuracy_of_raw
#print axioms measure_polyGood_compl_le_one_fifth
#print axioms polyHybridFineSampler_expectedQueries_le_canonicalBound
#print axioms lintegral_canonicalCapped_expectedSampleQueries_le
#print axioms ttcPolyVolumeQueryBound_source_le
#print axioms sourceSharpPolyHybridTTC_accuracy_and_expectedQueries
#print axioms sourceSharpCappedPolyHybridTTC_accuracy_and_expectedQueries
#print axioms sourceSharpCappedPolyHybridTTC_final

end Ttc.TTCSourceSharpOperationalFinal

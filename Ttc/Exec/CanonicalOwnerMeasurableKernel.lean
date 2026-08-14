import Ttc.Exec.CostedCanonicalOwnerTTCPlugin
import Ttc.Monadic.Kernel

/-!
# Measurable outer kernels for canonical-owner streams

For fixed genuine per-cube samplers, this file proves that the complete costed
canonical-owner trajectory depends measurably on its finite vector of Poisson
rates.  This removes the last Giry-measurability binder from the generic TTC
plug-in constructor.
-/

namespace Ttc.CanonicalOwnerMeasurableKernel

open MeasureTheory ProbabilityTheory
open Ttc.CostedAdaptiveIidCalls
open Ttc.CostedMarkedPoisson
open Ttc.CostedMarkedPoissonTrajectory
open Ttc.CanonicalOwnerPoissonAssembler
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.CostedInitialThinningTrajectory
open scoped ENNReal BigOperators Classical NNReal

variable {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
variable {L : Nat}

/-- A finite product of probability measures is measurably parameterized when
each coordinate measure is. -/
theorem measurable_pi_probability
    {E : Type*} [MeasurableSpace E]
    (mu : Omega → I → Measure E)
    (hprob : ∀ omega i, IsProbabilityMeasure (mu omega i))
    (hmu : ∀ i, Measurable fun omega => mu omega i) :
    Measurable fun omega => Measure.pi (mu omega) := by
  letI (omega : Omega) (i : I) : IsProbabilityMeasure (mu omega i) :=
    hprob omega i
  letI (omega : Omega) : IsProbabilityMeasure (Measure.pi (mu omega)) := inferInstance
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_pi.symm isPiSystem_pi ?_
  rintro _s ⟨s, hs, rfl⟩
  simp only [Measure.pi_pi]
  exact Finset.measurable_prod Finset.univ fun i _ =>
    (Measure.measurable_coe (hs i (Set.mem_univ i))).comp (hmu i)

/-- A fixed iid marked-call law, stopped at a Poisson count, is measurable in
the Poisson rate even though its cost coordinate is `ENNReal`. -/
theorem measurable_actualCostedMarkedLaw_poisson
    (xi : Measure (CostedMark (L + 1))) [IsProbabilityMeasure xi] :
    Measurable fun lam : Real =>
      actualCostedMarkedLaw (poissonMeasure lam.toNNReal) xi := by
  have hiid : IsProbabilityMeasure (iidCostedStreamLaw xi) := inferInstance
  have hprod : Measurable fun nu : Measure Nat =>
      nu.prod (iidCostedStreamLaw xi) := by
    rw [show (fun nu : Measure Nat => nu.prod (iidCostedStreamLaw xi)) =
        fun nu => nu.bind (fun N =>
          Measure.map (Prod.mk N) (iidCostedStreamLaw xi)) by
      funext nu
      rw [Measure.prod]]
    exact Measure.measurable_bind'
      (Measurable.map_prodMk_left (ν := iidCostedStreamLaw xi))
  unfold actualCostedMarkedLaw adaptiveCallLaw
  exact (Measure.measurable_map _ measurable_actualCostedMarkedMap).comp
    (hprod.comp (Ttc.measurable_poissonMeasure.comp measurable_real_toNNReal))

/-- The actual costed marked-Poisson law of one fixed sampler is measurable in
its real rate. -/
theorem measurable_levelZeroLaw_rate
    {q : Fin (L + 1) → Real} (S : ExpectedQueryFiniteSampler q) :
    Measurable fun lam : Real => levelZeroLaw S lam := by
  letI : IsProbabilityMeasure S.law := S.probability
  exact measurable_actualCostedMarkedLaw_poisson S.law

/-- For fixed marks/samplers, the independent family level-zero law is
measurable in the finite rate vector. -/
theorem measurable_jointLaw_rates
    (q : I → Fin (L + 1) → Real)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (S : ∀ i, ExpectedQueryFiniteSampler (q i)) :
    Measurable fun lam : I → NNReal =>
      (CubeMarkedFamily.mk q (fun i => (lam i : Real))
        (fun _ => NNReal.zero_le_coe) hq0 hqsum S).jointLaw := by
  apply measurable_pi_probability
  · intro lam i
    infer_instance
  · intro i
    exact (measurable_levelZeroLaw_rate (S i)).comp
      (by fun_prop)

/-- The assembled costed level-zero law is measurable in all cube rates. -/
theorem measurable_assembledLevelZeroLaw_rates
    (q : I → Fin (L + 1) → Real)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (S : ∀ i, ExpectedQueryFiniteSampler (q i))
    (owner : Fin L → I) :
    Measurable fun lam : I → NNReal =>
      CubeMarkedFamily.assembledLevelZeroLaw
        (CubeMarkedFamily.mk q (fun i => (lam i : Real))
          (fun _ => NNReal.zero_le_coe) hq0 hqsum S) owner := by
  let assemble := fun z : I → ENNReal × (Fin (L + 1) → Nat) =>
    (CubeMarkedFamily.totalQueryCost z,
      CubeMarkedFamily.retainedCounts owner z)
  change Measurable fun lam : I → NNReal => Measure.map assemble
    (CubeMarkedFamily.mk q (fun i => (lam i : Real))
      (fun _ => NNReal.zero_le_coe) hq0 hqsum S).jointLaw
  exact (Measure.measurable_map assemble
    ((CubeMarkedFamily.measurable_totalQueryCost (I := I) (L := L)).prodMk
      (CubeMarkedFamily.measurable_retainedCounts owner))).comp
    (measurable_jointLaw_rates q hq0 hqsum S)

set_option maxHeartbeats 2000000 in
/-- The fixed free-thinning trajectory is measurable in its costed level-zero
input law. -/
theorem measurable_costedTrajLaw_initial : Measurable
    (fun nu : Measure (ENNReal × (Fin L → Nat)) => costedTrajLaw nu) := by
  unfold costedTrajLaw
  unfold Arlib.Probability.inhomogeneousPathMeasure
  exact Ttc.measurable_trajMeasure
    (X := fun _ : Nat => ENNReal × (Fin L → Nat))
    (Arlib.Probability.inhomogeneousHistoryKernel
      (fun _ => carryCostKernel (Ttc.thinKernel L)))

/-- The complete costed thinning trajectory is measurable in the cube rates. -/
theorem measurable_assembledTrajectoryLaw_rates
    (q : I → Fin (L + 1) → Real)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (S : ∀ i, ExpectedQueryFiniteSampler (q i))
    (owner : Fin L → I) :
    Measurable fun lam : I → NNReal =>
      CubeMarkedFamily.assembledTrajectoryLaw
        (CubeMarkedFamily.mk q (fun i => (lam i : Real))
          (fun _ => NNReal.zero_le_coe) hq0 hqsum S) owner := by
  unfold CubeMarkedFamily.assembledTrajectoryLaw
  exact measurable_costedTrajLaw_initial.comp
    (measurable_assembledLevelZeroLaw_rates q hq0 hqsum S owner)

end Ttc.CanonicalOwnerMeasurableKernel

namespace Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin

open MeasureTheory ProbabilityTheory
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.CanonicalOwnerPoissonAssembler
open Ttc.CostedMarkedPoisson
open scoped ENNReal BigOperators Classical NNReal

variable {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
variable {L : Nat}

/-- Canonical-owner TTC plug-in with its outer trajectory kernel constructed
from a measurable vector of nonnegative Poisson rates. -/
noncomputable def ofMeasurableRates
    (q : I → Fin (L + 1) → Real)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (S : ∀ i, ExpectedQueryFiniteSampler (q i))
    (owner : Fin L → I)
    (lam : Omega → I → NNReal) (hlam : Measurable lam) :
    CanonicalOwnerTrajectoryPlugin I L Omega := by
  let family : Omega → CubeMarkedFamily I L := fun omega =>
    CubeMarkedFamily.mk q (fun i => (lam omega i : Real))
      (fun _ => NNReal.zero_le_coe) hq0 hqsum S
  let trajectoryKernel : Kernel Omega
      (Ttc.CostedCanonicalOwnerTTCPlugin.CostedCountPath L) :=
    { toFun := fun omega => (family omega).assembledTrajectoryLaw owner
      measurable' :=
        (Ttc.CanonicalOwnerMeasurableKernel.measurable_assembledTrajectoryLaw_rates
          q hq0 hqsum S owner).comp hlam }
  have hmarkov : IsMarkovKernel trajectoryKernel := by
    refine ⟨fun omega => ?_⟩
    change IsProbabilityMeasure ((family omega).assembledTrajectoryLaw owner)
    infer_instance
  exact
    { family := family
      owner := owner
      trajectoryKernel := trajectoryKernel
      trajectoryKernel_markov := hmarkov
      trajectoryKernel_apply := fun _ => rfl }

#print axioms Ttc.CanonicalOwnerMeasurableKernel.measurable_pi_probability
#print axioms Ttc.CanonicalOwnerMeasurableKernel.measurable_actualCostedMarkedLaw_poisson
#print axioms Ttc.CanonicalOwnerMeasurableKernel.measurable_assembledTrajectoryLaw_rates
#print axioms ofMeasurableRates

end Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin

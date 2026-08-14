import Arlib.Probability.NuIndepTensor
import Ttc.Exec.CVIndependentStreamMoments
import Ttc.Exec.CVSeedProjectedDependence

/-!
# Corrected-CV dependence on independent scalar streams

Each empirical coordinate is one complete scalar Markov path.  Scalar warm-start mixing
gives LV2 dependence between that path's prefix and its next state.  `NuIndep.pi_const`
then tensors these independent coordinate pairs with coefficient `k * nu`; arbitrary
measurable corrected-estimator statistics are obtained by postcomposition.
-/

namespace Ttc.CVIndependentStreamDependence

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler Ttc.CVCorrected
open scoped ENNReal Classical

variable {X Seed : Type*} [MeasurableSpace X] [MeasurableSpace Seed]

/-- Law of `k` independently executed complete scalar phase paths. -/
noncomputable def independentPathLaw (k : Nat) (P : Nat → Kernel X X)
    [∀ i, IsMarkovKernel (P i)] (mu0 : Measure X) :
    Measure (Fin k → Nat → X) :=
  Ttc.CVIndependentStreamMoments.independentStreamLaw
    (inhomogeneousPathMeasure P mu0)

instance independentPathLaw.isProbabilityMeasure
    (k : Nat) (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure X) [IsProbabilityMeasure mu0] :
    IsProbabilityMeasure (independentPathLaw k P mu0) := by
  unfold independentPathLaw
  infer_instance

/-- Operational package whose non-formal inputs are all scalar: a seed-projected scalar
phase kernel, scalar last-seed warmth, and scalar distributional mixing.  The block
factorizations merely identify the corrected estimator's previous-prefix and next-phase
statistics. -/
structure IndependentStreamOperational
    (k : Nat) (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (Q : Nat → Kernel Seed X) [∀ i, IsMarkovKernel (Q i)]
    (seed : X → Seed) (mu0 : Measure X) [IsProbabilityMeasure mu0]
    (V : Nat → (Fin k → Nat → X) → Real) (m : Nat) (eta : Real) where
  measurable_seed : Measurable seed
  factor : ∀ i, P i = Kernel.comap (Q i) seed measurable_seed
  pi : Nat → Measure Seed
  tau : Nat → Measure X
  tau_prob : ∀ i, IsProbabilityMeasure (tau i)
  warmConst : Nat → ENNReal
  mixError : Nat → ENNReal
  mixError_ne_top : ∀ i, mixError i ≠ ⊤
  u : (i : Nat) → (Fin k → Finset.Iic i → X) → Real
  v : Nat → (Fin k → X) → Real
  measurable_u : ∀ i, Measurable (u i)
  measurable_v : ∀ i, Measurable (v i)
  U_eq : ∀ i,
    accuracyU (independentPathLaw k P mu0) V (correctedAlpha m eta) i =
      fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l))
  V_eq : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1))
  last_seed_warm : ∀ i, IsWarm (warmConst i)
    (((inhomogeneousPathMeasure P mu0).map (Preorder.frestrictLe i)).map
      (fun h ↦ seed (h ⟨i, Finset.mem_Iic.2 le_rfl⟩))) (pi i)
  distributional_mixing : ∀ i (rho : Measure Seed),
    IsWarm (2 * warmConst i) rho (pi i) → IsProbabilityMeasure rho →
      TVLe (sampleFromKernel (Q i) rho) (tau i) (mixError i)
  dependence_budget : ∀ i,
    (k : Real) * (2 * (mixError i).toReal) ≤ correctedNu m eta

attribute [instance] IndependentStreamOperational.tau_prob

/-- The scalar seed-projected LV2 theorem, tensorized across the `k` independent complete
paths and postcomposed with the corrected estimator statistics. -/
theorem IndependentStreamOperational.correctedDependencePremises
    {k : Nat} {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {mu0 : Measure X} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → X) → Real} {m : Nat} {eta : Real}
    (hop : IndependentStreamOperational k P Q seed mu0 V m eta) :
    (∀ i, NuIndep (independentPathLaw k P mu0)
      (accuracyU (independentPathLaw k P mu0) V (correctedAlpha m eta) i)
      (V (i + 1)) (correctedNu m eta)) ∧
    (∀ i, NuIndep (independentPathLaw k P mu0)
      (fun omega ↦
        (accuracyU (independentPathLaw k P mu0) V
          (correctedAlpha m eta) i omega) ^ 2)
      (fun omega ↦ (V (i + 1) omega) ^ 2) (correctedNu m eta)) := by
  constructor <;> intro i
  · letI : IsProbabilityMeasure (hop.tau i) := hop.tau_prob i
    have hscalar : NuIndep (inhomogeneousPathMeasure P mu0)
        (Preorder.frestrictLe i) (fun omega ↦ omega (i + 1))
        (2 * (hop.mixError i).toReal) :=
      Ttc.CVSeedProjectedDependence.nuIndep_history_next_of_seedProjection
        P Q seed hop.measurable_seed hop.factor mu0 i (hop.last_seed_warm i)
        (hop.mixError_ne_top i) (hop.distributional_mixing i)
    have hblock := hscalar.pi_const_comp
      (Preorder.measurable_frestrictLe i) (measurable_pi_apply (i + 1))
      (hop.measurable_u i) (hop.measurable_v i)
    change NuIndep (independentPathLaw k P mu0)
      (fun omega ↦ hop.u i (fun l ↦ Preorder.frestrictLe i (omega l)))
      (fun omega ↦ hop.v i (fun l ↦ omega l (i + 1)))
      ((k : Real) * (2 * (hop.mixError i).toReal)) at hblock
    rw [hop.U_eq i, hop.V_eq i]
    exact hblock.mono (hop.dependence_budget i)
  · letI : IsProbabilityMeasure (hop.tau i) := hop.tau_prob i
    have hscalar : NuIndep (inhomogeneousPathMeasure P mu0)
        (Preorder.frestrictLe i) (fun omega ↦ omega (i + 1))
        (2 * (hop.mixError i).toReal) :=
      Ttc.CVSeedProjectedDependence.nuIndep_history_next_of_seedProjection
        P Q seed hop.measurable_seed hop.factor mu0 i (hop.last_seed_warm i)
        (hop.mixError_ne_top i) (hop.distributional_mixing i)
    have hblock := hscalar.pi_const_comp
      (Preorder.measurable_frestrictLe i) (measurable_pi_apply (i + 1))
      ((hop.measurable_u i).pow_const 2) ((hop.measurable_v i).pow_const 2)
    change NuIndep (independentPathLaw k P mu0)
      (fun omega ↦ (hop.u i (fun l ↦ Preorder.frestrictLe i (omega l))) ^ 2)
      (fun omega ↦ (hop.v i (fun l ↦ omega l (i + 1))) ^ 2)
      ((k : Real) * (2 * (hop.mixError i).toReal)) at hblock
    rw [hop.U_eq i, hop.V_eq i]
    exact hblock.mono (hop.dependence_budget i)

#print axioms IndependentStreamOperational.correctedDependencePremises

end Ttc.CVIndependentStreamDependence

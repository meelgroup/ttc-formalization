import Ttc.Volume.CVDirectSequentialAccuracy

/-! Dependence for augmented phase states whose kernel reads only a warm seed projection. -/

namespace Ttc.CVSeedProjectedDependence

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler Ttc.CVCorrected
open scoped ENNReal Classical

variable {X Seed Score : Type*}
  [MeasurableSpace X] [MeasurableSpace Seed] [MeasurableSpace Score]

/-- LV2 history/next dependence when the phase kernel factors through a seed projection.
No warmth of the full augmented state is required. -/
theorem nuIndep_history_next_of_seedProjection
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (Q : Nat → Kernel Seed X) [∀ i, IsMarkovKernel (Q i)]
    (seed : X → Seed) (hseed : Measurable seed)
    (hfactor : ∀ i, P i = Kernel.comap (Q i) seed hseed)
    (mu : Measure X) [IsProbabilityMeasure mu] (i : Nat)
    {pi : Measure Seed} {tau : Measure X} [IsProbabilityMeasure tau]
    {M eps : ENNReal}
    (hwarm : IsWarm M
      (((inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i)).map
        (fun h ↦ seed (h ⟨i, Finset.mem_Iic.2 le_rfl⟩))) pi)
    (heps : eps ≠ ⊤)
    (hmix : ∀ eta : Measure Seed, IsWarm (2 * M) eta pi →
      IsProbabilityMeasure eta → TVLe (sampleFromKernel (Q i) eta) tau eps) :
    NuIndep (inhomogeneousPathMeasure P mu) (Preorder.frestrictLe i)
      (fun omega ↦ omega (i + 1)) (2 * eps.toReal) := by
  let rho := (inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i)
  let lastState : (Finset.Iic i → X) → X :=
    fun h ↦ h ⟨i, Finset.mem_Iic.2 le_rfl⟩
  let lastSeed : (Finset.Iic i → X) → Seed := seed ∘ lastState
  have hlastState : Measurable lastState := measurable_pi_apply _
  have hlastSeed : Measurable lastSeed := hseed.comp hlastState
  letI : IsProbabilityMeasure rho := by
    dsimp [rho]
    exact Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe i).aemeasurable
  have hdep : NuIndep
      (rho ⊗ₘ Kernel.comap (Q i) lastSeed hlastSeed)
      (Prod.fst : ((Finset.Iic i → X) × X) → (Finset.Iic i → X))
      (Prod.snd : ((Finset.Iic i → X) × X) → X) (2 * eps.toReal) := by
    apply nuIndep_compProd_comap_of_distributionalWarm (Q i) hlastSeed
      (M := M) (eps := eps) (pi := pi) (tau := tau)
    · change IsWarm M (rho.map lastSeed) pi
      rw [show lastSeed = (fun h ↦ seed (h ⟨i, Finset.mem_Iic.2 le_rfl⟩)) from rfl]
      simpa only [rho] using hwarm
    · exact heps
    · exact hmix
  have hkernel : Kernel.comap (Q i) lastSeed hlastSeed =
      Kernel.comap (P i) lastState hlastState := by
    rw [hfactor i]
    symm
    exact Kernel.comap_comp_right (Q i) hlastState hseed
  have hjoint : rho ⊗ₘ Kernel.comap (Q i) lastSeed hlastSeed =
      (inhomogeneousPathMeasure P mu).map
        (fun omega ↦ (Preorder.frestrictLe i omega, omega (i + 1))) := by
    rw [hkernel]
    simpa only [rho, lastState, inhomogeneousHistoryKernel] using
      (map_history_next_inhomogeneousPathMeasure P mu i)
  intro S T hS hT
  have hrect := hdep S T hS hT
  rw [hjoint] at hrect
  have hpair : Measurable
      (fun omega : Nat → X ↦ (Preorder.frestrictLe i omega, omega (i + 1))) := by
    fun_prop
  have hST : MeasurableSet
      (Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T : Set ((Finset.Iic i → X) × X)) :=
    (hS.preimage measurable_fst).inter (hT.preimage measurable_snd)
  have hS' : MeasurableSet (Prod.fst ⁻¹' S : Set ((Finset.Iic i → X) × X)) :=
    hS.preimage measurable_fst
  have hT' : MeasurableSet (Prod.snd ⁻¹' T : Set ((Finset.Iic i → X) × X)) :=
    hT.preimage measurable_snd
  rw [Measure.real, Measure.map_apply hpair hST, Measure.real,
    Measure.map_apply hpair hS', Measure.real, Measure.map_apply hpair hT'] at hrect
  change |(inhomogeneousPathMeasure P mu).real
      (Preorder.frestrictLe i ⁻¹' S ∩ (fun omega ↦ omega (i + 1)) ⁻¹' T) -
        (inhomogeneousPathMeasure P mu).real (Preorder.frestrictLe i ⁻¹' S) *
          (inhomogeneousPathMeasure P mu).real
            ((fun omega ↦ omega (i + 1)) ⁻¹' T)| ≤ 2 * eps.toReal at hrect
  exact hrect

theorem nuIndep_historyStatistics_of_seedProjection
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (Q : Nat → Kernel Seed X) [∀ i, IsMarkovKernel (Q i)]
    (seed : X → Seed) (hseed : Measurable seed)
    (hfactor : ∀ i, P i = Kernel.comap (Q i) seed hseed)
    (mu : Measure X) [IsProbabilityMeasure mu] (i : Nat)
    {pi : Measure Seed} {tau : Measure X} [IsProbabilityMeasure tau]
    {M eps : ENNReal}
    (hwarm : IsWarm M
      (((inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i)).map
        (fun h ↦ seed (h ⟨i, Finset.mem_Iic.2 le_rfl⟩))) pi)
    (heps : eps ≠ ⊤)
    (hmix : ∀ eta : Measure Seed, IsWarm (2 * M) eta pi →
      IsProbabilityMeasure eta → TVLe (sampleFromKernel (Q i) eta) tau eps)
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (f : (Finset.Iic i → X) → C) (g : X → D)
    (hf : Measurable f) (hg : Measurable g) :
    NuIndep (inhomogeneousPathMeasure P mu)
      (fun omega ↦ f (Preorder.frestrictLe i omega))
      (fun omega ↦ g (omega (i + 1))) (2 * eps.toReal) :=
  (nuIndep_history_next_of_seedProjection P Q seed hseed hfactor mu i
    hwarm heps hmix).comp hf hg

/-- Corrected-accuracy operational package for an augmented `(score,seed)` state. -/
structure SeedProjectedOperational
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (Q : Nat → Kernel Seed X) [∀ i, IsMarkovKernel (Q i)]
    (seed : X → Seed) (score : X → Score)
    (mu0 : Measure X) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → X) → Real) (m : Nat) (eta : Real) where
  measurable_seed : Measurable seed
  measurable_score : Measurable score
  factor : ∀ i, P i = Kernel.comap (Q i) seed measurable_seed
  pi : Nat → Measure Seed
  tau : Nat → Measure X
  tau_prob : ∀ i, IsProbabilityMeasure (tau i)
  warmConst : Nat → ENNReal
  mixError : Nat → ENNReal
  mixError_ne_top : ∀ i, mixError i ≠ ⊤
  u : (i : Nat) → (Finset.Iic i → X) → Real
  v : Nat → Score → Real
  measurable_u : ∀ i, Measurable (u i)
  measurable_v : ∀ i, Measurable (v i)
  U_eq : ∀ i,
    accuracyU (inhomogeneousPathMeasure P mu0) V (correctedAlpha m eta) i =
      fun omega ↦ u i (Preorder.frestrictLe i omega)
  V_eq : ∀ i, V (i + 1) = fun omega ↦ v i (score (omega (i + 1)))
  last_seed_warm : ∀ i, IsWarm (warmConst i)
    (((inhomogeneousPathMeasure P mu0).map (Preorder.frestrictLe i)).map
      (fun h ↦ seed (h ⟨i, Finset.mem_Iic.2 le_rfl⟩))) (pi i)
  distributional_mixing : ∀ i (rho : Measure Seed),
    IsWarm (2 * warmConst i) rho (pi i) → IsProbabilityMeasure rho →
      TVLe (sampleFromKernel (Q i) rho) (tau i) (mixError i)
  dependence_budget : ∀ i, 2 * (mixError i).toReal ≤ correctedNu m eta

attribute [instance] SeedProjectedOperational.tau_prob

theorem SeedProjectedOperational.correctedDependencePremises
    {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {score : X → Score}
    {mu0 : Measure X} [IsProbabilityMeasure mu0]
    {V : Nat → (Nat → X) → Real} {m : Nat} {eta : Real}
    (hop : SeedProjectedOperational P Q seed score mu0 V m eta) :
    (∀ i, NuIndep (inhomogeneousPathMeasure P mu0)
      (accuracyU (inhomogeneousPathMeasure P mu0) V (correctedAlpha m eta) i)
      (V (i + 1)) (correctedNu m eta)) ∧
    (∀ i, NuIndep (inhomogeneousPathMeasure P mu0)
      (fun omega ↦ (accuracyU (inhomogeneousPathMeasure P mu0) V
        (correctedAlpha m eta) i omega) ^ 2)
      (fun omega ↦ (V (i + 1) omega) ^ 2) (correctedNu m eta)) := by
  constructor <;> intro i
  · have hdep := nuIndep_historyStatistics_of_seedProjection P Q seed
      hop.measurable_seed hop.factor mu0 i (hop.last_seed_warm i)
      (hop.mixError_ne_top i) (hop.distributional_mixing i)
      (hop.u i) (hop.v i ∘ score) (hop.measurable_u i)
      ((hop.measurable_v i).comp hop.measurable_score)
    change NuIndep (inhomogeneousPathMeasure P mu0)
      (fun omega ↦ hop.u i (Preorder.frestrictLe i omega))
      (fun omega ↦ hop.v i (score (omega (i + 1))))
      (2 * (hop.mixError i).toReal) at hdep
    rw [← hop.U_eq i, ← hop.V_eq i] at hdep
    exact hdep.mono (hop.dependence_budget i)
  · have hdep := nuIndep_historyStatistics_of_seedProjection P Q seed
      hop.measurable_seed hop.factor mu0 i (hop.last_seed_warm i)
      (hop.mixError_ne_top i) (hop.distributional_mixing i)
      (hop.u i) (hop.v i ∘ score) (hop.measurable_u i)
      ((hop.measurable_v i).comp hop.measurable_score)
    change NuIndep (inhomogeneousPathMeasure P mu0)
      (fun omega ↦ hop.u i (Preorder.frestrictLe i omega))
      (fun omega ↦ hop.v i (score (omega (i + 1))))
      (2 * (hop.mixError i).toReal) at hdep
    rw [← hop.U_eq i, ← hop.V_eq i] at hdep
    exact (hdep.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).mono
      (hop.dependence_budget i)

/-- Corrected one-run accuracy with warmth required only for the seed projection of an
augmented state; the statistic may read the score projection. -/
theorem corrected_lem_accuracy_concrete_of_seedProjected
    {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {score : X → Score}
    {mu0 : Measure X} [IsProbabilityMeasure mu0]
    (V Wbar W : Nat → (Nat → X) → Real) {m k : Nat} {eta : Real}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hk : CorrectedSampleBudget m k eta)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega ∂(inhomogeneousPathMeasure P mu0))
    (hVcap : ∀ j omega, V j omega ≤ 2 * correctedAlpha m eta *
      ∫ z, V j z ∂(inhomogeneousPathMeasure P mu0))
    (hV2 : ∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (inhomogeneousPathMeasure P mu0))
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤ 2 * correctedAlpha m eta ^ 2 *
      ∫ z, (V j z) ^ 2 ∂(inhomogeneousPathMeasure P mu0))
    (hWm : ∀ j, Measurable (Wbar j)) (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWint : ∀ j, Integrable (Wbar j) (inhomogeneousPathMeasure P mu0))
    (hWEpos : ∀ j, 0 < ∫ omega, Wbar j omega ∂(inhomogeneousPathMeasure P mu0))
    (hVdef : ∀ j omega, V j omega = min (Wbar j omega)
      (correctedAlpha m eta *
        ∫ z, Wbar j z ∂(inhomogeneousPathMeasure P mu0)))
    (hratio : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂(inhomogeneousPathMeasure P mu0)) ≤
        (1 + 8 / (k : Real)) *
          (∫ omega, V j omega ∂(inhomogeneousPathMeasure P mu0)) ^ 2)
    {Eexact : Set (Nat → X)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (inhomogeneousPathMeasure P mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact, phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : SeedProjectedOperational P Q seed score mu0 V m eta) :
    (inhomogeneousPathMeasure P mu0).real
      {omega | phaseProduct W m omega ∉
        Ttc.relErr eta (prefixMean (inhomogeneousPathMeasure P mu0) V m)} ≤ 1 / 5 := by
  have hdeps := hop.correctedDependencePremises
  exact corrected_lem_accuracy_concrete V Wbar W heta heta1 hk hVm hV0 hEpos hVcap
    hV2 hV2cap hdeps.1 hdeps.2 hWm hW0 hWint hWEpos hVdef hratio
    hEexact hExactFail hExact

#print axioms nuIndep_history_next_of_seedProjection
#print axioms nuIndep_historyStatistics_of_seedProjection
#print axioms SeedProjectedOperational.correctedDependencePremises
#print axioms corrected_lem_accuracy_concrete_of_seedProjected

end Ttc.CVSeedProjectedDependence

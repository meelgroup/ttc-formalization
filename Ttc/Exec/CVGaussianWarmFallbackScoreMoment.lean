import Ttc.Exec.CVGaussianWarmFallbackCappedOperational
import Arlib.Convexity.GaussianCooling.PhaseFromTV

/-!
# Scalar score moments for operational warm-fallback paths

Total variation does not preserve an unbounded second moment.  For the bounded body
score `phaseScore`, however, the repository's TV transport theorem gives the exact sharp
additive slack condition.  This file first extracts the next score marginal TV bound
from `IndependentStreamOperational`, then obtains `MemLp` and a raw factor `9` whenever
the explicit TV slack fits between the exact cool-law factor and `9`.
-/

namespace Ttc.CVGaussianWarmFallbackScoreMoment

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVIndependentStreamDependence
open scoped ENNReal Classical

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

/-- The actual next-score marginal of an operational scalar path is within the declared
mixing error of the score marginal of its phase reference. -/
theorem tvLe_operational_score_eval_succ
    {k m : Nat} {Q : Nat → Kernel Seed (Score × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (Score × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → Score × Seed) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eta) (i : Nat) :
    TVLe
      (Measure.map (fun omega : Nat → Score × Seed ↦ (omega (i + 1)).1)
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0))
      (Measure.map Prod.fst (hop.tau i)) (hop.mixError i) := by
  let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let rho : Measure Seed := Measure.map Prod.snd
    (Measure.map (fun omega : Nat → Score × Seed ↦ omega i) pathLaw)
  letI : IsProbabilityMeasure rho := by
    letI : IsProbabilityMeasure pathLaw := by
      dsimp only [pathLaw]
      infer_instance
    letI : IsProbabilityMeasure
        (Measure.map (fun omega : Nat → Score × Seed ↦ omega i) pathLaw) :=
      Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hrho : rho =
      ((pathLaw.map (Preorder.frestrictLe i)).map
        (fun h ↦ (h ⟨i, Finset.mem_Iic.2 le_rfl⟩).2)) := by
    dsimp only [rho]
    calc
      Measure.map Prod.snd
          (Measure.map (fun omega : Nat → Score × Seed ↦ omega i) pathLaw) =
          Measure.map (fun omega : Nat → Score × Seed ↦ (omega i).2) pathLaw := by
            rw [Measure.map_map measurable_snd (measurable_pi_apply i)]
            rfl
      _ = Measure.map
          (fun h : Finset.Iic i → Score × Seed ↦
            (h ⟨i, Finset.mem_Iic.2 le_rfl⟩).2)
          (Measure.map (Preorder.frestrictLe i) pathLaw) := by
            rw [Measure.map_map
              (by fun_prop : Measurable (fun h : Finset.Iic i → Score × Seed ↦
                (h ⟨i, Finset.mem_Iic.2 le_rfl⟩).2))
              (Preorder.measurable_frestrictLe i)]
            rfl
  have hwarm : IsWarm (2 * hop.warmConst i) rho (hop.pi i) := by
    rw [hrho]
    exact (hop.last_seed_warm i).mono (by
      calc
        hop.warmConst i = 1 * hop.warmConst i := by rw [one_mul]
        _ ≤ 2 * hop.warmConst i := by gcongr; norm_num)
  have hphase := hop.distributional_mixing i rho hwarm inferInstance
  have hnext : Measure.map (fun omega : Nat → Score × Seed ↦ omega (i + 1)) pathLaw =
      sampleFromKernel (Q i) rho := by
    rw [Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_succ]
    unfold stateScheduleFromSeed stateKernelFromSeed sampleFromKernel
    rw [Arlib.MarkovChains.bind_comap]
    rfl
  have := hphase.map measurable_fst
  rw [← hnext, Measure.map_map measurable_fst (measurable_pi_apply (i + 1))] at this
  exact this

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- A bounded measurable scalar score read from one operational path is in `L²`. -/
theorem memLp_pathScore_of_bounded
    {mu : Measure (Nat → State n × Seed)} [IsProbabilityMeasure mu]
    {f : State n → Real} (hf : Measurable f) {B : Real}
    (hfB : ∀ x, |f x| ≤ B) (i : Nat) :
    MemLp (fun omega : Nat → State n × Seed ↦ f (omega (i + 1)).1) 2 mu := by
  apply MemLp.of_bound
    (hf.comp (measurable_fst.comp (measurable_pi_apply (i + 1)))).aestronglyMeasurable B
  exact Filter.Eventually.of_forall fun omega ↦ by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using hfB (omega (i + 1)).1

/-- Sharp TV-to-factor-`9` transport for the operational Gaussian ratio score.

The displayed `hslack` is the concrete scalar inequality that TV alone cannot remove:
the additive perturbation `e * B²` must fit in the gap between the exact factor `C` and
`9`, measured in units of the squared exact mean. -/
theorem operational_phaseScore_sq_moment_le_nine
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {m : Nat} {sigmaSq : Nat → Real} {i : Nat} {K : Set (State n)}
    {X : Ω → State n} {e : ENNReal}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (hX : Measurable X)
    (hTV : TVLe (Measure.map X mu) (coolLaw m sigmaSq K i) e) (he : e ≠ ⊤)
    {C : Real} (hC0 : 0 ≤ C) (hC9 : C ≤ 9)
    (hexact : ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
        ∂(coolLaw m sigmaSq K i) ≤
      C * (∫ x, phaseScore m sigmaSq (interior K) i x
        ∂(coolLaw m sigmaSq K i)) ^ 2)
    (hslack : e.toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 9)) ≤
      (9 - C) * (chain m sigmaSq K (i + 1) / chain m sigmaSq K i) ^ 2) :
    ∫ omega, phaseScore m sigmaSq (interior K) i (X omega) ^ 2 ∂mu ≤
      9 * (∫ omega, phaseScore m sigmaSq (interior K) i (X omega) ∂mu) ^ 2 := by
  have hs : 0 ≤ 9 - C := sub_nonneg.2 hC9
  have hmain := phaseScore_interior_sq_moment_le_of_tvLe hsigma hKc hball hfin
    hKR hX hTV he hC0 hs hexact
  have heq : C + (9 - C) = 9 := by ring
  have hslack' : e.toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * (C + (9 - C)))) ≤
      (9 - C) * (chain m sigmaSq K (i + 1) / chain m sigmaSq K i) ^ 2 := by
    rw [heq]
    exact hslack
  simpa only [heq] using hmain hslack'

/-- Path-law form consumed directly by the scalar premise of
`corrected_gaussianWarmFallback_independent_accuracy_four_fifths_of_scalarMoment`. -/
theorem operational_path_phaseScore_memLp_and_sq_moment_le_nine
    {k mPhases : Nat}
    {Q : Nat → Kernel (State n) (State n × State n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V mPhases eta)
    {chainLength : Nat} {sigmaSq : Nat → Real} {i : Nat} {K : Set (State n)}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : Measure.map Prod.fst (hop.tau i) = coolLaw chainLength sigmaSq K i)
    {C : Real} (hC0 : 0 ≤ C) (hC9 : C ≤ 9)
    (hexact : ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
        ∂(coolLaw chainLength sigmaSq K i) ≤
      C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
        ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : (hop.mixError i).toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 9)) ≤
      (9 - C) *
        (chain chainLength sigmaSq K (i + 1) / chain chainLength sigmaSq K i) ^ 2) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × State n ↦
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧ ∫ omega, (g omega) ^ 2 ∂pathLaw ≤
      9 * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  dsimp only
  let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let X : (Nat → State n × State n) → State n := fun omega ↦ (omega (i + 1)).1
  have hfm := measurable_phaseScore (m := chainLength) (σsq := sigmaSq)
    (K := interior K) isOpen_interior.measurableSet i
  have hbound : ∀ x, |phaseScore chainLength sigmaSq (interior K) i x| ≤
      Real.exp (R ^ 2 / (2 * sigmaSq i)) := by
    intro x
    rw [abs_of_nonneg (phaseScore_nonneg chainLength sigmaSq (interior K) i x)]
    exact phaseScore_le hsigma (interior_subset.trans hKR) i x
  constructor
  · exact memLp_pathScore_of_bounded hfm hbound i
  · have htv := tvLe_operational_score_eval_succ hop i
    rw [htarget] at htv
    exact operational_phaseScore_sq_moment_le_nine hsigma hKc hball hfin hKR
      (by fun_prop) htv (hop.mixError_ne_top i) hC0 hC9 hexact hslack

/-- All scalar premises expected by
`corrected_gaussianWarmFallback_independent_accuracy_four_fifths_of_scalarMoment`, for
the literal path ratio-score family.  This is the wiring point: its two conclusions can
be passed directly as that theorem's `hgL2` and `hscalarSq` arguments. -/
theorem operational_path_phaseScore_scalarPremises
    {k mPhases : Nat}
    {Q : Nat → Kernel (State n) (State n × State n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V mPhases eta)
    {chainLength : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (C : Nat → Real) (hC0 : ∀ i, 0 ≤ C i) (hC9 : ∀ i, C i ≤ 9)
    (htarget : ∀ i,
      Measure.map Prod.fst (hop.tau i) = coolLaw chainLength sigmaSq K i)
    (hexact : ∀ i,
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂(coolLaw chainLength sigmaSq K i) ≤
        C i * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : ∀ i, (hop.mixError i).toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 9)) ≤
      (9 - C i) *
        (chain chainLength sigmaSq K (i + 1) / chain chainLength sigmaSq K i) ^ 2) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g : Nat → (Nat → State n × State n) → Real := fun i omega ↦
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    (∀ i, MemLp (g i) 2 pathLaw) ∧
      (∀ i, ∫ omega, (g i omega) ^ 2 ∂pathLaw ≤
        9 * (∫ omega, g i omega ∂pathLaw) ^ 2) := by
  dsimp only
  constructor <;> intro i
  · exact (operational_path_phaseScore_memLp_and_sq_moment_le_nine hop hsigma hKc
      hball hfin hKR (htarget i) (hC0 i) (hC9 i) (hexact i) (hslack i)).1
  · exact (operational_path_phaseScore_memLp_and_sq_moment_le_nine hop hsigma hKc
      hball hfin hKR (htarget i) (hC0 i) (hC9 i) (hexact i) (hslack i)).2

#print axioms tvLe_operational_score_eval_succ
#print axioms memLp_pathScore_of_bounded
#print axioms operational_phaseScore_sq_moment_le_nine
#print axioms operational_path_phaseScore_memLp_and_sq_moment_le_nine
#print axioms operational_path_phaseScore_scalarPremises

end Ttc.CVGaussianWarmFallbackScoreMoment

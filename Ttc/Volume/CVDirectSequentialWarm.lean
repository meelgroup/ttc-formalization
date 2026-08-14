/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVDirectSequentialAccuracy

/-!
# Warmness propagation along an inhomogeneous direct cooling trajectory

This file proves the exact marginal recursion for the time-dependent Markov trajectory and
then propagates phase warmness inductively.  If phase `i` preserves warmth relative to
`pi i`, and `pi i` is `C`-warm relative to `pi (i+1)`, the realized state at time `i` is
`M0 * C^i`-warm.  Hence mixing deadlines depending on `log M` remain polynomial even
though the warmness constant itself grows geometrically.
-/

namespace Ttc.CVDirectSequentialWarm

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E]

/-- Time zero of an inhomogeneous trajectory has the supplied initial law. -/
theorem map_eval_inhomogeneousPathMeasure_zero
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu] :
    (inhomogeneousPathMeasure P mu).map (fun omega ↦ omega 0) = mu := by
  have hdet := Kernel.traj_map_frestrictLe_of_le (X := fun _ : Nat ↦ E)
    (κ := inhomogeneousHistoryKernel P) (a := 0) (b := 0) le_rfl
  have hmap : Kernel.map
        (Kernel.traj (X := fun _ : Nat ↦ E) (inhomogeneousHistoryKernel P) 0)
        (fun x ↦ x 0) =
      Kernel.deterministic
        (fun x : (_i : Finset.Iic 0) → E ↦ x ⟨0, Finset.mem_Iic.2 le_rfl⟩)
        (measurable_pi_apply _) := by
    rw [show (fun x : Nat → E ↦ x 0) =
        (fun h : (_i : Finset.Iic 0) → E ↦ h ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘
          Preorder.frestrictLe 0 from rfl,
      Kernel.map_comp_right _ (Preorder.measurable_frestrictLe 0)
        (measurable_pi_apply _), hdet,
      Kernel.deterministic_map _ (measurable_pi_apply _)]
    rfl
  rw [inhomogeneousPathMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (by fun_prop), hmap,
    Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- The time-`i+1` marginal is the time-`i` marginal passed through phase kernel `P i`. -/
theorem map_eval_inhomogeneousPathMeasure_succ
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu] (i : Nat) :
    (inhomogeneousPathMeasure P mu).map (fun omega ↦ omega (i + 1)) =
      sampleFromKernel (P i)
        ((inhomogeneousPathMeasure P mu).map (fun omega ↦ omega i)) := by
  change (inhomogeneousPathMeasure P mu).map (fun omega ↦ omega (i + 1)) =
    ((inhomogeneousPathMeasure P mu).map (fun omega ↦ omega i)).bind (P i)
  have hjoint := map_history_next_inhomogeneousPathMeasure P mu i
  have hsnd := congrArg Measure.snd hjoint
  rw [Measure.snd_compProd] at hsnd
  rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)] at hsnd
  rw [inhomogeneousHistoryKernel, bind_comap,
    Measure.map_map (measurable_pi_apply _) (by fun_prop)] at hsnd
  simp only [Function.comp_def, Preorder.frestrictLe_apply] at hsnd
  exact hsnd.symm

/-- The geometric warmness budget accumulated through phase `i`. -/
noncomputable def accumulatedWarm (M0 C : ENNReal) (i : Nat) : ENNReal :=
  M0 * C ^ i

@[simp] theorem accumulatedWarm_zero (M0 C : ENNReal) :
    accumulatedWarm M0 C 0 = M0 := by simp [accumulatedWarm]

theorem accumulatedWarm_succ (M0 C : ENNReal) (i : Nat) :
    accumulatedWarm M0 C (i + 1) = accumulatedWarm M0 C i * C := by
  simp [accumulatedWarm, pow_succ, mul_assoc]

/-- Generic phase-by-phase warmth propagation.  The transition need only preserve the
current target's warmness, and consecutive targets need only satisfy a fixed domination
factor `C`. -/
theorem isWarm_map_eval_inhomogeneousPathMeasure
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (pi : Nat → Measure E) {M0 C : ENNReal}
    (hstart : IsWarm M0 mu0 (pi 0))
    (hpreserve : ∀ i (rho : Measure E) (M : ENNReal),
      IsWarm M rho (pi i) → IsWarm M (sampleFromKernel (P i) rho) (pi i))
    (hsucc : ∀ i, IsWarm C (pi i) (pi (i + 1))) :
    ∀ i, IsWarm (accumulatedWarm M0 C i)
      ((inhomogeneousPathMeasure P mu0).map (fun omega ↦ omega i)) (pi i) := by
  intro i
  induction i with
  | zero =>
      simpa only [accumulatedWarm_zero, map_eval_inhomogeneousPathMeasure_zero] using hstart
  | succ i ih =>
      rw [map_eval_inhomogeneousPathMeasure_succ]
      rw [accumulatedWarm_succ]
      exact (hpreserve i _ _ ih).trans (hsucc i)

/-- Rewriting the previous theorem into the exact last-state marginal used by the LV2
conditional-history argument. -/
theorem isWarm_historyLast_inhomogeneousPathMeasure
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (pi : Nat → Measure E) {M0 C : ENNReal}
    (hstart : IsWarm M0 mu0 (pi 0))
    (hpreserve : ∀ i (rho : Measure E) (M : ENNReal),
      IsWarm M rho (pi i) → IsWarm M (sampleFromKernel (P i) rho) (pi i))
    (hsucc : ∀ i, IsWarm C (pi i) (pi (i + 1))) (i : Nat) :
    IsWarm (accumulatedWarm M0 C i)
      (((inhomogeneousPathMeasure P mu0).map (Preorder.frestrictLe i)).map
        (fun h ↦ h ⟨i, Finset.mem_Iic.2 le_rfl⟩)) (pi i) := by
  have h := isWarm_map_eval_inhomogeneousPathMeasure P mu0 pi hstart hpreserve hsucc i
  let last : (Finset.Iic i → E) → E :=
    fun z ↦ z ⟨i, Finset.mem_Iic.2 le_rfl⟩
  have hlast : Measurable last := measurable_pi_apply _
  have hmap : Measure.map last
      (Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure P mu0)) =
      Measure.map (fun omega : Nat → E ↦ omega i)
        (inhomogeneousPathMeasure P mu0) := by
    calc
      _ = Measure.map (last ∘ Preorder.frestrictLe i)
          (inhomogeneousPathMeasure P mu0) :=
        Measure.map_map hlast (Preorder.measurable_frestrictLe i)
      _ = Measure.map (fun omega : Nat → E ↦ omega i)
          (inhomogeneousPathMeasure P mu0) := by
        congr 1
  change IsWarm (accumulatedWarm M0 C i)
    (Measure.map last
      (Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure P mu0))) (pi i)
  rw [hmap]
  exact h

end Ttc.CVDirectSequentialWarm

#print axioms Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_zero
#print axioms Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_succ
#print axioms Ttc.CVDirectSequentialWarm.isWarm_map_eval_inhomogeneousPathMeasure
#print axioms Ttc.CVDirectSequentialWarm.isWarm_historyLast_inhomogeneousPathMeasure

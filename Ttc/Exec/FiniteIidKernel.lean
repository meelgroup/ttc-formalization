/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.StatewiseCostedRejectionKernel

/-!
# A finite iid product kernel

Mathlib has finite product measures but no `Kernel.pi`.  The statewise iid stream already
constructed for rejection sampling supplies one: draw an infinite iid stream and retain
its first `k` coordinates.  This file packages that construction and identifies its law
exactly with `Measure.pi`.
-/

namespace Ttc.FiniteIidKernel

open MeasureTheory ProbabilityTheory
open Arlib.Probability
open Ttc.CostedWarmPhaseRejection
open Ttc.StatewiseCostedRejectionKernel
open scoped Classical

variable {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]

/-- The first `k` entries of an infinite sequence. -/
def firstCoordinates (k : Nat) (z : Nat → E) : Fin k → E :=
  fun j ↦ z j.1

theorem measurable_firstCoordinates (k : Nat) :
    Measurable (firstCoordinates (E := E) k) := by
  unfold firstCoordinates
  fun_prop

/-- `k` conditionally iid draws from a state-indexed Markov kernel. -/
noncomputable def finiteIidKernel (k : Nat) (kappa : Kernel A E)
    [IsMarkovKernel kappa] : Kernel A (Fin k → E) :=
  Kernel.map (iidRoundsKernel kappa) (firstCoordinates k)

instance finiteIidKernel.isMarkovKernel (k : Nat) (kappa : Kernel A E)
    [IsMarkovKernel kappa] : IsMarkovKernel (finiteIidKernel k kappa) := by
  unfold finiteIidKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_firstCoordinates k)

/-- The finite iid kernel is literally the finite product of its coordinate law. -/
theorem finiteIidKernel_apply (k : Nat) (kappa : Kernel A E)
    [IsMarkovKernel kappa] (a : A) :
    finiteIidKernel k kappa a = Measure.pi (fun _ : Fin k ↦ kappa a) := by
  rw [finiteIidKernel, Kernel.map_apply _ (measurable_firstCoordinates k),
    iidRoundsKernel_apply_eq_roundsMeasure]
  let mu := kappa a
  letI : IsProbabilityMeasure mu := inferInstance
  have hind : iIndepFun (fun j : Fin k ↦ draw (j : Nat)) (roundsMeasure mu) :=
    (iIndepFun_draw mu).precomp Fin.val_injective
  have hmap := hind.map_fun_eq_pi_map
    (fun j : Fin k ↦ (measurable_draw (j : Nat)).aemeasurable)
  have hmap' : Measure.map (fun z : Nat → E ↦ fun j : Fin k ↦ z (j : Nat))
      (roundsMeasure mu) =
      Measure.pi (fun j : Fin k ↦ Measure.map (draw (j : Nat)) (roundsMeasure mu)) := by
    simpa only [draw] using hmap
  change Measure.map (fun z : Nat → E ↦ fun j : Fin k ↦ z (j : Nat))
      (roundsMeasure mu) = Measure.pi (fun _ : Fin k ↦ mu)
  rw [hmap']
  congr 1
  funext j
  exact (measurePreserving_draw mu (j : Nat)).map_eq

#print axioms finiteIidKernel_apply

end Ttc.FiniteIidKernel

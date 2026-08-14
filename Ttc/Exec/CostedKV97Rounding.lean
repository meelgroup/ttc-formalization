/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.RawBallWalkQueryCost
import Ttc.Exec.CostedWarmPhaseRejection
import Arlib.Lattice.KV97.Lemma1

/-!
# Costed randomized rounding and rejection for the TTC sampler

This file supplies the operational object missing from `Ttc.kv97SampD`.  A one-round law
starts from a costed continuous draw, performs coordinatewise randomized rounding, records
one additional membership query for the rounded point, and then uses the generic iid
costed-rejection construction.  Its candidate marginal is exactly the Giry bind of the
continuous law with `roundLaw`, and its expected rejection cost is the standard inverse
acceptance factor times the one-round expected cost.

The concrete polytope acceptance lower bound and the identification with TTC's fine-lattice
mass function are downstream specializations.
-/

namespace Ttc.CostedKV97Rounding

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.Lattice Arlib.Lattice.Rounding
open Ttc.CostedWarmPhaseRejection
open scoped ENNReal Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev LatticePoint (n : Nat) := Fin n -> Int

/-- Coordinatewise randomized rounding as a genuine Markov kernel. -/
noncomputable def roundingKernel : Kernel (State n) (LatticePoint n) where
  toFun p := roundLaw (WithLp.ofLp p)
  measurable' :=
    (Arlib.KV97.measurable_roundLaw n).comp (Arlib.KV97.measurable_ofLp n)

instance : IsMarkovKernel (roundingKernel (n := n)) := by
  exact ⟨fun p => isProbabilityMeasure_roundLaw (WithLp.ofLp p)⟩

/-- One randomized-rounding round, retaining the incoming continuous-query cost and adding
one query for testing whether the rounded point lies in the target polytope. -/
noncomputable def costedRoundingKernel :
    Kernel (ENNReal × State n) (ENNReal × LatticePoint n) :=
  Kernel.map
    (Kernel.compProd Kernel.id
      (Kernel.comap (roundingKernel (n := n))
        (fun q : (ENNReal × State n) × (ENNReal × State n) => q.2.2)
        (by fun_prop)))
    (fun q => (q.1.1 + 1, q.2))

instance : IsMarkovKernel (costedRoundingKernel (n := n)) := by
  unfold costedRoundingKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Law of one costed continuous draw followed by one actual randomized-rounding
membership test. -/
noncomputable def costedRoundedLaw (xi : Measure (ENNReal × State n)) :
    Measure (ENNReal × LatticePoint n) :=
  xi.bind (costedRoundingKernel (n := n))

instance (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi] :
    IsProbabilityMeasure (costedRoundedLaw xi) := by
  unfold costedRoundedLaw
  infer_instance

/-- The ordinary law of a rounded continuous draw. -/
noncomputable def roundedMeasure (mu : Measure (State n)) : Measure (LatticePoint n) :=
  mu.bind (roundingKernel (n := n))

instance (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (roundedMeasure mu) := by
  unfold roundedMeasure
  infer_instance

theorem map_snd_costedRoundingKernel (z : ENNReal × State n) :
    Measure.map Prod.snd (costedRoundingKernel (n := n) z) =
      roundingKernel z.2 := by
  rw [costedRoundingKernel, Kernel.map_apply _ (by fun_prop),
    Measure.map_map measurable_snd (by fun_prop)]
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA]
  change
    (Kernel.compProd Kernel.id
      (Kernel.comap (roundingKernel (n := n))
        (fun q : (ENNReal × State n) × (ENNReal × State n) => q.2.2)
        (by fun_prop)) z) (Prod.snd ⁻¹' A) = roundingKernel z.2 A
  rw [Kernel.compProd_apply (hA.preimage measurable_snd), Kernel.id_apply,
    lintegral_dirac']
  · rw [Kernel.comap_apply]
    congr 1
  · exact Kernel.measurable_kernel_prodMk_left' (hA.preimage measurable_snd) z

/-- Forgetting all costs gives randomized rounding of the continuous endpoint marginal. -/
theorem map_snd_costedRoundedLaw (xi : Measure (ENNReal × State n))
    [IsProbabilityMeasure xi] :
    Measure.map Prod.snd (costedRoundedLaw xi) =
      roundedMeasure (Measure.map Prod.snd xi) := by
  rw [costedRoundedLaw, roundedMeasure]
  ext A hA
  rw [Measure.map_apply measurable_snd hA,
    Measure.bind_apply (hA.preimage measurable_snd) (by fun_prop),
    Measure.bind_apply hA (by fun_prop)]
  rw [lintegral_map (Kernel.measurable_coe _ hA) measurable_snd]
  apply lintegral_congr
  intro z
  have hz := congrArg (fun mu : Measure (LatticePoint n) => mu A)
    (map_snd_costedRoundingKernel (n := n) z)
  simpa [Measure.map_apply measurable_snd hA] using hz

theorem lintegral_fst_costedRoundingKernel (z : ENNReal × State n) :
    (∫⁻ y, y.1 ∂costedRoundingKernel (n := n) z) = z.1 + 1 := by
  rw [costedRoundingKernel, Kernel.map_apply _ (by fun_prop),
    lintegral_map measurable_fst (by fun_prop),
    Kernel.lintegral_compProd Kernel.id _ z (by fun_prop)]
  have hinner : ∀ b : ENNReal × State n,
      (∫⁻ c : LatticePoint n, b.1 + 1
        ∂Kernel.comap (roundingKernel (n := n))
          (fun q : (ENNReal × State n) × (ENNReal × State n) => q.2.2)
          (by fun_prop) (z, b)) = b.1 + 1 := by
    intro b
    rw [Kernel.comap_apply, lintegral_const, measure_univ, mul_one]
  simp_rw [hinner]
  rw [Kernel.id_apply]
  simp

/-- One rounded candidate costs the continuous draw's recorded membership queries plus
one membership test for the rounded lattice point. -/
theorem lintegral_fst_costedRoundedLaw (xi : Measure (ENNReal × State n))
    [IsProbabilityMeasure xi] :
    (∫⁻ y, y.1 ∂costedRoundedLaw xi) = (∫⁻ z, z.1 ∂xi) + 1 := by
  rw [costedRoundedLaw, Measure.lintegral_bind (Kernel.aemeasurable _) (by fun_prop)]
  simp_rw [lintegral_fst_costedRoundingKernel]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- Full iid rounded rejection loop with its actual accumulated membership-query cost. -/
noncomputable def costedKV97RejectionLaw
    (xi : Measure (ENNReal × State n)) (A : Set (LatticePoint n)) :
    Measure (ENNReal × LatticePoint n) :=
  costedRejectionLaw (costedRoundedLaw xi) A

theorem map_snd_costedKV97RejectionLaw
    (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi]
    {A : Set (LatticePoint n)} (hA : MeasurableSet A)
    (hpos : 0 < roundedMeasure (Measure.map Prod.snd xi) A) :
    Measure.map Prod.snd (costedKV97RejectionLaw xi A) =
      Arlib.condOn (roundedMeasure (Measure.map Prod.snd xi)) A := by
  unfold costedKV97RejectionLaw
  rw [map_snd_costedRejectionLaw (costedRoundedLaw xi) hA]
  · rw [map_snd_costedRoundedLaw xi]
  · have hmass := congrArg (fun mu : Measure (LatticePoint n) => mu A)
      (map_snd_costedRoundedLaw (n := n) xi)
    rw [Measure.map_apply measurable_snd hA] at hmass
    simpa [liftedAccept, hmass] using hpos

/-- Wald/Tonelli cost formula for the complete rounded rejection sampler. -/
theorem lintegral_fst_costedKV97RejectionLaw
    (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi]
    {A : Set (LatticePoint n)} (hA : MeasurableSet A) :
    (∫⁻ y, y.1 ∂costedKV97RejectionLaw xi A) =
      (roundedMeasure (Measure.map Prod.snd xi) A)⁻¹ *
        ((∫⁻ z, z.1 ∂xi) + 1) := by
  unfold costedKV97RejectionLaw
  rw [lintegral_fst_costedRejectionLaw (costedRoundedLaw xi) hA,
    lintegral_fst_costedRoundedLaw]
  have hmass := congrArg (fun mu : Measure (LatticePoint n) => mu A)
    (map_snd_costedRoundedLaw (n := n) xi)
  rw [Measure.map_apply measurable_snd hA] at hmass
  simp [liftedAccept, hmass]

#print axioms map_snd_costedRoundedLaw
#print axioms lintegral_fst_costedRoundedLaw
#print axioms map_snd_costedKV97RejectionLaw
#print axioms lintegral_fst_costedKV97RejectionLaw

end Ttc.CostedKV97Rounding

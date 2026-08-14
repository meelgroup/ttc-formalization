import Ttc.Exec.KV97RoundedEndpointBridge
import Ttc.Sampler.Bridge

/-!
# KV97 acceptance from a total-variation continuous sampler

`KV97RoundedEndpointBridge` previously transported the proved `1/8` acceptance
bound only for a continuous law presented by a density.  The operational hybrid
walk generally retains atoms, so that theorem cannot be applied to it.  This file
uses the measure-valued TV window already used by the sampler correctness proof,
sums the resulting singleton bounds, and identifies that finite sum with the
actual `roundedMeasure` acceptance event.
-/

namespace Ttc.KV97TVAcceptance

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.Lattice Arlib.Lattice.Rounding
open Ttc.KV97RoundedEndpointBridge
open scoped ENNReal Classical Pointwise BigOperators

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev LatticePoint (n : Nat) := Fin n → Int

variable {A : Type*} {n : Nat} {D : Ttc.DNF A} {J ι : Type*} [Fintype ι]

/-- The KV97 `1/8` rejection acceptance bound for an arbitrary probability law
that is TV-close to the uniform law on the inflated body.  In contrast to the
density version, this applies to finite-time lazy Markov-chain laws with holding
atoms.

The error entering the scalar KV97 lemma is `escape + theta`: `escape` is the
reference tent-kernel loss and `theta / Vol(P')` is the continuous-law TV error.
-/
theorem one_eighth_le_roundedMeasure_integerAcceptance_of_tvLe
    (mu : Measure (State n)) [IsProbabilityMeasure mu]
    (M : A → Set (State n)) (rho : Int) (i : Ttc.Cube A)
    (Amat : J → State n) (bvec : J → Real)
    (cen : State n) (gamma c r theta escape eta : Real)
    (lat : ι → LatticePoint n)
    (hgamma : 0 < gamma) (hc : 0 ≤ c)
    (hball : Metric.ball cen gamma ⊆ Arlib.Polytope.body Amat bvec)
    (hfin : volume (Arlib.Polytope.body Amat bvec) ≠ ⊤)
    (heta0 : 0 ≤ eta) (heta : eta ≤ 1 / 4)
    (htheta0 : 0 ≤ theta)
    (hloss : escape + theta ≤ 1 / 4)
    (htv : Arlib.TVLe mu
      (Arlib.uniformOn volume (Arlib.KV97.inflated Amat bvec c r))
      (ENNReal.ofReal
        (theta / (volume (Arlib.KV97.inflated Amat bvec c r)).toReal)))
    (hvol0 : volume (Arlib.KV97.inflated Amat bvec c r) ≠ 0)
    (hvoltop : volume (Arlib.KV97.inflated Amat bvec c r) ≠ ⊤)
    (hlattice :
      (volume (Arlib.Polytope.body Amat bvec)).toReal ≤
        (1 + eta) * (Fintype.card ι : Real))
    (hthin : Arlib.KV97.kappaOf c r / gamma ≤ 1 / (n : Real))
    (hlat : Function.Injective lat)
    (henum : ∀ z, Arlib.KV97.latEmb n z ∈ Ttc.latticeScale rho • Ttc.region M i ↔
      ∃ j, lat j = z)
    (hesc : ∀ j, ∫ p in (Arlib.KV97.inflated Amat bvec c r)ᶜ,
      prodTent (Arlib.KV97.latEmb n (lat j)) p ≤ escape) :
    ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure mu
        (integerAcceptance M rho i) := by
  let V := (volume (Arlib.KV97.inflated Amat bvec c r)).toReal
  have hV : 0 < V := ENNReal.toReal_pos hvol0 hvoltop
  have hlow : ∀ j,
      (1 - (0 : Real)) * (1 - (escape + theta)) / V ≤
        ∫ p, prodTent (Arlib.KV97.latEmb n (lat j)) p ∂mu := by
    intro j
    have hw := Ttc.prodTent_window_of_tvLe
      (Amat := Amat) (bvec := bvec) (cc := c) (r := r)
      (V := V) (E := escape) (theta := theta)
      hvol0 hvoltop rfl hV htv htheta0 (hesc j)
    simpa using hw.1
  have hacc : (1 : Real) / 8 ≤
      Arlib.KV97.acceptance
        (fun j => Arlib.KV97.latEmb n (lat j))
        (fun x => ∫ p, prodTent x p ∂mu) := by
    exact Arlib.KV97.acceptance_ge_one_eighth
      (fun j => Arlib.KV97.latEmb n (lat j))
      (fun x => ∫ p, prodTent x p ∂mu)
      hgamma hc hball hfin heta0 heta (by norm_num) hloss hlow hlattice hthin
  have hset : integerAcceptance M rho i = Set.range lat := by
    ext z
    simp only [integerAcceptance, Set.mem_preimage, Set.mem_range]
    exact henum z
  have hlatEmb : Function.Injective (fun j => Arlib.KV97.latEmb n (lat j)) :=
    Arlib.KV97.injective_latEmb n |>.comp hlat
  have heq :
      (Ttc.CostedKV97Rounding.roundedMeasure mu
        (integerAcceptance M rho i)).toReal =
        Arlib.KV97.acceptance
          (fun j => Arlib.KV97.latEmb n (lat j))
          (fun x => ∫ p, prodTent x p ∂mu) := by
    rw [hset, Arlib.KV97.toReal_measure_range_eq_sum_singleton hlat
      (fun _ => measure_ne_top _ _), Arlib.KV97.acceptance_def]
    apply Finset.sum_congr rfl
    intro j _
    rw [Ttc.KV97RoundedEndpointBridge.toReal_roundedMeasure_singleton]
  rw [← heq] at hacc
  exact ENNReal.ofReal_le_of_le_toReal hacc

/-- Positivity needed to construct the operational rejection sampler follows
immediately from the quantitative `1/8` bound. -/
theorem roundedMeasure_integerAcceptance_pos_of_one_eighth
    {mu : Measure (State n)} {M : A → Set (State n)} {rho : Int} {i : Ttc.Cube A}
    (h : ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure mu (integerAcceptance M rho i)) :
    0 < Ttc.CostedKV97Rounding.roundedMeasure mu (integerAcceptance M rho i) := by
  exact lt_of_lt_of_le (by positivity) h

#print axioms one_eighth_le_roundedMeasure_integerAcceptance_of_tvLe
#print axioms roundedMeasure_integerAcceptance_pos_of_one_eighth

end Ttc.KV97TVAcceptance

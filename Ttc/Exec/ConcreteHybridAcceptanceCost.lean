import Ttc.Exec.ConcreteHybridExpectedQuerySampler
import Ttc.Exec.KV97TVAcceptance

/-!
# Acceptance-certified concrete hybrid KV97 sampler

This file removes the qualitative positivity premise from the concrete sampler
constructor once the quantitative KV97 `1/8` acceptance certificate is known,
and substitutes the proved polynomial transition envelope into the operational
facet/membership-inspection cost.
-/

namespace Ttc.ConcreteHybridAcceptanceCost

open MeasureTheory ProbabilityTheory Set Pointwise
open Ttc.KV97RoundedEndpointBridge
open Ttc.ConcreteHybridExpectedQuerySampler
open Ttc.CostedLazyHitAndRunAdapter
open scoped ENNReal Classical

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

variable {n : Nat} {ι : Type} {A0 : Type*} [Fintype ι] {D : Ttc.DNF A0}

/-- The concrete all-dimensional endpoint sampler, with mere positivity derived
from the quantitative KV97 `1/8` acceptance certificate. -/
noncomputable def expectedQueryKV97HybridConcreteOfEighth
    (epsPrime rf : Real)
    (Am : {c : Ttc.Cube A0 // c ∈ D} → ι → State n)
    (bv : {c : Ttc.Cube A0 // c ∈ D} → ι → Real)
    (rin Rout delta Mw : {c : Ttc.Cube A0 // c ∈ D} → Real)
    (sigma : {c : Ttc.Cube A0 // c ∈ D} → Measure (State n))
    (hsigma : ∀ j, IsProbabilityMeasure (sigma j))
    (hbounded : ∀ j, Bornology.IsBounded
      (Arlib.KV97.inflated (Am j) (bv j) (Arlib.KV97.cOf epsPrime) rf))
    (hdelta : ∀ j, 0 < delta j) [NeZero n]
    (body : A0 → Set (State n)) (rho : Int)
    (i : {c : Ttc.Cube A0 // c ∈ D})
    (heighth : ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma i)
        (integerAcceptance body rho i.val)) :
    ExpectedQueryFineSampler
      (kv97SampMeasure body rho
        (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma) i) :=
  expectedQueryKV97HybridConcrete epsPrime rf Am bv rin Rout delta Mw sigma hsigma
    hbounded hdelta body rho i
    (Ttc.KV97TVAcceptance.roundedMeasure_integerAcceptance_pos_of_one_eighth heighth)

/-- After the `1/8` acceptance theorem and the hybrid transition envelope are
substituted, the full continuous-walk plus rounding/rejection execution costs at
most eight times the polynomial inspection envelope (plus the one rounding
inspection per rejection round).

This is a facet/membership-inspection count.  It does not price exact-real
inner products, comparisons, division, or continuous random generation.
-/
theorem expected_inspections_kv97HybridConcrete_le_polynomial
    (hn : 1 ≤ n)
    (epsPrime rf : Real)
    (Am : {c : Ttc.Cube A0 // c ∈ D} → ι → State n)
    (bv : {c : Ttc.Cube A0 // c ∈ D} → ι → Real)
    (rin Rout delta Mw : {c : Ttc.Cube A0 // c ∈ D} → Real)
    (sigma : {c : Ttc.Cube A0 // c ∈ D} → Measure (State n))
    (hsigma : ∀ j, IsProbabilityMeasure (sigma j))
    (hbounded : ∀ j, Bornology.IsBounded
      (Arlib.KV97.inflated (Am j) (bv j) (Arlib.KV97.cOf epsPrime) rf))
    (hdelta : ∀ j, 0 < delta j) [NeZero n]
    (body : A0 → Set (State n)) (rho : Int)
    (i : {c : Ttc.Cube A0 // c ∈ D})
    (hrin : 0 < rin i) (hRout : 0 < Rout i) (hM : 1 ≤ Mw i)
    (heps0 : 0 < epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rf)).toReal))
    (heps1 : epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rf)).toReal) ≤ 1)
    (heighth : ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma i)
        (integerAcceptance body rho i.val)) :
    let K := Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf
    let t := Ttc.kv97HybridSteps n (rin i) (Rout i) (delta i) (Mw i)
      (epsPrime / (4 * (volume K).toReal))
    let R := hybridRealization (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf (delta i)
      (hbounded i) (hdelta i)
    (∫⁻ z, z.1 ∂costedFineEndpointLaw (endpointLaw R (sigma i) t)
      body rho i.val) ≤
      8 * (ENNReal.ofReal
        (Ttc.hybridTransitionBound n (rin i) (Rout i) (delta i) (Mw i)
          (epsPrime / (4 * (volume K).toReal))) *
            hybridStepInspectionBound n (Fintype.card ι) + 1) := by
  dsimp only
  have hraw := expected_inspections_kv97HybridConcrete_le
    epsPrime rf Am bv rin Rout delta Mw sigma hsigma hbounded hdelta body rho i heighth
  refine hraw.trans ?_
  have hstep := hybrid_steps_mul_inspectionBound_le (ι := ι) hn hrin hRout
    (hdelta i) hM heps0 heps1
  have hofReal8 : ENNReal.ofReal ((1 : Real) / 8) = (8 : ENNReal)⁻¹ := by
    rw [show ((1 : Real) / 8) = (8 : Real)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hinv : (ENNReal.ofReal ((1 : Real) / 8))⁻¹ = (8 : ENNReal) := by
    rw [hofReal8, inv_inv]
  rw [hinv]
  gcongr

#print axioms expectedQueryKV97HybridConcreteOfEighth
#print axioms expected_inspections_kv97HybridConcrete_le_polynomial

end Ttc.ConcreteHybridAcceptanceCost

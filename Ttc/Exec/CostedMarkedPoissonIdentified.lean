/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CostedMarkedPoisson

namespace Ttc.CostedMarkedPoissonIdentified

open MeasureTheory ProbabilityTheory
open Ttc.CostedAdaptiveIidCalls
open Ttc.CostedMarkedPoisson
open scoped ENNReal BigOperators Classical NNReal

variable {L : Nat}

/-- Finite categorical law associated with a real probability vector. -/
noncomputable def categoricalLaw (q : Fin L → Real) : Measure (Fin L) :=
  Measure.sum fun i : Fin L => ENNReal.ofReal (q i) • Measure.dirac i

@[simp] theorem categoricalLaw_singleton (q : Fin L → Real) (i : Fin L) :
    categoricalLaw q {i} = ENNReal.ofReal (q i) := by
  rw [categoricalLaw, Measure.sum_smul_dirac_singleton]

theorem isProbabilityMeasure_categoricalLaw {q : Fin L → Real}
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) :
    IsProbabilityMeasure (categoricalLaw q) := by
  refine ⟨?_⟩
  rw [categoricalLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hq0 i), hq]
  norm_num

/-- Pure-mark version of the empirical-count pushforward. -/
noncomputable def iidMarkedCountLaw
    (nu : Measure Nat) (mu : Measure (Fin L)) : Measure (Fin L → Nat) :=
  Measure.map
    (fun p : Nat × (Nat → Fin L) =>
      fun a => ∑ j ∈ Finset.range p.1, if p.2 j = a then 1 else 0)
    (nu.prod (Measure.infinitePi fun _ : Nat => mu))

theorem measurable_markProjection :
    Measurable (fun omega : MarkStream L => fun j => (omega j).2) :=
  measurable_pi_iff.2 fun j => measurable_snd.comp (measurable_pi_apply j)

/-- Costs do not affect empirical marks: the marked law depends only on the one-call state
marginal. -/
theorem markedCountLaw_eq_iidMarkedCountLaw
    (nu : Measure Nat) [IsProbabilityMeasure nu]
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi] :
    markedCountLaw nu xi = iidMarkedCountLaw nu (Measure.map Prod.snd xi) := by
  unfold markedCountLaw iidMarkedCountLaw adaptiveCallLaw iidCostedStreamLaw
  let proj : MarkStream L → (Nat → Fin L) := fun omega j => (omega j).2
  let hist : Nat × (Nat → Fin L) → (Fin L → Nat) := fun p a =>
    ∑ j ∈ Finset.range p.1, if p.2 j = a then 1 else 0
  have hproj : Measurable proj := measurable_markProjection
  have hhist : Measurable hist := by
    apply measurable_from_prod_countable_right
    intro N
    apply measurable_pi_lambda
    intro a
    change Measurable fun c : Nat → Fin L =>
      ∑ j ∈ Finset.range N, if c j = a then 1 else 0
    apply Finset.measurable_sum
    intro j _hj
    exact Measurable.ite
      ((MeasurableSet.singleton a).preimage (measurable_pi_apply j))
      measurable_const measurable_const
  have hfactor : (fun p : Nat × MarkStream L => prefixMarkCounts p.1 p.2) =
      hist ∘ Prod.map id proj := by
    rfl
  rw [hfactor, ← Measure.map_map hhist (measurable_id.prodMap hproj)]
  rw [← Measure.map_prod_map nu (Measure.infinitePi fun _ : Nat => xi)
    measurable_id hproj]
  rw [Measure.map_id]
  rw [show Measure.map proj (Measure.infinitePi fun _ : Nat => xi) =
      Measure.infinitePi (fun _ : Nat => Measure.map Prod.snd xi) by
        simpa only [proj] using
          (Measure.infinitePi_map_pi (μ := fun _ : Nat => xi)
            (f := fun _ (z : CostedMark L) => z.2) (fun _ => measurable_snd))]

/-- The sole remaining pure combinatorial identity, with all cost and sampler semantics
removed from its statement. -/
structure CategoricalPoissonIdentified (lam : Real) (q : Fin L → Real) : Prop where
  count_eq : iidMarkedCountLaw (poissonMeasure lam.toNNReal) (categoricalLaw q) =
    Ttc.countLaw lam q

/-- Once the pure categorical identity is known, every genuine costed sampler with that
state marginal satisfies `MarkedPoissonIdentified`; costs cannot affect its marks. -/
theorem markedPoissonIdentified_of_stateMarginal
    {lam : Real} {q : Fin L → Real}
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi]
    (hmarg : Measure.map Prod.snd xi = categoricalLaw q)
    (hpure : CategoricalPoissonIdentified lam q) :
    MarkedPoissonIdentified lam q xi := by
  constructor
  rw [markedCountLaw_eq_iidMarkedCountLaw, hmarg]
  exact hpure.count_eq

/-- The real Poisson first-moment series. -/
theorem hasSum_nat_mul_poisson (r : NNReal) :
    HasSum (fun n : Nat => Real.exp (-(r : Real)) * (r : Real) ^ n /
      (Nat.factorial n : Real) * (n : Real)) (r : Real) := by
  have hbase := hasSum_one_poissonMeasure r
  have hshift : HasSum
      (fun n : Nat => Real.exp (-(r : Real)) * (r : Real) ^ (n + 1) /
        (Nat.factorial (n + 1) : Real) * ((n + 1 : Nat) : Real))
      (r : Real) := by
    have hm := hbase.mul_left (r : Real)
    have heq : (fun n : Nat => Real.exp (-(r : Real)) * (r : Real) ^ (n + 1) /
        (Nat.factorial (n + 1) : Real) * ((n + 1 : Nat) : Real)) =
        fun n : Nat => (r : Real) *
          (Real.exp (-(r : Real)) * (r : Real) ^ n / (Nat.factorial n : Real)) := by
      funext n
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      field_simp
      ring
    rw [heq]
    simpa using hm
  rw [← hasSum_nat_add_iff' 1]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift

theorem integrable_natCast_poisson (r : NNReal) :
    Integrable (fun n : Nat => (n : Real)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa [Real.norm_natCast] using (hasSum_nat_mul_poisson r).summable

/-- Exact `ENNReal` mean of a Poisson count. -/
theorem lintegral_natCast_poisson (r : NNReal) :
    (∫⁻ n : Nat, (n : ENNReal) ∂poissonMeasure r) = (r : ENNReal) := by
  rw [show (∫⁻ n : Nat, (n : ENNReal) ∂poissonMeasure r) =
      ∫⁻ n : Nat, ENNReal.ofReal (n : Real) ∂poissonMeasure r by
        apply lintegral_congr
        intro n
        simp]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_natCast_poisson r)
    (Filter.Eventually.of_forall fun n => Nat.cast_nonneg n)]
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [(hasSum_nat_mul_poisson r).tsum_eq]
  simp

/-- Exact expected membership-query cost of the honest Poisson-length marked execution. -/
theorem lintegral_fst_actualCostedMarkedLaw_poisson
    {L : Nat} (r : NNReal)
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi] :
    (∫⁻ z, z.1 ∂actualCostedMarkedLaw (poissonMeasure r) xi) =
      (r : ENNReal) * (∫⁻ z, z.1 ∂xi) := by
  rw [lintegral_fst_actualCostedMarkedLaw]
  rw [lintegral_mul_const _ (Measurable.of_discrete : Measurable fun n : Nat => (n : ENNReal))]
  rw [lintegral_natCast_poisson]

#print axioms lintegral_natCast_poisson
#print axioms lintegral_fst_actualCostedMarkedLaw_poisson

end Ttc.CostedMarkedPoissonIdentified

import Ttc.Exec.PolyHybridCanonicalFinal

/-!
# Bounded-rate canonical-owner TTC adapter

The volume oracle's estimator is allowed to be unbounded on its failure coins.
Consequently, using the raw estimate as a Poisson intensity need not have a
finite expected sampling cost, even when the volume oracle itself has finite
expected query cost.

This file clips only the operational Poisson intensities.  It does not alter or
strengthen the semantic `VolumeAlgorithm` contract.  The resulting sampling
cost has a deterministic cap.  On the event where no intensity was clipped,
the original and clipped trajectory kernels agree exactly; the generic
probability lemma below charges precisely the probability of leaving that
event.
-/

namespace Ttc.CanonicalOwnerRateCutoff

open MeasureTheory ProbabilityTheory Set
open Ttc.CanonicalOwnerPoissonAssembler
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
open scoped ENNReal BigOperators Classical NNReal

variable {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
variable {L : Nat}

/-- Coordinatewise clipping of a nonnegative Poisson-rate vector. -/
def clippedRates (cap : I → NNReal) (lam : Omega → I → NNReal) :
    Omega → I → NNReal :=
  fun omega i => min (lam omega i) (cap i)

theorem measurable_clippedRates (cap : I → NNReal)
    (lam : Omega → I → NNReal) (hlam : Measurable lam) :
    Measurable (clippedRates cap lam) := by
  exact measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp hlam).min measurable_const

/-- The event on which clipping is observationally inert. -/
def ratesWithinCap (cap : I → NNReal) (lam : Omega → I → NNReal) :
    Set Omega :=
  {omega | ∀ i, lam omega i ≤ cap i}

theorem measurableSet_ratesWithinCap (cap : I → NNReal)
    (lam : Omega → I → NNReal) (hlam : Measurable lam) :
    MeasurableSet (ratesWithinCap cap lam) := by
  classical
  simp only [ratesWithinCap, setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le
    ((measurable_pi_apply i).comp hlam) measurable_const

/-- The canonical-owner plug-in with every source intensity clipped at a
deterministic coordinatewise cap. -/
noncomputable def clippedPlugin
    (q : I → Fin (L + 1) → Real)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (S : ∀ i, Ttc.CostedMarkedPoisson.ExpectedQueryFiniteSampler (q i))
    (owner : Fin L → I)
    (lam : Omega → I → NNReal) (hlam : Measurable lam)
    (cap : I → NNReal) :
    CanonicalOwnerTrajectoryPlugin I L Omega :=
  CanonicalOwnerTrajectoryPlugin.ofMeasurableRates q hq0 hqsum S owner
    (clippedRates cap lam) (measurable_clippedRates cap lam hlam)

/-- Pointwise deterministic sampling-query cap.  This is the key repair for
unbounded bad volume-oracle outputs. -/
theorem clippedPlugin_expectedSampleQueries_le
    (q : I → Fin (L + 1) → Real)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (S : ∀ i, Ttc.CostedMarkedPoisson.ExpectedQueryFiniteSampler (q i))
    (owner : Fin L → I)
    (lam : Omega → I → NNReal) (hlam : Measurable lam)
    (cap : I → NNReal) (omega : Omega) :
    (clippedPlugin q hq0 hqsum S owner lam hlam cap).expectedSampleQueries omega ≤
      ∑ i, (cap i : ENNReal) * (S i).expectedQueries := by
  classical
  unfold clippedPlugin CanonicalOwnerTrajectoryPlugin.expectedSampleQueries
  dsimp only [CanonicalOwnerTrajectoryPlugin.ofMeasurableRates]
  simp only [Real.toNNReal_coe]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_right' (ENNReal.coe_le_coe.mpr (min_le_right _ _)) _

/-- The deterministic pointwise cap also bounds the outer expected sampling
cost, with no integrability assumption on the raw volume estimates. -/
theorem lintegral_clippedPlugin_expectedSampleQueries_le
    (q : I → Fin (L + 1) → Real)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (S : ∀ i, Ttc.CostedMarkedPoisson.ExpectedQueryFiniteSampler (q i))
    (owner : Fin L → I)
    (lam : Omega → I → NNReal) (hlam : Measurable lam)
    (cap : I → NNReal) (mu : Measure Omega) [IsProbabilityMeasure mu] :
    (∫⁻ omega,
        (clippedPlugin q hq0 hqsum S owner lam hlam cap).expectedSampleQueries omega
      ∂mu) ≤ ∑ i, (cap i : ENNReal) * (S i).expectedQueries := by
  calc
    _ ≤ ∫⁻ _omega, ∑ i, (cap i : ENNReal) * (S i).expectedQueries ∂mu :=
      lintegral_mono fun omega =>
        clippedPlugin_expectedSampleQueries_le q hq0 hqsum S owner lam hlam cap omega
    _ = _ := by simp

/-- Uniform form of the deterministic cap.  If `C` and `B` are polynomial
bounds for each intensity and each sampler call, respectively, the full
canonical-owner sampling budget is `|I|·C·B`. -/
theorem lintegral_clippedPlugin_expectedSampleQueries_le_uniform
    (q : I → Fin (L + 1) → Real)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (S : ∀ i, Ttc.CostedMarkedPoisson.ExpectedQueryFiniteSampler (q i))
    (owner : Fin L → I)
    (lam : Omega → I → NNReal) (hlam : Measurable lam)
    (cap : I → NNReal) (mu : Measure Omega) [IsProbabilityMeasure mu]
    (C B : ENNReal) (hcap : ∀ i, (cap i : ENNReal) ≤ C)
    (hS : ∀ i, (S i).expectedQueries ≤ B) :
    (∫⁻ omega,
        (clippedPlugin q hq0 hqsum S owner lam hlam cap).expectedSampleQueries omega
      ∂mu) ≤ (Fintype.card I : ENNReal) * C * B := by
  refine (lintegral_clippedPlugin_expectedSampleQueries_le
    q hq0 hqsum S owner lam hlam cap mu).trans ?_
  calc
    ∑ i, (cap i : ENNReal) * (S i).expectedQueries
        ≤ ∑ _i : I, C * B := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul (hcap i) (hS i) bot_le bot_le
    _ = (Fintype.card I : ENNReal) * C * B := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ac_rfl

/-- On a coin where all rates lie below their caps, the original and clipped
costed trajectory fibers are definitionally the same measure. -/
theorem clippedPlugin_trajectoryKernel_eq_of_mem
    (q : I → Fin (L + 1) → Real)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (S : ∀ i, Ttc.CostedMarkedPoisson.ExpectedQueryFiniteSampler (q i))
    (owner : Fin L → I)
    (lam : Omega → I → NNReal) (hlam : Measurable lam)
    (cap : I → NNReal) {omega : Omega}
    (homega : omega ∈ ratesWithinCap cap lam) :
    (clippedPlugin q hq0 hqsum S owner lam hlam cap).trajectoryKernel omega =
      (CanonicalOwnerTrajectoryPlugin.ofMeasurableRates
        q hq0 hqsum S owner lam hlam).trajectoryKernel omega := by
  apply congrArg (fun rates : I → NNReal =>
    (CubeMarkedFamily.mk q (fun i => (rates i : Real))
      (fun _ => NNReal.zero_le_coe) hq0 hqsum S).assembledTrajectoryLaw owner)
  funext i
  exact min_eq_left (homega i)

/-- Composition-product measures agree on every measurable event restricted
to an outer good set whenever their conditional kernels agree there. -/
theorem compProd_inter_fst_preimage_eq_of_kernel_eq_on
    {Y : Type*} [MeasurableSpace Y] (mu : Measure Omega)
    [SFinite mu] (K K' : Kernel Omega Y)
    [IsSFiniteKernel K] [IsSFiniteKernel K']
    (event : Set (Omega × Y)) (good : Set Omega)
    (hevent : MeasurableSet event) (hgood : MeasurableSet good)
    (hkernel : ∀ omega ∈ good, K omega = K' omega) :
    (mu.compProd K) (event ∩ Prod.fst ⁻¹' good) =
      (mu.compProd K') (event ∩ Prod.fst ⁻¹' good) := by
  have hset : MeasurableSet (event ∩ Prod.fst ⁻¹' good) :=
    hevent.inter (hgood.preimage measurable_fst)
  rw [Measure.compProd_apply hset, Measure.compProd_apply hset]
  apply lintegral_congr
  intro omega
  by_cases homega : omega ∈ good
  · rw [hkernel omega homega]
  · have hempty : Prod.mk omega ⁻¹' (event ∩ Prod.fst ⁻¹' good) = ∅ := by
      ext y
      simp [homega]
    rw [hempty, measure_empty, measure_empty]

/-- Pure probability bookkeeping for a cutoff adapter.  If two probability
measures agree on the part of the accuracy event lying in `G`, replacing the
first by the second loses at most the first measure's mass outside `G`. -/
theorem probability_accuracy_transfer_of_agree_on_good
    {X : Type*} [MeasurableSpace X] (mu nu : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (accuracy good : Set X) {delta beta : Real}
    (haccuracy : 1 - delta ≤ (mu accuracy).toReal)
    (hbad : (mu goodᶜ).toReal ≤ beta)
    (hagree : mu (accuracy ∩ good) = nu (accuracy ∩ good)) :
    1 - (delta + beta) ≤ (nu accuracy).toReal := by
  have hsubset : accuracy ⊆ (accuracy ∩ good) ∪ goodᶜ := by
    intro x hx
    by_cases hg : x ∈ good
    · exact Or.inl ⟨hx, hg⟩
    · exact Or.inr hg
  have hle : mu accuracy ≤ nu accuracy + mu goodᶜ := by
    calc
      mu accuracy ≤ mu ((accuracy ∩ good) ∪ goodᶜ) := measure_mono hsubset
      _ ≤ mu (accuracy ∩ good) + mu goodᶜ := measure_union_le _ _
      _ = nu (accuracy ∩ good) + mu goodᶜ := by rw [hagree]
      _ ≤ nu accuracy + mu goodᶜ :=
        add_le_add (measure_mono inter_subset_left) le_rfl
  have hreal : (mu accuracy).toReal ≤
      (nu accuracy).toReal + (mu goodᶜ).toReal := by
    have htop : nu accuracy + mu goodᶜ ≠ ∞ := by
      exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
    have := ENNReal.toReal_mono htop hle
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
  linarith

#print axioms clippedPlugin_expectedSampleQueries_le
#print axioms lintegral_clippedPlugin_expectedSampleQueries_le
#print axioms lintegral_clippedPlugin_expectedSampleQueries_le_uniform
#print axioms clippedPlugin_trajectoryKernel_eq_of_mem
#print axioms compProd_inter_fst_preimage_eq_of_kernel_eq_on
#print axioms probability_accuracy_transfer_of_agree_on_good

end Ttc.CanonicalOwnerRateCutoff

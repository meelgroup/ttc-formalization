import Ttc.Exec.SequentialCostedPathLumping
import Ttc.Process.PoissonLaws

/-!
# A costed level-zero draw followed by the free TTC thinning trajectory

The coupled TTC family makes one operational marked-Poisson draw at level zero and then
obtains every later level by binomial thinning.  This file carries the cost of that one
draw alongside the whole thinning trajectory.  In particular, the cost coordinate is
cumulative and is preserved by thinning; later levels are not charged as fresh sampler
calls.

Forgetting the cumulative cost gives exactly `Ttc.trajLaw` as soon as the state marginal
of the supplied level-zero law is the required product-Poisson law.  A second theorem
accepts the repository's `Ttc.countLaw` interface.  Finite-prefix query accounting is an
exact sum whose level-zero summand is the initial mean and whose later summands are zero.
An exact Poisson construction remains unbounded pathwise; these results assert an
expectation identity, not a deterministic cutoff.
-/

namespace Ttc.CostedInitialThinningTrajectory

open MeasureTheory ProbabilityTheory
open Arlib.Probability
open Ttc.SequentialCostedPathLumping
open scoped ENNReal BigOperators Classical

variable {S : Type*} [MeasurableSpace S]

/-- Lift a state kernel while preserving a cumulative cost coordinate. -/
noncomputable def carryCostKernel (P : Kernel S S) :
    Kernel (ENNReal × S) (ENNReal × S) :=
  (Kernel.deterministic (fun z : ENNReal × S => z.1) measurable_fst) ×ₖ
    (Kernel.comap P Prod.snd measurable_snd)

instance (P : Kernel S S) [IsMarkovKernel P] : IsMarkovKernel (carryCostKernel P) := by
  unfold carryCostKernel
  infer_instance

/-- Forgetting the preserved cost from one lifted step recovers the state step. -/
theorem map_snd_carryCostKernel (P : Kernel S S) [IsMarkovKernel P]
    (z : ENNReal × S) :
    Measure.map Prod.snd (carryCostKernel P z) = P z.2 := by
  change (Kernel.snd (carryCostKernel P)) z = P z.2
  rw [carryCostKernel, Kernel.snd_prod]
  rfl

/-- The cost coordinate of one lifted step is the incoming cumulative cost. -/
theorem map_fst_carryCostKernel (P : Kernel S S) [IsMarkovKernel P]
    (z : ENNReal × S) :
    Measure.map Prod.fst (carryCostKernel P z) = Measure.dirac z.1 := by
  change (Kernel.fst (carryCostKernel P)) z = Measure.dirac z.1
  rw [carryCostKernel, Kernel.fst_prod]
  rfl

variable {L : Nat}

/-- The costed coupled family: draw `(cost, levelZero)` once, then thin forever while
carrying that same cumulative cost. -/
noncomputable def costedTrajLaw
    (nu0 : Measure (ENNReal × (Fin L → Nat))) :
    Measure (Nat → ENNReal × (Fin L → Nat)) :=
  inhomogeneousPathMeasure
    (fun _ => carryCostKernel (Ttc.thinKernel L)) nu0

instance (nu0 : Measure (ENNReal × (Fin L → Nat))) [IsProbabilityMeasure nu0] :
    IsProbabilityMeasure (costedTrajLaw nu0) := by
  unfold costedTrajLaw
  infer_instance

/-- Forgetting costs from the whole costed trajectory yields the TTC trajectory when the
level-zero state marginal is the required product-Poisson law. -/
theorem map_forgetCost_costedTrajLaw_eq_trajLaw
    (theta : Fin L → Real)
    (nu0 : Measure (ENNReal × (Fin L → Nat))) [IsProbabilityMeasure nu0]
    (hzero : Measure.map Prod.snd nu0 =
      Measure.pi (fun i => poissonMeasure (theta i).toNNReal)) :
    Measure.map (pathMap Prod.snd) (costedTrajLaw nu0) = Ttc.trajLaw theta := by
  rw [costedTrajLaw]
  have h := map_inhomogeneousPathMeasure_pathMap
    (fun _ => carryCostKernel (Ttc.thinKernel L))
    (fun _ => Ttc.thinKernel L) nu0
    (Measure.pi (fun i => poissonMeasure (theta i).toNNReal))
    measurable_snd hzero
    (fun _ z => map_snd_carryCostKernel (Ttc.thinKernel L) z)
  exact h

/-- `countLaw` form of the trajectory identification. -/
theorem map_forgetCost_costedTrajLaw_eq_trajLaw_of_countLaw
    {lam : Real} (hlam : 0 ≤ lam) {q : Fin L → Real}
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1)
    (nu0 : Measure (ENNReal × (Fin L → Nat))) [IsProbabilityMeasure nu0]
    (hzero : Measure.map Prod.snd nu0 = Ttc.countLaw lam q) :
    Measure.map (pathMap Prod.snd) (costedTrajLaw nu0) =
      Ttc.trajLaw (fun i => lam * q i) := by
  apply map_forgetCost_costedTrajLaw_eq_trajLaw
  rw [hzero, Ttc.countLaw_eq_pi hlam hq0 hq]

/-- Query increment assigned to level `j`: all operational work occurs at level zero. -/
def levelQueryIncrement (j : Nat)
    (omega : Nat → ENNReal × (Fin L → Nat)) : ENNReal :=
  if j = 0 then (omega 0).1 else 0

theorem measurable_levelQueryIncrement (j : Nat) :
    Measurable (levelQueryIncrement (L := L) j) := by
  by_cases h : j = 0
  · subst j
    change Measurable (fun omega : Nat → ENNReal × (Fin L → Nat) => (omega 0).1)
    exact measurable_fst.comp (measurable_pi_apply 0)
  · have heq : levelQueryIncrement (L := L) j =
        (fun _ : Nat → ENNReal × (Fin L → Nat) => 0) := by
      funext omega
      simp [levelQueryIncrement, h]
    rw [heq]
    exact measurable_const

/-- Actual membership-query cost of evaluating a finite prefix of `J` levels.  Thinning
itself is free, so this sum contains only the initial marked-Poisson cost. -/
noncomputable def finitePrefixQueryCost (J : Nat)
    (omega : Nat → ENNReal × (Fin L → Nat)) : ENNReal :=
  ∑ j ∈ Finset.range J, levelQueryIncrement j omega

theorem measurable_finitePrefixQueryCost (J : Nat) :
    Measurable (finitePrefixQueryCost (L := L) J) := by
  unfold finitePrefixQueryCost
  apply Finset.measurable_sum
  intro j hj
  exact measurable_levelQueryIncrement j

/-- Per-level mean query cost: the initial mean at level zero, and zero thereafter. -/
noncomputable def levelQueryMean
    (nu0 : Measure (ENNReal × (Fin L → Nat))) (j : Nat) : ENNReal :=
  if j = 0 then ∫⁻ z, z.1 ∂nu0 else 0

/-- Exact finite-prefix accounting.  This is an expectation identity only; it does not
bound the unbounded Poisson number of initial calls on every sample path. -/
theorem lintegral_finitePrefixQueryCost_eq_sum_levelQueryMean
    (nu0 : Measure (ENNReal × (Fin L → Nat))) [IsProbabilityMeasure nu0]
    (J : Nat) :
    (∫⁻ omega, finitePrefixQueryCost J omega ∂costedTrajLaw nu0) =
      ∑ j ∈ Finset.range J, levelQueryMean nu0 j := by
  unfold finitePrefixQueryCost
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hzero : j = 0
    · subst j
      simp only [levelQueryIncrement, levelQueryMean, if_pos]
      rw [← lintegral_map measurable_fst (measurable_pi_apply 0)]
      rw [costedTrajLaw,
        Ttc.SequentialCost.map_eval_inhomogeneousPathMeasure_zero]
    · simp [levelQueryIncrement, levelQueryMean, hzero]
  · intro j hj
    exact measurable_levelQueryIncrement j

/-- A nonempty finite prefix costs exactly the initial marked-Poisson mean. -/
theorem lintegral_finitePrefixQueryCost_eq_initialMean
    (nu0 : Measure (ENNReal × (Fin L → Nat))) [IsProbabilityMeasure nu0]
    {J : Nat} (hJ : 0 < J) :
    (∫⁻ omega, finitePrefixQueryCost J omega ∂costedTrajLaw nu0) =
      ∫⁻ z, z.1 ∂nu0 := by
  rw [lintegral_finitePrefixQueryCost_eq_sum_levelQueryMean]
  rw [Finset.sum_eq_single 0]
  · simp [levelQueryMean]
  · intro b hb hne
    simp [levelQueryMean, hne]
  · simp [hJ]

#print axioms map_snd_carryCostKernel
#print axioms map_fst_carryCostKernel
#print axioms map_forgetCost_costedTrajLaw_eq_trajLaw
#print axioms map_forgetCost_costedTrajLaw_eq_trajLaw_of_countLaw
#print axioms lintegral_finitePrefixQueryCost_eq_sum_levelQueryMean
#print axioms lintegral_finitePrefixQueryCost_eq_initialMean

end Ttc.CostedInitialThinningTrajectory

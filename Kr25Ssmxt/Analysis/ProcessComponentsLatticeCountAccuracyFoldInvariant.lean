import Kr25Ssmxt.Analysis.ProbabilityBindGoodEventLowerBound

/-!
# Fold-level invariant accumulation for lattice-count accuracy

This module isolates the induction over the component list from the probabilistic work
needed to verify one component step.  The invariant itself remains an explicit family of
measurable state sets, so a proof of the stochastic prefix invariant can instantiate it
without depending on this induction.
-/

noncomputable section

open MeasureTheory

namespace Kr25Ssmxt

/-- If every component-processing step preserves a measurable prefix invariant except for
one fixed failure budget, the whole component fold satisfies the final invariant except
for the sum of those budgets.

INTERNAL: component-list induction in
`process_components_lattice_count_accuracy`.
-/
lemma process_components_lattice_count_accuracy_fold_invariant
    {n k : Nat}
    (O : TTCOracles n k)
    (b : Nat)
    (epsilonPrime deltaPrime threshold stepFailure : Real)
    (Ps : List (PolytopeData n))
    (good : Nat → Set (TTCState n))
    (hgood : ∀ i, MeasurableSet (good i))
    (hinitial : TTCState.initial n ∈ good 0)
    (hstepFailure : 0 ≤ stepFailure)
    (hkernel : ∀ P,
      Measurable
        (fun state ⇒
          processComponent O b epsilonPrime deltaPrime threshold P state))
    (hprobability : ∀ P state,
      IsProbabilityMeasure
        (processComponent O b epsilonPrime deltaPrime threshold P state))
    (hstep : ∀ i P state, state ∈ good i →
      (processComponent O b epsilonPrime deltaPrime threshold P state).real
          (good (i + 1)) ≥ 1 - stepFailure) :
    (processComponents O b epsilonPrime deltaPrime threshold Ps
        (TTCState.initial n)).real (good Ps.length) ≥
      1 - (Ps.length : Real) * stepFailure := by
  have hmeasurable : ∀ Qs : List (PolytopeData n),
      Measurable
        (fun state =>
          processComponents O b epsilonPrime deltaPrime threshold Qs state) := by
    intro Qs
    induction Qs with
    | nil =>
        simpa [processComponents] using
          (Measure.measurable_dirac :
            Measurable (fun state : TTCState n => Measure.dirac state))
    | cons P rest ih =>
        simp only [processComponents]
        exact (Measure.measurable_bind' ih).comp (hkernel P)
  have hprob : ∀ (Qs : List (PolytopeData n)) (state : TTCState n),
      IsProbabilityMeasure
        (processComponents O b epsilonPrime deltaPrime threshold Qs state) := by
    intro Qs
    induction Qs with
    | nil =>
        intro state
        simp only [processComponents]
        infer_instance
    | cons P rest ih =>
        intro state
        simp only [processComponents]
        letI : IsProbabilityMeasure
            (processComponent O b epsilonPrime deltaPrime threshold P state) :=
          hprobability P state
        apply isProbabilityMeasure_bind (hmeasurable rest).aemeasurable
        filter_upwards with nextState
        exact ih nextState
  have hindexed : ∀ (Qs : List (PolytopeData n)) (i : Nat) (state : TTCState n),
      state ∈ good i →
      (processComponents O b epsilonPrime deltaPrime threshold Qs state).real
          (good (i + Qs.length)) ≥
        1 - (Qs.length : Real) * stepFailure := by
    intro Qs
    induction Qs with
    | nil =>
        intro i state hstate
        simp only [processComponents, List.length_nil, Nat.cast_zero, zero_mul, sub_zero,
          Nat.add_zero]
        simp [hgood i, hstate]
    | cons P rest ih =>
        intro i state hstate
        have hbound := probability_bind_good_event_lower_bound
          (processComponent O b epsilonPrime deltaPrime threshold P state)
          (processComponents O b epsilonPrime deltaPrime threshold rest)
          (good (i + 1)) (good ((i + 1) + rest.length))
          ((rest.length : Real) * stepFailure) stepFailure
          (hprobability P state) (hprob rest) (hmeasurable rest)
          (hgood (i + 1)) (hgood ((i + 1) + rest.length))
          (mul_nonneg (Nat.cast_nonneg _) hstepFailure) hstepFailure
          (hstep i P state hstate) (ih (i + 1))
        simpa only [processComponents, List.length_cons, Nat.cast_add, Nat.cast_one,
          add_mul, one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          add_assoc, add_comm, add_left_comm] using hbound
  simpa using hindexed Ps 0 (TTCState.initial n) hinitial

end Kr25Ssmxt

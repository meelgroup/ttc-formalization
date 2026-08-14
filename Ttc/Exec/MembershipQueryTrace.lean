/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.ProperProposalGaussian

/-!
# Minimal membership-query traces

This file defines the smallest operational semantics needed to say that one Gaussian
proposal performs exactly one body-membership query.  The proposal point and the Boolean
answer are retained in the trace; a subsequent Metropolis coin decides whether a proper
proposal moves or holds.

There are two intentionally separate layers:

* `MembershipOracle K` is supplied data: an answer function, its measurability, and a proof
  that it decides membership in `K`.  An executable implementation must supply this data.
* `MembershipOracle.ofMeasurableSet` is a noncomputable classical witness for a measurable
  set.  It is sufficient for probability kernels, but it is not claimed to be executable.
  Measurability of a set does not provide an algorithm deciding membership.

The existing `properProposalGaussianAux` kernel retains only `(properMark, nextState)` and
forgets the sampled proposal point.  Therefore this file does not claim definitionally that
its trace is already present in that kernel.  A future raw Gaussian proposal kernel must
map the control-flow record below to `properProposalGaussianAux`; the query-count theorem
will then transfer without any further cost modelling.
-/

namespace Ttc.MembershipQuery

open MeasureTheory Set

variable {S : Type*} [MeasurableSpace S]

/-- A body-membership oracle with semantic and measurable answers.  This is data, not an
assumption that every measurable set has a computable decision procedure. -/
structure MembershipOracle (K : Set S) where
  answer : S -> Bool
  measurable_answer : Measurable answer
  answer_eq_true_iff : forall x, answer x = true <-> x ∈ K

namespace MembershipOracle

/-- Classical Boolean membership.  The definition is explicitly noncomputable: arbitrary
measurable-set membership is not executable merely because the set is measurable. -/
noncomputable def ofMeasurableSet (K : Set S) (hK : MeasurableSet K) :
    MembershipOracle K := by
  classical
  exact
    { answer := fun x => if x ∈ K then true else false
      measurable_answer := Measurable.piecewise hK measurable_const measurable_const
      answer_eq_true_iff := by
        intro x
        simp }

@[simp] theorem ofMeasurableSet_answer
    (K : Set S) (hK : MeasurableSet K) (x : S) :
    (ofMeasurableSet K hK).answer x = true <-> x ∈ K :=
  (ofMeasurableSet K hK).answer_eq_true_iff x

theorem answer_eq_false_iff {K : Set S} (oracle : MembershipOracle K) (x : S) :
    oracle.answer x = false <-> x ∉ K := by
  rw [Bool.eq_false_iff]
  exact not_congr (oracle.answer_eq_true_iff x)

end MembershipOracle

/-- One observable membership-oracle event. -/
structure QueryEvent (S : Type*) where
  point : S
  response : Bool

/-- A finite trace of membership-oracle events. -/
abbrev QueryTrace (S : Type*) := List (QueryEvent S)

/-- Membership-query cost is the number of recorded oracle calls. -/
def queryCost (trace : QueryTrace S) : Nat := trace.length

/-- Execute exactly one membership query and retain its argument and answer. -/
def query {K : Set S} (oracle : MembershipOracle K) (point : S) : QueryTrace S :=
  [{ point := point, response := oracle.answer point }]

@[simp] theorem query_cost {K : Set S} (oracle : MembershipOracle K) (point : S) :
    queryCost (query oracle point) = 1 := rfl

@[simp] theorem query_response {K : Set S} (oracle : MembershipOracle K) (point : S) :
    (query oracle point).head?.map QueryEvent.response = some (oracle.answer point) := rfl

/-- The recorded positive answer is exactly body membership. -/
theorem query_response_true_iff {K : Set S} (oracle : MembershipOracle K) (point : S) :
    ((query oracle point).head?.map QueryEvent.response = some true) <-> point ∈ K := by
  simp only [query, List.head?_cons, Option.map_some]
  simpa using oracle.answer_eq_true_iff point

/-! ## One proper Gaussian proposal round -/

/-- Random choices supplied to the deterministic control flow of one proposal round.
`proposal` is the sampled point in the proposal ball.  `metropolisAccepts` is the sampled
Bernoulli result for the Gaussian Metropolis acceptance probability. -/
structure ProperProposalChoices (S : Type*) where
  current : S
  proposal : S
  metropolisAccepts : Bool

/-- Result of one traced proposal round.  The proper mark records body membership.  A point
moves exactly when it is proper and the separate Metropolis coin accepts. -/
structure ProperProposalResult (S : Type*) where
  trace : QueryTrace S
  properMark : Bool
  nextState : S

/-- Operational semantics of one proper-proposal Gaussian round.  It calls the body oracle
once, then applies the Metropolis filter. -/
def properProposalRound {K : Set S} (oracle : MembershipOracle K)
    (choices : ProperProposalChoices S) : ProperProposalResult S :=
  let proper := oracle.answer choices.proposal
  { trace := query oracle choices.proposal
    properMark := proper
    nextState := if proper && choices.metropolisAccepts then choices.proposal
      else choices.current }

/-- One proper-proposal round makes exactly one membership-oracle call. -/
@[simp] theorem properProposalRound_queryCost {K : Set S} (oracle : MembershipOracle K)
    (choices : ProperProposalChoices S) :
    queryCost (properProposalRound oracle choices).trace = 1 := rfl

/-- The trace retains exactly the proposal point queried. -/
@[simp] theorem properProposalRound_queryPoint {K : Set S} (oracle : MembershipOracle K)
    (choices : ProperProposalChoices S) :
    (properProposalRound oracle choices).trace.head?.map QueryEvent.point =
      some choices.proposal := rfl

/-- The proper mark has exactly the intended membership semantics. -/
theorem properProposalRound_mark_true_iff {K : Set S} (oracle : MembershipOracle K)
    (choices : ProperProposalChoices S) :
    (properProposalRound oracle choices).properMark = true <-> choices.proposal ∈ K := by
  exact oracle.answer_eq_true_iff choices.proposal

/-- An improper proposal holds at the current point. -/
theorem properProposalRound_next_of_not_mem {K : Set S} (oracle : MembershipOracle K)
    (choices : ProperProposalChoices S) (h : choices.proposal ∉ K) :
    (properProposalRound oracle choices).nextState = choices.current := by
  have hans : oracle.answer choices.proposal = false :=
    (MembershipOracle.answer_eq_false_iff oracle choices.proposal).2 h
  simp [properProposalRound, hans]

/-- A proper proposal rejected by the Metropolis coin also holds. -/
theorem properProposalRound_next_of_filter_reject {K : Set S}
    (oracle : MembershipOracle K) (choices : ProperProposalChoices S)
    (hreject : choices.metropolisAccepts = false) :
    (properProposalRound oracle choices).nextState = choices.current := by
  simp [properProposalRound, hreject]

/-- A proper proposal accepted by the Metropolis coin moves to the proposal point. -/
theorem properProposalRound_next_of_mem_accept {K : Set S}
    (oracle : MembershipOracle K) (choices : ProperProposalChoices S)
    (hmem : choices.proposal ∈ K) (haccept : choices.metropolisAccepts = true) :
    (properProposalRound oracle choices).nextState = choices.proposal := by
  have hans : oracle.answer choices.proposal = true :=
    (oracle.answer_eq_true_iff choices.proposal).2 hmem
  simp [properProposalRound, hans, haccept]

/-! ## Gaussian specialization -/

abbrev GaussianState (n : Nat) := EuclideanSpace Real (Fin n)

/-- Noncomputable measurable-set oracle used by the current measure-theoretic Gaussian
development.  Supplying a computable oracle remains a separate implementation obligation. -/
noncomputable def measurableGaussianBodyOracle {n : Nat}
    (K : Set (GaussianState n)) (hK : MeasurableSet K) : MembershipOracle K :=
  MembershipOracle.ofMeasurableSet K hK

/-- Even for the classical measurable-body witness, the traced Gaussian control flow
records exactly one query and its mark is exactly membership. -/
theorem measurableGaussianBody_round_certificate {n : Nat}
    (K : Set (GaussianState n)) (hK : MeasurableSet K)
    (choices : ProperProposalChoices (GaussianState n)) :
    queryCost (properProposalRound (measurableGaussianBodyOracle K hK) choices).trace = 1 ∧
      ((properProposalRound (measurableGaussianBodyOracle K hK) choices).properMark = true <->
        choices.proposal ∈ K) := by
  exact ⟨properProposalRound_queryCost _ _, properProposalRound_mark_true_iff _ _⟩

/-! ### Axiom audit -/

#print axioms MembershipOracle.ofMeasurableSet
#print axioms properProposalRound_queryCost
#print axioms properProposalRound_mark_true_iff
#print axioms measurableGaussianBody_round_certificate

end Ttc.MembershipQuery

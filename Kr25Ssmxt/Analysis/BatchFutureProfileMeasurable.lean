import Kr25Ssmxt.Analysis.PolytopeCarrierMeasurable

/-!
# Measurable finite profiles of generated batches

For a fixed finite batch, suffix, and existing configuration, all future-membership bits and
all possible point-collision bits form a measurable finite discrete observable.  No property
of the oracle law is used.
-/

noncomputable section

namespace Kr25Ssmxt

open MeasureTheory

/--
The Boolean indicator of membership in a normalized polytope.

INTERNAL: one coordinate of a generated batch's finite future-membership profile.
-/
def polytopeMembershipBit {n : Nat} (P : PolytopeData n) (x : Point n) : Bool := by
  classical
  exact if x ∈ P.carrier then true else false

/--
Membership in a fixed normalized polytope is a measurable Boolean observable.

INTERNAL: coordinate measurability for the finite future-membership partition.
-/
lemma polytopeMembershipBit_measurable {n : Nat} (P : PolytopeData n) :
    Measurable (polytopeMembershipBit P) := by
  classical
  rw [show polytopeMembershipBit P =
      P.carrier.piecewise (fun _ => true) (fun _ => false) by
    funext x
    by_cases hx : x ∈ P.carrier <;> simp [polytopeMembershipBit, hx]]
  exact measurable_const.piecewise (polytope_carrier_measurable P) measurable_const

/--
Membership of every point in a fixed batch in every component of a fixed suffix.

INTERNAL: finite discrete partition used for the sampling branch of `processComponent`.
-/
def batchFutureProfile {n count : Nat} (Qs : List (PolytopeData n))
    (points : Fin count → LatticePoint n) : Fin count → Fin Qs.length → Bool :=
  fun i j => polytopeMembershipBit (Qs.get j) (points i).toPoint

/--
The Boolean indicator that two points coincide.

INTERNAL: one coordinate of the finite collision partition for `TTCState.addBatch`.
-/
def pointEqualityBit {n : Nat} (x y : LatticePoint n) : Bool := by
  classical
  exact if x = y then true else false

/--
Equality with a fixed point is a measurable Boolean observable.

INTERNAL: coordinate measurability for the finite collision partition.
-/
lemma pointEqualityBit_right_measurable {n : Nat} (y : LatticePoint n) :
    Measurable (fun x : LatticePoint n => pointEqualityBit x y) := by
  exact measurable_of_countable _

/--
Future-membership bits together with all equality tests against an existing finite sample
configuration.

INTERNAL: accounts for possible `Finset.union` collisions in `TTCState.addBatch` for an
arbitrary input state.
-/
def batchFutureProfileWithCollisions {n count : Nat} (Qs : List (PolytopeData n))
    (existing : Finset (SampleCopy n)) (points : Fin count → LatticePoint n) :
    (Fin count → Fin Qs.length → Bool) ×
      (Fin count → {copy // copy ∈ existing} → Bool) :=
  (batchFutureProfile Qs points,
    fun i copy => pointEqualityBit (points i) copy.1.2)

/--
The complete finite membership-and-collision profile of a generated batch is measurable.

INTERNAL: measurable finite partition of an arbitrary `generateSamples` law; in particular,
this assumes neither finiteness nor a probability-measure contract for that law.
-/
lemma batch_futureProfile_measurable {n count : Nat} (Qs : List (PolytopeData n))
    (existing : Finset (SampleCopy n)) :
    Measurable (batchFutureProfileWithCollisions (count := count) Qs existing) := by
  classical
  apply Measurable.prod
  · refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    change Measurable (fun points : Fin count → LatticePoint n =>
      polytopeMembershipBit (Qs.get j) (points i).toPoint)
    exact (polytopeMembershipBit_measurable (Qs.get j)).comp
      ((measurable_of_countable LatticePoint.toPoint).comp (measurable_pi_apply i))
  · refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun copy => ?_
    change Measurable (fun points : Fin count → LatticePoint n =>
      pointEqualityBit (points i) copy.1.2)
    exact (pointEqualityBit_right_measurable copy.1.2).comp (measurable_pi_apply i)

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · built the finite suffix-membership and existing-sample collision
  partition coordinatewise
-/

import Ttc.Exec.TtcCallBallAdmissible

/-!
# The circumradius, and why the radial parameter must be it

The whole expected-query chain carries a free `radialR : Set (Ttc.Space n) → Real`, and two
obligations pull on it in opposite directions:

* the *interface* needs `hrad : (radialR K) ^ 2 ≤ R2` — so `radialR` must be **small**;
* the *construction* needs the frontier theorem's `hKR : K ⊆ closedBall 0 R` at `R = radialR K`,
  and its expected-cost certificate lands at `sourceOneRunQueryBudget rc n (radialR K) eps`,
  which is **increasing** in the radius — so `radialR` must be **large** enough to contain `K`.

`Real.sqrt (cvSecondMoment K)` satisfies the first and fails the second: a second-moment
bound does not contain the body.  `Metric.diam K` satisfies the second and fails the first:
from `K ⊆ closedBall 0 r` one only gets `diam K ≤ 2r`, so `(diam K)^2 ≤ 4*R2`, not `≤ R2`.

The function that satisfies **both** is the circumradius about the origin,
`circumR K = sup {‖x‖ : x ∈ K}`.  It contains `K` by construction and is bounded by any
containing radius, on the nose.  That is the whole content of this file.

`Ttc.TtcRadialGeometry.ttcRadialR` is kept: it is the right choice for the `cvAdm` route,
where no containment is demanded.  This file is for the `cvAdmBall` route.

## Main results

* `circumR` — the circumradius, with junk value `0` off the bounded case.
* `subset_closedBall_circumR` — `K ⊆ closedBall 0 (circumR K)` for bounded `K`.
* `circumR_le_of_subset_closedBall` — `circumR K ≤ r` whenever `K ⊆ closedBall 0 r`.
* `circumR_sq_le_of_cvAdmBall` — the interface's `hrad`, at `cvAdmBall`.
* `cvAdmBall_callBody_circum` — TTC's own call bodies, at the declared radius that makes
  both obligations hold simultaneously.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Ttc.TtcCircumRadius

open MeasureTheory Metric Set
open Ttc.TtcCallBodyBounded
open Ttc.TtcCallBallAdmissible
open Ttc.TTCCVExpectedImplementation

variable {n : Nat}

/-- The circumradius of `K` about the origin.  The outer `max 0` makes the value junk-free
(`sSup` of an empty or unbounded set of reals is `0` by convention, and a radius must be
nonnegative in any case). -/
noncomputable def circumR (K : Set (Ttc.Space n)) : Real :=
  max 0 (sSup ((fun x : Ttc.Space n ↦ ‖x‖) '' K))

theorem circumR_nonneg (K : Set (Ttc.Space n)) : 0 ≤ circumR K := le_max_left _ _

/-- Norms on a bounded set are bounded above. -/
theorem bddAbove_norm_image {K : Set (Ttc.Space n)} (hK : Bornology.IsBounded K) :
    BddAbove ((fun x : Ttc.Space n ↦ ‖x‖) '' K) := by
  obtain ⟨r, hr⟩ := hK.subset_closedBall (0 : Ttc.Space n)
  refine ⟨r, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have := hr hx
  simpa [Metric.mem_closedBall, dist_zero_right] using this

/-- **The circumradius contains the body.** -/
theorem subset_closedBall_circumR {K : Set (Ttc.Space n)}
    (hK : Bornology.IsBounded K) : K ⊆ Metric.closedBall 0 (circumR K) := by
  intro x hx
  have hmem : ‖x‖ ∈ (fun y : Ttc.Space n ↦ ‖y‖) '' K := ⟨x, hx, rfl⟩
  have hle : ‖x‖ ≤ sSup ((fun y : Ttc.Space n ↦ ‖y‖) '' K) :=
    le_csSup (bddAbove_norm_image hK) hmem
  have : ‖x‖ ≤ circumR K := hle.trans (le_max_right _ _)
  simpa [Metric.mem_closedBall, dist_zero_right] using this

/-- **The circumradius is minimal among containing radii**, with no `2` lost. -/
theorem circumR_le_of_subset_closedBall {K : Set (Ttc.Space n)} {r : Real}
    (hr : 0 ≤ r) (hsub : K ⊆ Metric.closedBall 0 r) : circumR K ≤ r := by
  refine max_le hr ?_
  rcases Set.eq_empty_or_nonempty K with hempty | ⟨x0, hx0⟩
  · simp [hempty, Real.sSup_empty, hr]
  · refine Real.sSup_le ?_ hr
    rintro y ⟨x, hx, rfl⟩
    have := hsub hx
    simpa [Metric.mem_closedBall, dist_zero_right] using this

/-- **The interface's `hrad`, at `cvAdmBall`.**  The declared radius bounds the
circumradius exactly, because `cvAdmBall` asserts containment at `Real.sqrt R2`. -/
theorem circumR_sq_le_of_cvAdmBall {K : Set (Ttc.Space n)} {R2 : Real}
    (h : Ttc.CVShaped.cvAdmBall n K R2) : (circumR K) ^ 2 ≤ R2 := by
  have hR20 : 0 ≤ R2 := by
    have hm0 : 0 ≤ Ttc.cvSecondMoment K := by
      unfold Ttc.cvSecondMoment
      exact integral_nonneg (fun _ ↦ sq_nonneg _)
    exact hm0.trans h.1.2.2.2.2
  have hle : circumR K ≤ Real.sqrt R2 :=
    circumR_le_of_subset_closedBall (Real.sqrt_nonneg _) h.2
  have hsq : (circumR K) ^ 2 ≤ (Real.sqrt R2) ^ 2 := by
    have h0 := circumR_nonneg K
    nlinarith [Real.sqrt_nonneg R2]
  calc (circumR K) ^ 2 ≤ (Real.sqrt R2) ^ 2 := hsq
    _ = R2 := Real.sq_sqrt hR20

/-- Under `cvAdmBall`, the frontier theorem's `hKR` binder holds at `R := circumR K`. -/
theorem cvAdmBall_subset_closedBall_circumR {K : Set (Ttc.Space n)} {R2 : Real}
    (h : Ttc.CVShaped.cvAdmBall n K R2) : K ⊆ Metric.closedBall 0 (circumR K) := by
  refine subset_closedBall_circumR ?_
  exact (Metric.isBounded_closedBall).subset h.2

/-- The three interface conditions, at the circumradius.  This is the `hrad` argument of
`Ttc.CVEffectiveSourceReference.cvShapedExpectedImplementationOfEffectiveFamily` at
`Adm := cvAdmBall`. -/
theorem circumR_interface_hrad :
    ∀ (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real),
      Ttc.CVShaped.cvAdmBall n K R2 → (circumR K) ^ 2 ≤ R2 :=
  fun _ _ _ h ↦ circumR_sq_le_of_cvAdmBall h

variable {A : Type*}

/-- **TTC's own call bodies, at the declared radius the `cvAdmBall` route needs.**

Identical to `Ttc.TtcCallBallAdmissible.cvAdmBall_callBody`; restated here so the two facts
a caller needs — the admissibility and the circumradius containment — are adjacent. -/
theorem cvAdmBall_callBody_circum
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    Ttc.CVShaped.cvAdmBall n (callBody atoms phi eps delta j)
      (callDeclaredR2 atoms phi eps delta j) ∧
    callBody atoms phi eps delta j ⊆
      Metric.closedBall 0 (circumR (callBody atoms phi eps delta j)) ∧
    (circumR (callBody atoms phi eps delta j)) ^ 2 ≤
      callDeclaredR2 atoms phi eps delta j := by
  have h := cvAdmBall_callBody atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j
  exact ⟨h, cvAdmBall_subset_closedBall_circumR h, circumR_sq_le_of_cvAdmBall h⟩

#print axioms circumR
#print axioms subset_closedBall_circumR
#print axioms circumR_le_of_subset_closedBall
#print axioms circumR_sq_le_of_cvAdmBall
#print axioms circumR_interface_hrad
#print axioms cvAdmBall_callBody_circum

end Ttc.TtcCircumRadius

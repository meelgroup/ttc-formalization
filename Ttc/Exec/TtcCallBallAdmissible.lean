import Ttc.Exec.TtcCallBodyBounded
import Ttc.Exec.TtcRadialGeometry

/-!
# TTC's call bodies at a quantitative declared radius

`Ttc.CVShaped.cvAdmBall n K R2` asks for `CVAdmissible K R2` **and** the quantitative
containment `K ⊆ closedBall 0 (Real.sqrt R2)`.  That is strictly more than
`Ttc.CVAdmissible`, which bounds only the second moment — and a convex body of finite
volume and finite second moment need not be bounded at all, so the extra conjunct is not
free at the interface's full generality.

It *is* free at TTC's own call bodies, because those are `roundBody`s of bounded polytopes.
The declared radius is then the containment radius itself rather than the second moment,
which `CVAdmissible` permits since it only asks for an upper bound; the `CVAdmissible`
half's fifth component comes from
`Ttc.TtcRadialGeometry.cvSecondMoment_le_sq_of_subset_closedBall`.

Declaring the larger radius inflates the per-call complexity shape.  That is the honest
direction, and it is also the paper's own accounting: `thm:runtime`'s per-polytope factor
is `R_i/gamma_i`, an outer-over-inner radius ratio, not a second moment.

## Main result

* `cvAdmBall_callBody` — the `hadm` binder of
  `Ttc.CVShaped.ttc_volume_estimate_of_cvShapedExpectedImplementationAt` at
  `Adm := cvAdmBall` and `R2j j := (callRadius … j) ^ 2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Ttc.TtcCallBallAdmissible

open MeasureTheory Metric Set
open Ttc.TtcCallBodyBounded
open Ttc.TtcRadialGeometry
open Ttc.TTCCVExpectedImplementation

variable {A : Type*} {n : Nat}

/-- The per-call declared squared radius: the square of the explicit outer radius of
`Ttc.TtcCallBodyBounded.callRadius`. -/
noncomputable def callDeclaredR2
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (j : Fin (toDNFd (preprocess atoms phi)).length) : Real :=
  (callRadius atoms phi eps delta j) ^ 2

/-- The second moment of a call body is under its declared squared radius. -/
theorem cvSecondMoment_callBody_le
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    Ttc.cvSecondMoment (callBody atoms phi eps delta j) ≤
      callDeclaredR2 atoms phi eps delta j := by
  have hadm := callBody_admissible atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j
  exact cvSecondMoment_le_sq_of_subset_closedBall hadm.1 hadm.2.2.1 hadm.2.2.2.1
    (callRadius_nonneg atoms phi eps delta hphi hvol j)
    (callBody_subset_closedBall atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j)

/-- **The `hadm` binder at `cvAdmBall`.** -/
theorem cvAdmBall_callBody
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    Ttc.CVShaped.cvAdmBall n (callBody atoms phi eps delta j)
      (callDeclaredR2 atoms phi eps delta j) := by
  have hadm := callBody_admissible atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j
  have hr0 : 0 ≤ callRadius atoms phi eps delta j :=
    callRadius_nonneg atoms phi eps delta hphi hvol j
  refine ⟨⟨hadm.1, hadm.2.1, hadm.2.2.1, hadm.2.2.2.1,
    cvSecondMoment_callBody_le atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j⟩, ?_⟩
  have hsqrt : Real.sqrt (callDeclaredR2 atoms phi eps delta j) =
      callRadius atoms phi eps delta j := by
    unfold callDeclaredR2
    exact Real.sqrt_sq hr0
  rw [hsqrt]
  exact callBody_subset_closedBall atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j

/-- `cvAdmBall` implies Cousins–Vempala's own admissibility: the `hAdm` binder of
`Ttc.CVEffectiveSourceReference.cvShapedExpectedImplementationOfEffectiveFamily`. -/
theorem cvAdmBall_imp_cvAdmissible :
    ∀ (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real),
      Ttc.CVShaped.cvAdmBall n K R2 → Ttc.CVAdmissible K R2 :=
  fun _ _ _ h ↦ h.1

/-- Under `cvAdmBall`, the declared radius really is an outer radius: `K ⊆ closedBall 0 R`
with `R = Real.sqrt R2`.  This is the frontier theorem's `hKR` binder. -/
theorem cvAdmBall_subset_closedBall
    {n : Nat} {K : Set (Ttc.Space n)} {R2 : Real}
    (h : Ttc.CVShaped.cvAdmBall n K R2) :
    K ⊆ Metric.closedBall 0 (Real.sqrt R2) := h.2

#print axioms callDeclaredR2
#print axioms cvSecondMoment_callBody_le
#print axioms cvAdmBall_callBody
#print axioms cvAdmBall_imp_cvAdmissible
#print axioms cvAdmBall_subset_closedBall

end Ttc.TtcCallBallAdmissible

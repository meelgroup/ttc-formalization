import Ttc.Exec.TtcCallBallAdmissible
import Ttc.Exec.CVValidInteriorBridge
import Ttc.Exec.TtcRadialGeometry

/-!
# Declaring the interior circumradius as the per-call radius

`Ttc.CVShaped.cvAdmBall` lets the declared squared radius `R2` be *any* upper bound on the
containment radius.  That freedom costs the consumer a monotonicity obligation: the
construction's effective constant is evaluated at the body's own radius, the interface's
envelope at `R2`, and closing the gap needs the envelope to be monotone in `R2`.

For the slow canonical construction that monotonicity is genuinely awkward — its phase count
`slowPhasesP n R2` appears *inside a logarithm and multiplied by itself* — so this file takes
the other route: pin the declared radius to the value the construction actually runs at.
Then `hrad` and `heff` are `le_refl` and no monotonicity is needed.

The construction runs on `interior K` (a convex set need not be Borel), so the pinned radius
is `circumR (interior K)`.  This is legitimate because `Ttc.CVAdmissible K R2` only asks that
`R2` bound the second moment **from above**, and
`cvSecondMoment K = cvSecondMoment (interior K) ≤ (circumR (interior K))^2` for convex `K`.

## Main results

* `cvAdmCircum` — the predicate.
* `cvAdmCircum_callBody` — TTC's own call bodies satisfy it, at their own interior
  circumradius.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Ttc.TtcCallCircumAdmissible

open MeasureTheory Metric Set
open Ttc.TtcCircumRadius
open Ttc.TtcCallBodyBounded
open Ttc.CVValidInteriorBridge
open Ttc.TTCCVExpectedImplementation
open Ttc.TtcRadialGeometry (cvSecondMoment_le_sq_of_subset_closedBall)

/-- The declared squared radius **is** the squared circumradius of the interior. -/
def cvAdmCircum : Ttc.CVShaped.AdmissiblePredicate :=
  fun _ K R2 ↦ CVAdmissible K R2 ∧ R2 = (circumR (interior K)) ^ 2

/-- The `hAdm` binder: `cvAdmCircum` implies Cousins–Vempala's own admissibility. -/
theorem cvAdmCircum_imp_cvAdmissible :
    ∀ (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real),
      cvAdmCircum n K R2 → CVAdmissible K R2 :=
  fun _ _ _ h ↦ h.1

/-- The `hrad` binder, at `radialR := fun n K ↦ circumR (interior K)`.  It is an equality,
so no monotonicity is involved. -/
theorem circumInterior_sq_le_of_cvAdmCircum :
    ∀ (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real),
      cvAdmCircum n K R2 → (circumR (interior K)) ^ 2 ≤ R2 :=
  fun _ _ _ h ↦ le_of_eq h.2.symm

variable {A : Type*} {n : Nat}

/-- The second moment of a convex body is under the square of its **interior**
circumradius. -/
theorem cvSecondMoment_le_sq_circumR_interior
    {K : Set (Ttc.Space n)} (hKc : Convex Real K) (hK0 : volume K ≠ 0)
    (hKtop : volume K ≠ ⊤) (hb : Bornology.IsBounded K) :
    Ttc.cvSecondMoment K ≤ (circumR (interior K)) ^ 2 := by
  have hint : Ttc.cvSecondMoment K = Ttc.cvSecondMoment (interior K) :=
    (cvSecondMoment_interior_eq_of_convex hKc).symm
  rw [hint]
  refine cvSecondMoment_le_sq_of_subset_closedBall (convex_interior_of_valid hKc) ?_ ?_
    (circumR_nonneg _) (subset_closedBall_circumR (isBounded_interior hb))
  · rw [volume_interior_eq_of_convex hKc]; exact hK0
  · exact volume_interior_ne_top hKtop

/-- **TTC's own call bodies satisfy `cvAdmCircum`**, at their own interior circumradius. -/
theorem cvAdmCircum_callBody
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    cvAdmCircum n (callBody atoms phi eps delta j)
      ((circumR (interior (callBody atoms phi eps delta j))) ^ 2) := by
  have hadm := callBody_admissible atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j
  have hb := isBounded_callBody atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j
  exact ⟨⟨hadm.1, hadm.2.1, hadm.2.2.1, hadm.2.2.2.1,
      cvSecondMoment_le_sq_circumR_interior hadm.1 hadm.2.2.1 hadm.2.2.2.1 hb⟩, rfl⟩

/-- Under `cvAdmCircum`, the interior is contained in the ball of the declared radius — the
frontier theorem's `hKR` binder, at the radius the construction runs at. -/
theorem cvAdmCircum_interior_subset_closedBall
    {K : Set (Ttc.Space n)} {R2 : Real} (h : cvAdmCircum n K R2)
    (hb : Bornology.IsBounded K) :
    interior K ⊆ Metric.closedBall 0 (circumR (interior K)) :=
  subset_closedBall_circumR (isBounded_interior hb)

#print axioms cvAdmCircum_imp_cvAdmissible
#print axioms circumInterior_sq_le_of_cvAdmCircum
#print axioms cvSecondMoment_le_sq_circumR_interior
#print axioms cvAdmCircum_callBody
#print axioms cvAdmCircum_interior_subset_closedBall

end Ttc.TtcCallCircumAdmissible

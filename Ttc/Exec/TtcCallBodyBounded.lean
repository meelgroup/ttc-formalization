/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVShapedExpectedImplementation
import Ttc.Exec.TtcRadialGeometry

/-!
# TTC's own volume-call bodies are bounded

`Ttc.CVShaped.ttc_volume_estimate_of_cvShapedExpectedImplementation` is parametrised by
an `AdmissiblePredicate` and carries the obligation

```
hadm : ∀ j, Adm n (callBody atoms phi eps (4 * delta / 5) j)
                  (callSecondMoment atoms phi eps (4 * delta / 5) j)
```

At `Adm := Ttc.CVShaped.cvAdm` this is `Ttc.CVShaped.cvAdm_callBody`.  This file
discharges it at the *strictly stronger* predicate `Ttc.CVShaped.cvAdmBounded`, which
adds `Bornology.IsBounded K` to Cousins–Vempala admissibility.

The strengthening is not available at the interface's full generality: a convex body of
finite volume and finite second moment can be unbounded, so `CVAdmissible K R2` does not
imply `Bornology.IsBounded K`.  It *is* available here, because TTC's per-call bodies are
normalised bounded polytopes.  The uniformly slow canonical volume construction needs a
hard outer radius `K ⊆ closedBall 0 R`, and `callBody_subset_closedBall` below supplies
one explicitly: `R = (algGamma …)⁻¹ · diam (region …)`, the dilated inscribed radius and
the dilated region's diameter, both data the run already computes.

No geometry is reproved.  The `CVAdmissible` half is
`Ttc.TTCCVExpectedImplementation.callBody_admissible` verbatim, and the enclosing ball is
`Ttc.roundBody_subset_closedBall` fed by the same hypothesis-discharging steps that
`Ttc.TtcRadialGeometry.ttcRadialR_callBody_le` already assembled for this exact body.
-/

set_option autoImplicit false

namespace Ttc.TtcCallBodyBounded

open MeasureTheory

variable {A : Type*} {n : Nat}

/-- The explicit outer radius of TTC's `j`th volume-call body: the dilated inscribed
radius `algGamma` inverted, times the diameter of the dilated region of the `j`th cube. -/
noncomputable def callRadius
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (j : Fin (toDNFd (preprocess atoms phi)).length) : Real :=
  (algGamma atoms phi eps delta)⁻¹ *
    Metric.diam (region (atomSet (algAtoms atoms phi eps delta))
      ((toDNFd (preprocess atoms phi)).get j))

theorem callRadius_def
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    callRadius atoms phi eps delta j =
      (algGamma atoms phi eps delta)⁻¹ *
        Metric.diam (region (atomSet (algAtoms atoms phi eps delta))
          ((toDNFd (preprocess atoms phi)).get j)) := rfl

/-- The explicit outer radius is nonnegative. -/
theorem callRadius_nonneg
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    0 ≤ callRadius atoms phi eps delta j :=
  mul_nonneg
    (inv_nonneg.mpr (algGamma_pos_of_isPositive atoms phi eps delta hphi hvol).le)
    Metric.diam_nonneg

/-- **The explicit enclosure.**  TTC's `j`th volume-call body is contained in the closed
ball of radius `callRadius` about the origin. -/
theorem callBody_subset_closedBall
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    Ttc.TTCCVExpectedImplementation.callBody atoms phi eps delta j ⊆
      Metric.closedBall 0 (callRadius atoms phi eps delta j) := by
  have hmem : (toDNFd (preprocess atoms phi)).get j ∈ toDNFd (preprocess atoms phi) :=
    List.get_mem _ j
  have hgamma : 0 < algGamma atoms phi eps delta :=
    algGamma_pos_of_isPositive atoms phi eps delta hphi hvol
  have hballK := ball_subset_algCen atoms phi eps delta ⟨_, hmem⟩
  have hbddSol := algAtoms_bdd atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hbdd : Bornology.IsBounded (region (atomSet (algAtoms atoms phi eps delta))
      ((toDNFd (preprocess atoms phi)).get j)) :=
    isBounded_region_of_isBounded_sol (toDNFd_isDNFOf _) hbddSol hmem
  exact Ttc.roundBody_subset_closedBall hgamma hballK hbdd

/-- TTC's `j`th volume-call body is a bounded set. -/
theorem isBounded_callBody
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    Bornology.IsBounded
      (Ttc.TTCCVExpectedImplementation.callBody atoms phi eps delta j) :=
  Metric.isBounded_closedBall.subset
    (callBody_subset_closedBall atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j)

/-- **Deliverable.**  The `hadm` obligation of
`Ttc.CVShaped.ttc_volume_estimate_of_cvShapedExpectedImplementation` at the strengthened
predicate `Ttc.CVShaped.cvAdmBounded`. -/
theorem cvAdmBounded_callBody
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    Ttc.CVShaped.cvAdmBounded n
      (Ttc.TTCCVExpectedImplementation.callBody atoms phi eps delta j)
      (Ttc.TTCCVExpectedImplementation.callSecondMoment atoms phi eps delta j) :=
  ⟨Ttc.TTCCVExpectedImplementation.callBody_admissible atoms phi eps delta
      h_eps_pos h_eps_le hn hphi hvol j,
   isBounded_callBody atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j⟩

/-- The strengthened predicate implies Cousins–Vempala admissibility.  This is the
`hAdm` binder of
`Ttc.CVEffectiveSourceReference.cvShapedExpectedImplementationOfEffectiveFamily`. -/
theorem cvAdmBounded_imp_cvAdmissible :
    ∀ (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real),
      Ttc.CVShaped.cvAdmBounded n K R2 → Ttc.CVAdmissible K R2 :=
  fun _ _ _ h ↦ h.1

#print axioms callRadius_def
#print axioms callRadius_nonneg
#print axioms callBody_subset_closedBall
#print axioms isBounded_callBody
#print axioms cvAdmBounded_callBody
#print axioms cvAdmBounded_imp_cvAdmissible

end Ttc.TtcCallBodyBounded

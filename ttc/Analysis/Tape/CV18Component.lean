/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Constants
import ttc.Analysis.CommunityCV18VolumeProvider

/-!
# CV18 on a component: the old model's volume law

In one step of the sealed program, CV18 runs on a component `P` normalised by its inscribed
ball, with membership decided by checking the normalised facets.  Its estimate has the law
of the old model's CV18 call on `P` (`CommunityCV18.law`, `vlaw_cv18_component`): the
membership routine is the old `query P`, the parameters are the old `params`, and the
charged CV18 program has the community program's output law
(`ChargedCV18.cv18Program_runEstimate_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {n : ℕ}

/-- The normalised facets' offsets, computed. -/
abbrev cv18Off (P : ttc.PolytopeData n) : Fin P.presentation.facetCount → Num ℝ :=
  (cv18Offsets (loaded P)).val

theorem cv18Off_get (P : ttc.PolytopeData n) (j : Fin P.presentation.facetCount) :
    (cv18Off P j).get = P.cv18OffsetsProg.value j := by
  dsimp only [cv18Off, cv18Offsets]
  simp only [val_forEach, Charged.val_bind, A.sub, A.div, get_dot, Num.get_sub, Num.get_div]
  simp [ttc.PolytopeData.cv18OffsetsProg, ttc.Counted.forEach, ttc.Counted.dot_value,
    ttc.Counted.sub, ttc.Counted.div, dotProduct]

/-- **The sealed membership routine on the normalised component is the old `query P`.** -/
theorem memberOracle_cv18 (P : ttc.PolytopeData n) :
    memberOracle (allFacets P.presentation.facetCount (loaded P).normal (cv18Off P)) =
      ttc.CommunityCV18.query P := by
  funext y
  rw [Bool.eq_iff_iff, memberOracle, val_allFacets_iff, ttc.CommunityCV18.query,
    ttc.HalfspacePresentation.memberProg, ttc.Counted.allFacets_value]
  simp only [ttc.PolytopeData.cv18Presentation, cv18Off_get, ofPt, get_sealVector, loaded]
  simp [dotProduct]

/-- **CV18 on a component has the old model's volume law.** -/
theorem vlaw_cv18_component (hn : 3 ≤ n) (P : ttc.PolytopeData n) (eta delta : ℝ)
    (h : ttc.CommunityCV18.AdmissibleCV18Request eta delta) (eps roundness p : Num ℝ)
    (he : eps.get = eta / 2) (hr : roundness.get = ttc.CommunityCV18.roundness P)
    (hp : p.get = delta / 2) (b : ℕ) :
    (vlaw (cv18T n (allFacets P.presentation.facetCount (loaded P).normal (cv18Off P))
        eps roundness p) b).map (Option.map Num.get) =
      (ttc.CommunityCV18.law hn P eta delta h).map some := by
  have key := vlaw_cv18T (ttc.CommunityCV18.params hn P eta delta h)
    (allFacets P.presentation.facetCount (loaded P).normal (cv18Off P))
    (memberMP_allFacets _ _ _) eps roundness p he hr hp b
  erw [memberOracle_cv18] at key
  refine key.trans ?_
  rw [ttc.CommunityCV18.law, ttc.CommunityCV18.algorithm]
  exact congrArg (Measure.map some) (ttc.ChargedCV18.cv18Program_runEstimate_eq
    (ttc.CommunityCV18.params hn P eta delta h) (ttc.CommunityCV18.input P)
    (ttc.CommunityCV18.oracle P))

end ttc.Tape

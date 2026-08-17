/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Ttc.Exec.BddFromPos
import Ttc.Exec.CVEffectiveTotalise

/-!
# `Exec/CVValidBounded`: `CVValidInput` already implies `Bornology.IsBounded`

`Ttc.CVEffectiveTotalise.CVValidInput` (`Exec/CVEffectiveTotalise`) states

```
0 < a.2.1 ∧ 0 < a.2.2 ∧ a.2.2 < 1 ∧ Convex Real a.1 ∧
  Metric.ball (0 : Ttc.Space n) 1 ⊆ a.1 ∧ volume a.1 ≠ ⊤
```

and in particular does **not** state `Bornology.IsBounded a.1`, which
`Ttc.TtcCircumRadius.subset_closedBall_circumR`,
`Ttc.CVValidInteriorBridge.circumR_interior_le` and
`Ttc.CVValidInteriorBridge.validInput_interior_facts` all want.  It does not need to:
boundedness is a *consequence* of the last three conjuncts.

## Nothing new is proved here

The mathematical content is already in the repository, as
`Ttc.isBounded_of_convex_of_interior_of_volume_ne_top` (`Exec/BddFromPos`, the "step 4"
crux of that file):

> a convex subset of `Ttc.Space n` with an interior point and finite volume is bounded

proved there contrapositively by sliding balls of a fixed radius along a segment
(`Ttc.ball_combo_subset_of_convex`, `Ttc.nsmul_volume_ball_le_of_convex_of_not_isBounded`).
Mathlib has no such lemma; `AUDIT.md` §1h records the same fact as the reason the headline
chain's `hbdd` was derived rather than dropped.

So this file is a two-step restatement.  The only gap between the two hypothesis sets is
the interior point, and `Metric.ball (0 : Ttc.Space n) 1 ⊆ a.1` supplies it: the unit ball
is open and contains `0`, so `0 ∈ interior a.1`.

## `hn : 1 ≤ n` is not needed

`Metric.mem_ball_self one_pos` produces the interior point at every `n`, `n = 0` included
— there `Ttc.Space 0` is a single point and every set is bounded anyway.  Neither theorem
below carries a dimension hypothesis.

## Main results

* `Ttc.CVValidBounded.isBounded_of_convex_of_ball_subset_of_volume_ne_top` — the
  ball-shaped form of the `Exec/BddFromPos` crux;
* `Ttc.CVEffectiveTotalise.CVValidInput.isBounded` — the same, read off a `CVValidInput`,
  usable as `h.isBounded`.
-/

set_option autoImplicit false

namespace Ttc.CVValidBounded

open MeasureTheory Set

open scoped ENNReal

variable {n : Nat}

/-- **A convex set containing the unit ball and of finite volume is bounded.**

Immediate from `Ttc.isBounded_of_convex_of_interior_of_volume_ne_top` (`Exec/BddFromPos`),
whose interior hypothesis is met at `0`: `Metric.ball 0 1` is open, contains `0`, and is
contained in `K`, so `0 ∈ interior K`.  No hypothesis on `n`. -/
theorem isBounded_of_convex_of_ball_subset_of_volume_ne_top {K : Set (Ttc.Space n)}
    (hK : Convex Real K) (hball : Metric.ball (0 : Ttc.Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) : Bornology.IsBounded K :=
  Ttc.isBounded_of_convex_of_interior_of_volume_ne_top hK
    ⟨0, interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self one_pos)⟩ hfin

end Ttc.CVValidBounded

namespace Ttc.CVEffectiveTotalise

open MeasureTheory

open scoped ENNReal

variable {n : Nat}

/-- **`CVValidInput` implies `Bornology.IsBounded`.**

The convexity, unit-ball and finite-volume conjuncts of `CVValidInput` are exactly the
hypotheses of `Ttc.CVValidBounded.isBounded_of_convex_of_ball_subset_of_volume_ne_top`;
the three numeric conjuncts are unused.  Stated in this namespace so that a
`h : CVValidInput a` can be spent as `h.isBounded`.  No hypothesis on `n`. -/
theorem CVValidInput.isBounded {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) : Bornology.IsBounded a.1 := by
  obtain ⟨-, -, -, hK, hball, hfin⟩ := h
  exact Ttc.CVValidBounded.isBounded_of_convex_of_ball_subset_of_volume_ne_top hK hball hfin

end Ttc.CVEffectiveTotalise

/-! ## Axiom profile -/

#print axioms Ttc.CVValidBounded.isBounded_of_convex_of_ball_subset_of_volume_ne_top
#print axioms Ttc.CVEffectiveTotalise.CVValidInput.isBounded

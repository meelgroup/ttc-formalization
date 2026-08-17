import Ttc.Exec.CVEffectiveTotalise
import Ttc.Exec.TtcCircumRadius
import Ttc.Volume.CVMomentInputBridge
import Arlib.Convexity.GaussianCooling.InteriorBridge

/-!
# The interior bridge, packaged for `CVValidInput`

`Ttc.CVEffectiveTotalise.CVValidInput` is the predicate guarding the accuracy field of
`Ttc.CVEffectiveSourceReference.EffectiveSourcePublicReferenceTVCertificates`:

```
0 < eps ∧ 0 < p ∧ p < 1 ∧ Convex ℝ K ∧ ball 0 1 ⊆ K ∧ volume K ≠ ⊤.
```

It deliberately carries **no** `MeasurableSet K`, and must not: a convex set need not be
Borel (an open ball together with a non-Borel subset of its bounding sphere is convex and
not Borel — `Ttc/Volume/CousinsVempala.lean:819` records this), so the hypothesis
`∀ K, Convex ℝ K → … → MeasurableSet K` would be *false* and any construction carrying it
would be vacuous.

The slow canonical volume construction, on the other hand, needs `MeasurableSet K` before
it can even define its schedule.  The repository's standing solution (`AUDIT.md` §0n(e),
`Arlib/Convexity/GaussianCooling/InteriorBridge.lean`) is to run the construction on
`interior K` — open, hence Borel — and transport back, which is lossless because a convex
set's frontier is Haar-null (`Convex.addHaar_frontier`).

**This file packages that transport for `CVValidInput`**, so the assembly never needs a
`dite` on measurability.  Nothing here is new mathematics: item 5 below is
`Ttc.CV.volume_interior_eq`, already proved in `Ttc/Volume/CousinsVempala.lean:840`; the
`ae`-level statement it rests on is `Arlib.GaussianCooling.interior_ae_eq`.

## Main results

* `measurableSet_interior`, `convex_interior_of_valid`, `ball_subset_interior_of_valid`,
  `volume_interior_ne_top` — the four cheap inheritances.
* `volume_interior_eq_of_convex` (+ `toReal_volume_interior_eq_of_convex`) — the
  load-bearing one: the reported number is unchanged.
* `isBounded_interior`, `circumR_interior_le` — the geometry the frontier theorem's
  `hKR` binder consumes.
* `validInput_interior_facts` — **the bundle**: exactly the list the assembly needs to
  instantiate the frontier theorem at `interior a.1` and transport back to `a.1`.
* `uniformOn_interior_eq_of_convex`, `cvSecondMoment_interior_eq_of_convex`,
  `cvAdmBall_interior` — the same transport at the `cvAdmBall` admissibility predicate.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Ttc.CVValidInteriorBridge

open MeasureTheory Metric Set

variable {n : Nat}

/-! ## 1–4.  The cheap inheritances -/

/-- **The interior is measurable.**  This is the single fact `CVValidInput` cannot supply
about `a.1` itself, and the entire reason this file exists. -/
theorem measurableSet_interior (K : Set (Ttc.Space n)) : MeasurableSet (interior K) :=
  isOpen_interior.measurableSet

/-- **Convexity is inherited by the interior** (`Convex.interior`). -/
theorem convex_interior_of_valid {K : Set (Ttc.Space n)} (hK : Convex Real K) :
    Convex Real (interior K) :=
  hK.interior

/-- **The unit ball survives passage to the interior**, because the ball is open and the
interior is the largest open subset. -/
theorem ball_subset_interior_of_valid {K : Set (Ttc.Space n)}
    (hball : Metric.ball (0 : Ttc.Space n) 1 ⊆ K) :
    Metric.ball (0 : Ttc.Space n) 1 ⊆ interior K :=
  interior_maximal hball Metric.isOpen_ball

/-- **Finiteness of the volume is inherited**, by monotonicity along `interior_subset`. -/
theorem volume_interior_ne_top {K : Set (Ttc.Space n)} (hfin : volume K ≠ ⊤) :
    volume (interior K) ≠ ⊤ :=
  ((measure_mono interior_subset).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne

/-! ## 5.  The load-bearing one: the reported number is unchanged -/

/-- **`vol(interior K) = vol(K)` for convex `K`.**

This is the fact that makes the whole interior route *lossless*: the construction runs on
`interior a.1`, which is measurable, and the number it reports is literally the number the
interface asks about.

No new proof — this is `Ttc.CV.volume_interior_eq`
(`Ttc/Volume/CousinsVempala.lean:840`), which goes through `Convex.addHaar_frontier`.
Note that no `ball 0 1 ⊆ K` hypothesis is needed: the identity holds for every convex set,
degenerate ones included (both sides are then `0`). -/
theorem volume_interior_eq_of_convex {K : Set (Ttc.Space n)} (hK : Convex Real K) :
    volume (interior K) = volume K :=
  Ttc.CV.volume_interior_eq hK

/-- The `toReal` corollary of `volume_interior_eq_of_convex`, which is the form the
accuracy field's `|V̂ - vol K| ≤ eps * vol K` statement reads the volume in. -/
theorem toReal_volume_interior_eq_of_convex {K : Set (Ttc.Space n)} (hK : Convex Real K) :
    (volume (interior K)).toReal = (volume K).toReal := by
  rw [volume_interior_eq_of_convex hK]

/-! ## 6–7.  The geometry the frontier theorem's `hKR` binder consumes -/

/-- **Boundedness is inherited by the interior.** -/
theorem isBounded_interior {K : Set (Ttc.Space n)} (hb : Bornology.IsBounded K) :
    Bornology.IsBounded (interior K) :=
  hb.subset interior_subset

/-- **The circumradius does not grow under passage to the interior.**

`K` sits in `closedBall 0 (circumR K)`, hence so does `interior K`, and `circumR` is
minimal among containing radii. -/
theorem circumR_interior_le {K : Set (Ttc.Space n)} (hb : Bornology.IsBounded K) :
    Ttc.TtcCircumRadius.circumR (interior K) ≤ Ttc.TtcCircumRadius.circumR K :=
  Ttc.TtcCircumRadius.circumR_le_of_subset_closedBall
    (Ttc.TtcCircumRadius.circumR_nonneg K)
    (interior_subset.trans (Ttc.TtcCircumRadius.subset_closedBall_circumR hb))

/-! ## 8.  The bundle -/

/-- **Everything the assembly needs, from `CVValidInput` plus boundedness.**

Given a valid, bounded input `a = (K, eps, p)`, the body `interior a.1` is measurable,
convex, contains the unit ball, has finite volume, has *the same* volume as `a.1` (so the
estimate transports verbatim), is contained in the closed ball of its own circumradius (the
frontier theorem's `hKR` binder), and that circumradius is no larger than `circumR a.1` (so
the expected-cost certificate, which is increasing in the radius, transports too).

This is exactly the list the assembly needs to instantiate the frontier theorem at
`interior a.1` and then transport its conclusion back to `a.1`, with no `dite` on
measurability anywhere. -/
theorem validInput_interior_facts
    {n : Nat} {a : Ttc.CVAdaptive.VolumeInput n}
    (h : Ttc.CVEffectiveTotalise.CVValidInput a) (hb : Bornology.IsBounded a.1) :
    MeasurableSet (interior a.1) ∧
    Convex Real (interior a.1) ∧
    Metric.ball (0 : Ttc.Space n) 1 ⊆ interior a.1 ∧
    volume (interior a.1) ≠ ⊤ ∧
    (volume (interior a.1)).toReal = (volume a.1).toReal ∧
    interior a.1 ⊆ Metric.closedBall 0 (Ttc.TtcCircumRadius.circumR (interior a.1)) ∧
    Ttc.TtcCircumRadius.circumR (interior a.1) ≤ Ttc.TtcCircumRadius.circumR a.1 := by
  obtain ⟨-, -, -, hconv, hball, hfin⟩ := h
  refine ⟨measurableSet_interior a.1, convex_interior_of_valid hconv,
    ball_subset_interior_of_valid hball, volume_interior_ne_top hfin,
    toReal_volume_interior_eq_of_convex hconv, ?_, circumR_interior_le hb⟩
  exact Ttc.TtcCircumRadius.subset_closedBall_circumR (isBounded_interior hb)

/-! ## 9.  The same transport at `cvAdmBall` -/

/-- **The uniform law does not see the frontier.**  The exact mirror of
`Ttc.CVAdaptive.uniformOn_closure_eq_of_convex`, with `Arlib.GaussianCooling.interior_ae_eq`
in place of `Arlib.ae_eq_closure_of_convex`. -/
theorem uniformOn_interior_eq_of_convex {K : Set (Ttc.Space n)} (hK : Convex Real K) :
    Arlib.uniformOn volume (interior K) = Arlib.uniformOn volume K := by
  rw [Arlib.uniformOn_def, Arlib.uniformOn_def, volume_interior_eq_of_convex hK,
    Measure.restrict_congr_set (Arlib.GaussianCooling.interior_ae_eq hK)]

/-- **The second moment is unchanged by passage to the interior**, since it is an integral
against `uniformOn volume K`. -/
theorem cvSecondMoment_interior_eq_of_convex {K : Set (Ttc.Space n)} (hK : Convex Real K) :
    Ttc.cvSecondMoment (interior K) = Ttc.cvSecondMoment K := by
  unfold Ttc.cvSecondMoment
  rw [uniformOn_interior_eq_of_convex hK]

/-- **`cvAdmBall` is inherited by the interior.**  Every one of the five `CVAdmissible`
fields transports (convexity, the unit ball, and — through
`volume_interior_eq_of_convex` and `cvSecondMoment_interior_eq_of_convex` — the two volume
guards and the moment bound), and the containment half is `interior_subset`. -/
theorem cvAdmBall_interior {K : Set (Ttc.Space n)} {R2 : Real}
    (h : Ttc.CVShaped.cvAdmBall n K R2) :
    Ttc.CVShaped.cvAdmBall n (interior K) R2 := by
  obtain ⟨⟨hconv, hball, hK0, hKtop, hmoment⟩, hsub⟩ := h
  refine ⟨⟨convex_interior_of_valid hconv, ball_subset_interior_of_valid hball, ?_, ?_, ?_⟩,
    interior_subset.trans hsub⟩
  · rw [volume_interior_eq_of_convex hconv]; exact hK0
  · rw [volume_interior_eq_of_convex hconv]; exact hKtop
  · rw [cvSecondMoment_interior_eq_of_convex hconv]; exact hmoment

section AxiomCheck

#print axioms Ttc.CVValidInteriorBridge.measurableSet_interior
#print axioms Ttc.CVValidInteriorBridge.convex_interior_of_valid
#print axioms Ttc.CVValidInteriorBridge.ball_subset_interior_of_valid
#print axioms Ttc.CVValidInteriorBridge.volume_interior_ne_top
#print axioms Ttc.CVValidInteriorBridge.volume_interior_eq_of_convex
#print axioms Ttc.CVValidInteriorBridge.toReal_volume_interior_eq_of_convex
#print axioms Ttc.CVValidInteriorBridge.isBounded_interior
#print axioms Ttc.CVValidInteriorBridge.circumR_interior_le
#print axioms Ttc.CVValidInteriorBridge.validInput_interior_facts
#print axioms Ttc.CVValidInteriorBridge.uniformOn_interior_eq_of_convex
#print axioms Ttc.CVValidInteriorBridge.cvSecondMoment_interior_eq_of_convex
#print axioms Ttc.CVValidInteriorBridge.cvAdmBall_interior

end AxiomCheck

end Ttc.CVValidInteriorBridge

import Ttc.Exec.CVEffectiveSourceReferenceFamily

/-!
# Totalising a partial certificate family

`Ttc.CVEffectiveSourceReference.EffectiveSourcePublicReferenceTVCertificates` demands the
five administrative fields, the `1/40` path-TV bound and the expected-cost budget for
**every** input `a = (K, eps, p)`, while the `4/5` accuracy floor is demanded only on the
valid branch.  A construction, by contrast, only ever produces a law when the geometry is
good: the slow canonical route needs `MeasurableSet K`, `Convex ℝ K`, `ball 0 1 ⊆ K` and
`volume K ≠ ⊤` before it can even define its schedule.

The existing radial-log audit
(`Ttc.CVGaussianHybridWeightedCertificate.operationalColdHotRadialAuditOfOneRunCertificates`)
papers over this by requiring a one-run certificate at every input, including inputs where
no accurate estimate can exist — on a non-convex `K` of finite volume, the `4/5` field of
`SourceReferenceTVOneRunCertificate` is simply unobtainable.  So that constructor cannot be
invoked by any real construction.

This file supplies the missing step, once and generically: given certificates on the valid
inputs only, replace the law by a point mass and the cost and value by `0` everywhere else.
Every total field then holds on the degenerate branch for a trivial reason — a Dirac mass
is a probability measure, `TVLe μ μ 0` weakens to the `1/40` budget, and a zero cost is
under any budget — and the accuracy field is never asked about those inputs.

## Main results

* `CVValidInput` — the hypotheses of the `accuracy` field, as one predicate.
* `totaliseActual` / `totaliseCost` / `totaliseValue` — the three replacements.
* `effectiveSourcePublicReferenceTVCertificates_of_valid` — the glue.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Ttc.CVEffectiveTotalise

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability
open Ttc.CVEffectiveSourceReference
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSourceReferenceTVCapstone
open scoped ENNReal Classical

variable {n : Nat}

/-- Exactly the six hypotheses guarding the `accuracy` field of
`Ttc.CVEffectiveSourceReference.EffectiveSourcePublicReferenceTVCertificates`, bundled as
one predicate on the input. -/
def CVValidInput (a : Ttc.CVAdaptive.VolumeInput n) : Prop :=
  0 < a.2.1 ∧ 0 < a.2.2 ∧ a.2.2 < 1 ∧ Convex Real a.1 ∧
    Metric.ball (0 : Ttc.Space n) 1 ⊆ a.1 ∧ volume a.1 ≠ ⊤

/-- The law, replaced by a point mass off the valid branch. -/
noncomputable def totaliseActual
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    [∀ a, MeasurableSpace (Omega a)] [∀ a, Nonempty (Omega a)]
    (law : ∀ a, Measure (Omega a)) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measure (Omega a) :=
  if CVValidInput a then law a else Measure.dirac (Classical.arbitrary (Omega a))

/-- The recorded query cost, replaced by `0` off the valid branch. -/
noncomputable def totaliseCost
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    (cost : ∀ a, Omega a → ENNReal) (a : Ttc.CVAdaptive.VolumeInput n) :
    Omega a → ENNReal :=
  if CVValidInput a then cost a else fun _ ↦ 0

/-- The estimate, replaced by `0` off the valid branch. -/
noncomputable def totaliseValue
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    (value : ∀ a, Omega a → Real) (a : Ttc.CVAdaptive.VolumeInput n) :
    Omega a → Real :=
  if CVValidInput a then value a else fun _ ↦ 0

@[simp] theorem totaliseActual_of_valid
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    [∀ a, MeasurableSpace (Omega a)] [∀ a, Nonempty (Omega a)]
    (law : ∀ a, Measure (Omega a)) {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) : totaliseActual law a = law a := by
  simp [totaliseActual, h]

@[simp] theorem totaliseCost_of_valid
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    (cost : ∀ a, Omega a → ENNReal) {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) : totaliseCost cost a = cost a := by
  simp [totaliseCost, h]

@[simp] theorem totaliseValue_of_valid
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    (value : ∀ a, Omega a → Real) {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) : totaliseValue value a = value a := by
  simp [totaliseValue, h]

/-- **The glue.**

From one-run reference-TV certificates on the valid inputs only, plus measurability of the
cost and value on all inputs, the totalised family satisfies every field of
`EffectiveSourcePublicReferenceTVCertificates`.

The degenerate branch is genuinely trivial and is not hiding an assumption: the law is a
point mass (hence a probability measure, and at TV distance `0` from itself), the cost is
identically `0` (hence under any budget), and the `4/5` accuracy field is guarded by
exactly `CVValidInput`, so it is never asked there. -/
theorem effectiveSourcePublicReferenceTVCertificates_of_valid
    (effective : Ttc.CVAdaptive.VolumeInput n → Real)
    (radialR : Set (Ttc.Space n) → Real)
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    [∀ a, MeasurableSpace (Omega a)] [∀ a, Nonempty (Omega a)]
    (law ref : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal) (value : ∀ a, Omega a → Real)
    (hcost : ∀ a, Measurable (cost a)) (hvalue : ∀ a, Measurable (value a))
    (hvalid : ∀ a, CVValidInput a →
      SourceReferenceTVOneRunCertificate (law a) (ref a) (cost a) (value a)
        (effective a) n (radialR a.1) a.2.1
        ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal)) :
    EffectiveSourcePublicReferenceTVCertificates n effective radialR Omega
      (totaliseActual law) (totaliseActual ref) (totaliseCost cost)
      (totaliseValue value) where
  actual_probability a := by
    by_cases h : CVValidInput a
    · simpa [totaliseActual, h] using (hvalid a h).actual_probability
    · simpa [totaliseActual, h] using Measure.dirac.isProbabilityMeasure
  reference_probability a := by
    by_cases h : CVValidInput a
    · simpa [totaliseActual, h] using (hvalid a h).reference_probability
    · simpa [totaliseActual, h] using Measure.dirac.isProbabilityMeasure
  cost_measurable a := by
    by_cases h : CVValidInput a
    · simpa [totaliseCost, h] using hcost a
    · simpa [totaliseCost, h] using (measurable_const : Measurable (fun _ : Omega a ↦ (0 : ENNReal)))
  value_measurable a := by
    by_cases h : CVValidInput a
    · simpa [totaliseValue, h] using hvalue a
    · simpa [totaliseValue, h] using (measurable_const : Measurable (fun _ : Omega a ↦ (0 : Real)))
  path_tv a := by
    by_cases h : CVValidInput a
    · simpa [totaliseActual, h] using (hvalid a h).path_tv
    · simp only [totaliseActual, if_neg h]
      exact Arlib.TVLe.mono (Arlib.TVLe.refl _) (by simp)
  reference_expected_queries a := by
    by_cases h : CVValidInput a
    · simpa [totaliseActual, totaliseCost, h] using
        (hvalid a h).reference_expected_queries
    · simp [totaliseActual, totaliseCost, h]
  accuracy K eps p heps hp hp1 hKc hball hfin := by
    have h : CVValidInput ((K, eps, p) : Ttc.CVAdaptive.VolumeInput n) :=
      ⟨heps, hp, hp1, hKc, hball, hfin⟩
    simpa [totaliseActual, totaliseValue, h] using (hvalid _ h).accuracy

/-! ## The existential form

A construction does not hand back a named reference law: the frontier theorem concludes
`∃ reference, SourceReferenceTVOneRunCertificate …`, and only on the valid branch.  The
consumer, by contrast, needs a *function* `∀ a, Measure (Omega a)`.  Choosing under a
guard is the standard `dite` + `Classical.choose` move, done once here so no caller has to
repeat it. -/

/-- The reference law chosen from the per-input existential, with a point mass off the
valid branch. -/
noncomputable def chosenReference
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    [∀ a, MeasurableSpace (Omega a)] [∀ a, Nonempty (Omega a)]
    {P : ∀ a, Measure (Omega a) → Prop}
    (H : ∀ a, CVValidInput a → ∃ r : Measure (Omega a), P a r)
    (a : Ttc.CVAdaptive.VolumeInput n) : Measure (Omega a) :=
  if h : CVValidInput a then Classical.choose (H a h)
  else Measure.dirac (Classical.arbitrary (Omega a))

theorem chosenReference_spec
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    [∀ a, MeasurableSpace (Omega a)] [∀ a, Nonempty (Omega a)]
    {P : ∀ a, Measure (Omega a) → Prop}
    (H : ∀ a, CVValidInput a → ∃ r : Measure (Omega a), P a r)
    {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) :
    P a (chosenReference H a) := by
  simp only [chosenReference, dif_pos h]
  exact Classical.choose_spec (H a h)

/-- **The glue, in the form a construction actually produces.**

Per-input *existential* one-run certificates on the valid inputs give a total certificate
family, with the reference law chosen once and for all. -/
theorem effectiveSourcePublicReferenceTVCertificates_of_exists
    (effective : Ttc.CVAdaptive.VolumeInput n → Real)
    (radialR : Set (Ttc.Space n) → Real)
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    [∀ a, MeasurableSpace (Omega a)] [∀ a, Nonempty (Omega a)]
    (law : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal) (value : ∀ a, Omega a → Real)
    (hcost : ∀ a, Measurable (cost a)) (hvalue : ∀ a, Measurable (value a))
    (H : ∀ a, CVValidInput a →
      ∃ r : Measure (Omega a),
        SourceReferenceTVOneRunCertificate (law a) r (cost a) (value a)
          (effective a) n (radialR a.1) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal)) :
    EffectiveSourcePublicReferenceTVCertificates n effective radialR Omega
      (totaliseActual law) (totaliseActual (chosenReference H)) (totaliseCost cost)
      (totaliseValue value) :=
  effectiveSourcePublicReferenceTVCertificates_of_valid effective radialR law
    (chosenReference H) cost value hcost hvalue
    (fun a h ↦ chosenReference_spec H h)

#print axioms totaliseActual
#print axioms totaliseCost
#print axioms totaliseValue
#print axioms effectiveSourcePublicReferenceTVCertificates_of_valid
#print axioms chosenReference
#print axioms chosenReference_spec
#print axioms effectiveSourcePublicReferenceTVCertificates_of_exists

end Ttc.CVEffectiveTotalise

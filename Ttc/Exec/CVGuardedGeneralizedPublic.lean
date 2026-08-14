import Ttc.Exec.CVGeneralPolynomialCutoffCapstone
import Ttc.Volume.CVBodyRegularization

/-! Guarding proof-dependent closed-body execution laws on arbitrary public inputs. -/

namespace Ttc.CVGuardedGeneralizedPublic

open MeasureTheory ProbabilityTheory Metric Set
open Ttc.CVGeneralPolynomialCutoffCapstone
open scoped ENNReal Classical

variable {n : Nat}

abbrev VolumeInput (n : Nat) := Ttc.CVAdaptive.VolumeInput n

/-- The precise closed-body hypotheses available after public-input regularization. -/
def ClosedAdmissible (a : VolumeInput n) : Prop :=
  0 < a.2.1 ∧ 0 < a.2.2 ∧ a.2.2 < 1 ∧
    Convex Real a.1 ∧ IsClosed a.1 ∧ Bornology.IsBounded a.1 ∧
    0 < volume a.1 ∧ closedBall (0 : Ttc.Space n) 1 ⊆ a.1 ∧ volume a.1 ≠ ⊤

/-- Run closed-body code on the closure of the public body. -/
def regularizedInput (a : VolumeInput n) : VolumeInput n :=
  (closure a.1, a.2.1, a.2.2)

variable (X : VolumeInput n → Type) [∀ a, MeasurableSpace (X a)]
  [∀ a, Inhabited (X a)]

/-- Totalize a proof-dependent law by a Dirac law off the closed admissible branch. -/
noncomputable def guardedClosedLaw
    (rawLaw : ∀ a, ClosedAdmissible a → Measure (X a))
    (a : VolumeInput n) : Measure (X (regularizedInput a)) :=
  if h : ClosedAdmissible (regularizedInput a) then rawLaw (regularizedInput a) h
  else Measure.dirac default

instance guardedClosedLaw.isProbabilityMeasure
    (rawLaw : ∀ a, ClosedAdmissible a → Measure (X a))
    [hprob : ∀ a h, IsProbabilityMeasure (rawLaw a h)] (a : VolumeInput n) :
    IsProbabilityMeasure (guardedClosedLaw X rawLaw a) := by
  unfold guardedClosedLaw
  split <;> infer_instance

noncomputable def guardedClosedCost
    (rawCost : ∀ a, ClosedAdmissible a → X a → ENNReal)
    (a : VolumeInput n) : X (regularizedInput a) → ENNReal :=
  if h : ClosedAdmissible (regularizedInput a) then rawCost (regularizedInput a) h
  else fun _ ↦ 0

noncomputable def guardedClosedValue
    (rawValue : ∀ a, ClosedAdmissible a → X a → Real)
    (a : VolumeInput n) : X (regularizedInput a) → Real :=
  if h : ClosedAdmissible (regularizedInput a) then rawValue (regularizedInput a) h
  else fun _ ↦ 0

theorem measurable_guardedClosedCost
    (rawCost : ∀ a, ClosedAdmissible a → X a → ENNReal)
    (hcost : ∀ a h, Measurable (rawCost a h)) (a : VolumeInput n) :
    Measurable (guardedClosedCost X rawCost a) := by
  unfold guardedClosedCost
  split
  · exact hcost _ _
  · fun_prop

theorem measurable_guardedClosedValue
    (rawValue : ∀ a, ClosedAdmissible a → X a → Real)
    (hvalue : ∀ a h, Measurable (rawValue a h)) (a : VolumeInput n) :
    Measurable (guardedClosedValue X rawValue a) := by
  unfold guardedClosedValue
  split
  · exact hvalue _ _
  · fun_prop

/-- Guarded one-run certificate.  Invalid inputs are lawful and cost zero.  On public
admissible inputs, closure supplies the exact closed-body hypotheses and preserves
Lebesgue volume. -/
theorem guardedGeneralizedPublicOneRunCertificates
    (hn : 1 ≤ n)
    (rawEnvelope : VolumeInput n → Real)
    (rawLaw : ∀ a, ClosedAdmissible a → Measure (X a))
    [∀ a h, IsProbabilityMeasure (rawLaw a h)]
    (rawCost : ∀ a, ClosedAdmissible a → X a → ENNReal)
    (rawValue : ∀ a, ClosedAdmissible a → X a → Real)
    (hcost : ∀ a h, Measurable (rawCost a h))
    (hvalue : ∀ a h, Measurable (rawValue a h))
    (hexpected : ∀ a h,
      (∫⁻ x, rawCost a h x ∂rawLaw a h) ≤ ENNReal.ofReal (rawEnvelope a))
    (haccuracy : ∀ a (h : ClosedAdmissible a),
      4 / 5 ≤ (rawLaw a h).real
        {x | rawValue a h x ∈
          Icc ((1 - a.2.1) * (volume a.1).toReal)
            ((1 + a.2.1) * (volume a.1).toReal)}) :
    GeneralizedPublicOneRunCertificates n
      (fun a ↦ rawEnvelope (regularizedInput a))
      (fun a ↦ X (regularizedInput a))
      (guardedClosedLaw X rawLaw)
      (guardedClosedCost X rawCost)
      (guardedClosedValue X rawValue) := by
  refine
    { probability := fun _ ↦ inferInstance
      cost_measurable := measurable_guardedClosedCost X rawCost hcost
      value_measurable := measurable_guardedClosedValue X rawValue hvalue
      expected_queries := ?_
      accuracy := ?_ }
  · intro a
    unfold guardedClosedLaw guardedClosedCost
    split
    · exact hexpected _ _
    · simp
  · intro K eps p heps hp hp1 hKc hball hfin
    let a : VolumeInput n := (K, eps, p)
    let b : VolumeInput n := regularizedInput a
    have hgeom := Ttc.CVAdaptive.closure_concrete_geometry hn hKc hball hfin
    have hb : ClosedAdmissible b := by
      exact ⟨heps, hp, hp1, hgeom.1, hgeom.2.1, hgeom.2.2.1,
        hgeom.2.2.2.1, hgeom.2.2.2.2.1, hgeom.2.2.2.2.2.1⟩
    have hb' : ClosedAdmissible (regularizedInput (K, eps, p)) := by
      simpa only [a, b] using hb
    have hvol := Ttc.CVAdaptive.volume_closure_eq_of_convex hKc
    unfold guardedClosedLaw guardedClosedValue
    simp only [dif_pos hb']
    simpa only [a, b, regularizedInput, hvol] using haccuracy b hb

/-- Public expected-query oracle from closed-admissible raw one-run laws.  This is the
guarded counterpart of `expectedQueryVolumeAlgorithmOfGeneralizedCertificates`. -/
noncomputable def guardedExpectedQueryVolumeAlgorithm
    (hn : 1 ≤ n)
    (rawEnvelope : VolumeInput n → Real)
    (rawLaw : ∀ a, ClosedAdmissible a → Measure (X a))
    [∀ a h, IsProbabilityMeasure (rawLaw a h)]
    (rawCost : ∀ a, ClosedAdmissible a → X a → ENNReal)
    (rawValue : ∀ a, ClosedAdmissible a → X a → Real)
    (hcost : ∀ a h, Measurable (rawCost a h))
    (hvalue : ∀ a h, Measurable (rawValue a h))
    (hexpected : ∀ a h,
      (∫⁻ x, rawCost a h x ∂rawLaw a h) ≤ ENNReal.ofReal (rawEnvelope a))
    (haccuracy : ∀ a (h : ClosedAdmissible a),
      4 / 5 ≤ (rawLaw a h).real
        {x | rawValue a h x ∈
          Icc ((1 - a.2.1) * (volume a.1).toReal)
            ((1 + a.2.1) * (volume a.1).toReal)}) :
    Ttc.ExpectedQueryVolumeAlgorithm n :=
  expectedQueryVolumeAlgorithmOfGeneralizedCertificates n
    (fun a ↦ rawEnvelope (regularizedInput a))
    (fun a ↦ X (regularizedInput a))
    (guardedClosedLaw X rawLaw)
    (guardedClosedCost X rawCost)
    (guardedClosedValue X rawValue)
    (guardedGeneralizedPublicOneRunCertificates X hn rawEnvelope rawLaw rawCost rawValue
      hcost hvalue hexpected haccuracy)

/-- Displayed amplified bound for the guarded oracle.  All invalid-input totalization is
inside the one-run law; the public expected bound is the same explicit global-cutoff
envelope evaluated at the closure-regularized input. -/
theorem guardedExpectedBound_le_amplified
    (hn : 1 ≤ n)
    (rawEnvelope : VolumeInput n → Real)
    (rawLaw : ∀ a, ClosedAdmissible a → Measure (X a))
    [∀ a h, IsProbabilityMeasure (rawLaw a h)]
    (rawCost : ∀ a, ClosedAdmissible a → X a → ENNReal)
    (rawValue : ∀ a, ClosedAdmissible a → X a → Real)
    (hcost : ∀ a h, Measurable (rawCost a h))
    (hvalue : ∀ a h, Measurable (rawValue a h))
    (hexpected : ∀ a h,
      (∫⁻ x, rawCost a h x ∂rawLaw a h) ≤ ENNReal.ofReal (rawEnvelope a))
    (haccuracy : ∀ a (h : ClosedAdmissible a),
      4 / 5 ≤ (rawLaw a h).real
        {x | rawValue a h x ∈
          Icc ((1 - a.2.1) * (volume a.1).toReal)
            ((1 + a.2.1) * (volume a.1).toReal)})
    (K : Set (Ttc.Space n)) (eps p : Real)
    (hE : 0 ≤ rawEnvelope (regularizedInput (K, eps, p)))
    (hp : 0 < p) (hp1 : p < 1) :
    (guardedExpectedQueryVolumeAlgorithm X hn rawEnvelope rawLaw rawCost rawValue
      hcost hvalue hexpected haccuracy).expectedBound K eps p ≤
      ENNReal.ofReal
        (generalizedAmplifiedEnvelope
          (rawEnvelope (regularizedInput (K, eps, p))) p) := by
  change generalizedPublicExpectedBound
      (fun a ↦ rawEnvelope (regularizedInput a)) (K, eps, p) ≤ _
  exact generalizedPublicExpectedBound_le_amplified hE hp hp1

#print axioms guardedGeneralizedPublicOneRunCertificates
#print axioms guardedExpectedQueryVolumeAlgorithm
#print axioms guardedExpectedBound_le_amplified

end Ttc.CVGuardedGeneralizedPublic

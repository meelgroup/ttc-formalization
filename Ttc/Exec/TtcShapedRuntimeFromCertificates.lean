import Ttc.Exec.CVEffectiveTotalise
import Ttc.Exec.TtcCallBallAdmissible
import Ttc.Exec.TtcCircumRadius
import Ttc.Exec.CVValidBounded

/-!
# From per-input one-run certificates to a TTC runtime bound

This file closes the **generic half** of the runtime assembly: everything between "the
volume construction produces a one-run reference-TV certificate on each valid input" and
"TTC's accuracy and query cost are both bounded, over one law".  It mentions no schedule,
no Gaussian cooling and no phase count — the construction supplies those, and this file is
what it plugs into.

The chain, all of it already proved elsewhere and merely composed here:

1. `Ttc.CVEffectiveTotalise.effectiveSourcePublicReferenceTVCertificates_of_exists`
   totalises the family: certificates on the *valid* inputs suffice, degenerate inputs get
   a point mass, zero cost and zero value.
2. `Ttc.CVEffectiveSourceReference.cvShapedExpectedImplementationOfEffectiveFamily`
   turns it into a `CVShapedExpectedImplementation` at the shape
   `cvComplexityShapeClipped * OV`, where `OV` is whatever overhead envelope the
   construction pays over Cousins–Vempala's own Theorem 1.1 expression.
3. `Ttc.CVShaped.ttc_volume_estimate_of_cvShapedExpectedImplementationAt` transports that
   to TTC at the per-call *declared* radii.

The admissibility predicate is `Ttc.CVShaped.cvAdmBall` — Cousins–Vempala's own
`CVAdmissible` **plus** the quantitative containment `K ⊆ closedBall 0 (Real.sqrt R2)`.  The
extra conjunct is not free at the interface's full generality (a convex body of finite
volume and finite second moment need not be bounded), but it is free at TTC's own call
bodies, which are `roundBody`s of bounded polytopes — that is
`Ttc.TtcCallBallAdmissible.cvAdmBall_callBody`.

The radial parameter is the **circumradius** `Ttc.TtcCircumRadius.circumR`.  It is the only
choice satisfying both of the chain's opposing demands; see that file's docstring.

## Main result

* `ttc_runtime_of_effectiveCertificates`
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.TtcShapedRuntime

open MeasureTheory ProbabilityTheory Metric Set
open Ttc.CVShaped
open Ttc.CVEffectiveSourceReference
open Ttc.CVEffectiveTotalise
open Ttc.TtcCircumRadius
open Ttc.TtcCallBallAdmissible
open Ttc.CVSourceReferenceTVCapstone
open Ttc.TTCCVExpectedImplementation
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem
open scoped ENNReal BigOperators Classical

/-- The complexity shape a construction with overhead envelope `OV` meets: the confidence
factor `max 1 (log (1/p))` times the overhead.  No constant is pretending to absorb `OV`.

⚠ **This used to be `cvComplexityShapeClipped n R2 eps p * OV n R2 eps p`** — Cousins–Vempala's
whole Theorem 1.1 expression times the overhead.  That factor was never earned: the one-run
budget reached it only through `1 ≤ cvBaseClipped`, and what every discharge site actually
proves is `expected queries ≤ OV`.  The confidence factor is the part that *is* earned, by
repeated runs.  See `lean/PLAN-SHAPE.md`.

The paper-contract layer is untouched: `Ttc.cvComplexityShapeClipped` still states Theorem
1.1's expression, and
`Ttc.CVSourceTheorem11Arithmetic.sourceAmplifiedQueryEnvelope_le_cvComplexityShapeClipped`
still proves the amplified budget fits under it. -/
noncomputable def shapeOf (OV : (n : Nat) → Real → Real → Real → Real) : ComplexityShape :=
  fun n R2 eps p ↦ Ttc.CVSourceTheorem11Arithmetic.cvConfidenceShape n R2 eps p *
    OV n R2 eps p

/-- **The implementation, from per-input certificates on the valid inputs only.** -/
noncomputable def implementationOfEffectiveCertificates
    (OV : (n : Nat) → Real → Real → Real → Real)
    (hOV : ∀ (n : Nat) (R2 eps p : Real), 1 ≤ OV n R2 eps p)
    (effective : ∀ n, Ttc.CVAdaptive.VolumeInput n → Real)
    (heff0 : ∀ n a, 0 ≤ effective n a)
    (heff : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      cvAdmBall n K R2 → effective n (K, eps, p) ≤ OV n R2 eps p)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    [nOmega : ∀ n a, Nonempty (Omega n a)]
    (law : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcost : ∀ n a, Measurable (cost n a))
    (hvalue : ∀ n a, Measurable (value n a))
    (H : ∀ n a, CVValidInput a →
      ∃ r : Measure (Omega n a),
        SourceReferenceTVOneRunCertificate (law n a) r (cost n a) (value n a)
          (effective n a) n (circumR a.1) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal)) :
    CVShapedExpectedImplementation cvAdmBall (shapeOf OV) :=
  cvShapedExpectedImplementationOfEffectiveFamily cvAdmBall
    cvAdmBall_imp_cvAdmissible 1 (by norm_num) OV hOV effective heff0
    (fun n K eps p R2 hK ↦ by
      simpa using heff n K eps p R2 hK)
    (fun _ ↦ circumR) circumR_interface_hrad Omega
    (fun n ↦ totaliseActual (law n))
    (fun n ↦ totaliseActual (chosenReference (H n)))
    (fun n ↦ totaliseCost (cost n))
    (fun n ↦ totaliseValue (value n))
    (fun n ↦ effectiveSourcePublicReferenceTVCertificates_of_exists
      (effective n) circumR (law n) (cost n) (value n) (hcost n) (hvalue n) (H n))

variable {A : Type*} {n : Nat}

/-- **The generic half of the runtime assembly, discharged.**

Both conjuncts are about the same law `canonicalFullOperationalLaw V P`, which executes the
supplied volume oracle and the capped sampling oracle; the second integrates the run's own
recorded query cost.  The volume term is the per-cube sum of the construction's own shape
at that cube's **declared outer radius squared**, which is the paper's per-polytope
`R_i/gamma_i` rather than a global normalisation.

Read the caveat in `RUNTIME-ENDGAME.md` §4 before quoting the second conjunct: the shape is
`cvComplexityShapeClipped * OV`, **not** the paper's `O(m n^5 rho^2 r_max)` exponents. -/
theorem ttc_runtime_of_effectiveCertificates
    (OV : (n : Nat) → Real → Real → Real → Real)
    (hOV : ∀ (n : Nat) (R2 eps p : Real), 1 ≤ OV n R2 eps p)
    (effective : ∀ n, Ttc.CVAdaptive.VolumeInput n → Real)
    (heff0 : ∀ n a, 0 ≤ effective n a)
    (heff : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      cvAdmBall n K R2 → effective n (K, eps, p) ≤ OV n R2 eps p)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    [nOmega : ∀ n a, Nonempty (Omega n a)]
    (law : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcost : ∀ n a, Measurable (cost n a))
    (hvalue : ∀ n a, Measurable (value n a))
    (H : ∀ n a, CVValidInput a →
      ∃ r : Measure (Omega n a),
        SourceReferenceTVOneRunCertificate (law n a) r (cost n a) (value n a)
          (effective n a) n (circumR a.1) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal))
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let I := implementationOfEffectiveCertificates OV hOV effective heff0 heff
      Omega law cost value hcost hvalue H
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      shapedVolumeQueryEnvelopeAt I atoms phi eps deltaRun
        (fun j ↦ callDeclaredR2 atoms phi eps deltaRun j) +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  exact ttc_volume_estimate_of_cvShapedExpectedImplementationAt
    (implementationOfEffectiveCertificates OV hOV effective heff0 heff
      Omega law cost value hcost hvalue H)
    atoms phi eps delta (fun j ↦ callDeclaredR2 atoms phi eps (4 * delta / 5) j)
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol
    (fun j ↦ cvAdmBall_callBody atoms phi eps (4 * delta / 5)
      h_eps_pos h_eps_le hn1 hphi hvol j)

/-! ## The dimension-guarded form

`ttc_runtime_of_effectiveCertificates` asks for certificates at **every** dimension, and the
slow canonical construction supplies them only for `21 ≤ n`.  That gap cannot be closed by a
cleverer choice of law: below the valid range the law is a point mass, at which the
certificate's `4/5` accuracy field is not provable — and `CVValidInput` really is satisfiable
at every `n`, `n = 0` included, since `Ttc.Space 0` is a single point and its unit ball is
everything.

So the dimension is guarded the way the repository already guards it elsewhere: below `21`
the oracle is the semantic exact-volume witness, whose declared query cost is identically
`0`.  That branch is honest about what it is, and it is the reason the capstone carries
`21 ≤ n`. -/

/-- The reference law chosen from the guarded per-input existential, total in both `n` and
the input. -/
noncomputable def chosenReference21
    {Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type}
    [∀ n a, MeasurableSpace (Omega n a)] [∀ n a, Nonempty (Omega n a)]
    {P : ∀ n a, Measure (Omega n a) → Prop}
    (H : ∀ n, 21 ≤ n → ∀ a, CVValidInput a → ∃ r : Measure (Omega n a), P n a r)
    (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Measure (Omega n a) :=
  if h : 21 ≤ n ∧ CVValidInput a then Classical.choose (H n h.1 a h.2)
  else Measure.dirac (Classical.arbitrary (Omega n a))

theorem chosenReference21_spec
    {Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type}
    [∀ n a, MeasurableSpace (Omega n a)] [∀ n a, Nonempty (Omega n a)]
    {P : ∀ n a, Measure (Omega n a) → Prop}
    (H : ∀ n, 21 ≤ n → ∀ a, CVValidInput a → ∃ r : Measure (Omega n a), P n a r)
    {n : Nat} (hn : 21 ≤ n) {a : Ttc.CVAdaptive.VolumeInput n} (ha : CVValidInput a) :
    P n a (chosenReference21 H n a) := by
  simp only [chosenReference21, dif_pos (⟨hn, ha⟩ : 21 ≤ n ∧ CVValidInput a)]
  exact Classical.choose_spec (H n hn a ha)

/-- **The implementation, from certificates supplied only in the valid dimension range.** -/
noncomputable def implementationOfEffectiveCertificates21
    (OV : (n : Nat) → Real → Real → Real → Real)
    (hOV : ∀ (n : Nat) (R2 eps p : Real), 1 ≤ OV n R2 eps p)
    (effective : ∀ n, Ttc.CVAdaptive.VolumeInput n → Real)
    (heff0 : ∀ n a, 0 ≤ effective n a)
    (heff : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      cvAdmBall n K R2 → effective n (K, eps, p) ≤ OV n R2 eps p)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    [nOmega : ∀ n a, Nonempty (Omega n a)]
    (law : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcost : ∀ n a, Measurable (cost n a))
    (hvalue : ∀ n a, Measurable (value n a))
    (H : ∀ n, 21 ≤ n → ∀ a, CVValidInput a →
      ∃ r : Measure (Omega n a),
        SourceReferenceTVOneRunCertificate (law n a) r (cost n a) (value n a)
          (effective n a) n (circumR a.1) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal)) :
    CVShapedExpectedImplementation cvAdmBall (shapeOf OV) :=
  cvShapedExpectedImplementationOfEffectiveFamilyTwentyOne cvAdmBall
    cvAdmBall_imp_cvAdmissible 1 (by norm_num) OV hOV effective heff0
    (fun n K eps p R2 hK ↦ by simpa using heff n K eps p R2 hK)
    (fun _ ↦ circumR) circumR_interface_hrad Omega
    (fun n ↦ totaliseActual (law n))
    (fun n ↦ totaliseActual (chosenReference21 H n))
    (fun n ↦ totaliseCost (cost n))
    (fun n ↦ totaliseValue (value n))
    (fun n hn ↦ effectiveSourcePublicReferenceTVCertificates_of_valid
      (effective n) circumR (law n) (chosenReference21 H n) (cost n) (value n)
      (hcost n) (hvalue n)
      (fun a ha ↦ chosenReference21_spec H hn ha))

/-- **The generic half of the runtime assembly, in the dimension-guarded form.**

Identical to `ttc_runtime_of_effectiveCertificates` except that the certificates are
required only for `21 ≤ n`, which is the range the slow canonical construction is valid in
and the range the capstone quantifies over anyway. -/
theorem ttc_runtime_of_effectiveCertificates21
    (OV : (n : Nat) → Real → Real → Real → Real)
    (hOV : ∀ (n : Nat) (R2 eps p : Real), 1 ≤ OV n R2 eps p)
    (effective : ∀ n, Ttc.CVAdaptive.VolumeInput n → Real)
    (heff0 : ∀ n a, 0 ≤ effective n a)
    (heff : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      cvAdmBall n K R2 → effective n (K, eps, p) ≤ OV n R2 eps p)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    [nOmega : ∀ n a, Nonempty (Omega n a)]
    (law : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcost : ∀ n a, Measurable (cost n a))
    (hvalue : ∀ n a, Measurable (value n a))
    (H : ∀ n, 21 ≤ n → ∀ a, CVValidInput a →
      ∃ r : Measure (Omega n a),
        SourceReferenceTVOneRunCertificate (law n a) r (cost n a) (value n a)
          (effective n a) n (circumR a.1) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal))
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let I := implementationOfEffectiveCertificates21 OV hOV effective heff0 heff
      Omega law cost value hcost hvalue H
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      shapedVolumeQueryEnvelopeAt I atoms phi eps deltaRun
        (fun j ↦ callDeclaredR2 atoms phi eps deltaRun j) +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  exact ttc_volume_estimate_of_cvShapedExpectedImplementationAt
    (implementationOfEffectiveCertificates21 OV hOV effective heff0 heff
      Omega law cost value hcost hvalue H)
    atoms phi eps delta (fun j ↦ callDeclaredR2 atoms phi eps (4 * delta / 5) j)
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol
    (fun j ↦ cvAdmBall_callBody atoms phi eps (4 * delta / 5)
      h_eps_pos h_eps_le hn1 hphi hvol j)

/-! ## The fully generic form

`ttc_runtime_of_effectiveCertificates21` pins the admissibility predicate to `cvAdmBall` and
the radial parameter to `circumR`.  Both choices force the consumer to prove that its
overhead envelope is *monotone in the declared squared radius*, because `effective` is
evaluated at the body's own radius while `OV` is evaluated at the declared `R2 ≥ it`.

For a construction whose envelope is an awkward function of `R2` — the slow canonical one
is: its phase count `slowPhasesP n R2` appears inside a logarithm, multiplied by itself —
that monotonicity is a real obstacle and an avoidable one.  The way round is to let the
*predicate* pin the declared radius to the value the construction actually uses, at which
point `hrad` and `heff` are both `le_refl` and no monotonicity is needed at all.  That is
legitimate because `CVAdmissible K R2` only requires `R2` to be an **upper** bound on the
second moment, so a caller may declare any radius it can justify.

So this version takes the predicate and the radial parameter as arguments. The two
specialisations above are instances of it. -/
noncomputable def implementationOfEffectiveCertificatesGen
    (Adm : AdmissiblePredicate)
    (hAdm : ∀ (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real),
      Adm n K R2 → CVAdmissible K R2)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2, Adm n K R2 → (radialR n K) ^ 2 ≤ R2)
    (OV : (n : Nat) → Real → Real → Real → Real)
    (hOV : ∀ (n : Nat) (R2 eps p : Real), 1 ≤ OV n R2 eps p)
    (effective : ∀ n, Ttc.CVAdaptive.VolumeInput n → Real)
    (heff0 : ∀ n a, 0 ≤ effective n a)
    (heff : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      Adm n K R2 → effective n (K, eps, p) ≤ OV n R2 eps p)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    [nOmega : ∀ n a, Nonempty (Omega n a)]
    (law : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcost : ∀ n a, Measurable (cost n a))
    (hvalue : ∀ n a, Measurable (value n a))
    (H : ∀ n, 21 ≤ n → ∀ a, CVValidInput a →
      ∃ r : Measure (Omega n a),
        SourceReferenceTVOneRunCertificate (law n a) r (cost n a) (value n a)
          (effective n a) n (radialR n a.1) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal)) :
    CVShapedExpectedImplementation Adm (shapeOf OV) :=
  cvShapedExpectedImplementationOfEffectiveFamilyTwentyOne Adm hAdm 1 (by norm_num)
    OV hOV effective heff0
    (fun n K eps p R2 hK ↦ by simpa using heff n K eps p R2 hK)
    radialR hrad Omega
    (fun n ↦ totaliseActual (law n))
    (fun n ↦ totaliseActual (chosenReference21 H n))
    (fun n ↦ totaliseCost (cost n))
    (fun n ↦ totaliseValue (value n))
    (fun n hn ↦ effectiveSourcePublicReferenceTVCertificates_of_valid
      (effective n) (radialR n) (law n) (chosenReference21 H n) (cost n) (value n)
      (hcost n) (hvalue n)
      (fun a ha ↦ chosenReference21_spec H hn ha))

/-- **The generic half of the runtime assembly, at an arbitrary admissibility predicate and
radial parameter.**

The extra `hadm` binder is the price of the generality: TTC's own call bodies must satisfy
whatever predicate the construction chose, at whatever per-call declared radii it uses. -/
theorem ttc_runtime_of_effectiveCertificatesGen
    (Adm : AdmissiblePredicate)
    (hAdm : ∀ (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real),
      Adm n K R2 → CVAdmissible K R2)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2, Adm n K R2 → (radialR n K) ^ 2 ≤ R2)
    (OV : (n : Nat) → Real → Real → Real → Real)
    (hOV : ∀ (n : Nat) (R2 eps p : Real), 1 ≤ OV n R2 eps p)
    (effective : ∀ n, Ttc.CVAdaptive.VolumeInput n → Real)
    (heff0 : ∀ n a, 0 ≤ effective n a)
    (heff : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      Adm n K R2 → effective n (K, eps, p) ≤ OV n R2 eps p)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    [nOmega : ∀ n a, Nonempty (Omega n a)]
    (law : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcost : ∀ n a, Measurable (cost n a))
    (hvalue : ∀ n a, Measurable (value n a))
    (H : ∀ n, 21 ≤ n → ∀ a, CVValidInput a →
      ∃ r : Measure (Omega n a),
        SourceReferenceTVOneRunCertificate (law n a) r (cost n a) (value n a)
          (effective n a) n (radialR n a.1) a.2.1
          ((1 - a.2.1) * (volume a.1).toReal) ((1 + a.2.1) * (volume a.1).toReal))
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (R2j : Fin (toDNFd (preprocess atoms phi)).length → Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (hadm : ∀ j, Adm n (callBody atoms phi eps (4 * delta / 5) j) (R2j j)) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let I := implementationOfEffectiveCertificatesGen Adm hAdm radialR hrad OV hOV
      effective heff0 heff Omega law cost value hcost hvalue H
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      shapedVolumeQueryEnvelopeAt I atoms phi eps deltaRun R2j +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) :=
  ttc_volume_estimate_of_cvShapedExpectedImplementationAt
    (implementationOfEffectiveCertificatesGen Adm hAdm radialR hrad OV hOV
      effective heff0 heff Omega law cost value hcost hvalue H)
    atoms phi eps delta R2j
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol hadm

#print axioms shapeOf
#print axioms implementationOfEffectiveCertificates
#print axioms ttc_runtime_of_effectiveCertificates
#print axioms chosenReference21
#print axioms chosenReference21_spec
#print axioms implementationOfEffectiveCertificates21
#print axioms ttc_runtime_of_effectiveCertificates21
#print axioms implementationOfEffectiveCertificatesGen
#print axioms ttc_runtime_of_effectiveCertificatesGen

end Ttc.TtcShapedRuntime

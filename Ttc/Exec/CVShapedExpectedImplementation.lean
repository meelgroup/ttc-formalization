import Ttc.Exec.CVCappedRadialLogInterface

/-!
# Shape-generic expected-query CV interface

`Ttc/Exec/TTCCVExpectedImplementation.lean` and
`Ttc/Exec/CVCappedRadialLogInterface.lean` each carry their own copy of the same three
declarations — an implementation structure, the per-call sum, and the TTC transport —
differing only in *which* real-valued complexity shape the per-call bound is stated at
(`cvComplexityShapeClipped`, `cvRadialLogComplexityShapeClipped`,
`cvCappedRadialLogComplexityShapeClipped`).

Nothing in that transport depends on the shape.  `cappedTTC_fullTrajectory` is stated for
an arbitrary `Ttc.ExpectedQueryVolumeAlgorithm n`, and the per-call step is a single
`Finset.sum_le_sum` over the run's own DNF.  So the shape can simply be a parameter, and
this file makes it one.

The reason this is needed rather than merely tidy: the uniformly slow canonical schedule
of `Ttc/Exec/CVSlowCanonical*.lean` is bounded by `cvSlowCanonicalCappedRadialShape`,
which is `cvCappedRadialLogComplexityShapeClipped` **times an explicit schedule
overhead** (`Ttc.CVSlowCanonicalRuntimeComparison.slowCanonicalRetainedScalar_le_publicShape`).
That overhead grows with the phase count, the stream count and the radius, so no fixed
`runtimeConstant` absorbs it and the existing capped interface cannot be inhabited by
that construction.  Rather than clone the interface a fourth time, the shape becomes an
argument and each construction supplies its own.

## Main results

* `CVShapedExpectedImplementation` — the shape-parametric interface.
* `ttcPolyVolumeQueryBound_le_shapedVolumeQueryEnvelope` — the per-call sum.
* `ttc_volume_estimate_of_cvShapedExpectedImplementation` — the TTC transport, at
  `21 ≤ n`, in the same form as
  `Ttc.CVCappedRadialLogInterface.ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation`.
* `CVShapedExpectedImplementation.ofCapped` — the existing capped interface is the
  instance at `shape := cvCappedRadialLogComplexityShapeClipped`, so nothing is lost.
* `CVShapedExpectedImplementation.mono` — a bound at a smaller shape gives one at a
  larger shape, which is how a construction hands its own envelope to a coarser
  interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.CVShaped

open MeasureTheory ProbabilityTheory Metric Set
open Ttc.TTCCVExpectedImplementation
open Ttc.CVCappedRadialLogInterface
open Ttc.CVHotRefreshHonestRuntime
open Ttc.CVRadialLogEnvelope
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem
open scoped ENNReal BigOperators Classical

/-- A real-valued complexity shape in dimension, squared radius, accuracy and
confidence.  This is the only thing the three existing CV interfaces differ in. -/
abbrev ComplexityShape := (n : Nat) → Real → Real → Real → Real

/-- An admissibility predicate on the input body and its declared squared radius.

Cousins–Vempala's own hypothesis is `Ttc.CVAdmissible` — convex, containing the unit
ball, of positive finite volume, with second moment at most `R2`.  A *construction* may
need more: the uniformly slow canonical schedule needs a hard containment
`K ⊆ closedBall 0 R`, which a second-moment bound does not supply (a convex body of finite
volume and finite second moment can still be unbounded).  Making the predicate a parameter
lets such a construction state its real hypothesis instead of quietly overclaiming, at the
price of one extra obligation at the TTC call site — where it is discharged, because TTC's
own call bodies are bounded polytopes. -/
abbrev AdmissiblePredicate := (n : Nat) → Set (Ttc.Space n) → Real → Prop

/-- Cousins–Vempala's own admissibility, as an `AdmissiblePredicate`. -/
def cvAdm : AdmissiblePredicate := fun _ K R2 ↦ CVAdmissible K R2

/-- `CVAdmissible` together with boundedness of the body.  This is what a construction
needing an explicit outer radius must ask for; the radius may then be taken to be
`Metric.diam K`, since `ball 0 1 ⊆ K` puts the origin in `K`. -/
def cvAdmBounded : AdmissiblePredicate :=
  fun _ K R2 ↦ CVAdmissible K R2 ∧ Bornology.IsBounded K

/-- `CVAdmissible` together with a **quantitative** containment at the declared radius.

This is the predicate a construction needing an explicit outer radius should ask for.  It
is satisfiable precisely because `CVAdmissible K R2` only requires `R2` to be an *upper*
bound on the second moment: a caller is free to declare `R2` to be the squared containment
radius rather than the second moment itself, and
`Ttc.TtcRadialGeometry.cvSecondMoment_le_sq_of_subset_closedBall` then supplies the
`CVAdmissible` half.  Declaring a larger `R2` only inflates the complexity shape, which is
the honest direction. -/
def cvAdmBall : AdmissiblePredicate :=
  fun _ K R2 ↦ CVAdmissible K R2 ∧ K ⊆ Metric.closedBall 0 (Real.sqrt R2)

/-- Expected-query CV implementation stated at an arbitrary complexity `shape`.

The field list is exactly that of
`Ttc.CVCappedRadialLogInterface.CVCappedRadialLogExpectedImplementation`, with the fixed
shape replaced by the parameter. -/
structure CVShapedExpectedImplementation (Adm : AdmissiblePredicate)
    (shape : ComplexityShape) where
  algorithm : (n : Nat) → Ttc.ExpectedQueryVolumeAlgorithm n
  runtimeConstant : Real
  runtimeConstant_nonneg : 0 ≤ runtimeConstant
  expectedBound_le : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
    1 ≤ n → 0 < eps → eps < 1 → 0 < p → p < 1 → Adm n K R2 →
    (algorithm n).expectedBound K eps p ≤ ENNReal.ofReal
      (runtimeConstant * shape n R2 eps p)

namespace CVShapedExpectedImplementation

/-- The direct constructor, for algorithms proved against `shape` itself. -/
noncomputable def ofExpectedBound (Adm : AdmissiblePredicate) (shape : ComplexityShape)
    (algorithm : (n : Nat) → Ttc.ExpectedQueryVolumeAlgorithm n)
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (hbound : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      1 ≤ n → 0 < eps → eps < 1 → 0 < p → p < 1 → Adm n K R2 →
      (algorithm n).expectedBound K eps p ≤ ENNReal.ofReal
        (runtimeConstant * shape n R2 eps p)) :
    CVShapedExpectedImplementation Adm shape where
  algorithm := algorithm
  runtimeConstant := runtimeConstant
  runtimeConstant_nonneg := hconstant
  expectedBound_le := hbound

/-- An implementation at a pointwise-smaller shape is one at the larger shape.  The
nonnegativity side condition is only needed where the smaller shape is evaluated. -/
noncomputable def mono {Adm : AdmissiblePredicate} {shape shape' : ComplexityShape}
    (I : CVShapedExpectedImplementation Adm shape)
    (hle : ∀ (n : Nat) (R2 eps p : Real), 0 ≤ shape n R2 eps p →
      shape n R2 eps p ≤ shape' n R2 eps p)
    (hnonneg : ∀ (n : Nat) (R2 eps p : Real), 0 ≤ shape n R2 eps p) :
    CVShapedExpectedImplementation Adm shape' where
  algorithm := I.algorithm
  runtimeConstant := I.runtimeConstant
  runtimeConstant_nonneg := I.runtimeConstant_nonneg
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK :=
    (I.expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK).trans
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hle n R2 eps p (hnonneg n R2 eps p))
          I.runtimeConstant_nonneg))

/-- The existing honestly capped radial-log interface is the instance of this one at
`shape := cvCappedRadialLogComplexityShapeClipped`. -/
noncomputable def ofCapped (I : CVCappedRadialLogExpectedImplementation) :
    CVShapedExpectedImplementation cvAdm cvCappedRadialLogComplexityShapeClipped where
  algorithm := I.algorithm
  runtimeConstant := I.runtimeConstant
  runtimeConstant_nonneg := I.runtimeConstant_nonneg
  expectedBound_le := I.expectedBound_le

end CVShapedExpectedImplementation

variable {A : Type*} {n : Nat}

/-- Exact sum of the supplied implementation's per-call bounds over TTC's rounded call
bodies, at the implementation's own shape. -/
noncomputable def shapedVolumeQueryEnvelope {Adm : AdmissiblePredicate}
    {shape : ComplexityShape} (I : CVShapedExpectedImplementation Adm shape)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : ENNReal :=
  ∑ j : Fin (toDNFd (preprocess atoms phi)).length,
    ENNReal.ofReal
      (I.runtimeConstant *
        shape n (callSecondMoment atoms phi eps delta j)
          (algBlock atoms phi eps delta).epsPrime
          (algBlock atoms phi eps delta).deltaPrime)

/-- The actual input-wise TTC volume budget of the supplied implementation is bounded by
the finite per-call sum at its own shape.

The proof is the shape-independent one: the four parameter-range facts about
`algBlock`'s `epsPrime`/`deltaPrime`, then one `Finset.sum_le_sum` applying the
implementation's own field at `callBody`, whose `CVAdmissible` witness is
`callBody_admissible`. -/
theorem ttcPolyVolumeQueryBound_le_shapedVolumeQueryEnvelope {Adm : AdmissiblePredicate}
    {shape : ComplexityShape} (I : CVShapedExpectedImplementation Adm shape)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (hadm : ∀ j : Fin (toDNFd (preprocess atoms phi)).length,
      Adm n (callBody atoms phi eps delta j)
        (callSecondMoment atoms phi eps delta j)) :
    ttcPolyVolumeQueryBound atoms phi eps delta (I.algorithm n) ≤
      shapedVolumeQueryEnvelope I atoms phi eps delta := by
  have heps0 : 0 < (algBlock atoms phi eps delta).epsPrime :=
    algBlock_epsPrime_pos atoms phi eps delta
  have heps1 : (algBlock atoms phi eps delta).epsPrime < 1 := by
    rw [algBlock_epsPrime_eq atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol]
    linarith
  have hp0 : 0 < (algBlock atoms phi eps delta).deltaPrime :=
    algBlock_deltaPrime_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
      h_delta_pos
  have hp1 : (algBlock atoms phi eps delta).deltaPrime < 1 :=
    lt_of_le_of_lt
      (algBlock_deltaPrime_le_half atoms phi eps delta h_eps_pos h_eps_le hn
        hphi hvol h_delta_le) (by norm_num)
  unfold ttcPolyVolumeQueryBound volOfExpectedAlgQueryBound shapedVolumeQueryEnvelope
  apply Finset.sum_le_sum
  intro j _
  exact I.expectedBound_le n (callBody atoms phi eps delta j)
    (algBlock atoms phi eps delta).epsPrime
    (algBlock atoms phi eps delta).deltaPrime
    (callSecondMoment atoms phi eps delta j)
    hn heps0 heps1 hp0 hp1 (hadm j)

/-- **TTC compatibility at an arbitrary CV complexity shape.**

Same statement as
`Ttc.CVCappedRadialLogInterface.ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation`,
with the fixed capped shape replaced by the implementation's own.  The `21 ≤ n` premise
is inherited unchanged: it prevents lower dimensions from silently routing through the
non-operational exact-volume semantic witness.

Both conjuncts are about the same law `canonicalFullOperationalLaw V P`, which executes
the supplied volume oracle and the capped sampling oracle; the second conjunct
integrates the run's own recorded query cost. -/
theorem ttc_volume_estimate_of_cvShapedExpectedImplementation {Adm : AdmissiblePredicate}
    {shape : ComplexityShape} (I : CVShapedExpectedImplementation Adm shape)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (hadm : ∀ j : Fin (toDNFd (preprocess atoms phi)).length,
      Adm n (callBody atoms phi eps (4 * delta / 5) j)
        (callSecondMoment atoms phi eps (4 * delta / 5) j)) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      shapedVolumeQueryEnvelope I atoms phi eps deltaRun +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  let deltaRun := 4 * delta / 5
  let hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hd0 : 0 < deltaRun := by dsimp [deltaRun]; linarith
  have hd1 : deltaRun ≤ 1 := by dsimp [deltaRun]; linarith
  let V := I.algorithm n
  letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn1 hphi hvol
  have hmain := cappedTTC_fullTrajectory V atoms phi eps delta
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn1 hphi hvol
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact add_le_add
    (ttcPolyVolumeQueryBound_le_shapedVolumeQueryEnvelope I atoms phi eps deltaRun
      h_eps_pos h_eps_le hd0 hd1 hn1 hphi hvol hadm)
    (le_refl (canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun))

/-! ## The per-call declared radius

The envelope above evaluates the shape at `callSecondMoment`, TTC's own per-call second
moment.  A construction whose admissibility predicate is quantitative — `cvAdmBall`, say —
needs to evaluate it at the *declared* radius instead, since `CVAdmissible K R2` only makes
`R2` an upper bound.  The following generalises both the envelope and the transport to a
caller-supplied per-call radius `R2j`; the versions above are the special case
`R2j := callSecondMoment`. -/

/-- The per-call sum at a caller-supplied declared squared radius. -/
noncomputable def shapedVolumeQueryEnvelopeAt {Adm : AdmissiblePredicate}
    {shape : ComplexityShape} (I : CVShapedExpectedImplementation Adm shape)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (R2j : Fin (toDNFd (preprocess atoms phi)).length → Real) : ENNReal :=
  ∑ j : Fin (toDNFd (preprocess atoms phi)).length,
    ENNReal.ofReal
      (I.runtimeConstant *
        shape n (R2j j)
          (algBlock atoms phi eps delta).epsPrime
          (algBlock atoms phi eps delta).deltaPrime)

theorem ttcPolyVolumeQueryBound_le_shapedVolumeQueryEnvelopeAt
    {Adm : AdmissiblePredicate} {shape : ComplexityShape}
    (I : CVShapedExpectedImplementation Adm shape)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (R2j : Fin (toDNFd (preprocess atoms phi)).length → Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (hadm : ∀ j, Adm n (callBody atoms phi eps delta j) (R2j j)) :
    ttcPolyVolumeQueryBound atoms phi eps delta (I.algorithm n) ≤
      shapedVolumeQueryEnvelopeAt I atoms phi eps delta R2j := by
  have heps0 : 0 < (algBlock atoms phi eps delta).epsPrime :=
    algBlock_epsPrime_pos atoms phi eps delta
  have heps1 : (algBlock atoms phi eps delta).epsPrime < 1 := by
    rw [algBlock_epsPrime_eq atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol]
    linarith
  have hp0 : 0 < (algBlock atoms phi eps delta).deltaPrime :=
    algBlock_deltaPrime_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
      h_delta_pos
  have hp1 : (algBlock atoms phi eps delta).deltaPrime < 1 :=
    lt_of_le_of_lt
      (algBlock_deltaPrime_le_half atoms phi eps delta h_eps_pos h_eps_le hn
        hphi hvol h_delta_le) (by norm_num)
  unfold ttcPolyVolumeQueryBound volOfExpectedAlgQueryBound shapedVolumeQueryEnvelopeAt
  apply Finset.sum_le_sum
  intro j _
  exact I.expectedBound_le n (callBody atoms phi eps delta j)
    (algBlock atoms phi eps delta).epsPrime
    (algBlock atoms phi eps delta).deltaPrime (R2j j)
    hn heps0 heps1 hp0 hp1 (hadm j)

/-- **TTC compatibility at an arbitrary shape and an arbitrary per-call declared radius.**

This is the form a construction with a quantitative admissibility predicate consumes.  The
resulting envelope reads, per cube, the shape at that cube's own declared radius — which is
the paper's own per-polytope `R_i/gamma_i`, rather than a global normalisation. -/
theorem ttc_volume_estimate_of_cvShapedExpectedImplementationAt
    {Adm : AdmissiblePredicate} {shape : ComplexityShape}
    (I : CVShapedExpectedImplementation Adm shape)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (R2j : Fin (toDNFd (preprocess atoms phi)).length → Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (hadm : ∀ j, Adm n (callBody atoms phi eps (4 * delta / 5) j) (R2j j)) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      shapedVolumeQueryEnvelopeAt I atoms phi eps deltaRun R2j +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  let deltaRun := 4 * delta / 5
  let hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hd0 : 0 < deltaRun := by dsimp [deltaRun]; linarith
  have hd1 : deltaRun ≤ 1 := by dsimp [deltaRun]; linarith
  let V := I.algorithm n
  letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn1 hphi hvol
  have hmain := cappedTTC_fullTrajectory V atoms phi eps delta
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn1 hphi hvol
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact add_le_add
    (ttcPolyVolumeQueryBound_le_shapedVolumeQueryEnvelopeAt I atoms phi eps deltaRun R2j
      h_eps_pos h_eps_le hd0 hd1 hn1 hphi hvol hadm)
    (le_refl (canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun))

/-- TTC's own call bodies satisfy Cousins–Vempala's admissibility, so an implementation at
`cvAdm` needs no extra obligation at the call site. -/
theorem cvAdm_callBody
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    cvAdm n (callBody atoms phi eps delta j)
      (callSecondMoment atoms phi eps delta j) :=
  callBody_admissible atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol j

#print axioms shapedVolumeQueryEnvelopeAt
#print axioms ttcPolyVolumeQueryBound_le_shapedVolumeQueryEnvelopeAt
#print axioms ttc_volume_estimate_of_cvShapedExpectedImplementationAt
#print axioms cvAdm_callBody
#print axioms CVShapedExpectedImplementation.ofExpectedBound
#print axioms CVShapedExpectedImplementation.mono
#print axioms CVShapedExpectedImplementation.ofCapped
#print axioms ttcPolyVolumeQueryBound_le_shapedVolumeQueryEnvelope
#print axioms ttc_volume_estimate_of_cvShapedExpectedImplementation

end Ttc.CVShaped

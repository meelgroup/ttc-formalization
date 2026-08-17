import Ttc.Exec.CVSlowOneRunValid
import Ttc.Exec.CVValidInteriorBridge

/-!
# The total per-input families the runtime assembly consumes

`Ttc.TtcShapedRuntime.ttc_runtime_of_effectiveCertificates`
(`Ttc/Exec/TtcShapedRuntimeFromCertificates.lean:112`) takes four *total* families —
an index type `Omega n a`, a law, a cost and a value — plus their two instances and two
measurability facts, and one obligation `H` that is only asked on the **valid** inputs.
This file supplies the four families for the slow canonical route, together with
everything about them that holds unconditionally.  It does **not** prove `H`.

## The parameter choices

The construction runs on `interior a.1`, not on `a.1`: a convex set need not be Borel, so
the schedule cannot even be defined on `a.1`, while `interior a.1` is open hence
measurable.  This is the repository's standing `InteriorBridge` pattern
(`Ttc/Exec/CVValidInteriorBridge.lean`), and it is lossless because
`volume (interior a.1) = volume a.1` for convex `a.1`.

For an input `a = (K, eps, p)`:

* `slowRadius n a := circumR (interior a.1)` and `slowR2 n a := slowRadius n a ^ 2`;
* `slowEpsInt n a := a.2.1 / 2` — the construction is run at **half** the requested
  accuracy, leaving the other half for the interior/accuracy transport;
* `slowPhases n a := Ttc.CVSlowOneRunValid.slowCanonicalPhases n (slowR2 n a)`;
* `slowStreams n a := correctedRuntimeSamples (slowPhases n a) (slowEpsInt n a)`.

Every one of these depends on **data only**, so the index type, the cost and the value are
total with no case split, and the two measurability facts hold with no hypothesis on `a`.

## The `dite` guard on the law, and why it is not just `CVValidInput a`

The law's term contains the schedule
`Ttc.CVSlowCanonicalRetainedReference.slowCanonicalCostedActiveSchedule`, whose *first*
explicit argument is a proof of `1 ≤ n`, and whose positivity arguments are supplied in the
producer by `canonical_hq0 hn` / `canonical_hs0 hn` at `hn : 21 ≤ n`.  `CVValidInput` carries
no dimension hypothesis at all, and cannot: at `n = 0` the input `(univ, 1/2, 1/2)` is valid
(`Ttc.Space 0` is a single point, `ball 0 1 = univ`, `volume univ = 1 ≠ ⊤`, and `univ` is
convex), so `CVValidInput a → 1 ≤ n` is false.  The guard is therefore
`CVValidInput a ∧ 21 ≤ n`, which is the weakest guard under which the producer's own term
can be written down verbatim.  See the note at the end of this docstring.

## Main results

* `slowOmega`, `slowOmegaMeasurableSpace`, `slowOmegaNonempty` — the index type and its two
  instances;
* `slowCost`, `slowValue`, `measurable_slowCost`, `measurable_slowValue` — total and
  unconditionally measurable;
* `slowLaw`, `slowLaw_of_valid` — the law and its unfolding on the guarded branch;
* `slowFamilies_measurable` — the convenience bundle.

**Interface note (not discharged here).**  `H` in
`ttc_runtime_of_effectiveCertificates` is quantified over *all* `n`, while the producer
`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` requires `21 ≤ n`.  No total
choice of law can repair that: on the degenerate branch the law is a point mass at an
opaque point, and the certificate's `accuracy` field is then not provable.  Closing `H`
will need a dimension guard on the interface side.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVSlowTotalFamilies

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling
open Ttc.CVCorrectedRuntime
open Ttc.CVSlowOneRunValid
open Ttc.CVSlowCanonicalRetainedReference
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVGaussianHybridWeightedCertificate (gaussianScorePrefixReadout
  measurable_gaussianScorePrefixReadout)
open Ttc.CVSlowSourceReferenceCertificate (slowInitialPair slowSourceInitialVariance
  slowReferenceWarm)
open Ttc.CVSlowFullBodySourceSchedule (slowSourceSigmaSq)
open Ttc.CVEffectiveTotalise (CVValidInput)
open Ttc.TtcCircumRadius (circumR)
open scoped ENNReal Classical BigOperators

variable {n : Nat}

/-! ## Step 1 — the parameter choices -/

/-- The declared containment radius of the body the construction runs on: the circumradius
of `interior a.1`. -/
noncomputable def slowRadius (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  circumR (interior a.1)

/-- The declared squared-radius budget, taken at the body's own circumradius, so that the
producer's `hR2 : R ^ 2 ≤ R2` binder is `le_refl`. -/
noncomputable def slowR2 (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowRadius n a ^ 2

/-- The internal accuracy: half the requested accuracy. -/
noncomputable def slowEpsInt (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  a.2.1 / 2

/-- The canonical phase count at the declared squared radius. -/
noncomputable def slowPhases (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Nat :=
  slowCanonicalPhases n (slowR2 n a)

/-- The number of independent cooling streams. -/
noncomputable def slowStreams (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Nat :=
  correctedRuntimeSamples (slowPhases n a) (slowEpsInt n a)

theorem slowR2_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowR2 n a = circumR (interior a.1) ^ 2 := rfl

theorem slowEpsInt_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowEpsInt n a = a.2.1 / 2 := rfl

theorem slowPhases_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowPhases n a = slowCanonicalPhases n (slowR2 n a) := rfl

theorem slowStreams_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowStreams n a = correctedRuntimeSamples (slowPhases n a) (slowEpsInt n a) := rfl

/-! ## Step 2 — the index type -/

/-- **The index type of one run**: `slowStreams n a` independent heterogeneous retained
histories.  It depends on data only, never on a proof, so it is total. -/
abbrev slowOmega (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Type :=
  Fin (slowStreams n a) → HeterogeneousHistoryState (Ttc.Space n) (Ttc.Space n)

/-- The measurable structure on `slowOmega`, in the exact shape the assembly's `mOmega`
binder asks for. -/
@[reducible] def slowOmegaMeasurableSpace : ∀ (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n),
    MeasurableSpace (slowOmega n a) := fun _ _ ↦ inferInstance

/-- `slowOmega` is inhabited, in the exact shape the assembly's `nOmega` binder asks for. -/
theorem slowOmegaNonempty : ∀ (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n),
    Nonempty (slowOmega n a) := fun _ _ ↦ inferInstance

/-! ## Step 3 — the cost and the value -/

/-- **The recorded query cost of one run**: the sum, over the independent streams, of the
cost coordinate accumulated in that stream's history.  This is the producer's own cost
function, verbatim. -/
noncomputable def slowCost (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowOmega n a → ENNReal :=
  fun omega ↦ ∑ j, (omega j).1.1

/-- **The volume estimate one run reports**: the finite-prefix Gaussian score readout of
the stored score prefixes, at the canonical initial normalizer `chain m σsq (interior K) 0`.
This is the producer's own value function, verbatim, at the parameter choices of this
file. -/
noncomputable def slowValue (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowOmega n a → Real :=
  fun omega ↦ gaussianScorePrefixReadout (slowPhases n a) (slowPhases n a) (slowStreams n a)
    (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior a.1)
    (chain (slowPhases n a) (slowSourceSigmaSq n (slowSourceInitialVariance n))
      (interior a.1) 0)
    (independentStoredScorePrefixCurrent (slowPhases n a) omega)

/-- **The cost is measurable, with no hypothesis on the input.** -/
theorem measurable_slowCost (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measurable (slowCost n a) := by
  unfold slowCost
  apply Finset.measurable_sum
  intro j _hj
  exact measurable_fst.comp (measurable_fst.comp (measurable_pi_apply j))

/-- **The value is measurable, with no hypothesis on the input.**

Both halves are already proved: the readout by
`Ttc.CVGaussianHybridWeightedCertificate.measurable_gaussianScorePrefixReadout` and the
stored-prefix projection by
`Ttc.CVHeterogeneousRetainedPathLaw.measurable_independentStoredScorePrefixCurrent`. -/
theorem measurable_slowValue (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measurable (slowValue n a) :=
  (measurable_gaussianScorePrefixReadout _).comp
    (measurable_independentStoredScorePrefixCurrent _)

/-! ## Step 4 — the geometry of the interior body, on the guarded branch -/

/-- The body the construction runs on is measurable — unconditionally, because it is open.
This is the whole point of running on `interior a.1`. -/
theorem measurableSet_slowBody (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    MeasurableSet (interior a.1) :=
  Ttc.CVValidInteriorBridge.measurableSet_interior a.1

/-- The body the construction runs on is convex, on a valid input. -/
theorem convex_slowBody {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) :
    Convex Real (interior a.1) :=
  Ttc.CVValidInteriorBridge.convex_interior_of_valid h.2.2.2.1

/-- The body the construction runs on contains the unit ball, on a valid input. -/
theorem ball_subset_slowBody {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) :
    ball (0 : Ttc.Space n) 1 ⊆ interior a.1 :=
  Ttc.CVValidInteriorBridge.ball_subset_interior_of_valid h.2.2.2.2.1

/-- The stationary tails of the canonical schedule are probability measures, at the
parameter choices of this file.  Copied from
`Ttc.CVSlowOneRunValid.canonical_isProbabilityMeasure_slowStationaryTail`. -/
theorem slowIsProbabilityMeasure_stationaryTail
    {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) (hn : 21 ≤ n) (j : Nat) :
    IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a) (slowRadius n a))
      (slowSourceInitialVariance n) (interior a.1) j) :=
  canonical_isProbabilityMeasure_slowStationaryTail (R2 := slowR2 n a)
    (eps := slowEpsInt n a) (R := slowRadius n a) hn (measurableSet_slowBody n a)
    (convex_slowBody h) (ball_subset_slowBody h) j

/-- The canonical **costed** active schedule is Markov at the parameter choices of this
file.  This is the instance argument of `independentHeterogeneousRetainedPathLaw`. -/
theorem slowIsMarkovKernel_costedSchedule
    {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) (hn : 21 ≤ n) (i : Nat) :
    IsMarkovKernel (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
      (slowPhases n a + 1) (slowStreams n a)
      (q := slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
      (canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
      (canonical_hs0 hn) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
      (slowUniformSlack n (slowPhases n a) (interior a.1))
      (slowUniformBoundSq n (slowRadius n a)) i) := by
  letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a) (slowRadius n a))
      (slowSourceInitialVariance n) (interior a.1) j) := fun j ↦
    slowIsProbabilityMeasure_stationaryTail h hn j
  infer_instance

/-! ## Step 5 — the law -/

/-- **The law of one run, totalised.**

On the guarded branch this is the producer's own law
(`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical`), at the parameter choices
of this file: the independent heterogeneous retained path law of the canonical *costed*
active schedule on `interior a.1`, started from `slowInitialPair n`, run for
`slowPhases n a` phases across `slowStreams n a` independent streams.

Off the guarded branch it is a point mass; nothing in the assembly reads it there.  See
the file docstring for why the guard carries `21 ≤ n` and not merely `CVValidInput a`. -/
noncomputable def slowLaw (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measure (slowOmega n a) :=
  if h : CVValidInput a ∧ 21 ≤ n then
    @independentHeterogeneousRetainedPathLaw _ _ _ _ (slowStreams n a)
      (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
        (slowPhases n a + 1) (slowStreams n a)
        (q := slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
        (canonical_hq0 h.2 (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
        (canonical_hs0 h.2) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
        (slowUniformSlack n (slowPhases n a) (interior a.1))
        (slowUniformBoundSq n (slowRadius n a)))
      (fun i ↦ slowIsMarkovKernel_costedSchedule h.1 h.2 i)
      (slowInitialPair n) (slowPhases n a)
  else Measure.dirac (Classical.arbitrary _)

/-- **The unfolding of `slowLaw` on the guarded branch.**

Proof irrelevance makes the right-hand side independent of *which* proofs of
`CVValidInput a` and `21 ≤ n` are supplied, so a caller holding different proof terms still
gets this equation. -/
theorem slowLaw_of_valid {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) (hn : 21 ≤ n) :
    slowLaw n a =
      @independentHeterogeneousRetainedPathLaw _ _ _ _ (slowStreams n a)
        (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
          (slowPhases n a + 1) (slowStreams n a)
          (q := slowUniformQ n (slowPhases n a) (slowStreams n a) (slowEpsInt n a)
            (slowRadius n a))
          (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
          (canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
          (canonical_hs0 hn) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
          (slowUniformSlack n (slowPhases n a) (interior a.1))
          (slowUniformBoundSq n (slowRadius n a)))
        (fun i ↦ slowIsMarkovKernel_costedSchedule h hn i)
        (slowInitialPair n) (slowPhases n a) :=
  dif_pos ⟨h, hn⟩

/-- The same unfolding, spelled the way
`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` spells its own law — with
`slowCanonicalPhases n R2` and `correctedRuntimeSamples …` in place of `slowPhases` and
`slowStreams`, at `R2 := slowR2 n a`, `eps := slowEpsInt n a`, `R := slowRadius n a`,
`K := interior a.1`.  Landing this by `rfl` is the check that the parameter abbreviations
of this file really do reproduce the producer's term. -/
theorem slowLaw_of_valid_producerSpelling {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) (hn : 21 ≤ n) :
    slowLaw n a =
      @independentHeterogeneousRetainedPathLaw _ _ _ _
        (correctedRuntimeSamples (slowCanonicalPhases n (slowR2 n a)) (slowEpsInt n a))
        (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
          (slowCanonicalPhases n (slowR2 n a) + 1)
          (correctedRuntimeSamples (slowCanonicalPhases n (slowR2 n a)) (slowEpsInt n a))
          (q := slowUniformQ n (slowCanonicalPhases n (slowR2 n a))
            (correctedRuntimeSamples (slowCanonicalPhases n (slowR2 n a)) (slowEpsInt n a))
            (slowEpsInt n a) (slowRadius n a))
          (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
          (canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
          (canonical_hs0 hn) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
          (slowUniformSlack n (slowCanonicalPhases n (slowR2 n a)) (interior a.1))
          (slowUniformBoundSq n (slowRadius n a)))
        (fun i ↦ slowIsMarkovKernel_costedSchedule h hn i)
        (slowInitialPair n) (slowCanonicalPhases n (slowR2 n a)) :=
  slowLaw_of_valid h hn

/-- The same for the value: the producer's readout, spelled the producer's way. -/
theorem slowValue_producerSpelling (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowValue n a =
      fun omega ↦ gaussianScorePrefixReadout (slowCanonicalPhases n (slowR2 n a))
        (slowCanonicalPhases n (slowR2 n a))
        (correctedRuntimeSamples (slowCanonicalPhases n (slowR2 n a)) (slowEpsInt n a))
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior a.1)
        (chain (slowCanonicalPhases n (slowR2 n a))
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior a.1) 0)
        (independentStoredScorePrefixCurrent (slowCanonicalPhases n (slowR2 n a)) omega) :=
  rfl

/-- The same for the cost. -/
theorem slowCost_producerSpelling (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    slowCost n a = fun omega ↦ ∑ j, (omega j).1.1 := rfl

/-! ## Step 6 — the bundle -/

/-- **The two measurability facts the assembly's `hcost` / `hvalue` binders ask for**, in
one place and with no hypothesis on the input. -/
theorem slowFamilies_measurable :
    (∀ (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n), Measurable (slowCost n a)) ∧
    (∀ (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n), Measurable (slowValue n a)) :=
  ⟨measurable_slowCost, measurable_slowValue⟩

/-- **Shape check.**  The four families slot into the `H` binder of
`Ttc.TtcShapedRuntime.ttc_runtime_of_effectiveCertificates`
(`Ttc/Exec/TtcShapedRuntimeFromCertificates.lean:127`) with the two instances found by
`inferInstance`.  Elaborating this `Prop` is the check; it is not proved here. -/
example (effective : ∀ n, Ttc.CVAdaptive.VolumeInput n → Real) : Prop :=
  ∀ (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n), CVValidInput a →
    ∃ r : Measure (slowOmega n a),
      Ttc.CVSourceReferenceTVCapstone.SourceReferenceTVOneRunCertificate
        (slowLaw n a) r (slowCost n a) (slowValue n a) (effective n a) n
        (circumR a.1) a.2.1 ((1 - a.2.1) * (volume a.1).toReal)
        ((1 + a.2.1) * (volume a.1).toReal)

section AxiomCheck

#print axioms Ttc.CVSlowTotalFamilies.slowRadius
#print axioms Ttc.CVSlowTotalFamilies.slowR2
#print axioms Ttc.CVSlowTotalFamilies.slowEpsInt
#print axioms Ttc.CVSlowTotalFamilies.slowPhases
#print axioms Ttc.CVSlowTotalFamilies.slowStreams
#print axioms Ttc.CVSlowTotalFamilies.slowR2_eq
#print axioms Ttc.CVSlowTotalFamilies.slowEpsInt_eq
#print axioms Ttc.CVSlowTotalFamilies.slowPhases_eq
#print axioms Ttc.CVSlowTotalFamilies.slowStreams_eq
#print axioms Ttc.CVSlowTotalFamilies.slowOmega
#print axioms Ttc.CVSlowTotalFamilies.slowOmegaMeasurableSpace
#print axioms Ttc.CVSlowTotalFamilies.slowOmegaNonempty
#print axioms Ttc.CVSlowTotalFamilies.slowCost
#print axioms Ttc.CVSlowTotalFamilies.slowValue
#print axioms Ttc.CVSlowTotalFamilies.measurable_slowCost
#print axioms Ttc.CVSlowTotalFamilies.measurable_slowValue
#print axioms Ttc.CVSlowTotalFamilies.measurableSet_slowBody
#print axioms Ttc.CVSlowTotalFamilies.convex_slowBody
#print axioms Ttc.CVSlowTotalFamilies.ball_subset_slowBody
#print axioms Ttc.CVSlowTotalFamilies.slowIsProbabilityMeasure_stationaryTail
#print axioms Ttc.CVSlowTotalFamilies.slowIsMarkovKernel_costedSchedule
#print axioms Ttc.CVSlowTotalFamilies.slowLaw
#print axioms Ttc.CVSlowTotalFamilies.slowLaw_of_valid
#print axioms Ttc.CVSlowTotalFamilies.slowLaw_of_valid_producerSpelling
#print axioms Ttc.CVSlowTotalFamilies.slowValue_producerSpelling
#print axioms Ttc.CVSlowTotalFamilies.slowCost_producerSpelling
#print axioms Ttc.CVSlowTotalFamilies.slowFamilies_measurable

end AxiomCheck

end Ttc.CVSlowTotalFamilies

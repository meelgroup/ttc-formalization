import Ttc.Exec.TTCSourceSharpOperationalFinal

/-!
# Full canonical-owner TTC sampling cost

The canonical-owner construction draws every per-cube marked Poisson stream at
level zero.  The infinite TTC trajectory after level zero is obtained only by
binomial thinning, which makes no further membership queries.  Consequently,
the cost stored in the zeroth trajectory state is the sampling cost of the
*entire* trajectory, not merely an arbitrarily chosen finite prefix.

This file exposes that fact through a `J`-free query-cost API and restates the
source-sharp operational theorem using it.  The older finite-prefix statements
remain available for compatibility.
-/

namespace Ttc.CostedInitialThinningTrajectory

open MeasureTheory
open scoped ENNReal BigOperators

variable {L : Nat}

/-- The membership-query cost of the complete thinning trajectory.  All
costly marked-Poisson calls occur in the initial state; every later transition
is query-free thinning. -/
def fullTrajectoryQueryCost
    (omega : Nat → ENNReal × (Fin L → Nat)) : ENNReal :=
  (omega 0).1

theorem measurable_fullTrajectoryQueryCost :
    Measurable (fullTrajectoryQueryCost (L := L)) :=
  measurable_fst.comp (measurable_pi_apply 0)

/-- Every nonempty prefix already contains the complete trajectory query
cost.  In particular `J = 1` accounts for all samples used by the infinite
count path consumed by `ttcPolyRun`. -/
theorem finitePrefixQueryCost_eq_fullTrajectoryQueryCost
    {J : Nat} (hJ : 0 < J)
    (omega : Nat → ENNReal × (Fin L → Nat)) :
    finitePrefixQueryCost J omega = fullTrajectoryQueryCost omega := by
  unfold finitePrefixQueryCost fullTrajectoryQueryCost
  rw [Finset.sum_eq_single 0]
  · simp [levelQueryIncrement]
  · intro b hb hb0
    simp [levelQueryIncrement, hb0]
  · simp [hJ]

/-- Exact expected full-trajectory cost under the initial-thinning law. -/
theorem lintegral_fullTrajectoryQueryCost_eq_initialMean
    (nu0 : Measure (ENNReal × (Fin L → Nat))) [IsProbabilityMeasure nu0] :
    (∫⁻ omega, fullTrajectoryQueryCost omega ∂costedTrajLaw nu0) =
      ∫⁻ z, z.1 ∂nu0 := by
  simpa only [finitePrefixQueryCost_eq_fullTrajectoryQueryCost (J := 1)
    (by decide)] using
    (lintegral_finitePrefixQueryCost_eq_initialMean nu0 (J := 1) (by decide))

end Ttc.CostedInitialThinningTrajectory

namespace Ttc.CostedCanonicalOwnerTTCPlugin

open MeasureTheory ProbabilityTheory
open Ttc.CostedInitialThinningTrajectory
open scoped ENNReal

variable {I : Type*} [Fintype I] {n : Nat}
variable {A : Type*} {atoms : A → LinAtom n} {phi : BForm A}
variable {eps delta : Real}

/-- Actual volume-query cost plus the sampling-query cost of the complete
canonical-owner trajectory. -/
noncomputable def canonicalFullPolyQueryCost
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    V.Ω × CostedCountPath (algIndex atoms phi eps delta) → ENNReal :=
  fun z ↦ ttcPolyVolumeQueryCost atoms phi eps delta V z.1 +
    fullTrajectoryQueryCost z.2

theorem measurable_canonicalFullPolyQueryCost
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    letI := V.mΩ
    Measurable (canonicalFullPolyQueryCost
      (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) := by
  letI := V.mΩ
  exact ((measurable_ttcPolyVolumeQueryCost atoms phi eps delta V).comp
    measurable_fst).add
      (measurable_fullTrajectoryQueryCost.comp measurable_snd)

/-- The old prefix-indexed cost is pointwise the full operational cost as soon
as the prefix is nonempty. -/
theorem canonicalActualPolyQueryCost_eq_full
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    {J : Nat} (hJ : 0 < J)
    (z : V.Ω × CostedCountPath (algIndex atoms phi eps delta)) :
    canonicalActualPolyQueryCost
        (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P J z =
      canonicalFullPolyQueryCost
        (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P z := by
  unfold canonicalActualPolyQueryCost canonicalFullPolyQueryCost
  rw [finitePrefixQueryCost_eq_fullTrajectoryQueryCost hJ]

/-- Exact decomposition of the full operational TTC query cost. -/
theorem lintegral_canonicalFullPolyQueryCost
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    letI := V.mΩ
    (∫⁻ z, canonicalFullPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P z
        ∂canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) =
      (∫⁻ omega, ttcPolyVolumeQueryCost atoms phi eps delta V omega ∂V.μ) +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ := by
  letI := V.mΩ
  rw [← lintegral_canonicalActualPolyQueryCost V P (J := 1) (by decide)]
  apply lintegral_congr
  intro z
  exact (canonicalActualPolyQueryCost_eq_full V P (J := 1) (by decide) z).symm

/-- Full-cost version of the generic operational bound, without an arbitrary
finite-prefix parameter. -/
theorem lintegral_canonicalFullPolyQueryCost_le
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    letI := V.mΩ
    (∫⁻ z, canonicalFullPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P z
        ∂canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) ≤
      ttcPolyVolumeQueryBound atoms phi eps delta V +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ := by
  letI := V.mΩ
  rw [lintegral_canonicalFullPolyQueryCost V P]
  exact add_le_add (lintegral_ttcPolyVolumeQueryCost_le atoms phi eps delta V) le_rfl

end Ttc.CostedCanonicalOwnerTTCPlugin

namespace Ttc.TTCSourceSharpOperationalFinal

open MeasureTheory ProbabilityTheory Set
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CostedCanonicalOwnerTTCPlugin
open scoped ENNReal Classical

variable {A : Type*} {n : Nat}

/-- J-free source-sharp operational headline.  The second conjunct integrates
the actual volume cost and all marked-Poisson sampling queries used to create
the complete TTC trajectory. -/
theorem sourceSharpCappedPolyHybridTTC_fullTrajectory
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    letI := V.mΩ
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤
      ((canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P)
        (canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P)).toReal) ∧
    ((∫⁻ z, canonicalFullPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P z
        ∂canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := deltaRun) V P) ≤
      ttcSourceVolumeQueryEnvelope atoms phi eps deltaRun runtimeConstant radialR +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  let deltaRun := 4 * delta / 5
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn hphi hvol
  have hmain := sourceSharpCappedPolyHybridTTC_final atoms phi eps delta
    runtimeConstant radialR Omega oneLaw cost value hcert hconstant h_eps_pos
    h_eps_le h_delta_pos h_delta_le hn hphi hvol (J := 1) (by decide)
  refine ⟨hmain.1, ?_⟩
  refine (lintegral_congr fun z ↦ ?_).trans_le hmain.2
  exact (canonicalActualPolyQueryCost_eq_full V P (J := 1) (by decide) z).symm

#print axioms Ttc.CostedInitialThinningTrajectory.finitePrefixQueryCost_eq_fullTrajectoryQueryCost
#print axioms Ttc.CostedCanonicalOwnerTTCPlugin.lintegral_canonicalFullPolyQueryCost
#print axioms sourceSharpCappedPolyHybridTTC_fullTrajectory

end Ttc.TTCSourceSharpOperationalFinal

namespace Ttc.TTCSourceSharpOperationalTheorem

open MeasureTheory ProbabilityTheory Set
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open scoped ENNReal Classical

variable {A : Type*} {n : Nat} {I : Type*} [Fintype I]

/-- TTC's estimate paired with the actual query cost of its complete
canonical-owner trajectory. -/
noncomputable def canonicalFullOperationalPair
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    V.Ω × CostedCountPath (algIndex atoms phi eps delta) → Real × ENNReal :=
  fun z ↦
    (ttcPolyRun atoms phi eps delta V.toVolumeAlgorithm z.1
      (Ttc.SequentialCostedPathLumping.pathMap Prod.snd z.2),
    canonicalFullPolyQueryCost
      (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P z)

theorem measurable_canonicalFullOperationalPair
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    letI := V.mΩ
    Measurable (canonicalFullOperationalPair V P) := by
  letI := V.mΩ
  let stateMap :
      V.Ω × CostedCountPath (algIndex atoms phi eps delta) →
        V.Ω × CountPath (algIndex atoms phi eps delta) :=
    Prod.map id (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
  have hstate : Measurable stateMap := measurable_id.prodMap
    (Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd)
  have hout : Measurable (fun z :
      V.Ω × CountPath (algIndex atoms phi eps delta) ↦
      ttcPolyRun atoms phi eps delta V.toVolumeAlgorithm z.1 z.2) :=
    measurable_fst.comp
      (measurable_polyPair atoms phi eps delta V.toVolumeAlgorithm 0 0)
  exact (hout.comp hstate).prodMk
    (measurable_canonicalFullPolyQueryCost V P)

/-! ## The same law in the elementary cost model

`Ttc.canonicalFullPolyQueryCost` charges the volume calls at their actual query counts and
the sampler at the **level-zero** marked Poisson process
(`Ttc.fullTrajectoryQueryCost` is `(omega 0).1`, thinning being free).  The cost below
charges `Model/Pseudocode`'s three elementary costs instead, folded along the run by
`Ttc.elemRunCost`, so the samples paid for are the ones the absorption loop actually
reaches.

The volume side stays as it is — `Ttc.ttcPolyVolumeQueryCost` is the *actual* query count
at the run's own coin, with no supplied price — and is converted into the elementary model
by charging `Ttc.memCost n r` per query, which is `Ttc.volCallCost` summed over the cubes.
So `Q` never appears as a binder: it is read off the run.  `Tw` is the walk length the run
is *configured* with, an input to the algorithm rather than a bound on it. -/

/-- **The cost of one run in the elementary model**: every volume query charged
`Ttc.memCost n r`, plus the loop's own removal, thinning, draw and generation charges. -/
noncomputable def elemFullCost
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n) (r Tw : Nat)
    (z : V.Ω × CostedCountPath (algIndex atoms phi eps delta)) : ENNReal :=
  (memCost n r : ENNReal) * ttcPolyVolumeQueryCost atoms phi eps delta V z.1
    + (ttcPolyElemCost atoms phi eps delta V.toVolumeAlgorithm z.1
        (Ttc.SequentialCostedPathLumping.pathMap Prod.snd z.2) r 0 Tw : ENNReal)

set_option maxHeartbeats 1000000 in
theorem measurable_elemFullCost
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n) (r Tw : Nat) :
    letI := V.mΩ
    Measurable (elemFullCost (atoms := atoms) (phi := phi) (eps := eps) (delta := delta)
      V r Tw) := by
  letI := V.mΩ
  have hstate : Measurable (fun z : V.Ω × CostedCountPath (algIndex atoms phi eps delta) ↦
      (z.1, Ttc.SequentialCostedPathLumping.pathMap Prod.snd z.2)) :=
    measurable_fst.prodMk
      ((Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd).comp measurable_snd)
  have hloop := (measurable_ttcPolyElemCost_ennreal atoms phi eps delta
    V.toVolumeAlgorithm r 0 Tw).comp hstate
  exact (measurable_const.mul
    ((measurable_ttcPolyVolumeQueryCost atoms phi eps delta V).comp measurable_fst)).add hloop

/-- **TTC's estimate paired with its elementary-model cost.**  The first component is
`Ttc.canonicalFullOperationalPair`'s verbatim, so the estimate's law does not move. -/
noncomputable def elemFullOperationalPair
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n) (r Tw : Nat) :
    V.Ω × CostedCountPath (algIndex atoms phi eps delta) → Real × ENNReal :=
  fun z ↦
    (ttcPolyRun atoms phi eps delta V.toVolumeAlgorithm z.1
      (Ttc.SequentialCostedPathLumping.pathMap Prod.snd z.2),
    elemFullCost (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V r Tw z)

theorem measurable_elemFullOperationalPair
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n) (r Tw : Nat) :
    letI := V.mΩ
    Measurable (elemFullOperationalPair (atoms := atoms) (phi := phi) (eps := eps)
      (delta := delta) V r Tw) := by
  letI := V.mΩ
  have hstate : Measurable (fun z : V.Ω × CostedCountPath (algIndex atoms phi eps delta) ↦
      (z.1, Ttc.SequentialCostedPathLumping.pathMap Prod.snd z.2)) :=
    measurable_fst.prodMk
      ((Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd).comp measurable_snd)
  have hout : Measurable (fun z :
      V.Ω × CountPath (algIndex atoms phi eps delta) ↦
      ttcPolyRun atoms phi eps delta V.toVolumeAlgorithm z.1 z.2) :=
    measurable_fst.comp
      (measurable_polyPair atoms phi eps delta V.toVolumeAlgorithm 0 0)
  exact (hout.comp hstate).prodMk (measurable_elemFullCost V r Tw)


/-- Public output law for the estimate and the complete operational query
cost. -/
noncomputable def canonicalFullOperationalLaw
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) : Measure (Real × ENNReal) := by
  letI := V.mΩ
  exact Measure.map (canonicalFullOperationalPair V P)
    (canonicalCostedPolyJoint
      (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)

/-- **The same law with the elementary cost model in the second coordinate.**

Same joint randomness, same estimate — `Ttc.elemFullOperationalPair`'s first component is
`Ttc.canonicalFullOperationalPair`'s verbatim — and `Ttc.elemFullCost` in place of
`Ttc.canonicalFullPolyQueryCost`. -/
noncomputable def elemFullOperationalLaw
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (r Tw : Nat) : Measure (Real × ENNReal) := by
  letI := V.mΩ
  exact Measure.map (elemFullOperationalPair V r Tw)
    (canonicalCostedPolyJoint
      (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)

/-- **Changing the cost model does not move the estimate's law.**

Both laws are the same joint pushed along pairs with the *same* first component, so the
first marginals are equal — which is what lets an accuracy statement proved for one be read
off the other, with no re-proof. -/
theorem map_fst_elemFullOperationalLaw
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (r Tw : Nat) :
    Measure.map Prod.fst (elemFullOperationalLaw V P r Tw)
      = Measure.map Prod.fst (canonicalFullOperationalLaw V P) := by
  letI := V.mΩ
  unfold elemFullOperationalLaw canonicalFullOperationalLaw
  rw [Measure.map_map measurable_fst (measurable_elemFullOperationalPair V r Tw),
    Measure.map_map measurable_fst (measurable_canonicalFullOperationalPair V P)]
  rfl

#print axioms measurable_elemFullOperationalPair
#print axioms map_fst_elemFullOperationalLaw

instance canonicalFullOperationalLaw.instIsProbabilityMeasure
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ) :
    IsProbabilityMeasure (canonicalFullOperationalLaw V P) := by
  letI := V.mΩ
  unfold canonicalFullOperationalLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_canonicalFullOperationalPair V P).aemeasurable

/-- Projection of an internal same-law accuracy/cost result to the public
`(estimate, full cost)` law. -/
theorem canonicalFullOperationalLaw_accuracy_and_expectedQueries
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    {failure : Real} {B : ENNReal}
    (hacc : 1 - failure ≤
      ((canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
        (canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)).toReal)
    (hcost : (∫⁻ z, canonicalFullPolyQueryCost
        (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P z
      ∂canonicalCostedPolyJoint
        (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) ≤ B) :
    (1 - failure ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤ B) := by
  letI := V.mΩ
  let mu := canonicalCostedPolyJoint
    (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P
  have hout := measurable_canonicalFullOperationalPair V P
  constructor
  · have hS : MeasurableSet
        {r : Real × ENNReal | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)} :=
      measurableSet_Icc.preimage measurable_fst
    unfold canonicalFullOperationalLaw
    change 1 - failure ≤
      ((Measure.map (canonicalFullOperationalPair V P)
        (canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P))
        {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}).toReal
    rw [Measure.map_apply hout hS]
    exact hacc
  · unfold canonicalFullOperationalLaw
    rw [lintegral_map measurable_snd hout]
    exact hcost

/-- Public J-free TTC headline.  Its `.2` coordinate is the actual cost of all
volume calls and all samples generated for the complete TTC count trajectory. -/
theorem ttc_volume_estimate_operational_sourceSharp_fullTrajectory
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    letI := V.mΩ
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      ttcSourceVolumeQueryEnvelope atoms phi eps deltaRun runtimeConstant radialR +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) := by
  let deltaRun := 4 * delta / 5
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn hphi hvol
  have hmain := sourceSharpCappedPolyHybridTTC_fullTrajectory atoms phi eps delta
    runtimeConstant radialR Omega oneLaw cost value hcert hconstant h_eps_pos
    h_eps_le h_delta_pos h_delta_le hn hphi hvol
  exact canonicalFullOperationalLaw_accuracy_and_expectedQueries V P hmain.1 hmain.2

#print axioms canonicalFullOperationalLaw_accuracy_and_expectedQueries
#print axioms ttc_volume_estimate_operational_sourceSharp_fullTrajectory

end Ttc.TTCSourceSharpOperationalTheorem

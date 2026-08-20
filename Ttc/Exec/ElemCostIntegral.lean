/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.TTCFullTrajectoryQueryCost

/-!
# The elementary cost model's expectation

`Ttc.TTCSourceSharpOperationalTheorem.elemFullOperationalLaw`'s second coordinate is
`Ttc.elemFullCost`, which splits into a volume half and a loop half.  The two are bounded
by completely different means, and neither needs anything from the other:

* the **volume half** `memCost n r · ttcPolyVolumeQueryCost` reads only the volume coin, so
  its integral against the joint collapses to an integral against `V.μ`
  (`Measure.lintegral_compProd`) and is bounded by the oracle's own certified envelope —
  exactly as `Ttc.CostedCanonicalOwnerTTCPlugin.lintegral_canonicalActualPolyQueryCost`
  does it;
* the **loop half** `Ttc.elemRunCost` is bounded *pointwise* by `Ttc.elemRunCost_le`, so its
  integral against a probability measure is bounded by the same constant with no kernel
  manipulation at all.

That asymmetry is why the elementary model is cheaper to integrate than the level-zero one:
the loop half never has to be pushed through the trajectory kernel.
-/

namespace Ttc.TTCSourceSharpOperationalTheorem

open MeasureTheory ProbabilityTheory
open Ttc.CostedCanonicalOwnerTTCPlugin Ttc.CostedInitialThinningTrajectory
open scoped ENNReal

variable {A : Type*} {n : Nat} {I : Type*} [Fintype I]

set_option maxHeartbeats 1000000 in
/-- **The elementary cost, in expectation.**

`B` bounds the loop half **almost everywhere** — not pointwise.  That matters: the loop
half is bounded via `Ttc.elemRunCost_le`, whose `Ttc.Terminates` guard is *false* at some
coins (`Exec/Complexity` §2), so a pointwise hypothesis would be one nothing satisfies
(`CLAUDE.md` §11).  Almost everywhere is what `Ttc.trajLaw_ae_terminates` can supply. -/
theorem lintegral_snd_elemFullOperationalLaw_le
    {atoms : A → LinAtom n} {phi : BForm A} {eps delta : Real}
    (V : ExpectedQueryVolumeAlgorithm n)
    (P : @CanonicalOwnerTrajectoryPlugin I _
      (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (r Tw : Nat) (B : ENNReal)
    (hB : ∀ᵐ z ∂canonicalCostedPolyJoint (atoms := atoms) (phi := phi) (eps := eps)
        (delta := delta) V P,
      ((ttcPolyElemCost atoms phi eps delta V.toVolumeAlgorithm z.1
        (Ttc.SequentialCostedPathLumping.pathMap Prod.snd z.2) r 0 Tw : Nat) : ENNReal) ≤ B) :
    (∫⁻ x, x.2 ∂elemFullOperationalLaw V P r Tw)
      ≤ (memCost n r : ENNReal) * ttcPolyVolumeQueryBound atoms phi eps delta V + B := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  have hvolm : Measurable (fun z : V.Ω × CostedCountPath (algIndex atoms phi eps delta) ↦
      ttcPolyVolumeQueryCost atoms phi eps delta V z.1) :=
    (measurable_ttcPolyVolumeQueryCost atoms phi eps delta V).comp measurable_fst
  -- push the lintegral through the map defining the law
  have hmap : (∫⁻ x, x.2 ∂elemFullOperationalLaw V P r Tw)
      = ∫⁻ z, elemFullCost (atoms := atoms) (phi := phi) (eps := eps) (delta := delta)
          V r Tw z ∂canonicalCostedPolyJoint V P := by
    unfold elemFullOperationalLaw
    rw [lintegral_map measurable_snd (measurable_elemFullOperationalPair V r Tw)]
    rfl
  rw [hmap]
  unfold elemFullCost
  rw [lintegral_add_left
    (f := fun z : V.Ω × CostedCountPath (algIndex atoms phi eps delta) ↦
      (memCost n r : ENNReal) * ttcPolyVolumeQueryCost atoms phi eps delta V z.1)
    (measurable_const.mul hvolm)]
  refine add_le_add ?_ ?_
  · -- volume half: only the volume coin is read
    rw [lintegral_const_mul _ hvolm]
    gcongr
    have hjoint : canonicalCostedPolyJoint (atoms := atoms) (phi := phi) (eps := eps)
        (delta := delta) V P = V.μ.compProd P.trajectoryKernel := rfl
    rw [hjoint, Measure.lintegral_compProd hvolm]
    simpa using lintegral_ttcPolyVolumeQueryCost_le atoms phi eps delta V
  · -- loop half: pointwise, against a probability measure
    refine le_trans (lintegral_mono_ae hB) ?_
    simp

#print axioms lintegral_snd_elemFullOperationalLaw_le

end Ttc.TTCSourceSharpOperationalTheorem

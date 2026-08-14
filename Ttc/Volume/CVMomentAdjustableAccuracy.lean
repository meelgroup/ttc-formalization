/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVAdjustableVolumeAlgorithm
import Ttc.Volume.CVMomentVolumeComposition

/-!
# Running the adjustable CV oracle on the moment-truncated body

The unconditional Markov truncation is slightly enlarged to the runtime ball
`closedBall 0 (markovRuntimeC n (sqrt R2) eta * sqrt n)`.  This enlargement has two
advantages: it still loses at most an `eta` fraction of volume, and it automatically
contains the unit ball required by the public volume-oracle interface.

The capstone applies the already proved adjustable-radius CV algorithm to that bounded
body and transports its estimate back to the original moment-bounded input.  This is an
accuracy theorem; the expected membership-query law is assembled separately in `Ttc.Exec`.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Ttc.CV

variable {n : Nat}

/-- The closed moment-runtime truncation used by the polynomial fallback. -/
noncomputable def momentRuntimeBody (n : Nat) (K : Set (Space n))
    (R2 eta : Real) : Set (Space n) :=
  closure K ∩ closedBall 0
    (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n)

theorem convex_momentRuntimeBody {K : Set (Space n)} {R2 eta : Real}
    (hK : Convex Real K) : Convex Real (momentRuntimeBody n K R2 eta) := by
  exact hK.closure.inter (convex_closedBall 0 _)

theorem isClosed_momentRuntimeBody {K : Set (Space n)} {R2 eta : Real} :
    IsClosed (momentRuntimeBody n K R2 eta) := by
  exact isClosed_closure.inter isClosed_closedBall

theorem ball_one_subset_momentRuntimeBody (hn : 1 <= n)
    {K : Set (Space n)} {R2 eta : Real}
    (hball : ball (0 : Space n) 1 ⊆ K) :
    ball (0 : Space n) 1 ⊆ momentRuntimeBody n K R2 eta := by
  have hnR : (1 : Real) <= n := by exact_mod_cast hn
  have hsqrt : (1 : Real) <= Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt hnR
  have hrad : (1 : Real) <=
      markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n := by
    nlinarith [one_le_markovRuntimeC n (Real.sqrt R2) eta]
  intro x hx
  refine ⟨subset_closure (hball hx), ?_⟩
  exact mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp hx).le.trans hrad)

theorem momentRuntimeBody_subset_closure (K : Set (Space n)) (R2 eta : Real) :
    momentRuntimeBody n K R2 eta ⊆ closure K := inter_subset_left

/-- Enlarging the raw Markov ball to the runtime ball cannot increase the lost volume. -/
theorem volume_momentRuntimeBody_mem_relErr
    (hn : 1 <= n) {K : Set (Space n)} {R2 eta : Real}
    (hK : Ttc.CVAdmissible K R2) (hR2 : 0 < R2) (heta : 0 < eta) :
    (volume (momentRuntimeBody n K R2 eta)).toReal ∈
      Ttc.relErr eta (volume K).toReal := by
  let A := closure K ∩ closedBall 0
    (markovMomentTruncationRadius (Real.sqrt R2) eta)
  let B := momentRuntimeBody n K R2 eta
  have hraw : (volume A).toReal ∈ Ttc.relErr eta (volume K).toReal := by
    simpa only [A] using volume_markovClosure_mem_relErr hK hR2 heta
  have hAB : A ⊆ B := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    exact mem_closedBall_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx.2).trans
      (markovMomentTruncationRadius_le_C_sqrt_n hn))
  have hBcl : B ⊆ closure K := inter_subset_left
  have hvolcl : volume (closure K) = volume K :=
    Arlib.addHaar_closure_of_convex volume hK.1
  have hKtop : volume K ≠ ⊤ := hK.2.2.2.1
  have hAclTop : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop ((measure_mono (hAB.trans hBcl)).trans_eq hvolcl)
  have hBtop : volume B ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop ((measure_mono hBcl).trans_eq hvolcl)
  have hlow : (volume A).toReal <= (volume B).toReal :=
    ENNReal.toReal_mono hBtop (measure_mono hAB)
  have hupp : (volume B).toReal <= (volume K).toReal := by
    rw [← hvolcl]
    exact ENNReal.toReal_mono (hvolcl ▸ hKtop) (measure_mono hBcl)
  rcases hraw with ⟨hrawLo, _hrawHi⟩
  constructor
  · exact hrawLo.trans hlow
  · have hKnonneg : 0 <= (volume K).toReal := ENNReal.toReal_nonneg
    nlinarith

/-- Relative-error transport from the enlarged moment-runtime body to the original body. -/
theorem mem_relErr_momentRuntimeBody_trans
    (hn : 1 <= n) {K : Set (Space n)} {R2 eta eps x : Real}
    (hK : Ttc.CVAdmissible K R2) (hR2 : 0 < R2) (heta : 0 < eta)
    (heps : 0 <= eps)
    (hx : x ∈ Ttc.relErr eps (volume (momentRuntimeBody n K R2 eta)).toReal) :
    x ∈ Ttc.relErr (eps + eta + eps * eta) (volume K).toReal := by
  exact relErr_trans heps heta.le (volume K).toReal_nonneg hx
    (volume_momentRuntimeBody_mem_relErr hn hK hR2 heta)

/-- A completely proved moment-input accuracy theorem: run the public adjustable CV
algorithm on the polynomial-radius Markov truncation and transport the result back to `K`.

Both the inner estimator and truncation spend `epsilon/4`; for `epsilon <= 1` their
composed relative error is at most `epsilon`. -/
theorem adjustable_moment_volume_accuracy
    (hn : 21 <= n) {K : Set (Space n)} {R2 epsilon p : Real}
    (hK : Ttc.CVAdmissible K R2) (hR2 : 0 < R2)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon <= 1)
    (hp : 0 < p) (hp1 : p < 1) :
    let V := adjustableConcreteVolumeAlgorithm n hn
    let eta := epsilon / 4
    let epsInner := epsilon / 4
    let B := momentRuntimeBody n K R2 eta
    1 - p <= V.μ.real
      {omega | V.est B epsInner p omega ∈
        Ttc.relErr epsilon (volume K).toReal} := by
  dsimp only
  let V := adjustableConcreteVolumeAlgorithm n hn
  let eta : Real := epsilon / 4
  let epsInner : Real := epsilon / 4
  let B := momentRuntimeBody n K R2 eta
  have hn1 : 1 <= n := by omega
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hepsInner : 0 < epsInner := by dsimp [epsInner]; positivity
  have hBconv : Convex Real B := by
    simpa only [B] using convex_momentRuntimeBody (n := n) (R2 := R2) (eta := eta) hK.1
  have hBball : ball (0 : Space n) 1 ⊆ B := by
    simpa only [B] using ball_one_subset_momentRuntimeBody (n := n) hn1 hK.2.1
  have hBtop : volume B ≠ ⊤ := by
    have hvolcl : volume (closure K) = volume K :=
      Arlib.addHaar_closure_of_convex volume hK.1
    exact ne_top_of_le_ne_top hK.2.2.2.1
      ((measure_mono (momentRuntimeBody_subset_closure (n := n) K R2 eta)).trans_eq hvolcl)
  have hcorrect : 1 - p <= V.μ.real
      {omega | V.est B epsInner p omega ∈
        Ttc.relErr epsInner (volume B).toReal} :=
    V.correct B epsInner p hepsInner hp hp1 hBconv hBball hBtop
  letI : IsProbabilityMeasure V.μ := V.isProb
  refine hcorrect.trans (measureReal_mono ?_)
  intro omega homega
  have htrans := mem_relErr_momentRuntimeBody_trans hn1 hK hR2 heta hepsInner.le homega
  exact Ttc.CV.relErr_mono (by
      dsimp [epsInner, eta]
      nlinarith) (volume K).toReal_nonneg htrans

/-- Accuracy and polynomial geometry in one statement.  This is the semantic half of the
moment-radius fallback that the costed execution theorem can consume directly. -/
theorem adjustable_moment_accuracy_and_radius
    (hn : 21 <= n) {K : Set (Space n)} {R2 epsilon p : Real}
    (hK : Ttc.CVAdmissible K R2) (hR2 : 0 < R2)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon <= 1)
    (hp : 0 < p) (hp1 : p < 1) :
    let eta := epsilon / 4
    let C := markovRuntimeC n (Real.sqrt R2) eta
    let B := momentRuntimeBody n K R2 eta
    let V := adjustableConcreteVolumeAlgorithm n hn
    B ⊆ closedBall 0 (C * Real.sqrt n) ∧
      C ^ 2 * (n : Real) <= 2 * (n : Real) + 8 * R2 / epsilon ∧
      1 - p <= V.μ.real
        {omega | V.est B (epsilon / 4) p omega ∈
          Ttc.relErr epsilon (volume K).toReal} := by
  dsimp only
  let eta : Real := epsilon / 4
  let C : Real := markovRuntimeC n (Real.sqrt R2) eta
  let B := momentRuntimeBody n K R2 eta
  let V := adjustableConcreteVolumeAlgorithm n hn
  have hn1 : 1 <= n := by omega
  have heta : 0 < eta := by dsimp [eta]; positivity
  constructor
  · intro x hx
    exact hx.2
  constructor
  · have hC := cvAdmissible_markovRuntimeC_sq_mul_n_le hn1 hR2 heta
    calc
      C ^ 2 * (n : Real) <= 2 * (n : Real) + 2 * R2 / eta := by
        simpa only [C] using hC
      _ = 2 * (n : Real) + 8 * R2 / epsilon := by
        dsimp only [eta]
        field_simp [hepsilon.ne']
        <;> ring
  · simpa only [V, B, eta] using
      (adjustable_moment_volume_accuracy hn hK hR2 hepsilon hepsilon1 hp hp1)

#print axioms volume_momentRuntimeBody_mem_relErr
#print axioms mem_relErr_momentRuntimeBody_trans
#print axioms adjustable_moment_volume_accuracy
#print axioms adjustable_moment_accuracy_and_radius

end Ttc.CVAdaptive

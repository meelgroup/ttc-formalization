/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVTheorem11
import Ttc.Volume.CVMomentInputBridge
import Ttc.Volume.RadBound
import Ttc.Exec.TTCCVExpectedImplementation

/-!
# The canonical radial data for the TTC runtime capstones

The public expected-query interfaces of the Cousins--Vempala runtime chain carry a free
function argument `radialR : ∀ n, Set (Space n) → ℝ` together with a companion
`radialN`, and their constructors demand

* `hrad  : ∀ n K R2, CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2`,
* `hNpos : ∀ n K, 0 < radialN n K`,
* `hNle  : ∀ n K R2, CVAdmissible K R2 → radialN n K ≤ max 1 R2`

(see `Ttc/Exec/CVCappedRadialLogExpectedImplementation.lean` and
`Ttc/Exec/CVSourceDimensionGuardTwentyOne.lean`).  Until now nobody supplied a concrete
`radialR`.

This file supplies the *canonical* choice and discharges all three conditions.  The
choice is forced by the interface itself: `CVAdmissible K R2` says, among other things,
`cvSecondMoment K ≤ R2`, so `R2` **is** an upper bound for `E_K‖X‖²`, and the paper's `R`
in the runtime theorem is `E_K[‖X‖²]^{1/2}`.  Hence

* `ttcRadialR n K := Real.sqrt (cvSecondMoment K)`,
* `ttcRadialN n K := max 1 (cvSecondMoment K)`.

No geometric radius is invented here; the two definitions are read straight off the
admissibility predicate, which is what makes the three obligations one-liners.
-/

set_option autoImplicit false

namespace Ttc.TtcRadialGeometry

open MeasureTheory

/-- The canonical radial parameter for the runtime interfaces: the square root of the
second moment of the uniform law on `K`, i.e. the paper's `R = E_K[‖X‖²]^{1/2}`. -/
noncomputable def ttcRadialR (n : Nat) (K : Set (Ttc.Space n)) : Real :=
  Real.sqrt (Ttc.cvSecondMoment K)

/-- The canonical clipped radial normalisation for the runtime interfaces. -/
noncomputable def ttcRadialN (n : Nat) (K : Set (Ttc.Space n)) : Real :=
  max 1 (Ttc.cvSecondMoment K)

/-- `E_K‖X‖²` is nonnegative: it is the integral of a square. -/
theorem cvSecondMoment_nonneg (n : Nat) (K : Set (Ttc.Space n)) :
    0 ≤ Ttc.cvSecondMoment K := by
  unfold Ttc.cvSecondMoment
  exact integral_nonneg (fun _ ↦ sq_nonneg _)

/-- The canonical radial parameter is nonnegative. -/
theorem ttcRadialR_nonneg (n : Nat) (K : Set (Ttc.Space n)) : 0 ≤ ttcRadialR n K :=
  Real.sqrt_nonneg _

/-- **The `hrad` obligation.**  `R2` bounds the second moment by admissibility, and the
canonical radius squares back to the second moment. -/
theorem ttcRadialR_sq_le (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real)
    (hK : Ttc.CVAdmissible K R2) : (ttcRadialR n K) ^ 2 ≤ R2 := by
  rw [ttcRadialR, Real.sq_sqrt (cvSecondMoment_nonneg n K)]
  exact hK.2.2.2.2

/-- **The `hNpos` obligation.** -/
theorem ttcRadialN_pos (n : Nat) (K : Set (Ttc.Space n)) : 0 < ttcRadialN n K :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- **The `hNle` obligation.** -/
theorem ttcRadialN_le (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real)
    (hK : Ttc.CVAdmissible K R2) : ttcRadialN n K ≤ max 1 R2 :=
  max_le_max le_rfl hK.2.2.2.2

/-- All three interface obligations for the canonical radial data at once.  This is
exactly the triple `⟨hrad, hNpos, hNle⟩` demanded by
`Ttc.CVCappedRadialLogInterface.cvCappedRadialLogExpectedImplementationOfReferenceTVFamily`. -/
theorem ttcRadial_interface_conditions :
    (∀ n (K : Set (Ttc.Space n)) R2, Ttc.CVAdmissible K R2 → (ttcRadialR n K) ^ 2 ≤ R2) ∧
    (∀ n (K : Set (Ttc.Space n)), 0 < ttcRadialN n K) ∧
    (∀ n (K : Set (Ttc.Space n)) R2, Ttc.CVAdmissible K R2 → ttcRadialN n K ≤ max 1 R2) :=
  ⟨fun n K R2 hK => ttcRadialR_sq_le n K R2 hK,
   fun n K => ttcRadialN_pos n K,
   fun n K R2 hK => ttcRadialN_le n K R2 hK⟩

/-! ## The canonical radius of a body enclosed by an explicit ball

The runtime capstones instantiate `radialR` at TTC's own per-cube bodies, which are
`roundBody c γ K` for `K` the (dilated) region of a cube, `c` the inscribed-ball centre
and `γ` the inscribed radius.  `Ttc.roundBody_subset_closedBall` encloses that body in
the explicit ball of radius `γ⁻¹ · diam K`, and the two lemmas below turn such an
enclosure into a bound on `ttcRadialR`. -/

/-- The second moment of the uniform law on a nondegenerate convex body contained in
`closedBall 0 R` is at most `R ^ 2`.  Measurability of `K` is not assumed: convexity lets
us pass through `closure K`, which has the same volume and the same uniform law. -/
theorem cvSecondMoment_le_sq_of_subset_closedBall {n : Nat} {K : Set (Ttc.Space n)}
    {R : Real} (hconv : Convex Real K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hR : 0 ≤ R) (hsub : K ⊆ Metric.closedBall 0 R) :
    Ttc.cvSecondMoment K ≤ R ^ 2 := by
  have hvol : volume (closure K) = volume K :=
    Arlib.addHaar_closure_of_convex volume hconv
  have hKm : MeasurableSet (closure K) := isClosed_closure.measurableSet
  have hK0' : volume (closure K) ≠ 0 := by rw [hvol]; exact hK0
  have hKtop' : volume (closure K) ≠ ⊤ := by rw [hvol]; exact hKtop
  have hsub' : closure K ⊆ Metric.closedBall 0 R :=
    closure_minimal hsub Metric.isClosed_closedBall
  have hint := Ttc.CVAdaptive.integrable_norm_sq_uniformOn_of_subset_closedBall
    hKm hK0' hKtop' hR hsub'
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume (closure K)) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0' hKtop'
  have hae : ∀ᵐ x ∂(Arlib.uniformOn volume (closure K)), ‖x‖ ^ 2 ≤ R ^ 2 := by
    have hac : Arlib.uniformOn volume (closure K) ≪ volume.restrict (closure K) :=
      Measure.smul_absolutelyContinuous
    refine hac.ae_le ?_
    filter_upwards [ae_restrict_mem hKm] with x hx
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp (hsub' hx)
    nlinarith [norm_nonneg x]
  rw [← Ttc.CVAdaptive.cvSecondMoment_closure_eq_of_convex hconv]
  calc Ttc.cvSecondMoment (closure K)
      ≤ ∫ _x : Ttc.Space n, R ^ 2 ∂(Arlib.uniformOn volume (closure K)) :=
        integral_mono_ae hint (integrable_const _) hae
    _ = R ^ 2 := by simp

/-- The canonical radial parameter of a nondegenerate convex body enclosed by
`closedBall 0 R` is at most `R`. -/
theorem ttcRadialR_le_of_subset_closedBall {n : Nat} {K : Set (Ttc.Space n)} {R : Real}
    (hconv : Convex Real K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hR : 0 ≤ R) (hsub : K ⊆ Metric.closedBall 0 R) :
    ttcRadialR n K ≤ R := by
  rw [ttcRadialR]
  calc Real.sqrt (Ttc.cvSecondMoment K)
      ≤ Real.sqrt (R ^ 2) :=
        Real.sqrt_le_sqrt (cvSecondMoment_le_sq_of_subset_closedBall hconv hK0 hKtop hR hsub)
    _ = R := by rw [Real.sqrt_sq hR]

/-- **The per-cube bound.**  For the bodies the TTC runtime actually calls the volume
oracle on — `roundBody c γ K` with `Metric.ball c γ ⊆ K` — the canonical radial parameter
is bounded by `γ⁻¹ · diam K`, an explicit function of the run's own data: `γ` is the
dilated inscribed radius `algGamma`, and `diam K` is the region's diameter. -/
theorem ttcRadialR_roundBody_le {n : Nat} {c : Ttc.Space n} {γ : Real}
    {K : Set (Ttc.Space n)} (hγ : 0 < γ) (hconv : Convex Real K)
    (hball : Metric.ball c γ ⊆ K) (hbdd : Bornology.IsBounded K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) :
    ttcRadialR n (Ttc.roundBody c γ K) ≤ γ⁻¹ * Metric.diam K := by
  have hRnn : 0 ≤ γ⁻¹ * Metric.diam K :=
    mul_nonneg (inv_pos.mpr hγ).le Metric.diam_nonneg
  refine ttcRadialR_le_of_subset_closedBall (Ttc.convex_roundBody hconv) ?_ ?_ hRnn
    (Ttc.roundBody_subset_closedBall hγ hball hbdd)
  · rw [Ttc.volume_roundBody hγ]
    refine mul_ne_zero ?_ hK0
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (inv_pos.mpr hγ) n
  · exact Ttc.volume_roundBody_ne_top hγ hKtop

/-- **The bound at TTC's own volume-call bodies.**  `callBody atoms phi eps delta j` is
literally the body the capstone
`ttc_volume_estimate_operational_sourceSharp_fullTrajectory_cvShapeRuntime` feeds to
`radialR`, namely
`roundBody (algCen …) (algGamma …) (region (atomSet (algAtoms …)) …)`.  Its canonical
radial parameter is bounded by `algGamma⁻¹ · diam (region …)`: the dilated inscribed
radius and the dilated region's diameter, both data the run already computes. -/
theorem ttcRadialR_callBody_le {A : Type*} {n : Nat}
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    ttcRadialR n (Ttc.TTCCVExpectedImplementation.callBody atoms phi eps delta j) ≤
      (algGamma atoms phi eps delta)⁻¹ *
        Metric.diam (region (atomSet (algAtoms atoms phi eps delta))
          ((toDNFd (preprocess atoms phi)).get j)) := by
  have hmem : (toDNFd (preprocess atoms phi)).get j ∈ toDNFd (preprocess atoms phi) :=
    List.get_mem _ j
  have hgamma : 0 < algGamma atoms phi eps delta :=
    algGamma_pos_of_isPositive atoms phi eps delta hphi hvol
  have hballK := ball_subset_algCen atoms phi eps delta ⟨_, hmem⟩
  have hbddSol := algAtoms_bdd atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hbdd : Bornology.IsBounded (region (atomSet (algAtoms atoms phi eps delta))
      ((toDNFd (preprocess atoms phi)).get j)) :=
    isBounded_region_of_isBounded_sol (toDNFd_isDNFOf _) hbddSol hmem
  exact ttcRadialR_roundBody_le hgamma (convex_region (algAtoms atoms phi eps delta) _)
    hballK hbdd (Arlib.MarkovChains.volume_ne_zero_of_ball_subset hgamma hballK)
    (volume_ne_top_of_isBounded hbdd)

#print axioms cvSecondMoment_nonneg
#print axioms ttcRadialR_nonneg
#print axioms ttcRadialR_sq_le
#print axioms ttcRadialN_pos
#print axioms ttcRadialN_le
#print axioms ttcRadial_interface_conditions
#print axioms cvSecondMoment_le_sq_of_subset_closedBall
#print axioms ttcRadialR_le_of_subset_closedBall
#print axioms ttcRadialR_roundBody_le
#print axioms ttcRadialR_callBody_le

end Ttc.TtcRadialGeometry

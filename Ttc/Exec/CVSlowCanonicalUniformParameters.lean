import Ttc.Exec.CVSlowCanonicalRobustCertificate
import Ttc.Exec.CVSlowCanonicalShareBounds
import Ttc.Exec.CVMinimalScoreAwareWarmLogArithmetic

/-!
# One uniform schedule selection for the slow canonical robust certificate

`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`
is stated for a *fixed but arbitrary* choice of the schedule parameters
`C, q, slack, boundSq, meanTailFloor`, each supplied as a binder together with its
side conditions.  This file makes those choices **explicit functions of the input**
`(n, m, k, eps, R, K)` and discharges every side condition that is pure arithmetic
plus convex geometry of the body.

The selection is:

* `C := 4` (constant), which sits strictly inside the required window `(1, 7)`;
* `meanTailFloor := slowCanonicalJointTailFloor m k eps R (slowSourceInitialVariance n)`;
* `q := rAwareGlobalRadiusQ n R (slowSourceInitialVariance n) meanTailFloor`;
* `slack := fun j ↦ phaseMomentSlackSeven m (slowSourceSigmaSq n …) K C j / 2`;
* `boundSq := phaseScoreTransportBoundSqSeven R (slowSourceSigmaSq n …)`.

The last three shapes are forced by the frontier theorem's own binders `hqRAware`,
`hslackDef` and `hboundDef`, so only `C` and `meanTailFloor` are genuinely free.

Everything is proved from the four geometry inputs `MeasurableSet K`,
`ball 0 1 ⊆ K`, `volume K ≠ ⊤` and `1 ≤ n`, kept visible as binders.  `m`, `k` and
`scoreScale` are left as plain parameters: this round does not pin them numerically.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Ttc.CVSlowCanonicalUniformParameters

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVGlobalLogarithmicRadius
open Ttc.CVRAwareGlobalRadius
open Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowRadiusQReferencePhaseTV
open Ttc.CVSlowCanonicalShareBounds
open Ttc.CVMinimalScoreAwareWarmLogArithmetic

/-! ## Step 1 — the selection -/

/-- The exact-moment comparison factor, uniformly `2`: strictly inside `(1, 7)`.

**Not `4`.**  Both sit inside the frontier theorem's window, but the R-aware joint tail
floor's defining branch `1/(6 * exp (R^2/(2*s0)))` only yields
`floor * (exp (R^2/(2 sigma_i)) * 15) <= 5/2`, while `phaseMomentSlackSeven`'s right-hand
side at `C i = c` is `((7 - c)/2) * ratio^2`.  At `c = 4` that is `(3/2) * ratio^2`, which
is below `5/2` at `ratio = 1`, so `htailBudget` is not derivable there; at `c = 2` it is
exactly `(5/2) * ratio^2`, which is what
`Ttc.CVSlowCanonicalShareBounds.slowCanonicalJointTailFloor_moment_le` proves.  This was
found by discharging `htailBudget` rather than by inspection, and the constant is chosen to
match it. -/
noncomputable def slowUniformC : Nat → Real := fun _ ↦ 2

/-- The joint tail floor at the canonical initial variance. -/
noncomputable def slowUniformMeanTailFloor (n m k : Nat) (eps R : Real) : Real :=
  slowCanonicalJointTailFloor m k eps R (slowSourceInitialVariance n)

/-- The run-global truncation radius selected by the floor above. -/
noncomputable def slowUniformQ (n m k : Nat) (eps R : Real) : Real :=
  rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
    (slowUniformMeanTailFloor n m k eps R)

/-- The half factor-seven phase moment slack at `C = 4`. -/
noncomputable def slowUniformSlack (n m : Nat)
    (K : Set (EuclideanSpace Real (Fin n))) : Nat → Real :=
  fun j ↦ phaseMomentSlackSeven m
    (slowSourceSigmaSq n (slowSourceInitialVariance n)) K slowUniformC j / 2

/-- The factor-seven score transport bound. -/
noncomputable def slowUniformBoundSq (n : Nat) (R : Real) : Nat → Real :=
  phaseScoreTransportBoundSqSeven R
    (slowSourceSigmaSq n (slowSourceInitialVariance n))

/-! ## Step 2 — the easy side conditions -/

theorem slowUniformC_gt_one (i : Nat) : 1 < slowUniformC i := by
  unfold slowUniformC; norm_num

theorem slowUniformC_lt_seven (i : Nat) : slowUniformC i < 7 := by
  unfold slowUniformC; norm_num

theorem slowUniformBoundSq_pos {n : Nat} {R : Real} (i : Nat) :
    0 < slowUniformBoundSq n R i := by
  unfold slowUniformBoundSq phaseScoreTransportBoundSqSeven
  positivity

theorem slowUniformMeanTailFloor_pos {n m k : Nat} {eps R : Real}
    (heps : 0 < eps) : 0 < slowUniformMeanTailFloor n m k eps R :=
  slowCanonicalJointTailFloor_pos heps

/-- The frontier's `hqRAware` holds definitionally for the selection. -/
theorem slowUniformQ_rAware (n m k : Nat) (eps R : Real) :
    slowUniformQ n m k eps R =
      rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
        (slowUniformMeanTailFloor n m k eps R) := rfl

/-- The initial variance is positive, and is exactly the value `one_le_slow_radius`
wants at its lower binder. -/
theorem slowSourceInitialVariance_pos {n : Nat} (hn : 1 ≤ n) :
    0 < slowSourceInitialVariance n := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  unfold slowSourceInitialVariance
  positivity

/-! ## Step 3 — positivity of the selected slack -/

theorem slowUniformSlack_pos {n m : Nat} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace Real (Fin n))}
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : Nat) :
    0 < slowUniformSlack n m K i := by
  unfold slowUniformSlack
  refine div_pos ?_ (by norm_num)
  exact phaseMomentSlackSeven_pos
    (slowSourceSigmaSq_pos hn (slowSourceInitialVariance_pos hn))
    hball hfin slowUniformC_lt_seven i

/-! ## Step 4 — the selected radius is at least four, hence the radial floor -/

theorem four_le_slowUniformQ {n : Nat} (hn : 1 ≤ n) (m k : Nat) (eps R : Real) :
    4 ≤ slowUniformQ n m k eps R :=
  four_le_globalLogarithmicRadiusQ hn (one_le_rAwareRadiusCalls _ _ _)

theorem slowUniformQ_rad {n : Nat} (hn : 1 ≤ n) (m k : Nat) (eps R : Real)
    (i : Nat) :
    1 ≤ slowUniformQ n m k eps R *
      Real.sqrt (slowSourceSigmaSq n (slowSourceInitialVariance n) i) *
      Real.sqrt n :=
  one_le_slow_radius hn (four_le_slowUniformQ hn m k eps R) (by rfl) i

/-! ## Step 5 — the mean tail budget -/

/-- The geometric variance schedule never lets a consecutive cooling-chain ratio
drop below one, so the joint floor is inside half of the mean transport budget. -/
theorem slowUniformMeanTailFloor_le_meanBudget {n m k : Nat} (hn : 1 ≤ n)
    {eps R : Real} (heps : 0 < eps)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : Nat) :
    slowUniformMeanTailFloor n m k eps R ≤
      (scoreAwareMeanEta m k eps *
        (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
          chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i)) / 2 := by
  have hs0 := slowSourceInitialVariance_pos hn
  have hratio : (1 : Real) ≤
      chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
        chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i :=
    one_le_chain_ratio_of_sigmaSq_le_succ hK hfin hball
      (slowSourceSigmaSq_pos hn hs0) (slowSourceSigmaSq_mono_succ hn hs0 i)
  exact slowCanonicalJointTailFloor_mean_le heps hratio

/-! ## Step 6 — the capstone bundle -/

/-- **All schedule side conditions of the frontier theorem, at the uniform
selection.**  Every conjunct is one of the frontier's binders, instantiated at
`C := slowUniformC`, `meanTailFloor := slowUniformMeanTailFloor`,
`q := slowUniformQ`, `slack := slowUniformSlack`, `boundSq := slowUniformBoundSq`.
The only inputs are `1 ≤ n`, `0 < eps` and the four geometry facts about `K`. -/
theorem slowUniformParameters_valid {n : Nat} (hn : 1 ≤ n) (m k : Nat)
    {eps R : Real} (heps : 0 < eps)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) :
    (∀ i, 1 < slowUniformC i) ∧
    (∀ i, slowUniformC i < 7) ∧
    (∀ i, 0 < slowUniformSlack n m K i) ∧
    (∀ i, 0 < slowUniformBoundSq n R i) ∧
    (0 < slowUniformMeanTailFloor n m k eps R) ∧
    (4 ≤ slowUniformQ n m k eps R) ∧
    (slowUniformQ n m k eps R =
      rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
        (slowUniformMeanTailFloor n m k eps R)) ∧
    (∀ i, 1 ≤ slowUniformQ n m k eps R *
      Real.sqrt (slowSourceSigmaSq n (slowSourceInitialVariance n) i) *
      Real.sqrt n) ∧
    (slowUniformSlack n m K = fun j ↦ phaseMomentSlackSeven m
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K slowUniformC j / 2) ∧
    (slowUniformBoundSq n R = phaseScoreTransportBoundSqSeven R
      (slowSourceSigmaSq n (slowSourceInitialVariance n))) ∧
    (∀ i : Fin m, slowUniformMeanTailFloor n m k eps R ≤
      (scoreAwareMeanEta m k eps *
        (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
            ((i : Nat) + 1) /
          chain m (slowSourceSigmaSq n (slowSourceInitialVariance n))
            K (i : Nat))) / 2) := by
  refine ⟨slowUniformC_gt_one, slowUniformC_lt_seven,
    fun i ↦ slowUniformSlack_pos hn hball hfin i,
    fun i ↦ slowUniformBoundSq_pos i,
    slowUniformMeanTailFloor_pos heps,
    four_le_slowUniformQ hn m k eps R,
    slowUniformQ_rAware n m k eps R,
    fun i ↦ slowUniformQ_rad hn m k eps R i,
    rfl, rfl, fun i ↦ ?_⟩
  exact slowUniformMeanTailFloor_le_meanBudget hn heps hK hball hfin (i : Nat)

#print axioms slowUniformC
#print axioms slowUniformMeanTailFloor
#print axioms slowUniformQ
#print axioms slowUniformSlack
#print axioms slowUniformBoundSq
#print axioms slowUniformC_gt_one
#print axioms slowUniformC_lt_seven
#print axioms slowUniformBoundSq_pos
#print axioms slowUniformMeanTailFloor_pos
#print axioms slowUniformQ_rAware
#print axioms slowSourceInitialVariance_pos
#print axioms slowUniformSlack_pos
#print axioms four_le_slowUniformQ
#print axioms slowUniformQ_rad
#print axioms slowUniformMeanTailFloor_le_meanBudget
#print axioms slowUniformParameters_valid

end Ttc.CVSlowCanonicalUniformParameters

import Ttc.Volume.AdaptiveTerminalWarmLawAdjustable
import Ttc.Volume.CVHybridVarianceBudget
import Ttc.Exec.CVSourceTruncatedFixedCost
import Ttc.Exec.CVGaussianScoreSeedPhaseKernel

/-! Basic phasewise bodies and steps for a globally selected truncation radius `q`. -/

set_option autoImplicit false

namespace Ttc.CVAdaptiveRadiusQPrimitives

open MeasureTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open scoped ENNReal Classical

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def radiusQBody
    (q : Real) (K : Set (State n)) (s : Real) : Set (State n) :=
  K ∩ closedBall 0 (q * Real.sqrt s * Real.sqrt n)

noncomputable def radiusQDelta (n : Nat) (q s : Real) : Real :=
  min (Real.sqrt s / (max 8 (2 * q) * Real.sqrt n))
    (1 / (2 * (n : Real)))

theorem measurableSet_radiusQBody {q s : Real} {K : Set (State n)}
    (hK : MeasurableSet K) : MeasurableSet (radiusQBody q K s) :=
  hK.inter measurableSet_closedBall

theorem convex_radiusQBody {q s : Real} {K : Set (State n)}
    (hK : Convex Real K) : Convex Real (radiusQBody q K s) :=
  hK.inter (convex_closedBall 0 _)

theorem radiusQDelta_pos
    (hn : 1 ≤ n) {q s : Real} (_hq : 0 < q) (hs : 0 < s) :
    0 < radiusQDelta n q s := by
  unfold radiusQDelta
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hden : 0 < max 8 (2 * q) * Real.sqrt n := by positivity
  exact lt_min (div_pos hsqrt hden) (by positivity)

theorem radiusQDelta_le_n (n : Nat) (q s : Real) :
    radiusQDelta n q s ≤ 1 / (2 * (n : Real)) :=
  min_le_right _ _

theorem radiusQDelta_le_radius (n : Nat) (q s : Real) :
    radiusQDelta n q s ≤
      Real.sqrt s / (max 8 (2 * q) * Real.sqrt n) :=
  min_le_left _ _

theorem radiusQBody_subset_of_le {q : Real} (hq : 0 ≤ q)
    {K : Set (State n)} {sold snext : Real} (hs : sold ≤ snext) :
    radiusQBody q K sold ⊆ radiusQBody q K snext := by
  intro x hx
  change x ∈ K ∩ closedBall 0 (q * Real.sqrt sold * Real.sqrt n) at hx
  change x ∈ K ∩ closedBall 0 (q * Real.sqrt snext * Real.sqrt n)
  refine ⟨hx.1, ?_⟩
  rw [mem_closedBall_zero_iff]
  have hxnorm := mem_closedBall_zero_iff.mp hx.2
  have hsqrt := Real.sqrt_le_sqrt hs
  exact hxnorm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt hq) (Real.sqrt_nonneg _))

theorem norm_le_radiusQBody {q s : Real} {K : Set (State n)}
    {x : State n} (hx : x ∈ radiusQBody q K s) :
    ‖x‖ ≤ q * Real.sqrt s * Real.sqrt n := by
  exact mem_closedBall_zero_iff.mp hx.2

theorem tvLe_hybridRadiusQ_coolLaw_full
    (hn : 1 ≤ n) {q N s0 : Real} (hq : 1 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n) :
    TVLe
      (coolLaw m (sigmaSq n N s0)
        (radiusQBody q K (sigmaSq n N s0 i)) i)
      (coolLaw m (sigmaSq n N s0) K i)
      (ENNReal.ofReal
        ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  have hsigma : ∀ j, 0 < sigmaSq n N s0 j := sigmaSq_pos hn hN hs0
  let s := sigmaSq n N s0 i
  have hs : 0 < s := hsigma i
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsquare : sigmaSq n N s0 i = Real.sqrt s ^ 2 := by
    simpa only [s] using (Real.sq_sqrt hs.le).symm
  simpa only [radiusQBody, s] using
    (tvLe_coolLaw_inter_closedBall_relative_adjustable
      hn hq hsigma hsqrt hK hKc hball hfin hi hsquare
      (by simpa only [s] using hrad))

theorem tvLe_scoreSeedReference_hybridRadiusQ_full_of_local
    (hn : 1 ≤ n) {q N s0 : Real} (hq : 1 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (c : Real) (actual : Measure (State n × State n)) {eps : ENNReal}
    (hlocal : TVLe actual
      (Ttc.CVGaussianScoreSeedPhaseKernel.scoreSeedReference c
        (coolLaw m (sigmaSq n N s0)
          (radiusQBody q K (sigmaSq n N s0 i)) i)) eps) :
    TVLe actual
      (Ttc.CVGaussianScoreSeedPhaseKernel.scoreSeedReference c
        (coolLaw m (sigmaSq n N s0) K i))
      (eps + ENNReal.ofReal
        ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  have htail := tvLe_hybridRadiusQ_coolLaw_full
    (m := m) hn hq hN hs0 hK hKc hball hfin hi hrad
  have htailPair := htail.map
    (by fun_prop : Measurable (fun y : State n ↦ (y, c • y)))
  exact hlocal.trans (by
    simpa only [Ttc.CVGaussianScoreSeedPhaseKernel.scoreSeedReference] using htailPair)

theorem radiusQBody_eq_of_outer_radius
    {q s R : Real} {K : Set (State n)}
    (hKR : K ⊆ closedBall 0 R)
    (hR : R ≤ q * Real.sqrt s * Real.sqrt n) :
    radiusQBody q K s = K := by
  apply Set.Subset.antisymm inter_subset_left
  intro x hx
  exact ⟨hx, closedBall_subset_closedBall hR (hKR hx)⟩

#print axioms tvLe_hybridRadiusQ_coolLaw_full
#print axioms tvLe_scoreSeedReference_hybridRadiusQ_full_of_local
#print axioms radiusQBody_eq_of_outer_radius

end Ttc.CVAdaptiveRadiusQPrimitives

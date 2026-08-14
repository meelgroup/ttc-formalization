import Ttc.Exec.CVGaussianHybridAcceptedWarm
import Ttc.Exec.CVGaussianScoreSeedPhaseKernel
import Ttc.Volume.CVRunwiseTailParameters
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Reference-warmth audit and micro-cooling repair for the hybrid schedule

The accelerated (hot) CV phases may have variance ratio `3/2`.  The dimension-free
`2e` reference-warmth lemma only applies to ratios at most `1 + 2/n`; applying it
directly to a coarse hot phase is therefore invalid.

The repair formalized here subdivides a coarse multiplicative increment `1+a` into `n`
additive-variance microsteps.  Their endpoints are

`s * (1 + t*a/n)`, for `t=0,...,n`.

Every consecutive micro-ratio is between one and `1+2/n` when `0 <= a <= 1/2`, while
the final endpoint is exactly `s*(1+a)`.  Hence the existing Gaussian `2e` warmth
theorem applies at every internal transition.  Implementationally these microsteps can
be composed inside one coarse score phase, so the source phase-score product is
unchanged and the reference cost grows by only a factor `n`.
-/

set_option autoImplicit false

namespace Ttc.CVHybridReferenceWarmRepair

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVAdaptive Ttc.CVCorrectedRuntime
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def microReferenceWarm : ENNReal :=
  ENNReal.ofReal (2 * Real.exp 1)

/-- The first accelerated chunk can literally use rate `1/2`; thus the hot schedule is
not globally in the dimension-free `2/n` regime. -/
theorem adaptivePhaseRate_one_one_zero :
    adaptivePhaseRate 1 1 0 = (1 / 2 : Real) := by
  unfold adaptivePhaseRate adaptiveChunkRate
  have hchunk : adaptivePhaseChunk 1 1 0 = 0 := by
    simpa using adaptivePhaseChunk_offset (N := (1 : Real)) (s₀ := (1 : Real))
      (by norm_num) (by norm_num) 0
  rw [hchunk]
  simp [adaptiveChunkStart]

/-- Already in dimension six, the exact warmth envelope for a ratio-`3/2` coarse phase
is strictly larger than the claimed constant `2e`.  This does not prove that no sharper
warmness argument exists, but it machine-checks that the existing exact-factor theorem
cannot be specialized to the constant envelope. -/
theorem gaussianReferenceWarm_lt_accelerated_ratio_three_halves :
    microReferenceWarm < acceleratedSeedWarmFactor 6 (3 / 2 : Real) := by
  have hsqrt : Real.sqrt (3 / 2 : Real) ^ 2 = 3 / 2 := by
    rw [Real.sq_sqrt]
    norm_num
  have hpow : Real.sqrt (3 / 2 : Real) ^ 6 = 27 / 8 := by
    calc
      Real.sqrt (3 / 2 : Real) ^ 6 =
          (Real.sqrt (3 / 2 : Real) ^ 2) ^ 3 := by ring
      _ = (3 / 2 : Real) ^ 3 := by rw [hsqrt]
      _ = 27 / 8 := by norm_num
  unfold microReferenceWarm acceleratedSeedWarmFactor
  rw [hpow]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  nlinarith

/-- Additive-variance interpolation between `s` and `s*(1+a)`. -/
noncomputable def microVariance (s a : Real) (n t : Nat) : Real :=
  s * (1 + (t : Real) * a / (n : Real))

/-- The exact ratio of consecutive additive-variance microsteps. -/
noncomputable def microRatio (a : Real) (n t : Nat) : Real :=
  (1 + ((t + 1 : Nat) : Real) * a / (n : Real)) /
    (1 + (t : Real) * a / (n : Real))

theorem microVariance_pos
    {s a : Real} (hs : 0 < s) (ha : 0 <= a) {n : Nat} (t : Nat) :
    0 < microVariance s a n t := by
  unfold microVariance
  have : 0 <= (t : Real) * a / (n : Real) := by positivity
  positivity

theorem microVariance_succ_eq_ratio_mul
    {s a : Real} (ha : 0 <= a) {n : Nat} (hn : 1 <= n) (t : Nat) :
    microVariance s a n (t + 1) =
      microRatio a n t * microVariance s a n t := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hden : 1 + (t : Real) * a / (n : Real) ≠ 0 :=
    ne_of_gt (by
      have : 0 <= (t : Real) * a / (n : Real) := by positivity
      linarith)
  unfold microVariance microRatio
  field_simp [ne_of_gt hnR, hden]

theorem one_le_microRatio
    {a : Real} (ha : 0 <= a) {n : Nat} (hn : 1 <= n) (t : Nat) :
    1 <= microRatio a n t := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hden : 0 < 1 + (t : Real) * a / (n : Real) := by positivity
  rw [microRatio, le_div_iff₀ hden]
  push_cast
  field_simp [ne_of_gt hnR]
  nlinarith [mul_nonneg (Nat.cast_nonneg t) ha]

/-- Every microstep lies in the dimension-free adjacent-Gaussian regime.  The bound is
deliberately loose (`a <= 1/2` actually gives `1+1/(2n)`). -/
theorem microRatio_le_one_add_two_div
    {a : Real} (ha0 : 0 <= a) (ha2 : a <= 1 / 2)
    {n : Nat} (hn : 1 <= n) (t : Nat) :
    microRatio a n t <= 1 + 2 / (n : Real) := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hden : 0 < 1 + (t : Real) * a / (n : Real) := by positivity
  rw [microRatio, div_le_iff₀ hden]
  push_cast
  have ht0 : (0 : Real) <= t := by positivity
  field_simp [ne_of_gt hnR]
  nlinarith

/-- After exactly `n` microsteps the intended coarse endpoint is reached, with no
overshoot or approximation. -/
theorem microVariance_endpoint
    {s a : Real} {n : Nat} (hn : 1 <= n) :
    microVariance s a n n = s * (1 + a) := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  unfold microVariance
  field_simp [ne_of_gt hnR]

/-! ## Polynomial size of the repair -/

/-- Number of internal reference-mixing transitions after replacing every coarse phase
by `n` additive-variance microsteps. -/
def microExpandedPhaseCount (n coarsePhases : Nat) : Nat :=
  n * coarsePhases

/-- In the source endpoint branch the micro-expanded schedule still has a concrete
polynomial phase bound, namely `O(C^2*n^3)`.  Thus the repair costs one additional
dimension factor but does not change the `eps^-2` sample dependence. -/
theorem concrete_source_microExpandedPhaseCount_lt
    {n : Nat} {C eps : Real} (hn : 1 <= n) (hC : 0 < C)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4) :
    ((microExpandedPhaseCount n
      (terminalPhaseCount n C (polynomialEndpointSigmaSq n (eps / 4)) + 1) : Nat) : Real) <
      (n : Real) * (80 * C ^ 2 * (n : Real) ^ 2 + 3) := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hm := concrete_source_phaseCount_lt hn hC hsource
  have hm' :
      (terminalPhaseCount n C (polynomialEndpointSigmaSq n (eps / 4)) : Real) + 1 <
        80 * C ^ 2 * (n : Real) ^ 2 + 3 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hm
  unfold microExpandedPhaseCount
  push_cast
  exact mul_lt_mul_of_pos_left hm' hnR

/-- If each internal microstep has reference mean at most `B`, the entire expanded
schedule costs at most `n*m*B`.  This is the deterministic cost multiplier consumed by
the retained-history reference construction. -/
theorem sum_microExpandedPhaseCost_le
    {n m : Nat} {B : Real} (hB : 0 <= B) {cost : Nat -> Real}
    (hcost0 : forall i, 0 <= cost i)
    (hcost : forall i, i < microExpandedPhaseCount n m -> cost i <= B) :
    (Finset.range (microExpandedPhaseCount n m)).sum cost <=
      (n : Real) * (m : Real) * B := by
  calc
    (Finset.range (microExpandedPhaseCount n m)).sum cost <=
        (Finset.range (microExpandedPhaseCount n m)).sum (fun _ => B) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcost i (Finset.mem_range.mp hi)
    _ = (n : Real) * (m : Real) * B := by
      simp [microExpandedPhaseCount]

/-- The existing `2e` Gaussian reference theorem applies to every internal microstep.
This is the analytic core needed by a costed composed-microkernel implementation. -/
theorem isWarm_scoreSeedReference_microStep
    (hn : 1 <= n) {s a : Real} (hs : 0 < s)
    (ha0 : 0 <= a) (ha2 : a <= 1 / 2)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < n + 1)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta <= 1 / (2 * (n : Real))) :
    IsWarm microReferenceWarm
      (Measure.map Prod.snd
        (Ttc.CVGaussianScoreSeedPhaseKernel.scoreSeedReference
          (1 - 1 / (2 * (n : Real)))
          (coolLaw (n + 1) (microVariance s a n) K i)))
      (ellGaussianProb K delta (microVariance s a n (i + 1))) := by
  exact isWarm_snd_scoreSeedReference_standard hn
    (fun j => microVariance_pos hs ha0 j) hK hKc hball hfin hi
    (one_le_microRatio ha0 hn i)
    (microRatio_le_one_add_two_div ha0 ha2 hn i)
    (microVariance_succ_eq_ratio_mul ha0 hn i) hdelta hdeltan

#print axioms adaptivePhaseRate_one_one_zero
#print axioms gaussianReferenceWarm_lt_accelerated_ratio_three_halves
#print axioms microVariance_succ_eq_ratio_mul
#print axioms microRatio_le_one_add_two_div
#print axioms microVariance_endpoint
#print axioms isWarm_scoreSeedReference_microStep

end Ttc.CVHybridReferenceWarmRepair

import Ttc.Exec.CVGaussianAdaptiveBlockOperational
import Ttc.Exec.CVGaussianScoreAwareParameters
import Arlib.MarkovChains.Continuous.AdjustableRadiusSampler

/-! A concrete adjustable-radius deadline in the exact shape consumed by the
accelerated Gaussian block operation. -/

namespace Ttc.CVGaussianAdaptiveMixing

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVSequentialPhaseSampler
open Ttc.CVGaussianScoreAwareParameters
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The natural ceiling of the explicit adjustable-radius speedy-Gaussian deadline.
The use of `ENNReal.toReal` is harmless under the finite, nonzero hypotheses in the
consumer theorem below. -/
noncomputable def adjustableSpeedyDeadline
    (n : Nat) (delta sigmaSq : Real) (M eta : ENNReal) : Nat :=
  ⌈4 * 640 ^ 2 * sigmaSq * (n : Real) *
      (Real.log M.toReal + 2 * Real.log (1 / eta.toReal)) /
        (delta * Real.log 2) ^ 2 + 1⌉₊ + 1

theorem adjustableSpeedyDeadline_spec
    (n : Nat) (delta sigmaSq : Real) (M eta : ENNReal) :
    4 * 640 ^ 2 * sigmaSq * (n : Real) *
        (Real.log M.toReal + 2 * Real.log (1 / eta.toReal)) /
          (delta * Real.log 2) ^ 2 + 1 ≤
      (adjustableSpeedyDeadline n delta sigmaSq M eta : Real) := by
  have hceil := Nat.le_ceil
    (4 * 640 ^ 2 * sigmaSq * (n : Real) *
      (Real.log M.toReal + 2 * Real.log (1 / eta.toReal)) /
        (delta * Real.log 2) ^ 2 + 1)
  rw [adjustableSpeedyDeadline]
  push_cast
  linarith

/-- Adjustable-radius mixing, converted from `MixesWithin` to the literal
`sampleFromKernel (iteratedKernel …)` interface used by the finite-retry operation. -/
theorem tvLe_adjustableSpeedyDeadline
    (hn : 21 ≤ n) {q R delta sigmaSq : Real} (hq : 1 < q)
    (hsigmaSq : 0 < sigmaSq) (hdelta : 0 < delta)
    (hdeltaq : delta ≤ Real.sqrt sigmaSq /
      (max 8 (2 * q) * Real.sqrt n))
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRsigma : R ≤ q * Real.sqrt sigmaSq * Real.sqrt n)
    {nu : Measure (State n)} [IsProbabilityMeasure nu]
    {M eta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hwarm : IsWarm M nu (ellGaussianProb K delta sigmaSq)) :
    TVLe
      (sampleFromKernel
        (iteratedKernel (lazy (speedyMetropolisGaussian K delta sigmaSq))
          (adjustableSpeedyDeadline n delta sigmaSq M eta)) nu)
      (ellGaussianProb K delta sigmaSq) eta := by
  have hsigma : 0 < Real.sqrt sigmaSq := Real.sqrt_pos.2 hsigmaSq
  have hsquare : Real.sqrt sigmaSq ^ 2 = sigmaSq := Real.sq_sqrt hsigmaSq.le
  have hMreal : 1 ≤ M.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hMtop hM1
  have hetaReal0 : 0 < eta.toReal := ENNReal.toReal_pos heta0 hetatop
  have hetaReal1 : eta.toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) heta1
  have hwarm' : IsWarm (ENNReal.ofReal M.toReal) nu
      (ellGaussianProb K delta (Real.sqrt sigmaSq ^ 2)) := by
    rw [ENNReal.ofReal_toReal hMtop, hsquare]
    exact hwarm
  have hdeadline :
      4 * 640 ^ 2 * Real.sqrt sigmaSq ^ 2 * (n : Real) *
          (Real.log M.toReal + 2 * Real.log (1 / eta.toReal)) /
            (delta * Real.log 2) ^ 2 + 1 ≤
        (adjustableSpeedyDeadline n delta sigmaSq M eta : Real) := by
    rw [hsquare]
    exact adjustableSpeedyDeadline_spec n delta sigmaSq M eta
  have hmix :=
    mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit_adjustable
      hn hq hsigma hdelta hdeltaq hK hKc hK0 hR hKR hRsigma hMreal hwarm'
      hetaReal0 hetaReal1 hdeadline
  rw [mixesWithin_iff, hsquare] at hmix
  rw [← iterate_eq_sampleFrom_iteratedKernel]
  simpa only [ENNReal.ofReal_toReal hetatop] using hmix

/-- The preceding theorem at the phasewise score-aware error share.  Thus the `hmix`
binder of `seedProjectedOperational_gaussianAdaptive_scoreAware` is discharged by body
geometry and the explicit ceiling deadline. -/
theorem hmix_gaussianAdaptive_scoreAware
    (hn : 21 ≤ n) {q R delta : Real} (hq : 1 < q) (hdelta : 0 < delta)
    {N s₀ : Real} (hN : 0 < N) (hs₀ : 0 < s₀)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hdeltaq : ∀ i, delta ≤ Real.sqrt (adaptiveSigmaSq N s₀ i) /
      (max 8 (2 * q) * Real.sqrt n))
    (hRsigma : ∀ i, R ≤ q * Real.sqrt (adaptiveSigmaSq N s₀ i) * Real.sqrt n)
    {m k : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real} (hslack : ∀ i, 0 < slack i)
    (hboundSq : ∀ i, 0 < boundSq i)
    {warmBudget : Nat → ENNReal} (hwarmOne : ∀ i, 1 ≤ warmBudget i)
    (hwarmTop : ∀ i, warmBudget i ≠ ⊤) :
    ∀ i (nu : Measure (State n)),
      IsWarm ((2 * warmBudget i) / scoreAwareEta m k eps slack boundSq i) nu
          (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)) →
      IsProbabilityMeasure nu →
        TVLe (sampleFromKernel
          (iteratedKernel
            (lazy (speedyMetropolisGaussian K delta (adaptiveSigmaSq N s₀ i)))
            (adjustableSpeedyDeadline n delta (adaptiveSigmaSq N s₀ i)
              ((2 * warmBudget i) / scoreAwareEta m k eps slack boundSq i)
              (scoreAwareZeta m k eps slack boundSq i))) nu)
          (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i))
          (scoreAwareZeta m k eps slack boundSq i) := by
  intro i nu hwarm hprob
  letI : IsProbabilityMeasure nu := hprob
  let eta := scoreAwareEta m k eps slack boundSq i
  let M := (2 * warmBudget i) / eta
  have hspos := scoreAwareShare_pos (m := m) (k := k) heps hslack hboundSq i
  have hslt := scoreAwareShare_lt_one (m := m) (k := k)
    (slack := slack) (boundSq := boundSq) heps heps1 i
  have heta0 : eta ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr hspos
  have hetatop : eta ≠ ⊤ := by dsimp [eta, scoreAwareEta]; exact ENNReal.ofReal_ne_top
  have heta1 : eta ≤ 1 := by
    dsimp [eta, scoreAwareEta]
    simpa using ENNReal.ofReal_le_ofReal hslt.le
  have hnumtop : (2 : ENNReal) * warmBudget i ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (hwarmTop i)
  have hMtop : M ≠ ⊤ := ENNReal.div_ne_top hnumtop heta0
  have hM1 : 1 ≤ M := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl heta0) (Or.inl hetatop)).2
    rw [one_mul]
    calc
      eta ≤ 1 := heta1
      _ ≤ 2 * warmBudget i := by
        calc
          (1 : ENNReal) ≤ 1 * warmBudget i := by simpa using hwarmOne i
          _ ≤ 2 * warmBudget i := by gcongr; norm_num
  have hz0 : scoreAwareZeta m k eps slack boundSq i ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    exact div_pos hspos (by norm_num)
  have hz1 : scoreAwareZeta m k eps slack boundSq i ≤ 1 :=
    (scoreAwareZeta_le_sixteenth heps heps1 i).trans (by norm_num)
  simpa only [M, eta] using
    (tvLe_adjustableSpeedyDeadline hn hq (adaptiveSigmaSq_pos hN hs₀ i) hdelta
      (hdeltaq i) hK hKc hK0 hR hKR (hRsigma i) hM1 hMtop hz0
      ENNReal.ofReal_ne_top hz1 hwarm)

#print axioms adjustableSpeedyDeadline_spec
#print axioms tvLe_adjustableSpeedyDeadline
#print axioms hmix_gaussianAdaptive_scoreAware

end Ttc.CVGaussianAdaptiveMixing

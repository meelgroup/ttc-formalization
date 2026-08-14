import Ttc.Exec.CVGaussianCappedCostEnvelope
import Ttc.Exec.CVSourceSharpIndependentCertificate

/-!
# Source-sharp cost accounting for independent Gaussian streams

This file performs the expected-cost calculation before any timeout is imposed.  For
`k` independent complete Gaussian streams the cost is bounded by exactly

`k * sum_i activePhaseMean i`.

Consequently the source cutoff needs only one Markov argument, at the end of a complete
run.  In particular, no factor `1 / correctedNu` occurs in any statement below.

The final section records the precise remaining arithmetic seam.  The operational
constructor deliberately accepts arbitrary step and retry schedules.  With that interface
there cannot be a universal comparison with the source budget: even a single active phase
can be assigned an arbitrarily large step count.  A source-rate capstone must therefore
instantiate the concrete schedule and prove its deterministic phase-sum bound; probabilistic
cost composition itself is closed here.
-/

namespace Ttc.CVGaussianSourceSharpCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVGaussianCappedCostEnvelope
open Ttc.CVGaussianAdaptiveAcceptedWarm
open Arlib.GaussianCooling.Chunked
open Ttc.CVSeedProjectedDependence
open Ttc.CVIndependentStreamDependence
open Ttc.CVIndependentStreamGeneralizedCertificate
open Ttc.CVSourceSharpIndependentCertificate
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.GenericCostedPhaseCertificate
open scoped ENNReal Classical BigOperators

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The division-free active-phase expected-cost envelope. -/
noncomputable def gaussianActiveMeanEnvelope
    (m : Nat) (warm : Nat → ENNReal)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) : ENNReal :=
  if i + 1 < m then
    ENNReal.ofReal
      (Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
        (warm i).toReal (steps i) (retries i))
  else 0

/-- Real form of `gaussianActiveMeanEnvelope`, intended for the final deterministic
source-rate calculation. -/
noncomputable def gaussianActiveMeanEnvelopeReal
    (m : Nat) (warm : Nat → ENNReal)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) : Real :=
  if i + 1 < m then
    Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
      (warm i).toReal (steps i) (retries i)
  else 0

theorem gaussianActiveMeanEnvelopeReal_nonneg
    (m : Nat) (warm : Nat → ENNReal)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    0 ≤ gaussianActiveMeanEnvelopeReal m warm steps retries i := by
  unfold gaussianActiveMeanEnvelopeReal
  split_ifs
  · exact Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope_nonneg
      (ENNReal.toReal_nonneg) (steps i) (retries i)
  · norm_num

theorem ofReal_gaussianActiveMeanEnvelopeReal
    (m : Nat) (warm : Nat → ENNReal)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    ENNReal.ofReal (gaussianActiveMeanEnvelopeReal m warm steps retries i) =
      gaussianActiveMeanEnvelope m warm steps retries i := by
  unfold gaussianActiveMeanEnvelopeReal gaussianActiveMeanEnvelope
  split_ifs <;> simp

/-- It is enough to prove the remaining source comparison in ordinary real arithmetic.
This lemma is the intended endpoint for schedule-specific phase-count, step-count and
warmness estimates. -/
theorem sharpPhaseSum_le_sourceBudget_of_real
    (runtimeConstant : Real) (n k m : Nat) (radius eps : Real)
    (warm : Nat → ENNReal) (steps : Nat → Nat → Nat)
    (retries : Nat → Nat)
    (hreal : (k : Real) * ∑ i ∈ Finset.range m,
        gaussianActiveMeanEnvelopeReal m warm steps retries i ≤
      sourceOneRunQueryEnvelope runtimeConstant n radius eps) :
    (k : ENNReal) * ∑ i ∈ Finset.range m,
        gaussianActiveMeanEnvelope m warm steps retries i ≤
      sourceOneRunQueryBudget runtimeConstant n radius eps := by
  unfold sourceOneRunQueryBudget
  rw [← ENNReal.ofReal_natCast]
  simp_rw [← ofReal_gaussianActiveMeanEnvelopeReal]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
    gaussianActiveMeanEnvelopeReal_nonneg m warm steps retries i)]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Expected queries of the actual independent costed law are at most `k` times the sum
of the active scalar phase means.  This is the Gaussian specialization of the sharp
independent-stream Tonelli theorem. -/
theorem lintegral_independentQueryCost_gaussian_le_activeMeanEnvelope
    (hn : 2 ≤ n) (k m : Nat)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (q R : Real) (hq : 1 < q) (hR : 0 ≤ R)
    (delta sigma shrink : Nat → Real)
    (hdelta : ∀ j, 0 < delta j) (hsigma : ∀ j, 0 < sigma j)
    (hshrink : ∀ j, shrink j ≠ 0)
    (hdeltan : ∀ j, delta j ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ j, j + 1 < m →
      delta j ≤ sigma j / (max 8 (2 * q) * Real.sqrt n))
    (hRsigma : ∀ j, j + 1 < m → R ≤ q * sigma j * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback tail : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    [∀ j, IsProbabilityMeasure (tail j)]
    [∀ j, IsProbabilityMeasure
      (ellGaussianProb K (delta j) ((sigma j) ^ 2))]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real) (eta : Real)
    (hop : SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
          hdelta hshrink steps retries fallback) tail)
      Prod.snd Prod.fst mu0 V m eta)
    (hpi : ∀ j, hop.pi j = ellGaussianProb K (delta j) ((sigma j) ^ 2))
    (hMtop : ∀ j, hop.warmConst j ≠ ⊤) :
    (∫⁻ omega, independentQueryCost m omega
      ∂independentCostedLaw k
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule m
            (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
              hdelta hshrink steps retries fallback) tail)) mu0) ≤
      (k : ENNReal) * ∑ j ∈ Finset.range m,
        gaussianActiveMeanEnvelope m hop.warmConst steps retries j := by
  let Q := costedStateScheduleFromSeed
    (costedActiveReferenceTailSchedule m
      (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback) tail)
  refine lintegral_independentQueryCost_le_phaseBounds k m Q mu0
    (gaussianActiveMeanEnvelope m hop.warmConst steps retries) ?_
  intro j hj
  unfold gaussianActiveMeanEnvelope
  by_cases hactive : j + 1 < m
  · rw [if_pos hactive]
    exact phaseMean_costedActive_gaussian_le_of_operational hn m j hactive
      hK hKc hball q R hq hR delta sigma shrink hdelta hsigma hshrink
      hdeltan hdeltaq hRsigma hKR steps retries fallback tail mu0 V eta hop hpi
      (hMtop j)
  · rw [if_neg hactive]
    exact le_of_eq
      (lintegral_stepMean_costedStateActiveReferenceTailSchedule_inactive m
        (warmFallbackCostedSchedule K hK delta (fun l ↦ (sigma l) ^ 2) shrink
          hdelta hshrink steps retries fallback) tail
        (stateMarginal Q mu0 j) j hactive)

/-- Direct adapter to the source-shaped budget.  `hsum` is now the sole runtime seam;
there is no per-phase timeout or division by the dependence allowance. -/
theorem lintegral_independentQueryCost_gaussian_le_sourceOneRunQueryBudget
    (hn : 2 ≤ n) (k m : Nat)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (q radius runtimeConstant eps : Real) (hq : 1 < q) (hR : 0 ≤ radius)
    (delta sigma shrink : Nat → Real)
    (hdelta : ∀ j, 0 < delta j) (hsigma : ∀ j, 0 < sigma j)
    (hshrink : ∀ j, shrink j ≠ 0)
    (hdeltan : ∀ j, delta j ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ j, j + 1 < m →
      delta j ≤ sigma j / (max 8 (2 * q) * Real.sqrt n))
    (hRsigma : ∀ j, j + 1 < m → radius ≤ q * sigma j * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ radius)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback tail : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    [∀ j, IsProbabilityMeasure (tail j)]
    [∀ j, IsProbabilityMeasure
      (ellGaussianProb K (delta j) ((sigma j) ^ 2))]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real) (eta : Real)
    (hop : SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
          hdelta hshrink steps retries fallback) tail)
      Prod.snd Prod.fst mu0 V m eta)
    (hpi : ∀ j, hop.pi j = ellGaussianProb K (delta j) ((sigma j) ^ 2))
    (hMtop : ∀ j, hop.warmConst j ≠ ⊤)
    (hsum : (k : ENNReal) * ∑ j ∈ Finset.range m,
        gaussianActiveMeanEnvelope m hop.warmConst steps retries j ≤
      sourceOneRunQueryBudget runtimeConstant n radius eps) :
    (∫⁻ omega, independentQueryCost m omega
      ∂independentCostedLaw k
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule m
            (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
              hdelta hshrink steps retries fallback) tail)) mu0) ≤
      sourceOneRunQueryBudget runtimeConstant n radius eps :=
  (lintegral_independentQueryCost_gaussian_le_activeMeanEnvelope hn k m hK hKc
    hball q radius hq hR delta sigma shrink hdelta hsigma hshrink hdeltan
    hdeltaq hRsigma hKR steps retries fallback tail mu0 V eta hop hpi hMtop).trans hsum

/-! ## Exponential warm-envelope obstruction in the concrete adaptive package -/

/-- The exact accelerated successor factor used by the current operational package is
at least one whenever the cooling ratio is at least one. -/
theorem one_le_acceleratedSeedWarmFactor {n : Nat} {cc : Real} (hcc : 1 ≤ cc) :
    1 ≤ acceleratedSeedWarmFactor n cc := by
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hsqrt : 1 ≤ Real.sqrt cc := Real.one_le_sqrt.2 hcc
  have hpow : 1 ≤ Real.sqrt cc ^ n := one_le_pow₀ hsqrt
  nlinarith

/-- The `adaptiveAcceptedBudget` recurrence used by
`seedProjectedOperational_gaussianAdaptive_{block,scoreAware}` forces at least a factor
sixteen of warmness growth at every phase, even before adding fallback warmness. -/
theorem sixteen_mul_warmBudget_le_succ
    {n i : Nat} {N s₀ : Real} (hN : 0 < N) (hs₀ : 0 < s₀)
    (retries : Nat → Nat) (warmBudget fallbackBudget : Nat → ENNReal)
    (hretry : 1 ≤ retries i)
    (hgrowth : adaptiveAcceptedBudget n N s₀ retries warmBudget i +
        fallbackBudget i ≤ warmBudget (i + 1)) :
    16 * warmBudget i ≤ warmBudget (i + 1) := by
  have hratio : 1 ≤ 1 + adaptivePhaseRate N s₀ i := by
    have hr := adaptiveChunkRate_pos hN hs₀
      (adaptivePhaseChunk N s₀ i)
    unfold adaptivePhaseRate
    exact le_add_of_nonneg_right hr.le
  have hfactor : (1 : ENNReal) ≤
      acceleratedSeedWarmFactor n (1 + adaptivePhaseRate N s₀ i) :=
    one_le_acceleratedSeedWarmFactor hratio
  have hretryE : (1 : ENNReal) ≤ retries i := by exact_mod_cast hretry
  calc
    16 * warmBudget i =
        1 * ((16 : ENNReal) * 1 * warmBudget i) := by simp
    _ ≤ (retries i : ENNReal) *
        ((16 : ENNReal) *
          acceleratedSeedWarmFactor n
            (1 + adaptivePhaseRate N s₀ i) * warmBudget i) := by
      gcongr
    _ = adaptiveAcceptedBudget n N s₀ retries warmBudget i := by
      simp only [adaptiveAcceptedBudget]
    _ ≤ adaptiveAcceptedBudget n N s₀ retries warmBudget i +
        fallbackBudget i := le_add_right le_rfl
    _ ≤ warmBudget (i + 1) := hgrowth

/-- Iterating the current recurrence gives an exponential lower bound on the warm
certificate itself.  This is a bound on the operational proof's mandatory envelope, not
on the true (possibly much smaller) warmness of the path law. -/
theorem sixteen_pow_le_warmBudget
    {n : Nat} {N s₀ : Real} (hN : 0 < N) (hs₀ : 0 < s₀)
    (retries : Nat → Nat) (warmBudget fallbackBudget : Nat → ENNReal)
    (hwarm0 : 1 ≤ warmBudget 0) (hretry : ∀ i, 1 ≤ retries i)
    (hgrowth : ∀ i, adaptiveAcceptedBudget n N s₀ retries warmBudget i +
        fallbackBudget i ≤ warmBudget (i + 1)) :
    ∀ i, (16 : ENNReal) ^ i ≤ warmBudget i := by
  intro i
  induction i with
  | zero => simpa using hwarm0
  | succ i ih =>
      rw [pow_succ]
      calc
        (16 : ENNReal) ^ i * 16 = 16 * (16 : ENNReal) ^ i := mul_comm _ _
        _ ≤ 16 * warmBudget i := mul_le_mul_left' ih 16
        _ ≤ warmBudget (i + 1) :=
          sixteen_mul_warmBudget_le_succ hN hs₀ retries warmBudget fallbackBudget
            (hretry i) (hgrowth i)

/-- One nonempty retry block with at least one step already costs at least `10*M` in the
real reference-mean envelope. -/
theorem ten_mul_le_retryReferenceMeanEnvelope
    {M : Real} (hM : 0 ≤ M) {steps : Nat → Nat} {L : Nat}
    (hL : 0 < L) (hstep : 1 ≤ steps 0) :
    10 * M ≤
      Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
        M steps L := by
  unfold Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
  have hmem : 0 ∈ Finset.range L := Finset.mem_range.2 hL
  calc
    10 * M = 10 * ((1 : Real) * M) := by ring
    _ ≤ 10 * ((steps 0 : Real) * M) := by
      have hs : (1 : Real) ≤ steps 0 := by exact_mod_cast hstep
      gcongr
    _ ≤ ∑ j ∈ Finset.range L, 10 * ((steps j : Real) * M) := by
      exact Finset.single_le_sum
        (s := Finset.range L) (f := fun j ↦ 10 * ((steps j : Real) * M))
        (fun j _ ↦ (by positivity : (0 : Real) ≤ 10 * ((steps j : Real) * M))) hmem

/-- Hence any active phase `i` contributes at least ten times its certified warmness to
the sharp real phase sum, provided the operational retry and step counts are nonzero. -/
theorem ten_mul_warm_toReal_le_sharpPhaseSum
    {m i : Nat} (hi : i + 1 < m) (warm : Nat → ENNReal)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (hretry : 0 < retries i) (hstep : 1 ≤ steps i 0) :
    10 * (warm i).toReal ≤
      ∑ j ∈ Finset.range m,
        gaussianActiveMeanEnvelopeReal m warm steps retries j := by
  have himem : i ∈ Finset.range m := Finset.mem_range.2 (Nat.lt_of_succ_lt hi)
  calc
    10 * (warm i).toReal ≤
        gaussianActiveMeanEnvelopeReal m warm steps retries i := by
      rw [gaussianActiveMeanEnvelopeReal, if_pos hi]
      exact ten_mul_le_retryReferenceMeanEnvelope ENNReal.toReal_nonneg hretry hstep
    _ ≤ ∑ j ∈ Finset.range m,
        gaussianActiveMeanEnvelopeReal m warm steps retries j := by
      exact Finset.single_le_sum
        (fun j _ ↦ gaussianActiveMeanEnvelopeReal_nonneg m warm steps retries j) himem

/-- Combining the last two facts, the current recurrence makes the phase-sum envelope
exponential in every active index.  Thus a polynomial source comparison cannot be proved
from this warm certificate without replacing the compounding recurrence by a sharp
normalised/fallback-weighted warmness argument. -/
theorem ten_mul_sixteen_pow_le_sharpPhaseSum
    {n m i : Nat} {N s₀ : Real} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hi : i + 1 < m)
    (warmBudget fallbackBudget : Nat → ENNReal)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (hwarm0 : 1 ≤ warmBudget 0) (hretry : ∀ j, 1 ≤ retries j)
    (hsteps : ∀ j, 1 ≤ steps j 0)
    (hwarmTop : ∀ j, warmBudget j ≠ ⊤)
    (hgrowth : ∀ j, adaptiveAcceptedBudget n N s₀ retries warmBudget j +
        fallbackBudget j ≤ warmBudget (j + 1)) :
    10 * (16 : Real) ^ i ≤
      ∑ j ∈ Finset.range m,
        gaussianActiveMeanEnvelopeReal m warmBudget steps retries j := by
  have hp := sixteen_pow_le_warmBudget hN hs₀ retries warmBudget fallbackBudget
    hwarm0 hretry hgrowth i
  have hpReal : (16 : Real) ^ i ≤ (warmBudget i).toReal := by
    have := ENNReal.toReal_mono (hwarmTop i) hp
    simpa using this
  calc
    10 * (16 : Real) ^ i ≤ 10 * (warmBudget i).toReal := by gcongr
    _ ≤ _ := ten_mul_warm_toReal_le_sharpPhaseSum hi warmBudget steps retries
      (Nat.zero_lt_of_lt (hretry i)) (hsteps i)

/-- Minimal concrete witness to the compounding recurrence: one retry, no fallback
warmness, and equality in `hgrowth`. -/
noncomputable def compoundingWarmBudget (n i : Nat) : ENNReal :=
  Nat.rec 1 (fun j M ↦
    (1 : ENNReal) *
      (((16 : ENNReal) * acceleratedSeedWarmFactor n (1 + adaptivePhaseRate 1 1 j)) * M)) i

theorem compoundingWarmBudget_zero (n : Nat) :
    compoundingWarmBudget n 0 = 1 := rfl

theorem compoundingWarmBudget_succ (n i : Nat) :
    compoundingWarmBudget n (i + 1) =
      (16 * acceleratedSeedWarmFactor n (1 + adaptivePhaseRate 1 1 i)) *
        compoundingWarmBudget n i := by
  simp [compoundingWarmBudget]

theorem compoundingWarmBudget_growth (n i : Nat) :
    adaptiveAcceptedBudget n 1 1 (fun _ ↦ 1) (compoundingWarmBudget n) i + 0 ≤
      compoundingWarmBudget n (i + 1) := by
  rw [compoundingWarmBudget_succ]
  simp [adaptiveAcceptedBudget]

theorem compoundingWarmBudget_ne_top (n : Nat) :
    ∀ i, compoundingWarmBudget n i ≠ ⊤ := by
  intro i
  induction i with
  | zero => simp [compoundingWarmBudget]
  | succ i ih =>
      rw [compoundingWarmBudget_succ]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) (by
          unfold acceleratedSeedWarmFactor
          exact ENNReal.ofReal_ne_top)) ih

/-- Even after fixing every retry count and every first-attempt step count to one, the
current warm recurrence makes the sharp phase-sum envelope eventually exceed any fixed
source envelope as the abstract phase count grows.  This is the exact counter-bound for
the presently quantified operational interface. -/
theorem exists_compoundingPhaseSum_gt_sourceEnvelope
    (runtimeConstant : Real) (n : Nat) (radius eps : Real) :
    ∃ m : Nat,
      sourceOneRunQueryEnvelope runtimeConstant n radius eps <
        ∑ j ∈ Finset.range m,
          gaussianActiveMeanEnvelopeReal m (compoundingWarmBudget n)
            (fun _ _ ↦ 1) (fun _ ↦ 1) j := by
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt
    (sourceOneRunQueryEnvelope runtimeConstant n radius eps) (by norm_num : (1 : Real) < 16)
  refine ⟨i + 2, ?_⟩
  have hlower := ten_mul_sixteen_pow_le_sharpPhaseSum
    (n := n) (m := i + 2) (i := i) (N := 1) (s₀ := 1)
    (by norm_num) (by norm_num) (by omega)
    (compoundingWarmBudget n) (fun _ ↦ 0) (fun _ _ ↦ 1) (fun _ ↦ 1)
    (by simp [compoundingWarmBudget]) (fun _ ↦ by simp) (fun _ ↦ by simp)
    (compoundingWarmBudget_ne_top n) (compoundingWarmBudget_growth n)
  calc
    sourceOneRunQueryEnvelope runtimeConstant n radius eps < (16 : Real) ^ i := hi
    _ ≤ 10 * (16 : Real) ^ i := by
      have hp : (0 : Real) ≤ 16 ^ i := by positivity
      nlinarith
    _ ≤ _ := hlower

/-! ## Exact deterministic obstruction in the abstract schedule interface -/

/-- A single retry with a constant step count has exactly the displayed linear envelope. -/
theorem retryReferenceMeanEnvelope_const_one (T : Nat) :
    Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
        1 (fun _ ↦ T) 1 = 10 * (T : Real) := by
  simp [Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope]

/-- For every fixed source budget there is a one-retry step schedule whose one active
phase envelope exceeds it.  Thus no theorem quantifying over the constructor's arbitrary
`steps` argument can produce a universal source constant. -/
theorem exists_onePhaseEnvelope_gt_sourceBudget
    (runtimeConstant : Real) (n : Nat) (radius eps : Real) :
    ∃ T : Nat,
      sourceOneRunQueryBudget runtimeConstant n radius eps <
        ENNReal.ofReal
          (Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
            1 (fun _ ↦ T) 1) := by
  let B := sourceOneRunQueryBudget runtimeConstant n radius eps
  obtain ⟨T, hT⟩ := exists_nat_gt B.toReal
  refine ⟨T, ?_⟩
  rw [retryReferenceMeanEnvelope_const_one]
  have hBtop : B ≠ ⊤ := by
    unfold B sourceOneRunQueryBudget
    exact ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_lt_toReal hBtop ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity : (0 : Real) ≤ 10 * (T : Real))]
  have hT0 : (0 : Real) ≤ T := by positivity
  nlinarith

/-- The obstruction already occurs in the exact `k * sum active means` expression, with
one stream and two schedule states (hence one active transition). -/
theorem exists_sharpPhaseSum_gt_sourceBudget
    (runtimeConstant : Real) (n : Nat) (radius eps : Real) :
    ∃ steps : Nat → Nat → Nat,
      sourceOneRunQueryBudget runtimeConstant n radius eps <
        (1 : ENNReal) * ∑ j ∈ Finset.range 2,
          gaussianActiveMeanEnvelope 2 (fun _ ↦ 1) steps (fun _ ↦ 1) j := by
  obtain ⟨T, hT⟩ := exists_onePhaseEnvelope_gt_sourceBudget
    runtimeConstant n radius eps
  refine ⟨fun _ _ ↦ T, ?_⟩
  simpa [gaussianActiveMeanEnvelope, retryReferenceMeanEnvelope_const_one] using hT

#print axioms lintegral_independentQueryCost_gaussian_le_activeMeanEnvelope
#print axioms lintegral_independentQueryCost_gaussian_le_sourceOneRunQueryBudget
#print axioms sharpPhaseSum_le_sourceBudget_of_real
#print axioms sixteen_pow_le_warmBudget
#print axioms ten_mul_sixteen_pow_le_sharpPhaseSum
#print axioms exists_compoundingPhaseSum_gt_sourceEnvelope
#print axioms exists_onePhaseEnvelope_gt_sourceBudget
#print axioms exists_sharpPhaseSum_gt_sourceBudget

end Ttc.CVGaussianSourceSharpCost

import Ttc.Exec.CVRelativeMeanClippingAssembly

/-!
# Source-sharp first-moment allocation

The score-aware operational error already contains the very small corrected covariance
share.  Its old aggregate estimate unnecessarily required the uniform
`correctedRuntimeSamples` lower bound.  Keeping the fourth power of `correctedAlpha`
shows that the aggregate relative mean error is small for *every nonempty stream
family*.  Thus the first-moment part does not reintroduce a factor proportional to the
number of cooling phases.
-/

set_option autoImplicit false

namespace Ttc.CVSourceWeightedMeanRepair

open Ttc.CVCorrected Ttc.CVGaussianBlockRetryParameters
open Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVGaussianScoreAwareParameters
open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVIndependentStreamMoments Ttc.CVIndependentStreamDependence
open Ttc.CVScoreSeedPhaseKernel Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianSourceWeightedMoment Ttc.CVRelativeMeanClippingAssembly
open Ttc.CVWeightedIndependentStreamAccuracy Ttc.CVCorrectedClippingBias
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The score-aware aggregate mean error is below one percent of the requested inner
accuracy for any positive number of streams.  No `CorrectedSampleBudget` or
`correctedRuntimeSamples ≤ k` premise occurs. -/
theorem scoreAwareMeanGamma_le_div_hundred_of_pos
    {m k : Nat} {eps : Real} (hk : 0 < k) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m k eps ≤ eps / 100 := by
  let x : Real := m
  let a : Real := correctedAlpha m eps
  let nu : Real := correctedNu m eps
  let b : Real := blockShare m k eps
  have hx0 : 0 ≤ x := by positivity
  have hx1 : 0 < x + 1 := by positivity
  have hk1 : (1 : Real) ≤ k + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have heps2 : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg eps]
  have haLower : 100000 * (x + 1) ≤ a := by
    dsimp only [a, x]
    unfold correctedAlpha
    rw [le_div_iff₀ (sq_pos_of_pos heps)]
    nlinarith
  have ha1 : 1 ≤ a := by
    have : (1 : Real) ≤ 100000 * (x + 1) := by nlinarith
    exact this.trans haLower
  have hnu0 : 0 ≤ nu := by
    dsimp only [nu]
    exact correctedNu_nonneg
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact (blockShare_pos heps).le
  have hbNu : b ≤ nu / 8 := by
    dsimp only [b]
    unfold blockShare
    calc
      nu / (8 * ((k : Real) + 1)) ≤ nu / (8 * 1) := by
        apply div_le_div_of_nonneg_left hnu0 (by norm_num)
        nlinarith
      _ = nu / 8 := by ring
  have haSimple : x + 1 ≤ a := by
    exact (by nlinarith : x + 1 ≤ 100000 * (x + 1)).trans haLower
  have hnuSmall : nu ≤ eps ^ 2 /
      (100000 * (x + 1) ^ 5) := by
    dsimp only [nu]
    rw [correctedNu]
    apply div_le_div_of_nonneg_left (sq_nonneg eps) (by positivity)
    calc
      100000 * (x + 1) ^ 5 =
          100000 * (x + 1) ^ 4 * (x + 1) := by ring
      _ ≤
          100000 * a ^ 4 * (x + 1) := by gcongr
      _ = 100000 * a ^ 4 * (x + 1) := rfl
  have hbSmall : b ≤ eps ^ 2 /
      (800000 * (x + 1) ^ 5) := by
    calc
      b ≤ nu / 8 := hbNu
      _ ≤ (eps ^ 2 /
          (100000 * (x + 1) ^ 5)) / 8 := by gcongr
      _ = eps ^ 2 /
          (800000 * (x + 1) ^ 5) := by
        field_simp [ne_of_gt hx1]
        <;> ring
  have hratio : x ^ 2 ≤ (x + 1) ^ 5 := by
    have hle : x ≤ x + 1 := by linarith
    have hsq : x ^ 2 ≤ (x + 1) ^ 2 := by gcongr
    have hpow1 : 1 ≤ (x + 1) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hpow1 (sq_nonneg (x + 1))]
  have hsmall : 4 * x ^ 2 * ((7 / 5 : Real) * b) ≤ eps ^ 2 / 10000 := by
    calc
      4 * x ^ 2 * ((7 / 5 : Real) * b) ≤
          4 * x ^ 2 * ((7 / 5 : Real) *
            (eps ^ 2 /
              (800000 * (x + 1) ^ 5))) := by gcongr
      _ = (28 / 5 : Real) * eps ^ 2 * x ^ 2 /
          (800000 * (x + 1) ^ 5) := by ring
      _ ≤ (28 / 5 : Real) * eps ^ 2 * (x + 1) ^ 5 /
          (800000 * (x + 1) ^ 5) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (7 / 1000000 : Real) * eps ^ 2 := by
        field_simp [ne_of_gt hx1]
        <;> ring
      _ ≤ eps ^ 2 / 10000 := by
        nlinarith [sq_nonneg eps]
  have hsqrtSq : scoreAwareMeanEta m k eps ^ 2 = (7 / 5 : Real) * b := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    simpa only [b] using mul_nonneg (by norm_num) hb0
  have hgamma0 := scoreAwareMeanGamma_nonneg m k eps
  have hgammaSq : scoreAwareMeanGamma m k eps ^ 2 ≤ (eps / 100) ^ 2 := by
    calc
      scoreAwareMeanGamma m k eps ^ 2 =
          4 * x ^ 2 * ((7 / 5 : Real) * b) := by
        rw [scoreAwareMeanGamma, mul_pow, mul_pow, hsqrtSq]
        dsimp only [x]
        ring
      _ ≤ eps ^ 2 / 10000 := hsmall
      _ = (eps / 100) ^ 2 := by ring
  nlinarith [sq_nonneg (scoreAwareMeanGamma m k eps + eps / 100)]

/-- Source-sharp version of the relative clipped-prefix theorem.  The stream count only
has to be nonzero; the old `correctedRuntimeSamples m eps ≤ k` hypothesis is absent. -/
theorem relative_clippedPrefixTarget_sourceSharp
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat} {Q : Nat -> Kernel Seed (State n × Seed)}
    [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps R : Real} {sigmaSq : Nat -> Real} {K : Set (State n)}
    {C : Nat -> Real}
    (V : Nat -> (Fin k -> Nat -> State n × Seed) -> Real)
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    (hmixError : forall j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m k eps
        (relativePhaseSlack chainLength sigmaSq K C)
        (relativePhaseBoundSq R sigmaSq C)) j)
    (heps : 0 < eps) (heps1 : eps <= 1) (hm : 0 < m) (hk : 0 < k)
    (hsigma : forall j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : forall i, Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    (hC1 : forall i, 1 < C i)
    (hWint : forall j, Integrable
      (fun omega => streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hW2int : forall j, Integrable
      (fun omega => (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hWEpos : forall j, 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hrawSecond : forall j, ∫ omega, (streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) <=
      2 * (∫ omega, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hVdef : forall j omega, V j omega = min
      (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (correctedAlpha m eps * ∫ z, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) z
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)))
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 <= initialNormalizer) (hvolume : 0 <= volumeTarget)
    (hinitChain : initialNormalizer = chain chainLength sigmaSq K 0)
    (htargetChain : volumeTarget = chain chainLength sigmaSq K m) :
    ClippedPrefixTarget (independentPathLaw k (stateScheduleFromSeed Q) mu0) V m
      initialNormalizer volumeTarget
      ((m : Real) / (2 * correctedAlpha m eps) + scoreAwareMeanGamma m k eps +
        ((m : Real) / (2 * correctedAlpha m eps)) *
          scoreAwareMeanGamma m k eps) := by
  let pathLaw := independentPathLaw k (stateScheduleFromSeed Q) mu0
  let Wbar := fun j => streamAverage (k := k)
    (positiveScalarPhaseFamilyChainLength (Seed := Seed)
      chainLength sigmaSq K j)
  let gamma := scoreAwareMeanGamma m k eps
  have hgamma0 : 0 <= gamma := scoreAwareMeanGamma_nonneg _ _ _
  have hgammaSmall : gamma <= eps / 100 := by
    simpa only [gamma] using scoreAwareMeanGamma_le_div_hundred_of_pos hk heps heps1
  have hgamma1 : gamma <= 1 := by linarith
  have hmeanError := operational_relative_meanError hop hmixError heps heps1
    hsigma hball hfin hC1
  have hraw0 := operational_rawPrefix_mem_relErr_chainLength hop hk hsigma hK hKc
    hball hfin hKR (scoreAwareMeanEta_nonneg _ _ _) hgamma1
    (by simp [gamma, scoreAwareMeanGamma]) htarget hmeanError hm
  have hpref := prefixMean_positiveChainLength_eq_empirical
    (k := k) (m := m) (chainLength := chainLength) (Q := Q) (mu0 := mu0)
    (sigmaSq := sigmaSq) (K := K)
  have hrawTarget : initialNormalizer * prefixMean pathLaw Wbar m ∈
      Ttc.relErr gamma volumeTarget := by
    rw [hinitChain, hpref, htargetChain]
    exact hraw0
  apply clippedPrefixTarget_of_rawSecondMoment_approx
    (mu := pathLaw) (V := V) (Wbar := Wbar) (k := (8 : Real))
    (alpha := correctedAlpha m eps) (gamma := gamma)
  · norm_num
  · exact correctedAlpha_pos heps
  · exact one_le_correctedAlpha heps heps1
  · exact hinit
  · exact hvolume
  · exact hgamma0
  · rfl
  · intro j omega
    unfold Wbar streamAverage Ttc.CVEst.avgOf streamScore
    apply div_nonneg
    · exact Finset.sum_nonneg fun l _ =>
        positiveScalarPhaseFamilyChainLength_nonneg j (omega l)
    · positivity
  · intro j
    exact measurable_streamAverage
      (measurable_positiveScalarPhaseFamilyChainLength hK j)
  · simpa only [Wbar, pathLaw] using hWint
  · simpa only [Wbar, pathLaw] using hW2int
  · simpa only [Wbar, pathLaw] using hWEpos
  · intro j
    norm_num
    simpa only [Wbar, pathLaw] using hrawSecond j
  · intro j omega
    simpa only [Wbar, pathLaw] using hVdef j omega
  · exact hrawTarget

/-- Bias-aware weighted accuracy with the uniform sample-count premise removed. -/
theorem relative_weighted_accuracy_four_fifths_sourceSharp
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat} {Q : Nat -> Kernel Seed (State n × Seed)}
    [forall i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps beta requested R : Real} {sigmaSq : Nat -> Real} {K : Set (State n)}
    {C factor : Nat -> Real}
    (V W : Nat -> (Fin k -> Nat -> State n × Seed) -> Real)
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    (hmixError : forall j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m k eps
        (relativePhaseSlack chainLength sigmaSq K C)
        (relativePhaseBoundSq R sigmaSq C)) j)
    (heps : 0 < eps) (heps1 : eps <= 1) (hm : 0 < m) (hk : 0 < k)
    (hbeta : 0 <= beta)
    (haccuracyBudget : eps + beta + eps * beta <= requested)
    (hsigma : forall j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : forall i, Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    (hC1 : forall i, 1 < C i)
    (hWint : forall j, Integrable
      (fun omega => streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hW2int : forall j, Integrable
      (fun omega => (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hWEpos : forall j, 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hrawSecond : forall j, ∫ omega, (streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) <=
      2 * (∫ omega, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hVdef : forall j omega, V j omega = min
      (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (correctedAlpha m eps * ∫ z, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) z
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)))
    (hVm : forall j, Measurable (V j)) (hV0 : forall j omega, 0 <= V j omega)
    (hEpos : forall j, 0 < ∫ omega, V j omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hVcap : forall j omega, V j omega <= 2 * correctedAlpha m eps *
      ∫ z, V j z ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hV2 : forall j, Integrable (fun omega => (V j omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hV2cap : forall j omega, (V j omega) ^ 2 <=
      2 * correctedAlpha m eps ^ 2 *
        ∫ z, (V j z) ^ 2 ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hfactor0 : forall j, 0 <= factor j)
    (hphaseMoment : forall j, ∫ omega, (V j omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) <=
      factor j * (∫ omega, V j omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hprefix : forall i, i <= m ->
      prefixMomentRatio factor i <= 1 + eps ^ 2 / 6250)
    (hWm : forall j, Measurable (W j))
    {Eexact : Set (Fin k -> Nat -> State n × Seed)}
    (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw k (stateScheduleFromSeed Q) mu0).real
      Eexactᶜ <= 1 / 20)
    (hExact : forall omega, omega ∈ Eexact ->
      phaseProduct (fun j => streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j)) m omega = phaseProduct W m omega)
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 <= initialNormalizer) (hvolume : 0 <= volumeTarget)
    (hinitChain : initialNormalizer = chain chainLength sigmaSq K 0)
    (htargetChain : volumeTarget = chain chainLength sigmaSq K m)
    (hbetaDef : (m : Real) / (2 * correctedAlpha m eps) +
      scoreAwareMeanGamma m k eps +
      ((m : Real) / (2 * correctedAlpha m eps)) *
        scoreAwareMeanGamma m k eps <= beta) :
    4 / 5 <= (independentPathLaw k (stateScheduleFromSeed Q) mu0).real
      {omega | initialNormalizer * phaseProduct W m omega ∈
        Ttc.relErr requested volumeTarget} := by
  let Wbar := fun j => streamAverage (k := k)
    (positiveScalarPhaseFamilyChainLength (Seed := Seed)
      chainLength sigmaSq K j)
  have hclip0 := relative_clippedPrefixTarget_sourceSharp V hop hmixError
    heps heps1 hm hk hsigma hK hKc hball hfin hKR htarget hC1
    hWint hW2int hWEpos hrawSecond hVdef initialNormalizer volumeTarget
    hinit hvolume hinitChain htargetChain
  have hclip : ClippedPrefixTarget
      (independentPathLaw k (stateScheduleFromSeed Q) mu0) V m
      initialNormalizer volumeTarget beta :=
    Ttc.CV.relErr_mono hbetaDef hvolume hclip0
  apply corrected_independentStreams_accuracy_four_fifths_weighted_biasAware
    (P := stateScheduleFromSeed Q) (Q := Q) (seed := Prod.snd) (mu0 := mu0)
    (etaInner := eps) (beta := beta) (requested := requested)
    V Wbar W factor heps heps1 hbeta haccuracyBudget hVm hV0 hEpos hVcap
    hV2 hV2cap
  · intro j
    exact measurable_streamAverage
      (measurable_positiveScalarPhaseFamilyChainLength hK j)
  · exact hWm
  · intro j omega
    unfold Wbar streamAverage Ttc.CVEst.avgOf streamScore
    apply div_nonneg
    · exact Finset.sum_nonneg fun l _ =>
        positiveScalarPhaseFamilyChainLength_nonneg j (omega l)
    · positivity
  · simpa only [Wbar] using hWint
  · simpa only [Wbar] using hWEpos
  · simpa only [Wbar] using hVdef
  · exact hfactor0
  · exact hphaseMoment
  · exact hprefix
  · exact hEexact
  · exact hExactFail
  · simpa only [Wbar] using hExact
  · exact hop
  · exact hinit
  · exact hvolume
  · exact hclip

#print axioms scoreAwareMeanGamma_le_div_hundred_of_pos
#print axioms relative_clippedPrefixTarget_sourceSharp
#print axioms relative_weighted_accuracy_four_fifths_sourceSharp

end Ttc.CVSourceWeightedMeanRepair

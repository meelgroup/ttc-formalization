import Ttc.Exec.CVSharpUniformParameters
import Ttc.Exec.CVSharpFactorSeven
import Ttc.Exec.CVSlowCanonicalTailPhases
import Ttc.Exec.CVSlowOneRunValid
import Ttc.Exec.CVSlowCanonicalHopAssembly
import Ttc.Exec.CVSlowCanonicalAccuracyBudget

/-!
# The slow canonical frontier certificate at the **sharp** slack / transport pair

`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`
is the frontier one-run certificate at the *loose* pair

* `slack = fun j ↦ phaseMomentSlackSeven m σ K C j / 2`,
* `boundSq = phaseScoreTransportBoundSqSeven R σ = exp (R²/(2 σ_i))² · 15`.

This file is its **sharp twin**, at

* `slack = Ttc.CVSharpUniformParameters.slowSharpSlack n m K`
  (`phaseMomentSlackSeven … slowUniformC j / 6`),
* `boundSq = Ttc.CVSharpScoreTransport.slowSharpBoundSq n R`
  (`exp (R²/(2 σ_i (n+1)))² · 15`).

Nothing in the development is edited; every statement here is new.

## The obstruction that this file had to remove first

The brief for this assembly assumed every ingredient was already proved.  That is true of
the **second-moment** layer — `Ttc.CVSharpFactorSeven` carries the sharpened bound through
it — but it is *false* of the **first-moment** layer, and the failure is not incidental.

In the loose development the mean transport is paid out of the moment budget:
`Ttc.CVScoreAwareHalfMeanBudget.scoreAwareMixError_succ_halfSlack_mean_le_half` derives

`exp (R²/(2 σ_i)) · mixError_i ≤ scoreAwareMeanEta · ratio / 2`

from `mixError_i · boundSq_i ≤ slack_i` by a geometric-mean step, and that step works only
because the loose `boundSq_i` *is* `exp (R²/(2 σ_i))² · 15` — the square of the very
quantity appearing on the left.  Sharpening `boundSq` to `exp (R²/(2 σ_i (n+1)))² · 15`
removes exactly the factor the argument consumed: writing `x := R²/(2 σ_i (n+1))`, the
sharp budget controls `mixError · exp x ²` while the loose mean statement needs
`mixError · exp x ^(n+1)`, a deficit of `exp x ^ n`.  At a cold phase
(`σ_0 = 1/(16 n)`, so `x ≈ 8 R²`) neither branch of
`scoreAwareShare = min (blockShare …) (slack/(3 boundSq))` closes it: the second branch
leaves `r² · exp x ^(n-1) / 54`, and the first leaves `blockShare · exp x ^(n+1)`, and
`blockShare` has no `n`- or `R`-dependence at all.  So the loose mean statement is simply
**not available** at the sharp pair, and the frontier route cannot be replayed verbatim.

The repair is the one `Ttc.CVSharpFactorSeven` already made one layer up: the mean
transport is re-derived at an *arbitrary* sup bound `B` for the phase score, and then run
at `B := sharpPhaseSup`, the true sharp sup.  Concretely, §2 below proves the sharp mean
crux, and §3 re-derives — at a general `B`, with no transport argument re-proved — the four
links

`integral_phaseScore_interior_mem_Icc_of_tvLe`
  → `operational_rawPrefix_mem_relErr_chainLength_of_targetTV`
  → `relative_clippedPrefixTarget_sourceSharp_of_targetTV`
  → `relative_weighted_accuracy_four_fifths_sourceSharp_of_targetTV`,

each of which hard-codes `exp (R²/(2 σ_i))` today.  The bottom one is
`Arlib.GaussianCooling.integral_mem_Icc_of_tvLe`, which is already generic in `B`, exactly
like `sq_moment_le_of_tvLe_map` was for the second moment.

The sharp mean crux itself is *not* new arithmetic.  `scoreAwareMixError_mul_boundSq_le_slack`
at the `/6` slack gives `d · boundSqSharp ≤ (7 − C) r² / 6`, and
`Ttc.CVSharpFactorSeven.sharpPhaseSup_sq_mul_le_three_mul` gives `B² · 15 ≤ 3 · boundSqSharp`;
multiplying reproduces the loose proof's intermediate `d · (B² · 15) ≤ (7 − C) r² / 2`
verbatim, after which the loose argument applies unchanged.  The `/6` slack exists exactly
to absorb that factor three.

## The one forced extra binder

`sharpPhaseSup_sq_mul_le_three_mul` needs `R² ≤ σ_i` **at the terminal index only**, and
that is unavoidable: `Ttc.CVSharpFactorSeven.terminal_sharpPhaseSup_sq_eq_seven` records
that at `i + 1 = m` the loose bound is the true sup, so no `boundSq` strictly below the
seven bound is usable there.  Consequently every sharp statement below carries the
conditional binder `hR2 : ∀ i : Fin m, m ≤ i + 1 → R ^ 2 ≤ σ i` in exactly the shape
`Ttc.CVSharpFactorSeven` uses it; at the canonical phase count it is free
(`R² ≤ N ≤ σ_{m-1}` by `target_le_slowSourceSigmaSq_terminal`), which is how §7 discharges
it.  This is the only deviation from "the same theorem with two binders replaced".
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.CVSharpFrontier

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVIndependentStreamDependence Ttc.CVIndependentStreamMoments
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVRelativeMeanClippingAssembly
open Ttc.CVSourceWeightedMeanRepair
open Ttc.CVGaussianOperationalMean Ttc.CVGaussianOperationalAccuracy
open Ttc.CVGaussianWarmFallbackScoreMoment Ttc.CVCorrectedClippingBias
open Ttc.CVGaussianSourceWeightedMoment
open Ttc.CVWeightedIndependentStreamAccuracy
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowRadiusQReferencePhaseTV Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVSlowSourceTargetTVAccuracy Ttc.CVRAwareGlobalRadius
open Ttc.CVSlowCanonicalShareBounds Ttc.CVMinimalScoreAwareWarmLogArithmetic
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVSlowCanonicalPhaseMomentPackage
open Ttc.CVSlowCanonicalMomentInstantiation
open Ttc.CVSlowCanonicalRobustCertificate
open Ttc.CVCorrectedClippingArithmetic
open Ttc.CVSlowCanonicalSourceReferenceCertificate
open Ttc.CVSlowCanonicalRetainedReference Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVHeterogeneousHistoryReference Ttc.CVSourceReferenceTVCapstone
open Ttc.CVGaussianHybridWeightedCertificate
open Ttc.CVSlowCanonicalHopAssembly Ttc.CVSlowCanonicalAccuracyBudget
open Ttc.CVSharpScoreTransport Ttc.CVSharpUniformParameters Ttc.CVSharpFactorSeven
open scoped ENNReal Classical BigOperators

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## §1 — the schedule side conditions at the sharp pair

The sharp analogue of `Ttc.CVSlowCanonicalUniformParameters.slowUniformParameters_valid`.
Only the third, fourth, ninth and tenth conjuncts change at all: `hslack`/`hbound` become
`slowSharpSlack_pos`/`slowSharpBoundSq_pos`, and `hslackDef`/`hboundDef` are `rfl` at the
sharp definitions.  Everything else is literally the loose lemma's proof term, because
`C`, `q` and `meanTailFloor` are unchanged. -/

/-- **All schedule side conditions of the frontier theorem, at the sharp selection.**
`C := slowUniformC` (still `2`), `q := slowUniformQ`,
`meanTailFloor := slowUniformMeanTailFloor`, `slack := slowSharpSlack n m K` (the `/6`
slack) and `boundSq := slowSharpBoundSq n R` (the sharp transport bound). -/
theorem slowSharpParameters_valid {n : Nat} (hn : 1 ≤ n) (m k : Nat)
    {eps R : Real} (heps : 0 < eps)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) :
    (∀ i, 1 < slowUniformC i) ∧
    (∀ i, slowUniformC i < 7) ∧
    (∀ i, 0 < slowSharpSlack n m K i) ∧
    (∀ i, 0 < slowSharpBoundSq n R i) ∧
    (0 < slowUniformMeanTailFloor n m k eps R) ∧
    (4 ≤ slowUniformQ n m k eps R) ∧
    (slowUniformQ n m k eps R =
      rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
        (slowUniformMeanTailFloor n m k eps R)) ∧
    (∀ i, 1 ≤ slowUniformQ n m k eps R *
      Real.sqrt (slowSourceSigmaSq n (slowSourceInitialVariance n) i) *
      Real.sqrt n) ∧
    (slowSharpSlack n m K = fun j ↦ phaseMomentSlackSeven m
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K slowUniformC j / 6) ∧
    (slowSharpBoundSq n R = phaseScoreTransportBoundSqSharp n R
      (slowSourceSigmaSq n (slowSourceInitialVariance n))) ∧
    (∀ i : Fin m, slowUniformMeanTailFloor n m k eps R ≤
      (scoreAwareMeanEta m k eps *
        (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
            ((i : Nat) + 1) /
          chain m (slowSourceSigmaSq n (slowSourceInitialVariance n))
            K (i : Nat))) / 2) := by
  refine ⟨slowUniformC_gt_one, slowUniformC_lt_seven,
    fun i ↦ slowSharpSlack_pos hn hball hfin i,
    fun i ↦ slowSharpBoundSq_pos i,
    slowUniformMeanTailFloor_pos heps,
    four_le_slowUniformQ hn m k eps R,
    slowUniformQ_rAware n m k eps R,
    fun i ↦ slowUniformQ_rad hn m k eps R i,
    rfl, rfl, fun i ↦ ?_⟩
  exact slowUniformMeanTailFloor_le_meanBudget hn heps hK hball hfin (i : Nat)

#print axioms slowSharpParameters_valid

/-! ## §2 — the crux: the first-moment budget at the sharp pair

The sharp analogue of
`Ttc.CVScoreAwareHalfMeanBudget.scoreAwareMixError_succ_halfSlack_mean_le_half`.  The loose
statement multiplies the mixing error by the loose sup `exp (R²/(2 σ_i))`; this one
multiplies it by the **true** sup `Ttc.CVSharpFactorSeven.sharpPhaseSup`, which is what the
`B`-generic mean transport of §3 consumes.

The only genuinely new step is the first: where the loose proof reads
`d · boundSqSeven ≤ slack/2` straight off `scoreAwareMixError_mul_boundSq_le_slack` (because
`boundSqSeven` *is* `sup² · 15` there), the sharp proof composes
`d · boundSqSharp ≤ slack/6` with
`Ttc.CVSharpFactorSeven.sharpPhaseSup_sq_mul_le_three_mul`'s `sup² · 15 ≤ 3 · boundSqSharp`.
The product is the loose proof's own intermediate `d · (sup² · 15) ≤ (7 − C i) r² / 2`,
after which every remaining line of the loose argument applies verbatim.  This is exactly
why the sharp mixing slack has to be `… / 6`. -/

/-- **The sharp first-moment crux.**  At the `/6` slack and the sharpened transport bound,
the mixing error scaled by the *true* per-index score sup still fits half of the
geometric-mean first-moment allowance.

`hR2` is needed only at the terminal index `chainLength ≤ i + 1`; see
`Ttc.CVSharpFactorSeven.terminal_sharpPhaseSup_sq_eq_seven` for why it cannot be dropped. -/
theorem scoreAwareMixError_succ_sixthSlack_sharpMean_le_half
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {eps R s0 : Real}
    {K : Set (State n)} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hs0 : 0 < s0)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hC0 : ∀ j, 0 ≤ C j) (hC7 : ∀ j, C j < 7) {i : Nat}
    (hR2 : chainLength ≤ i + 1 → R ^ 2 ≤ slowSourceSigmaSq n s0 i) :
    sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i *
        (scoreAwareMixError (m + 1) k (eps / 2)
          (fun j ↦ phaseMomentSlackSeven chainLength (slowSourceSigmaSq n s0) K C j / 6)
          (phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0)) i).toReal ≤
      (scoreAwareMeanEta m k eps *
        (chain chainLength (slowSourceSigmaSq n s0) K (i + 1) /
          chain chainLength (slowSourceSigmaSq n s0) K i)) / 2 := by
  have hsigma : ∀ j, 0 < slowSourceSigmaSq n s0 j := slowSourceSigmaSq_pos hn hs0
  set e : Real := sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i with hedef
  set d : Real := (scoreAwareMixError (m + 1) k (eps / 2)
    (fun j ↦ phaseMomentSlackSeven chainLength (slowSourceSigmaSq n s0) K C j / 6)
    (phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0)) i).toReal with hddef
  set bs : Real := blockShare (m + 1) k (eps / 2) with hbsdef
  set b : Real := blockShare m k eps with hbdef
  set r : Real := chain chainLength (slowSourceSigmaSq n s0) K (i + 1) /
    chain chainLength (slowSourceSigmaSq n s0) K i with hrdef
  have he0 : 0 < e := sharpPhaseSup_pos _ _
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hb0 : 0 < b := blockShare_pos heps
  have hbs0 : 0 < bs := blockShare_pos (by positivity : 0 < eps / 2)
  have hr0 : 0 < r := div_pos (chain_pos hsigma hball hfin _)
    (chain_pos hsigma hball hfin _)
  have hslackPos : ∀ j,
      0 < phaseMomentSlackSeven chainLength (slowSourceSigmaSq n s0) K C j / 6 :=
    fun j ↦ div_pos (phaseMomentSlackSeven_pos hsigma hball hfin hC7 j) (by norm_num)
  have hboundPos : ∀ j, 0 < phaseScoreTransportBoundSqSharp n R
      (slowSourceSigmaSq n s0) j := phaseScoreTransportBoundSqSharp_pos
  -- the share bound, unchanged from the loose proof
  have hshare := scoreAwareMixError_toReal_le_three_share
    (m := m + 1) (k := k) (eps := eps / 2)
    (slack := fun j ↦ phaseMomentSlackSeven chainLength (slowSourceSigmaSq n s0) K C j / 6)
    (boundSq := phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0))
    (by positivity) (by linarith) hslackPos hboundPos i
  have hdbs : d ≤ 3 * bs := by
    refine hshare.trans ?_
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  -- the one new step: the `/6` slack plus the factor-three crux reproduce the loose
  -- proof's intermediate `d * (sup^2 * 15) ≤ (7 - C i) * r^2 / 2`
  have hmoment := scoreAwareMixError_mul_boundSq_le_slack
    (m := m + 1) (k := k) (eps := eps / 2)
    (slack := fun j ↦ phaseMomentSlackSeven chainLength (slowSourceSigmaSq n s0) K C j / 6)
    (boundSq := phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0))
    (by positivity) (by linarith) hslackPos hboundPos i
  have hcrux : e ^ 2 * (1 + 2 * 7) ≤
      3 * phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0) i :=
    sharpPhaseSup_sq_mul_le_three_mul hn hs0 hR2
  have hmoment' : d * (e ^ 2 * 15) ≤ (7 - C i) * r ^ 2 / 2 := by
    have hslackVal : phaseMomentSlackSeven chainLength (slowSourceSigmaSq n s0) K C i
        = (7 - C i) * r ^ 2 := rfl
    have h1 : d * (e ^ 2 * (1 + 2 * 7)) ≤
        d * (3 * phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0) i) :=
      mul_le_mul_of_nonneg_left hcrux hd0
    have h2 : d * phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0) i ≤
        (7 - C i) * r ^ 2 / 6 := by
      simpa only [hslackVal] using hmoment
    nlinarith [h1, h2]
  have hright : d * ((7 - C i) * r ^ 2 / 2) ≤ (3 * bs) * (7 * r ^ 2 / 2) := by
    have hAB : (7 - C i) * r ^ 2 / 2 ≤ 7 * r ^ 2 / 2 := by
      gcongr
      linarith [hC0 i]
    have hB0 : 0 ≤ 7 * r ^ 2 / 2 := by positivity
    exact (mul_le_mul_of_nonneg_left hAB hd0).trans
      (mul_le_mul_of_nonneg_right hdbs hB0)
  have hsq : (e * d) ^ 2 ≤ (7 / 10 : Real) * bs * r ^ 2 := by
    calc
      (e * d) ^ 2 = (d * (d * (e ^ 2 * 15))) / 15 := by ring
      _ ≤ (d * ((7 - C i) * r ^ 2 / 2)) / 15 := by gcongr
      _ ≤ ((3 * bs) * (7 * r ^ 2 / 2)) / 15 := by gcongr
      _ = (7 / 10 : Real) * bs * r ^ 2 := by ring
  have hbs : bs ≤ b / 1024 := by
    rw [show bs = blockShare (m + 1) k eps / 1024 by
      simpa only [hbsdef] using
        Ttc.CVScoreAwareHalfMeanBudget.blockShare_half_accuracy (m := m + 1) (k := k) heps]
    gcongr
    exact Ttc.CVScoreAwareHalfMeanBudget.blockShare_succ_le (m := m) (k := k) heps
  have hetaSq : (scoreAwareMeanEta m k eps) ^ 2 = (7 / 5 : Real) * b := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    exact mul_nonneg (by norm_num) hb0.le
  have heta0 := scoreAwareMeanEta_nonneg m k eps
  have hsq' : (e * d) ^ 2 ≤ (scoreAwareMeanEta m k eps * r / 2) ^ 2 := by
    calc
      (e * d) ^ 2 ≤ (7 / 10 : Real) * bs * r ^ 2 := hsq
      _ ≤ (7 / 10 : Real) * (b / 1024) * r ^ 2 := by gcongr
      _ ≤ (scoreAwareMeanEta m k eps * r / 2) ^ 2 := by
        have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
        nlinarith [hetaSq]
  have hed0 : 0 ≤ e * d := mul_nonneg he0.le hd0
  have htarget0 : 0 ≤ scoreAwareMeanEta m k eps * r / 2 := by positivity
  nlinarith [hsq', hed0, htarget0]

#print axioms scoreAwareMixError_succ_sixthSlack_sharpMean_le_half

/-! ## §3 — the first-moment layer at an arbitrary sup bound

`Arlib.GaussianCooling.integral_phaseScore_interior_mem_Icc_of_tvLe` and the three Ttc
lemmas built on it hard-code the sup as `exp (R²/(2 σ_i))`.  The Arlib workhorse one level
down, `Arlib.GaussianCooling.integral_mem_Icc_of_tvLe`, is already generic in the bound `B`,
so the sharp versions are obtained by re-deriving these four at a general `B` — exactly as
`Ttc.CVSharpFactorSeven` §3a did for the second moment, and with no transport argument
re-proved. -/

/-- Mean transport at an arbitrary sup bound: the first-moment analogue of
`Ttc.CVSharpFactorSeven.phaseScore_interior_sq_moment_le_of_tvLe_bound`. -/
theorem integral_phaseScore_interior_mem_Icc_of_tvLe_bound
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {chainLength : Nat} {sigmaSq : Nat → Real} {i : Nat}
    {K : Set (State n)} {X : Omega → State n} {e : ENNReal}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hX : Measurable X)
    (hTV : TVLe (Measure.map X mu) (coolLaw chainLength sigmaSq K i) e)
    (he : e ≠ ⊤) {B : Real} (hB : 0 < B)
    (hfB : ∀ x, phaseScore chainLength sigmaSq (interior K) i x ≤ B)
    {eta : Real}
    (hslack : B * e.toReal ≤ eta * (chain chainLength sigmaSq K (i + 1) /
      chain chainLength sigmaSq K i)) :
    ∫ omega, phaseScore chainLength sigmaSq (interior K) i (X omega) ∂mu ∈
      Set.Icc ((1 - eta) * (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i))
        ((1 + eta) * (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i)) := by
  haveI : IsProbabilityMeasure (Measure.map X mu) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI := coolLaw_isProbabilityMeasure (m := chainLength) (σsq := sigmaSq)
    hsigma hball hfin i
  have hmap : ∫ x, phaseScore chainLength sigmaSq (interior K) i x ∂(Measure.map X mu)
      = ∫ omega, phaseScore chainLength sigmaSq (interior K) i (X omega) ∂mu :=
    integral_map hX.aemeasurable
      (measurable_phaseScore isOpen_interior.measurableSet i).aestronglyMeasurable
  have hmean := integral_phaseScore_interior_coolLaw (m := chainLength) (i := i)
    hsigma hKc hball hfin
  rw [← hmap]
  exact integral_mem_Icc_of_tvLe hTV he
    (measurable_phaseScore isOpen_interior.measurableSet i) hB
    (phaseScore_nonneg chainLength sigmaSq (interior K) i) hfB hmean hslack

/-- The sharp analogue of
`Ttc.CVRelativeMeanClippingAssembly.operational_rawPrefix_mem_relErr_chainLength_of_targetTV`,
at an arbitrary per-index sup bound `B`. -/
theorem operational_rawPrefix_mem_relErr_chainLength_of_targetTV_bound
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps) (hk : 0 < k)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {eta gamma : Real}
    (heta : 0 ≤ eta) (hgamma : gamma ≤ 1)
    (hbudget : 2 * (m : Real) * eta ≤ gamma)
    {B : Nat → Real} (hB : ∀ i, 0 < B i)
    (hfB : ∀ i x, phaseScore chainLength sigmaSq (interior K) i x ≤ B i)
    {targetError : Nat → ENNReal}
    (htargetTV : ∀ i, TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw chainLength sigmaSq K i) (targetError i))
    (htargetError : ∀ i, targetError i ≠ ⊤)
    (herror : ∀ i : Fin m,
      (hop.mixError (i : Nat) + targetError (i : Nat)).toReal * B (i : Nat) ≤
        eta * (chain chainLength sigmaSq K ((i : Nat) + 1) /
          chain chainLength sigmaSq K (i : Nat)))
    (hm : 0 < m) :
    chain chainLength sigmaSq K 0 *
        prefixMean (independentPathLaw k (stateScheduleFromSeed Q) mu0)
          (empiricalPhaseFamily (Seed := Seed) k chainLength sigmaSq K) m ∈
      Ttc.relErr gamma (chain chainLength sigmaSq K m) := by
  apply prefixMean_mem_relErr_of_phaseMeans_budget hm heta hgamma hbudget
    (fun i ↦ chain_pos hsigma hball hfin i)
  intro i
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let g := Ttc.CVGaussianOperationalMean.scalarPhaseScore (Seed := Seed)
    chainLength sigmaSq K (i : Nat)
  have hg : Measurable g :=
    Ttc.CVGaussianOperationalMean.measurable_scalarPhaseScore hK i
  have htv0 := tvLe_operational_score_eval_succ hop (i : Nat)
  have htv : TVLe
      (Measure.map (fun omega : Nat → State n × Seed ↦
        (omega ((i : Nat) + 1)).1) scalarLaw)
      (coolLaw chainLength sigmaSq K (i : Nat))
      (hop.mixError (i : Nat) + targetError (i : Nat)) :=
    htv0.trans (htargetTV (i : Nat))
  have hmean : ∫ omega, g omega ∂scalarLaw ∈ Ttc.relErr eta
      (chain chainLength sigmaSq K ((i : Nat) + 1) /
        chain chainLength sigmaSq K (i : Nat)) := by
    apply integral_phaseScore_interior_mem_Icc_of_tvLe_bound hsigma hKc hball hfin
      (measurable_fst.comp (measurable_pi_apply ((i : Nat) + 1))) htv
      (ENNReal.add_ne_top.2 ⟨hop.mixError_ne_top (i : Nat),
        htargetError (i : Nat)⟩) (hB (i : Nat)) (hfB (i : Nat))
    simpa only [mul_comm] using herror i
  have hgInt : Integrable g scalarLaw := by
    apply Integrable.of_bound hg.aestronglyMeasurable (B (i : Nat))
    filter_upwards with omega
    dsimp only [g, Ttc.CVGaussianOperationalMean.scalarPhaseScore]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (phaseScore_nonneg chainLength sigmaSq (interior K) (i : Nat) _)]
    exact hfB (i : Nat) _
  have havg := integral_streamAverage hk scalarLaw hg hgInt
  simpa only [empiricalPhaseFamily, independentPathLaw, scalarLaw, g] using
    (havg ▸ hmean)

/-- The sharp analogue of
`Ttc.CVSlowCanonicalPhaseMomentPackage.operational_positiveStreamMean_upto_of_targetTV`,
at an arbitrary per-index sup bound `B`. -/
theorem operational_positiveStreamMean_upto_of_targetTV_bound
    {k m chainLength : Nat} (hk : 0 < k)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real} {eps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {eta : Real} (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    {B : Nat → Real} (hB : ∀ i, 0 < B i)
    (hfB : ∀ i x, phaseScore chainLength sigmaSq (interior K) i x ≤ B i)
    {targetError : Nat → ENNReal}
    (htargetTV : ∀ i, TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw chainLength sigmaSq K i) (targetError i))
    (htargetError : ∀ i, targetError i ≠ ⊤)
    (herror : ∀ i : Fin m,
      (hop.mixError (i : Nat) + targetError (i : Nat)).toReal * B (i : Nat) ≤
        eta * (chain chainLength sigmaSq K ((i : Nat) + 1) /
          chain chainLength sigmaSq K (i : Nat))) :
    ∀ j, j ≤ m → 0 < ∫ omega,
      streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          chainLength sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) := by
  intro j hj
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  cases j with
  | zero =>
      have havg := integral_streamAverage hk scalarLaw
        (g := fun _ : Nat → State n × State n ↦ (1 : Real)) measurable_const
        (integrable_const 1)
      have havg' : ∫ omega, streamAverage (k := k)
          (fun _ : Nat → State n × State n ↦ (1 : Real)) omega
          ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) = 1 := by
        simpa [independentPathLaw, scalarLaw] using havg
      simpa [positiveScalarPhaseFamilyChainLength, havg']
  | succ i =>
      have hi : i < m := Nat.lt_of_succ_le hj
      let g := Ttc.CVGaussianOperationalMean.scalarPhaseScore
        (Seed := State n) chainLength sigmaSq K i
      have hg : Measurable g :=
        Ttc.CVGaussianOperationalMean.measurable_scalarPhaseScore hK i
      have htv0 := tvLe_operational_score_eval_succ hop i
      have htv : TVLe
          (Measure.map (fun omega : Nat → State n × State n ↦
            (omega (i + 1)).1) scalarLaw)
          (coolLaw chainLength sigmaSq K i)
          (hop.mixError i + targetError i) := htv0.trans (htargetTV i)
      have hmean : ∫ omega, g omega ∂scalarLaw ∈ Ttc.relErr eta
          (chain chainLength sigmaSq K (i + 1) /
            chain chainLength sigmaSq K i) := by
        apply integral_phaseScore_interior_mem_Icc_of_tvLe_bound hsigma hKc hball
          hfin (measurable_fst.comp (measurable_pi_apply (i + 1))) htv
          (ENNReal.add_ne_top.2 ⟨hop.mixError_ne_top i, htargetError i⟩)
          (hB i) (hfB i)
        simpa only [mul_comm] using herror ⟨i, hi⟩
      have hratio : 0 < chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i :=
        div_pos (chain_pos hsigma hball hfin _)
          (chain_pos hsigma hball hfin _)
      have hgInt : Integrable g scalarLaw := by
        apply Integrable.of_bound hg.aestronglyMeasurable (B i)
        filter_upwards with omega
        dsimp only [g, Ttc.CVGaussianOperationalMean.scalarPhaseScore]
        rw [Real.norm_eq_abs, abs_of_nonneg
          (phaseScore_nonneg chainLength sigmaSq (interior K) i _)]
        exact hfB i _
      have hscalarPos : 0 < ∫ omega, g omega ∂scalarLaw := by
        have hlower := hmean.1
        exact (mul_pos (sub_pos.2 heta1) hratio).trans_le hlower
      have havg := integral_streamAverage hk scalarLaw hg hgInt
      simpa only [positiveScalarPhaseFamilyChainLength, independentPathLaw,
        scalarLaw, g, ← havg] using hscalarPos

#print axioms integral_phaseScore_interior_mem_Icc_of_tvLe_bound
#print axioms operational_rawPrefix_mem_relErr_chainLength_of_targetTV_bound
#print axioms operational_positiveStreamMean_upto_of_targetTV_bound

/-- The sharp analogue of
`Ttc.CVSourceWeightedMeanRepair.relative_clippedPrefixTarget_sourceSharp_of_targetTV`,
at an arbitrary per-index sup bound `B`.  The clipping half is untouched; only the
first-moment input `hmeanError` moves from the loose sup to `B`. -/
theorem relative_clippedPrefixTarget_sourceSharp_of_targetTV_bound
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps : Real} {sigmaSq : Nat → Real} {K : Set (State n)}
    {targetError : Nat → ENNReal}
    (V : Nat → (Fin k → Nat → State n × Seed) → Real)
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hm : 0 < m) (hk : 0 < k)
    (hsigma : ∀ j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤)
    {B : Nat → Real} (hB : ∀ i, 0 < B i)
    (hfB : ∀ i x, phaseScore chainLength sigmaSq (interior K) i x ≤ B i)
    (htargetTV : ∀ i, TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw chainLength sigmaSq K i) (targetError i))
    (htargetError : ∀ i, targetError i ≠ ⊤)
    (hmeanError : ∀ i : Fin m,
      (hop.mixError (i : Nat) + targetError (i : Nat)).toReal * B (i : Nat) ≤
        scoreAwareMeanEta m k eps *
          (chain chainLength sigmaSq K ((i : Nat) + 1) /
            chain chainLength sigmaSq K (i : Nat)))
    (hWint : ∀ j, Integrable
      (fun omega ↦ streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hW2int : ∀ j, Integrable
      (fun omega ↦ (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hWEpos : ∀ j, 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hrawSecond : ∀ j, ∫ omega, (streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) ≤
      2 * (∫ omega, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hVdef : ∀ j omega, V j omega = min
      (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (correctedAlpha m eps * ∫ z, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) z
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)))
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hinitChain : initialNormalizer = chain chainLength sigmaSq K 0)
    (htargetChain : volumeTarget = chain chainLength sigmaSq K m) :
    ClippedPrefixTarget (independentPathLaw k (stateScheduleFromSeed Q) mu0) V m
      initialNormalizer volumeTarget
      ((m : Real) / (2 * correctedAlpha m eps) + scoreAwareMeanGamma m k eps +
        ((m : Real) / (2 * correctedAlpha m eps)) *
          scoreAwareMeanGamma m k eps) := by
  let pathLaw := independentPathLaw k (stateScheduleFromSeed Q) mu0
  let Wbar := fun j ↦ streamAverage (k := k)
    (positiveScalarPhaseFamilyChainLength (Seed := Seed)
      chainLength sigmaSq K j)
  let gamma := scoreAwareMeanGamma m k eps
  have hgamma0 : 0 ≤ gamma := scoreAwareMeanGamma_nonneg _ _ _
  have hgammaSmall : gamma ≤ eps / 100 := by
    simpa only [gamma] using scoreAwareMeanGamma_le_div_hundred_of_pos hk heps heps1
  have hgamma1 : gamma ≤ 1 := by linarith
  have hraw0 := operational_rawPrefix_mem_relErr_chainLength_of_targetTV_bound
    hop hk hsigma hK hKc hball hfin (scoreAwareMeanEta_nonneg _ _ _)
    hgamma1 (by simp [gamma, scoreAwareMeanGamma]) hB hfB htargetTV htargetError
    hmeanError hm
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
    · exact Finset.sum_nonneg fun l _ ↦
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

/-- The sharp analogue of
`Ttc.CVSourceWeightedMeanRepair.relative_weighted_accuracy_four_fifths_sourceSharp_of_targetTV`,
at an arbitrary per-index sup bound `B`.  This is the theorem the sharp frontier calls in
place of the loose one. -/
theorem relative_weighted_accuracy_four_fifths_sourceSharp_of_targetTV_bound
    {Seed : Type*} [MeasurableSpace Seed]
    {k m chainLength : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps beta requested : Real} {sigmaSq : Nat → Real} {K : Set (State n)}
    {factor : Nat → Real} {targetError : Nat → ENNReal}
    (V W : Nat → (Fin k → Nat → State n × Seed) → Real)
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hm : 0 < m) (hk : 0 < k)
    (hbeta : 0 ≤ beta)
    (haccuracyBudget : eps + beta + eps * beta ≤ requested)
    (hsigma : ∀ j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤)
    {B : Nat → Real} (hB : ∀ i, 0 < B i)
    (hfB : ∀ i x, phaseScore chainLength sigmaSq (interior K) i x ≤ B i)
    (htargetTV : ∀ i, TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw chainLength sigmaSq K i) (targetError i))
    (htargetError : ∀ i, targetError i ≠ ⊤)
    (hmeanError : ∀ i : Fin m,
      (hop.mixError (i : Nat) + targetError (i : Nat)).toReal * B (i : Nat) ≤
        scoreAwareMeanEta m k eps *
          (chain chainLength sigmaSq K ((i : Nat) + 1) /
            chain chainLength sigmaSq K (i : Nat)))
    (hWint : ∀ j, Integrable
      (fun omega ↦ streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hW2int : ∀ j, Integrable
      (fun omega ↦ (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hWEpos : ∀ j, 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hrawSecond : ∀ j, ∫ omega, (streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := Seed)
        chainLength sigmaSq K j) omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) ≤
      2 * (∫ omega, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hVdef : ∀ j omega, V j omega = min
      (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) omega)
      (correctedAlpha m eps * ∫ z, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j) z
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)))
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hVcap : ∀ j omega, V j omega ≤ 2 * correctedAlpha m eps *
      ∫ z, V j z ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hV2 : ∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤
      2 * correctedAlpha m eps ^ 2 *
        ∫ z, (V j z) ^ 2 ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0))
    (hfactor0 : ∀ j, 0 ≤ factor j)
    (hphaseMoment : ∀ j, ∫ omega, (V j omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) ≤
      factor j * (∫ omega, V j omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hprefix : ∀ i, i ≤ m →
      prefixMomentRatio factor i ≤ 1 + eps ^ 2 / 6250)
    (hWm : ∀ j, Measurable (W j))
    {Eexact : Set (Fin k → Nat → State n × Seed)}
    (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw k (stateScheduleFromSeed Q) mu0).real
      Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega, omega ∈ Eexact →
      phaseProduct (fun j ↦ streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := Seed)
          chainLength sigmaSq K j)) m omega = phaseProduct W m omega)
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hinitChain : initialNormalizer = chain chainLength sigmaSq K 0)
    (htargetChain : volumeTarget = chain chainLength sigmaSq K m)
    (hbetaDef : (m : Real) / (2 * correctedAlpha m eps) +
      scoreAwareMeanGamma m k eps +
      ((m : Real) / (2 * correctedAlpha m eps)) *
        scoreAwareMeanGamma m k eps ≤ beta) :
    4 / 5 ≤ (independentPathLaw k (stateScheduleFromSeed Q) mu0).real
      {omega | initialNormalizer * phaseProduct W m omega ∈
        Ttc.relErr requested volumeTarget} := by
  let Wbar := fun j ↦ streamAverage (k := k)
    (positiveScalarPhaseFamilyChainLength (Seed := Seed)
      chainLength sigmaSq K j)
  have hclip0 := relative_clippedPrefixTarget_sourceSharp_of_targetTV_bound V hop
    heps heps1 hm hk hsigma hK hKc hball hfin hB hfB htargetTV htargetError
    hmeanError hWint hW2int hWEpos hrawSecond hVdef initialNormalizer volumeTarget
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
    · exact Finset.sum_nonneg fun l _ ↦
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

#print axioms relative_clippedPrefixTarget_sourceSharp_of_targetTV_bound
#print axioms relative_weighted_accuracy_four_fifths_sourceSharp_of_targetTV_bound

/-! ## §4 — the sharp per-phase first-moment error

The radial-tail half never touched `boundSq`, and the sharp sup is *below* the loose one,
so `Ttc.CVRAwareGlobalRadius.slowTargetError_rAware_scaled_le` covers it verbatim. -/

/-- The sharp analogue of
`Ttc.CVRAwareGlobalRadius.mix_add_slowTargetError_rAware_scaled_le`: mixing plus radial
tail, scaled by the **true** per-index score sup rather than the loose one. -/
theorem mix_add_slowTargetError_rAware_sharpScaled_le
    {n m chainLength i : Nat} (hn : 1 ≤ n) {R s0 b target : Real} {mix : ENNReal}
    (hs0 : 0 < s0) (hb : 0 < b) (hi : i < m) (hmixTop : mix ≠ ⊤)
    (hmix : mix.toReal *
      sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i ≤ target / 2)
    (hbudget : b ≤ target / 2) :
    (mix + slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
        sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i ≤ target := by
  have hsup0 : 0 ≤ sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i :=
    sharpPhaseSup_nonneg _ _
  have hsupLoose : sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i ≤
      Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) :=
    sharpPhaseSup_le_loose (slowSourceSigmaSq_pos hn hs0 i)
  have htail0 : 0 ≤ (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal :=
    ENNReal.toReal_nonneg
  have htailLoose : (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
      Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) ≤ target / 2 :=
    slowTargetError_rAware_scaled_le hn hs0 hb hi hbudget
  have htail : (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
      sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i ≤ target / 2 := by
    refine le_trans ?_ htailLoose
    exact mul_le_mul_of_nonneg_left hsupLoose htail0
  rw [ENNReal.toReal_add hmixTop (slowTargetError_ne_top n _ m i)]
  calc
    (mix.toReal + (slowTargetError n
        (rAwareGlobalRadiusQ n R s0 b) m i).toReal) *
          sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i =
      mix.toReal * sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i +
        (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
          sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i := by ring
    _ ≤ target / 2 + target / 2 := add_le_add hmix htail
    _ = target := by ring

#print axioms mix_add_slowTargetError_rAware_sharpScaled_le

/-! ## §5 — the estimator-moment binders at the sharp pair

The sharp analogue of `Ttc.CVSlowCanonicalMomentBinders.slowCanonical_momentBinders`.

* the factor-seven input becomes
  `Ttc.CVSharpFactorSeven.operational_slowCanonical_positiveScalar_factorSeven_sharp_upto`
  and its `htailBudget` becomes `Ttc.CVSharpFactorSeven.slowSharp_htailBudget`;
* `hWEpos` is **not** bound-independent — it consumes the first-moment budget, so it is
  re-derived here through §2 and §3;
* the stream-moment and clipped-moment bundles
  (`operational_slowCanonical_streamMoment_bundle_upto`,
  `operational_slowCanonical_clippedMoment_bundle_upto`) and the factor bundle
  (`corrected_factorEight_prefix_bundle`) **are** bound-independent: none of their
  statements mentions `slack` or `boundSq`, they consume only the factor-seven package and
  the positivity of the raw stream means, so they transfer verbatim. -/

/-- The finite-prefix scalar factor-seven package at the sharp pair. -/
theorem slowSharp_scalarFactorSeven
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat)) :
    ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n)) ∧
      ∫ omega, (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
        7 * (∫ omega, positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q)
            (slowInitialPair n))) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  exact operational_slowCanonical_positiveScalar_factorSeven_sharp_upto
    (b := slowUniformMeanTailFloor n m (correctedRuntimeSamples m eps) eps R)
    (C := fun _ ↦ 2)
    hop hn1 heps heps1 hs0 (slowUniformMeanTailFloor_pos heps)
    (slowSourceSigmaSq_pos hn1 hs0) hKc hball hfin hKR
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) hmixError
    (slowCanonical_htargetTV hop hn1 hK hKc hball hfin htau) rfl
    hexact hR2
    (slowSharp_htailBudget hn1 m (correctedRuntimeSamples m eps) hK hball hfin)

/-- The frontier's `hWEpos` on the estimator prefix, at the sharp pair.  This is the
conjunct the brief expected to be free and is not: it is re-derived through the sharp
first-moment crux (§2) and the `B`-generic mean transport (§3). -/
theorem slowSharp_hWEpos
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) j)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat)) :
    ∀ j, j ≤ m → 0 < ∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n) m
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)) := by
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have hmeanMix : ∀ i : Fin m,
      (hop.mixError (i : Nat)).toReal *
          sharpPhaseSup n R (slowSourceSigmaSq n (slowSourceInitialVariance n)) m
            (i : Nat) ≤
        (scoreAwareMeanEta m (correctedRuntimeSamples m eps) eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              (i : Nat))) / 2 := by
    intro i
    have hslackEq : slowSharpSlack n m K =
        fun j ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) j / 6 := rfl
    have hboundEq : slowSharpBoundSq n R =
        phaseScoreTransportBoundSqSharp n R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) := rfl
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1), hslackEq, hboundEq]
    simpa only [mul_comm] using
      scoreAwareMixError_succ_sixthSlack_sharpMean_le_half
        (n := n) (m := m) (k := correctedRuntimeSamples m eps) (chainLength := m)
        (eps := eps) (R := R) (s0 := slowSourceInitialVariance n)
        (K := K) (C := fun _ ↦ 2) (i := (i : Nat))
        hn1 heps heps1 hs0 hball hfin
        (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) (hR2 i)
  have hmeanError : ∀ i : Fin m,
      (hop.mixError (i : Nat) + slowTargetError n
            (rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
              (slowUniformMeanTailFloor n m (correctedRuntimeSamples m eps) eps R))
            m (i : Nat)).toReal *
          sharpPhaseSup n R (slowSourceSigmaSq n (slowSourceInitialVariance n)) m
            (i : Nat) ≤
        scoreAwareMeanEta m (correctedRuntimeSamples m eps) eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n))
              K (i : Nat)) := by
    intro i
    exact mix_add_slowTargetError_rAware_sharpScaled_le hn1 hs0
      (slowUniformMeanTailFloor_pos heps) i.isLt (hop.mixError_ne_top i)
      (hmeanMix i)
      (slowUniformMeanTailFloor_le_meanBudget hn1 heps hK hball hfin (i : Nat))
  exact operational_positiveStreamMean_upto_of_targetTV_bound
    (correctedRuntimeSamples_pos m eps) hop
    (slowSourceSigmaSq_pos hn1 hs0) hK hKc hball hfin
    (scoreAwareMeanEta_nonneg m (correctedRuntimeSamples m eps) eps)
    (Ttc.CVSlowCanonicalMomentBinders.scoreAwareMeanEta_lt_one m
      (correctedRuntimeSamples m eps) heps heps1)
    (fun i ↦ sharpPhaseSup_pos m i)
    (fun i x ↦ phaseScore_le_sharpPhaseSup hn1 hs0
      (interior_subset.trans hKR) x)
    (slowCanonical_htargetTV hop hn1 hK hKc hball hfin htau)
    (slowTargetError_ne_top n _ m) hmeanError

#print axioms slowSharp_scalarFactorSeven
#print axioms slowSharp_hWEpos

/-- **The seven estimator-moment binders of the frontier theorem, at the sharp pair.**
The sharp analogue of `Ttc.CVSlowCanonicalMomentBinders.slowCanonical_momentBinders`, at
`k := correctedRuntimeSamples m eps`,
`factor := fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)`, `C := fun _ ↦ 2`,
`q := slowUniformQ n m (correctedRuntimeSamples m eps) eps R`,
`slack := slowSharpSlack n m K` and `boundSq := slowSharpBoundSq n R`.

Conjuncts 1, 2, 4 and 6 come from the bound-independent stream/clipped moment bundles
`operational_slowCanonical_streamMoment_bundle_upto` and
`operational_slowCanonical_clippedMoment_bundle_upto`, fed by the sharp factor-seven
package; conjuncts 5 and 7 are `corrected_factorEight_prefix_bundle`, which mentions
neither `slack` nor `boundSq` and so transfers verbatim.  Conjunct 3 is the one that does
**not** transfer and is supplied by `slowSharp_hWEpos`. -/
theorem slowSharp_momentBinders
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat)) :
    (∀ j, j ≤ m → Integrable
      (fun omega ↦ streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, j ≤ m → Integrable
      (fun omega ↦ (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, j ≤ m → 0 < ∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, j ≤ m → ∫ omega, (streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ _j : Nat, 0 ≤ (fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)) _j) ∧
    (∀ j, j ≤ m → ∫ omega,
        (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
          (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n))
          K j omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      (fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)) j *
        (∫ omega, slowClippedPositiveEmpiricalFamily m
            (correctedRuntimeSamples m eps) eps Q (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ i, i ≤ m →
      prefixMomentRatio
        (fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)) i ≤
          1 + eps ^ 2 / 6250) := by
  have hscalar := slowSharp_scalarFactorSeven hn m heps heps1 hK hKc hball hfin
    hKR hop htau hmixError hexact hR2
  have hmeanPos := slowSharp_hWEpos hn m heps heps1 hK hKc hball hfin hKR
    hop htau hmixError hR2
  have hstream := operational_slowCanonical_streamMoment_bundle_upto
    (m := m) (eps := eps) heps heps1 hK
    (Q := Q) (mu0 := slowInitialPair n) hscalar
  have hclip := operational_slowCanonical_clippedMoment_bundle_upto
    (m := m) (eps := eps) heps heps1 hK (Q := Q) (mu0 := slowInitialPair n)
    (V := slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
      (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K)
    hscalar hmeanPos (fun _ _ _ ↦ rfl)
  refine ⟨fun j hj ↦ (hstream j hj).1, fun j hj ↦ (hstream j hj).2.1, hmeanPos,
    fun j hj ↦ (hstream j hj).2.2,
    (Ttc.CVSlowCanonicalMomentBinders.slowCanonical_factorBundle m heps heps1).1,
    fun j hj ↦ (hclip j hj).2,
    (Ttc.CVSlowCanonicalMomentBinders.slowCanonical_factorBundle m heps heps1).2⟩

#print axioms slowSharp_momentBinders

/-! ## §6 — the tail extension, at the sharp pair

`Ttc.CVSlowCanonicalTailPhases`'s tail identifications
(`slowCanonical_streamAverage_tail_eq_one`, `slowCanonical_clippedFamily_tail_eq_one`) are
**bound-independent**: they take `slack` and `boundSq` as free parameters and never
constrain them.  The reason is structural — past the active range the schedule is
`Kernel.const _ (slowStationaryTail …)`, whose score coordinate sits in `interior K`, so
the indicator is `1` and the raw stream average is a.e. the constant `1`; that argument
never mentions `boundSq`.  So the only bound-specific input to the `∀ j` extension is the
prefix bundle, and the assembly below is the loose one with `slowSharp_momentBinders` in
place of `slowCanonical_momentBinders`. -/

/-- The frontier's `hWint`, `hW2int`, `hWEpos`, `hrawSecond` and `hphaseMoment` at **all**
`j`, at the sharp pair. -/
theorem slowSharp_momentBinders_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm (slowSharpSlack n m K) (slowSharpBoundSq n R))
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat)) :
    (∀ j, Integrable
      (fun omega ↦ streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, Integrable
      (fun omega ↦ (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, 0 < ∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, ∫ omega, (streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ j, ∫ omega,
        (slowClippedPositiveEmpiricalFamily m
          (correctedRuntimeSamples m eps) eps Q
          (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      (1 + 8 / (correctedRuntimeSamples m eps : Real)) *
        (∫ omega, slowClippedPositiveEmpiricalFamily m
            (correctedRuntimeSamples m eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) := by
  have hbase := slowSharp_momentBinders hn m heps heps1 hK hKc hball hfin hKR
    hop htau hmixError hexact hR2
  have hk : 0 < correctedRuntimeSamples m eps := correctedRuntimeSamples_pos m eps
  have htail : ∀ j, m < j →
      (fun omega ↦ streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
        =ᵐ[independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) :=
    fun j hj ↦ Ttc.CVSlowCanonicalTailPhases.slowCanonical_streamAverage_tail_eq_one
      hn m (correctedRuntimeSamples m eps) hk hq4 hK hball scoreScale
      (slowSharpSlack n m K) (slowSharpBoundSq n R) hQ
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) hj
  have htailSq : ∀ j, m < j →
      (fun omega ↦ (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
        =ᵐ[independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) := by
    intro j hj
    filter_upwards [htail j hj] with omega homega
    rw [homega]
    norm_num
  have hclip : ∀ j, m < j →
      (fun omega ↦ slowClippedPositiveEmpiricalFamily m
          (correctedRuntimeSamples m eps) eps Q (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega)
        =ᵐ[independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) :=
    fun j hj ↦ Ttc.CVSlowCanonicalTailPhases.slowCanonical_clippedFamily_tail_eq_one
      hn m heps heps1 hq4 hK hball scoreScale
      (slowSharpSlack n m K) (slowSharpBoundSq n R) hQ hj
  have hclipSq : ∀ j, m < j →
      (fun omega ↦ (slowClippedPositiveEmpiricalFamily m
          (correctedRuntimeSamples m eps) eps Q (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2)
        =ᵐ[independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) := by
    intro j hj
    filter_upwards [hclip j hj] with omega homega
    rw [homega]
    norm_num
  refine ⟨fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · rcases Nat.lt_or_ge m j with hj | hj
    · exact (integrable_const (1 : Real)).congr (htail j hj).symm
    · exact hbase.1 j hj
  · rcases Nat.lt_or_ge m j with hj | hj
    · exact (integrable_const (1 : Real)).congr (htailSq j hj).symm
    · exact hbase.2.1 j hj
  · rcases Nat.lt_or_ge m j with hj | hj
    · rw [integral_congr_ae (htail j hj)]
      simp
    · exact hbase.2.2.1 j hj
  · rcases Nat.lt_or_ge m j with hj | hj
    · rw [integral_congr_ae (htail j hj), integral_congr_ae (htailSq j hj)]
      simp
    · exact hbase.2.2.2.1 j hj
  · rcases Nat.lt_or_ge m j with hj | hj
    · rw [integral_congr_ae (hclip j hj), integral_congr_ae (hclipSq j hj)]
      have hk8 : (0 : Real) ≤ 8 / (correctedRuntimeSamples m eps : Real) := by positivity
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_pow]
      linarith
    · exact hbase.2.2.2.2.2.1 j hj

#print axioms slowSharp_momentBinders_all

/-! ### The five sharp binders as five separate theorems

`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` and its sharp analogue
`exists_slowOneRunCertificate_canonical_sharp` consume them as five separate arguments, so
each conjunct of `slowSharp_momentBinders_all` is projected out under its own name — the
sharp analogues of `Ttc.CVSlowCanonicalTailPhases.slowCanonical_hWint_all` …
`slowCanonical_hphaseMoment_all`. -/

/-- The frontier's `hWint` at **all** `j`, at the sharp pair. -/
theorem slowSharp_hWint_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm (slowSharpSlack n m K) (slowSharpBoundSq n R))
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat)) :
    ∀ j, Integrable
      (fun omega ↦ streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)) := by
  exact (slowSharp_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR
    hq4 scoreScale hQ hop htau hmixError hexact hR2).1

/-- The frontier's `hW2int` at **all** `j`, at the sharp pair. -/
theorem slowSharp_hW2int_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm (slowSharpSlack n m K) (slowSharpBoundSq n R))
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat)) :
    ∀ j, Integrable
      (fun omega ↦ (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)) := by
  exact (slowSharp_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR
    hq4 scoreScale hQ hop htau hmixError hexact hR2).2.1

/-- The frontier's `hWEpos` at **all** `j`, at the sharp pair. -/
theorem slowSharp_hWEpos_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm (slowSharpSlack n m K) (slowSharpBoundSq n R))
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat)) :
    ∀ j, 0 < ∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)) := by
  exact (slowSharp_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR
    hq4 scoreScale hQ hop htau hmixError hexact hR2).2.2.1

/-- The frontier's `hrawSecond` at **all** `j`, at the sharp pair. -/
theorem slowSharp_hrawSecond_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm (slowSharpSlack n m K) (slowSharpBoundSq n R))
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat)) :
    ∀ j, ∫ omega, (streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2 := by
  exact (slowSharp_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR
    hq4 scoreScale hQ hop htau hmixError hexact hR2).2.2.2.1

/-- The frontier's `hphaseMoment` at **all** `j`, at the sharp pair. -/
theorem slowSharp_hphaseMoment_all
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {q : Real} (hq4 : 4 ≤ q) (scoreScale : Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (correctedRuntimeSamples m eps)
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm (slowSharpSlack n m K) (slowSharpBoundSq n R))
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat)) :
    ∀ j, ∫ omega,
        (slowClippedPositiveEmpiricalFamily m
          (correctedRuntimeSamples m eps) eps Q
          (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      (1 + 8 / (correctedRuntimeSamples m eps : Real)) *
        (∫ omega, slowClippedPositiveEmpiricalFamily m
            (correctedRuntimeSamples m eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2 := by
  exact (slowSharp_momentBinders_all hn m heps heps1 hK hKc hball hfin hKR
    hq4 scoreScale hQ hop htau hmixError hexact hR2).2.2.2.2

#print axioms slowSharp_hWint_all
#print axioms slowSharp_hW2int_all
#print axioms slowSharp_hWEpos_all
#print axioms slowSharp_hrawSecond_all
#print axioms slowSharp_hphaseMoment_all

/-! ## §7 — THE DELIVERABLE: the frontier certificate at the sharp pair -/

/-- **The sharp twin of the slow canonical frontier one-run certificate.**

This is
`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`
with its two schedule binders replaced,

* `hslackDef : slack = Ttc.CVSharpUniformParameters.slowSharpSlack n m K` (the `/6` slack)
  in place of `slack = fun j ↦ phaseMomentSlackSeven m σ K C j / 2`,
* `hboundDef : boundSq = Ttc.CVSharpScoreTransport.slowSharpBoundSq n R` (the sharp
  transport bound) in place of `boundSq = phaseScoreTransportBoundSqSeven R σ`,

and with the same conclusion.  The comparison-constant binders `C`, `hC1`, `hC7` of the
original are *gone* — `C` is pinned to `2` inside `slowSharpSlack` — so on that count the
statement is strictly stronger.

The one added binder is `hR2`, and it is forced: see
`Ttc.CVSharpFactorSeven.terminal_sharpPhaseSup_sq_eq_seven`.  It is required only at the
terminal index and is free on the canonical chain (`R² ≤ N ≤ σ_{m-1}`).

The original is untouched and remains the loose record. -/
theorem exists_sourceReferenceTVOneRunCertificate_slowCanonical_sharp
    (hn : 21 ≤ n) (m k : Nat) (hm : 0 < m) (hk : 1 ≤ k)
    {q eps beta requested R meanTailFloor : Real} (hq4 : 4 ≤ q)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hbeta : 0 ≤ beta)
    (haccuracyBudget : eps + beta + eps * beta ≤ requested)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    (hmeanTailFloor : 0 < meanTailFloor)
    (hqRAware : q = rAwareGlobalRadiusQ n R (slowSourceInitialVariance n) meanTailFloor)
    (hrad : ∀ i, 1 ≤ q * Real.sqrt
      (slowSourceSigmaSq n (slowSourceInitialVariance n) i) * Real.sqrt n)
    (slack boundSq : Nat → Real) (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i) (scoreScale : Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    [IsProbabilityMeasure (slowInitialPair n)]
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (hVliteral : V = slowClippedPositiveEmpiricalFamily m k eps Q
      (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K)
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      (slowInitialPair n) V m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n q (slowSourceInitialVariance n) K i)
    {factor : Nat → Real}
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2) slack boundSq) j)
    (hslackDef : slack = slowSharpSlack n m K)
    (hboundDef : boundSq = slowSharpBoundSq n R)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))
    (hmeanTailBudget : ∀ i : Fin m, meanTailFloor ≤
      (scoreAwareMeanEta m k eps *
        (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
            ((i : Nat) + 1) /
          chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i : Nat))) / 2)
    (hWint : ∀ j, Integrable
      (fun omega ↦ streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hW2int : ∀ j, Integrable
      (fun omega ↦ (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hWEpos : ∀ j, 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hrawSecond : ∀ j, ∫ omega, (streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    (hfactor0 : ∀ j, 0 ≤ factor j)
    (hphaseMoment : ∀ j, ∫ omega, (V j omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      factor j * (∫ omega, V j omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    (hprefix : ∀ i, i ≤ m → prefixMomentRatio factor i ≤ 1 + eps ^ 2 / 6250)
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hinitChain : initialNormalizer =
      chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0)
    (htargetChain : volumeTarget =
      chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K m)
    (hbetaDef : (m : Real) / (2 * correctedAlpha m eps) +
      scoreAwareMeanGamma m k eps +
      ((m : Real) / (2 * correctedAlpha m eps)) * scoreAwareMeanGamma m k eps ≤ beta)
    {runtimeConstant : Real} (T L : Nat)
    (hsteps : ∀ i, i < m → slowCanonicalSteps slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (eps / 2) slack boundSq)
      (scoreAwareEta (m + 1) k (eps / 2) slack boundSq)
      (scoreAwareZeta (m + 1) k (eps / 2) slack boundSq) i 0 ≤ T)
    (hretries : ∀ i, i < m →
      scoreAwareRetries (m + 1) k (eps / 2) slack boundSq i ≤ L)
    (hscalar : (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R requested) :
    ∃ reference : Measure (Fin k → HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (@independentHeterogeneousRetainedPathLaw _ _ _ _ k
          (slowCanonicalCostedActiveSchedule (by omega : 1 ≤ n) (m + 1) k
            (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
            (lt_of_lt_of_le (by norm_num) hq4)
            (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
            slowReferenceWarm slack boundSq)
          (by
            letI : ∀ j, IsProbabilityMeasure
                (slowStationaryTail n q (slowSourceInitialVariance n) K j) := fun j ↦
              isProbabilityMeasure_slowStationaryTail (by omega : 1 ≤ n)
                (lt_of_lt_of_le (by norm_num) hq4)
                (by unfold slowSourceInitialVariance; positivity) hK hKc hball
                (fun r ↦ one_le_slow_radius (by omega : 1 ≤ n) hq4 (by rfl) r) j
            intro i; infer_instance)
          (slowInitialPair n) m)
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ gaussianScorePrefixReadout m m k
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K initialNormalizer
          (independentStoredScorePrefixCurrent m omega))
        runtimeConstant n R requested
        ((1 - requested) * volumeTarget) ((1 + requested) * volumeTarget) := by
  subst Q
  subst V
  let Qc := slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq
  let pathLaw := independentPathLaw k (stateScheduleFromSeed Qc) (slowInitialPair n)
  let Wbar := fun j ↦ streamAverage (k := k)
    (positiveScalarPhaseFamilyChainLength (Seed := State n)
      m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have halpha : 2 ≤ correctedAlpha m eps := by
    have ha := correctedAlpha_ge_hundred_thousand (m := m) heps heps1
    linarith
  have hW0 : ∀ j omega, 0 ≤ Wbar j omega := by
    intro j omega
    unfold Wbar streamAverage Ttc.CVEst.avgOf streamScore
    apply div_nonneg
    · exact Finset.sum_nonneg fun l _ ↦
        positiveScalarPhaseFamilyChainLength_nonneg j (omega l)
    · positivity
  have hstats : ∀ j,
      Measurable (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ∧
      (∀ omega, 0 ≤ slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ∧
      0 < ∫ omega, slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega ∂pathLaw ∧
      (∀ omega, slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega ≤
        2 * correctedAlpha m eps * ∫ z,
          slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j z ∂pathLaw) ∧
      (∀ omega, (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2 ≤
        2 * correctedAlpha m eps ^ 2 * ∫ z,
          (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j z) ^ 2 ∂pathLaw) := by
    intro j
    apply clippedStatistic_caps_of_rawSecond halpha
      (hW0 j)
      (measurable_streamAverage
        (measurable_positiveScalarPhaseFamilyChainLength hK j))
      (by simpa only [Wbar, pathLaw] using hWint j)
      (by simpa only [Wbar, pathLaw] using hW2int j)
      (by simpa only [Wbar, pathLaw] using hWEpos j)
      (by simpa only [Wbar, pathLaw] using hrawSecond j)
    intro omega
    simp only [slowClippedPositiveEmpiricalFamily, Wbar, pathLaw]
  have hV2 : ∀ j, Integrable
      (fun omega ↦ (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2) pathLaw := by
    intro j
    refine Integrable.mono' (by simpa only [Wbar, pathLaw] using hW2int j)
      ((hstats j).1.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply (sq_le_sq₀ ((hstats j).2.1 omega) (hW0 j omega)).2
    exact min_le_left _ _
  have htargetTV := tvLe_map_fst_tau_fullCoolLaw_slowTargetError hop
    hn1 (lt_of_lt_of_le (by norm_num) hq4)
    (by unfold slowSourceInitialVariance; positivity) hK hKc hball hfin
    (fun i hi ↦ hrad i) (fun i hi ↦
      (htau i hi).trans (slowLocalPairReference_succ_length_eq m n q
        (slowSourceInitialVariance n) K hi))
  -- the sharp per-phase first-moment budget, through the crux of §2
  have hmeanMix : ∀ i : Fin m,
      (hop.mixError (i : Nat)).toReal *
          sharpPhaseSup n R (slowSourceSigmaSq n (slowSourceInitialVariance n)) m
            (i : Nat) ≤
        (scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              (i : Nat))) / 2 := by
    intro i
    have hslackEq : slowSharpSlack n m K =
        fun j ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) j / 6 := rfl
    have hboundEq : slowSharpBoundSq n R =
        phaseScoreTransportBoundSqSharp n R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) := rfl
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1), hslackDef, hboundDef,
      hslackEq, hboundEq]
    simpa only [mul_comm] using
      scoreAwareMixError_succ_sixthSlack_sharpMean_le_half
        (n := n) (m := m) (k := k) (chainLength := m)
        (eps := eps) (R := R) (s0 := slowSourceInitialVariance n)
        (K := K) (C := fun _ ↦ 2) (i := (i : Nat))
        hn1 heps heps1 hs0 hball hfin
        (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) (hR2 i)
  have hmeanError : ∀ i : Fin m,
      (hop.mixError (i : Nat) + slowTargetError n q m (i : Nat)).toReal *
          sharpPhaseSup n R (slowSourceSigmaSq n (slowSourceInitialVariance n)) m
            (i : Nat) ≤
        scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i : Nat)) := by
    intro i
    have hc := mix_add_slowTargetError_rAware_sharpScaled_le hn1
      hs0 hmeanTailFloor i.isLt
      (hop.mixError_ne_top i) (hmeanMix i) (hmeanTailBudget i)
    rw [← hqRAware] at hc
    exact hc
  have haccuracy := relative_weighted_accuracy_four_fifths_sourceSharp_of_targetTV_bound
    (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K)
    (fun j omega ↦ streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
    hop heps heps1 hm (by omega : 0 < k) hbeta haccuracyBudget
    (slowSourceSigmaSq_pos hn1 hs0)
    hK hKc hball hfin
    (B := fun j ↦ sharpPhaseSup n R
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) m j)
    (fun j ↦ sharpPhaseSup_pos m j)
    (fun j x ↦ phaseScore_le_sharpPhaseSup hn1 hs0 (interior_subset.trans hKR) x)
    htargetTV (slowTargetError_ne_top n q m)
    hmeanError hWint hW2int hWEpos hrawSecond
    (by intro j omega; rfl)
    (fun j ↦ (hstats j).1) (fun j ↦ (hstats j).2.1)
    (fun j ↦ (hstats j).2.2.1) (fun j ↦ (hstats j).2.2.2.1)
    hV2 (fun j ↦ (hstats j).2.2.2.2)
    hfactor0 hphaseMoment hprefix
    (by
      intro j
      exact measurable_streamAverage
        (measurable_positiveScalarPhaseFamilyChainLength hK j))
    (Eexact := Set.univ) MeasurableSet.univ (by simp)
    (by intro omega _; rfl)
    initialNormalizer volumeTarget hinit hvolume hinitChain htargetChain hbetaDef
  have haccuracy' : 4 / 5 ≤
      (independentPathLaw k (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq)) (slowInitialPair n)).real
        {omega | gaussianScorePrefixReadout m m k
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K initialNormalizer
          (independentPathScorePrefixCurrent m omega) ∈
          Icc ((1 - requested) * volumeTarget) ((1 + requested) * volumeTarget)} := by
    simpa only [gaussianScorePrefixReadout_independentPathScorePrefixCurrent,
      Ttc.relErr] using haccuracy
  have herror : (k : ENNReal) * (∑ i ∈ range m,
      slowCanonicalRetainedError m k (eps / 2) slack boundSq i) ≤
      ENNReal.ofReal (1 / 40 : Real) :=
    aggregate_slowCanonicalRetainedError_le_globalRadius
      hn1 (by positivity) (by linarith) hslack hbound
  have hbudget : (k : ENNReal) * (∑ i ∈ range m,
      slowCanonicalRetainedCost n m k q (eps / 2) K slack boundSq i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R requested :=
    (aggregate_slowCanonicalRetainedCost_le_uniform hsteps hretries).trans hscalar
  exact exists_sourceReferenceTVOneRunCertificate_slowCanonical hn m k hk hq4
    (by positivity) (by linarith)
    hK hKc hball hfin slack boundSq hslack hbound scoreScale
    (gaussianScorePrefixReadout m m k
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K initialNormalizer)
    (measurable_gaussianScorePrefixReadout initialNormalizer)
    herror hbudget haccuracy'

#print axioms exists_sourceReferenceTVOneRunCertificate_slowCanonical_sharp

/-! ## §8 — the canonical instantiation at the sharp pair

The sharp analogue of `Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical`. -/

/-- The added binder `hR2` of the sharp frontier, discharged at the canonical phase count:
the terminal index of the canonical chain is the one place where `R² ≤ σ_i` holds, and
there it is exactly `R² ≤ N ≤ σ_{m-1}`. -/
theorem canonical_hR2_sharp (hn : 21 ≤ n) {R R2 : Real} (hR2 : R ^ 2 ≤ R2) :
    ∀ i : Fin (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2),
      Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 ≤ (i : Nat) + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat) := by
  intro i hterm
  have hi := i.isLt
  have hphases : Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 =
      slowSourcePhases n (max 1 R2) (slowSourceInitialVariance n) + 1 := rfl
  have hidx : (i : Nat) = slowSourcePhases n (max 1 R2)
      (slowSourceInitialVariance n) := by omega
  rw [hidx]
  exact (hR2.trans (le_max_right 1 R2)).trans
    (target_le_slowSourceSigmaSq_terminal (by omega : 1 ≤ n)
      (Ttc.CVSlowOneRunValid.canonicalN_pos R2)
      (slowSourceInitialVariance_pos (by omega : 1 ≤ n))
      (Ttc.CVSlowOneRunValid.slowSourceInitialVariance_le_canonicalN hn R2))

/-- Every literal retry count of the canonical sharp schedule is bounded by the sharp
retry cap, so the frontier's `hretries` binder is dischargeable at
`L := slowSharpRetriesCap (m + 1) k (eps / 2) R`. -/
theorem canonical_hretries_sharp (hn : 21 ≤ n) (m k : Nat) {eps R : Real}
    (heps : 0 < eps)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    ∀ i, scoreAwareRetries (m + 1) k (eps / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R) i ≤
      slowSharpRetriesCap (m + 1) k (eps / 2) R :=
  fun i ↦ scoreAwareRetries_slowSharp_le (by omega : 1 ≤ n) (by positivity)
    hK hball hfin i

/-- **The slow canonical one-run certificate at the sharp slack / transport pair.**

The sharp analogue of `Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical`, with
`slack := Ttc.CVSharpUniformParameters.slowSharpSlack n m K` and
`boundSq := Ttc.CVSharpScoreTransport.slowSharpBoundSq n R` in place of the loose pair.
Every schedule side condition is discharged by `slowSharpParameters_valid`, the added
terminal binder `hR2` by `canonical_hR2_sharp`, and the residual binder list is exactly the
loose theorem's: the five unguarded estimator-moment facts, the six cost-side binders, the
declared radius, and the definitional `Q`/`hQ`.  (`hretries` can be discharged at the sharp
cap by `canonical_hretries_sharp`.) -/
theorem exists_slowOneRunCertificate_canonical_sharp
    (hn : 21 ≤ n) {eps R R2 : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hR2 : R ^ 2 ≤ R2)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n)
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
      (correctedRuntimeSamples (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
      (q := slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (Ttc.CVSlowOneRunValid.canonical_hq0 hn R2 eps R)
      (Ttc.CVSlowOneRunValid.canonical_hs0 hn) K hK 0 slowReferenceWarm
      (slowSharpSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
      (slowSharpBoundSq n R))
    (hWint : ∀ j, Integrable
      (fun omega ↦ streamAverage
        (k := correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hW2int : ∀ j, Integrable
      (fun omega ↦ (streamAverage
        (k := correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hWEpos : ∀ j, 0 < ∫ omega, streamAverage
        (k := correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hrawSecond : ∀ j, ∫ omega, (streamAverage
        (k := correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage
        (k := correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    (hphaseMoment : ∀ j, ∫ omega,
          (slowClippedPositiveEmpiricalFamily
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (correctedRuntimeSamples
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      (1 + 8 / (correctedRuntimeSamples
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps : Real)) *
        (∫ omega, slowClippedPositiveEmpiricalFamily
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (correctedRuntimeSamples
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (correctedRuntimeSamples
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    {runtimeConstant : Real} (T L : Nat)
    (hsteps : ∀ i, i < Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 →
      slowCanonicalSteps slowReferenceWarm n
        (slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
        (slowSourceInitialVariance n) K
        (scoreAwareRetries (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
          (slowSharpSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
          (slowSharpBoundSq n R))
        (scoreAwareEta (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
          (slowSharpSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
          (slowSharpBoundSq n R))
        (scoreAwareZeta (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
          (slowSharpSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
          (slowSharpBoundSq n R))
        i 0 ≤ T)
    (hretries : ∀ i, i < Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 →
      scoreAwareRetries (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
        (correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
        (slowSharpSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
        (slowSharpBoundSq n R) i ≤ L)
    (hscalar : ((correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps : Nat) : ENNReal) *
        ((Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 : Nat) : ENNReal) *
          ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R
        (slowAccuracyRequested (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps)) :
    ∃ reference : Measure
        (Fin (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) →
          HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (@independentHeterogeneousRetainedPathLaw _ _ _ _
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (slowCanonicalCostedActiveSchedule (by omega : 1 ≤ n)
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
            (correctedRuntimeSamples
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
            (q := slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
              (correctedRuntimeSamples
                (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
            (eps := eps / 2) (s0 := slowSourceInitialVariance n)
            (Ttc.CVSlowOneRunValid.canonical_hq0 hn R2 eps R)
            (Ttc.CVSlowOneRunValid.canonical_hs0 hn) K hK 0 slowReferenceWarm
            (slowSharpSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
            (slowSharpBoundSq n R))
          (by
            letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
                (slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
                  (correctedRuntimeSamples
                    (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
                (slowSourceInitialVariance n) K j) := fun j ↦
              Ttc.CVSlowOneRunValid.canonical_isProbabilityMeasure_slowStationaryTail
                hn hK hKc hball j
            intro i; infer_instance)
          (slowInitialPair n) (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ gaussianScorePrefixReadout
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
          (chain (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0)
          (independentStoredScorePrefixCurrent
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) omega))
        runtimeConstant n R
        (slowAccuracyRequested (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps)
        ((1 - slowAccuracyRequested (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps) *
            (volume K).toReal)
        ((1 + slowAccuracyRequested (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (correctedRuntimeSamples
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps) *
            (volume K).toReal) := by
  have hn1 : 1 ≤ n := by omega
  haveI : IsProbabilityMeasure (slowInitialPair n) :=
    Ttc.CVSlowOneRunValid.canonical_isProbabilityMeasure_slowInitialPair hn
  haveI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (correctedRuntimeSamples
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) := fun j ↦
    Ttc.CVSlowOneRunValid.canonical_isProbabilityMeasure_slowStationaryTail
      hn hK hKc hball j
  obtain ⟨-, -, hbslack, hbbound, hbfloor, hbq4, hbqRAware, hbrad,
    hbslackDef, hbboundDef, hbmeanTail⟩ :=
    slowSharpParameters_valid (n := n) hn1
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (correctedRuntimeSamples
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
      (R := R) heps hK hball hfin
  obtain ⟨hop, htau, hmixError⟩ :=
    Ttc.CVSlowCanonicalHopAssembly.exists_slowCanonicalHop_literal hn
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (correctedRuntimeSamples
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
      (correctedRuntimeSamples_pos _ _) hbq4 heps heps1 hK hKc hball hfin (0 : Real)
      hbslack hbbound hQ
  obtain ⟨-, -, -, -, hfactor0, -, hprefix⟩ :=
    slowSharp_momentBinders hn (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      heps heps1 hK hKc hball hfin hKR hop htau hmixError
      (Ttc.CVSlowOneRunValid.canonical_hexact hn hR2 hK hKc hball hfin hKR)
      (canonical_hR2_sharp hn hR2)
  exact exists_sourceReferenceTVOneRunCertificate_slowCanonical_sharp
    hn (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
    (correctedRuntimeSamples (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
    (Ttc.CVSlowOneRunValid.slowCanonicalPhases_pos n R2)
    (correctedRuntimeSamples_pos _ _)
    hbq4 heps heps1 (scoreAwareAccuracyBeta_nonneg _ _ heps)
    (slowAccuracyBudget_le _ _ eps)
    hK hKc hball hfin hKR hbfloor hbqRAware hbrad
    (slowSharpSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
    (slowSharpBoundSq n R)
    hbslack hbbound (0 : Real) hQ _ rfl hop htau hmixError
    hbslackDef hbboundDef (canonical_hR2_sharp hn hR2) hbmeanTail
    hWint hW2int hWEpos hrawSecond hfactor0 hphaseMoment hprefix
    (chain (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0)
    (volume K).toReal
    (Ttc.CVSlowOneRunValid.canonical_chain_zero_nonneg hn R2 hball hfin)
    ENNReal.toReal_nonneg
    rfl (Ttc.CVSlowOneRunValid.slowCanonical_volumeTarget_eq n R2 K).symm (le_refl _)
    T L hsteps hretries hscalar

#print axioms canonical_hR2_sharp
#print axioms canonical_hretries_sharp
#print axioms exists_slowOneRunCertificate_canonical_sharp

end Ttc.CVSharpFrontier

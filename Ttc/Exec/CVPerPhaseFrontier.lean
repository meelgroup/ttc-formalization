/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVPerPhaseMomentBundle
import Ttc.Exec.CVSlowUniformShareBounds
import Ttc.Exec.CVSharpFrontier
import Ttc.Exec.CVSlowRefreshSteps

/-!
# The slow canonical frontier certificate at the **per-phase** slack / transport pair

`Ttc.CVPerPhaseMomentBundle.slowCanonical_momentBinders_perPhase` proves the frontier's
seven estimator-moment binders at the `n`-aware stream count
`Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples n m eps` — a factor `n` below
`correctedRuntimeSamples m eps` — but its `hscalar` slot lives at the *transport target*
`sharpTransportedFactor n m j = if j < m then 1 + 4/n else 3`, i.e. `T = 2 C - 1` at the
sharp exact-law factor `C = 1 + 2/n`.

The frontier's own schedule
(`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`)
pins `slack` to `phaseMomentSlackSeven … / 2`, whose transport target is the hard-coded
constant `7`; under that schedule the factor `n` is destroyed at transport whatever the
exact-law factor is.  This file removes that obstruction by re-declaring the schedule at
the `relativePhase` family at `C = 1 + 2/n`:

* `perPhaseSlack n cl K i = relativePhaseSlack cl σ K (fun _ ↦ 1 + 2/n) i = (2/n) · r²`
* `perPhaseBoundSqGen n E i = (E i)² · (1 + 2 (2 C i - 1)) = (E i)² · (3 + 8/n)`

so that `slack / (3 · boundSq) = 2 r² / ((54n + 144) · (E i)²)`, against the current
schedule's `r² / (18 · exp (R²/(2 σ_i))²)`.  The retry cap and deadline payload depend on
the share only *logarithmically*, so at the same exponent that costs an additive
`log₂((54n+144)/36)` (§7 proves this), while `k` drops by a factor `n`.

## The transport exponent is a parameter, not a constant

P1 (`Ttc.CVSharpScoreTransport`) sharpens the transport *exponent* from `exp(R²/(2 σ_i))`
to `exp(R²/(2 σ_i (n+1)))`.  `Ttc.CVGaussianSourceWeightedMoment.relativePhaseBoundSq`
hard-codes the former, so a family built on it verbatim would be P2-only.  Everything
below is therefore stated against an abstract per-phase exponential factor `E`, and two
instantiations are given:

* `perPhaseBoundSq n R` at `E i := exp (R²/(2 σ_i))` — **definitionally**
  `relativePhaseBoundSq R σ (perPhaseC n)` (`perPhaseBoundSq_eq_relativePhaseBoundSq`), so
  the standard-exponent route stays interoperable with the existing development;
* `perPhaseBoundSqSharp n R` at `E i := exp (R²/(2 σ_i (n+1)))` — the **combined P1 + P2**
  family, which is the one the capstone wants.

The abstraction costs exactly two extra hypotheses, both discharged at each instantiation:
`hE0 : ∀ i, 0 < E i` and the link `hSE : ∀ i, S i ^ 2 ≤ 3 * E i ^ 2` between the true
per-phase score sup `S` and the exponent, which at the sharp family is
`Ttc.CVSharpFactorSeven.sharpPhaseSup_sq_mul_le_three_mul` divided by `15`, and at the
standard family is `1 ≤ 3`.

## What the `relativePhase` family costs relative to the sharp pair

At the **standard** exponent nothing at all: `perPhaseBoundSq` is `exp(R²/(2 σ_i))²` times
a constant — the loose *shape* with `15` replaced by `3 + 8/n` — so the sup appearing in
the mean budget is again the square root of the transport bound, and the loose first-moment
statements apply directly.

At the **sharp** exponent the deficit `Ttc.CVSharpFrontier` documents reappears, and is
paid the same way: the frontier below calls `Ttc.CVSharpFrontier`'s already-proved
`B`-generic first-moment layer
(`relative_weighted_accuracy_four_fifths_sourceSharp_of_targetTV_bound`,
`operational_positiveStreamMean_upto_of_targetTV_bound`,
`mix_add_slowTargetError_rAware_sharpScaled_le`), with `B := S`.  Since that layer is
already generic in `B`, *both* instantiations run through it and the standard one is
obtained by taking `S := E := exp(R²/(2 σ_i))`.  **Answer to the brief's question: the
§3 `_bound` chain of `Ttc.CVSharpFrontier` is reusable verbatim, and no first-moment
transport argument is re-proved here.**

Exactly **one** new analytic lemma is required: §2's `perPhaseMixError_succ_mean_le_half`,
the first-moment crux at this slack/boundSq pair.  It is
`Ttc.CVScoreAwareHalfMeanBudget.scoreAwareMixError_succ_halfSlack_mean_le_half` line for
line, with two constants changed: the moment step gives `d · S² ≤ 2 r²` (via
`S² ≤ 3 E²` and `3 E² ≤ E²(3 + 8/n)`) in place of `d · (e² · 15) ≤ (7 - C) r² / 2`, and
the square step then reads `(S d)² ≤ 3 bs · 2 r² = 6 bs r² ≤ (3 b / 512) r²`, comfortably
inside the target `(η r / 2)² = (7/20) b r²`.

Nothing in the development is edited; every statement here is new.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.CVPerPhaseFrontier

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVAdaptive
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
open Ttc.CVScoreAwareHalfMeanBudget
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVGlobalLogarithmicRadius
open Ttc.CVSlowGlobalRadiusTailBudget Ttc.CVSlowSourceCostEnvelope
open Ttc.CVGaussianAdaptiveMixing Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVSlowCanonicalDeadlineCost
open Ttc.CVSlowCanonicalRuntimeComparison
open Ttc.CVSharpScoreTransport Ttc.CVSharpFactorSeven Ttc.CVSharpFrontier
open Ttc.CVPerPhaseSamples Ttc.CVPerPhaseMomentBundle
open scoped ENNReal Classical BigOperators

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## §0 — the parameter layer

`C := fun _ ↦ 1 + 2/n`, the sharp exact-law factor of
`Ttc.CVPerPhaseSamples.slowSource_phaseScore_sq_moment_sharp` on the interior phases.  Its
transport target is `2 C - 1 = 1 + 4/n`, which is exactly
`Ttc.CVPerPhaseMomentBundle.sharpTransportedFactor n m j` on the interior. -/

/-- The per-phase comparison factor: the sharp exact-law relative second-moment constant
`1 + 2/n`. -/
noncomputable def perPhaseC (n : Nat) : Nat → Real := fun _ ↦ 1 + 2 / (n : Real)

theorem one_lt_perPhaseC {n : Nat} (hn : 1 ≤ n) (i : Nat) : 1 < perPhaseC n i := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  unfold perPhaseC
  have : (0 : Real) < 2 / (n : Real) := by positivity
  linarith

/-- The transport target of `perPhaseC` is `2 C - 1 = 1 + 4/n` — the interior branch of
`Ttc.CVPerPhaseMomentBundle.sharpTransportedFactor`. -/
theorem two_perPhaseC_sub_one (n : Nat) (m j : Nat) (hj : j < m) :
    2 * perPhaseC n j - 1 = sharpTransportedFactor n m j := by
  unfold perPhaseC sharpTransportedFactor
  rw [if_pos hj]
  ring

/-- **The schedule's mixing slack at the per-phase family: `((2/n) · r²) / 6`.**

The divisor `6` is *not* cosmetic and is the first half of the P2 schedule repair.  The
transport bridge
`Ttc.CVSharpFactorSeven.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound`
consumes `(mixError + targetError) · B² (1 + 2T)` against `(T - C) · r²`, i.e. it must pay
for the radial tail *out of the same budget* as the mixing error.  What the schedule
supplies is `Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError_mul_boundSq_le_slack`,
which is exactly tight — `mix · boundSq ≤ slack`, no divisor — so at the undivided slack
`(2/n) · r²` the mixing error alone saturates the whole budget and the tail has nowhere to
go.  The `6` is the product of the two factors the transport needs:

* a factor `3`, because the sup that the transport scales by is the **true** score sup `S`,
  linked to the declared exponent only by `S² ≤ 3 E²`, so `S² (1 + 2T) ≤ 3 · boundSq` at an
  interior index;
* a factor `2`, the split between the mixing error and the radial tail.

This is the exact analogue of the loose route's `slowUniformSlack = phaseMomentSlackSeven/2`
and the sharp route's `slowSharpSlack = phaseMomentSlackSeven/6`; the per-phase family
needs the sharp route's divisor for the sharp route's reason. -/
noncomputable def perPhaseSlack (n chainLength : Nat) (K : Set (State n)) : Nat → Real :=
  fun i ↦ relativePhaseSlack chainLength
    (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (perPhaseC n) i / 6

theorem perPhaseSlack_pos {n chainLength : Nat} (hn : 1 ≤ n)
    {K : Set (State n)} (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : Nat) :
    0 < perPhaseSlack n chainLength K i := by
  unfold perPhaseSlack
  exact div_pos (relativePhaseSlack_pos
    (slowSourceSigmaSq_pos hn (slowSourceInitialVariance_pos hn)) hball hfin
    (one_lt_perPhaseC hn) i) (by norm_num)

/-- The literal closed form of the slack: `((2/n) · r²) / 6`. -/
theorem perPhaseSlack_eq {n chainLength : Nat} (K : Set (State n)) (i : Nat) :
    perPhaseSlack n chainLength K i =
      (2 / (n : Real)) *
        (chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
          chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i) ^ 2
        / 6 := by
  unfold perPhaseSlack relativePhaseSlack perPhaseC
  ring

/-- **The exponent-parametric transport bound.**  `E` is the per-phase exponential factor;
the multiplier `1 + 2 (2 C i - 1)` is the one
`Ttc.CVGaussianSourceWeightedMoment.relativePhaseBoundSq` uses, at `C = perPhaseC n`. -/
noncomputable def perPhaseBoundSqGen (n : Nat) (E : Nat → Real) (i : Nat) : Real :=
  E i ^ 2 * (1 + 2 * (2 * perPhaseC n i - 1))

theorem perPhaseBoundSqGen_pos {n : Nat} (hn : 1 ≤ n) {E : Nat → Real}
    (hE0 : ∀ i, 0 < E i) (i : Nat) : 0 < perPhaseBoundSqGen n E i := by
  have h := one_lt_perPhaseC hn i
  have hmul : (0 : Real) < 1 + 2 * (2 * perPhaseC n i - 1) := by nlinarith
  unfold perPhaseBoundSqGen
  exact mul_pos (pow_pos (hE0 i) 2) hmul

/-- The literal closed form of the transport bound: `(E i)² · (3 + 8/n)`. -/
theorem perPhaseBoundSqGen_eq (n : Nat) (E : Nat → Real) (i : Nat) :
    perPhaseBoundSqGen n E i = E i ^ 2 * (3 + 8 / (n : Real)) := by
  unfold perPhaseBoundSqGen perPhaseC
  ring

/-- The standard transport exponent, `exp (R²/(2 σ_i))`. -/
noncomputable def perPhaseExp (n : Nat) (R : Real) (i : Nat) : Real :=
  Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i))

/-- The **P1-sharp** transport exponent, `exp (R²/(2 σ_i (n+1)))`; compare
`Ttc.CVSharpScoreTransport.phaseScoreTransportBoundSqSharp`. -/
noncomputable def perPhaseExpSharp (n : Nat) (R : Real) (i : Nat) : Real :=
  Real.exp (R ^ 2 /
    (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i * ((n : Real) + 1)))

theorem perPhaseExp_pos {n : Nat} {R : Real} (i : Nat) : 0 < perPhaseExp n R i :=
  Real.exp_pos _

theorem perPhaseExpSharp_pos {n : Nat} {R : Real} (i : Nat) :
    0 < perPhaseExpSharp n R i := Real.exp_pos _

/-- The transport bound at the **standard** exponent. -/
noncomputable def perPhaseBoundSq (n : Nat) (R : Real) : Nat → Real :=
  perPhaseBoundSqGen n (perPhaseExp n R)

/-- The transport bound at the **P1-sharp** exponent — the combined P1 + P2 family. -/
noncomputable def perPhaseBoundSqSharp (n : Nat) (R : Real) : Nat → Real :=
  perPhaseBoundSqGen n (perPhaseExpSharp n R)

/-- **Interoperability with the existing development.**  The standard instantiation *is*
`Ttc.CVGaussianSourceWeightedMoment.relativePhaseBoundSq` at `C = perPhaseC n`. -/
theorem perPhaseBoundSq_eq_relativePhaseBoundSq (n : Nat) (R : Real) :
    perPhaseBoundSq n R =
      relativePhaseBoundSq R
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) (perPhaseC n) := by
  funext i
  rfl

theorem perPhaseBoundSq_pos {n : Nat} (hn : 1 ≤ n) {R : Real} (i : Nat) :
    0 < perPhaseBoundSq n R i :=
  perPhaseBoundSqGen_pos hn (fun j ↦ perPhaseExp_pos j) i

theorem perPhaseBoundSqSharp_pos {n : Nat} (hn : 1 ≤ n) {R : Real} (i : Nat) :
    0 < perPhaseBoundSqSharp n R i :=
  perPhaseBoundSqGen_pos hn (fun j ↦ perPhaseExpSharp_pos j) i

/-- The sharp exponent is never above the standard one. -/
theorem perPhaseExpSharp_le_perPhaseExp {n : Nat} (hn : 1 ≤ n) {R : Real} (i : Nat) :
    perPhaseExpSharp n R i ≤ perPhaseExp n R i := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigma : 0 < slowSourceSigmaSq n (slowSourceInitialVariance n) i :=
    slowSourceSigmaSq_pos hn hs0 i
  have hn0 : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
  unfold perPhaseExpSharp perPhaseExp
  refine Real.exp_le_exp.2 ?_
  refine div_le_div_of_nonneg_left (sq_nonneg R) (by positivity) ?_
  nlinarith [mul_nonneg hsigma.le hn0]

#print axioms one_lt_perPhaseC
#print axioms two_perPhaseC_sub_one
#print axioms perPhaseSlack_pos
#print axioms perPhaseSlack_eq
#print axioms perPhaseBoundSqGen_pos
#print axioms perPhaseBoundSqGen_eq
#print axioms perPhaseBoundSq_eq_relativePhaseBoundSq
#print axioms perPhaseBoundSq_pos
#print axioms perPhaseBoundSqSharp_pos
#print axioms perPhaseExpSharp_le_perPhaseExp

/-! ## §1 — the share floor at the per-phase pair

`slack i / (3 · boundSq i) = (((2/n) r²)/6) / (3 (E i)² (3 + 8/n)) = 2 r² / ((54n + 144) (E i)²)`
with `r ≥ 1`, so any uniform upper bound `B` on `E` gives the single floor

`min (blockShare m k eps) (2 / ((54n + 144) B²))`.

At the standard exponent `B = exp (R²/(2 s0)) = exp (8 n R²)`; at the sharp exponent
`B = exp (8 R²)`, dimension-free, exactly as in `Ttc.CVSharpUniformParameters`. -/

/-- One lower share valid simultaneously at every slow phase, at the per-phase
slack/boundSq pair with per-phase exponents bounded by `B`. -/
noncomputable def perPhaseShareFloorGen (n m k : Nat) (eps B : Real) : Real :=
  min (blockShare m k eps) (2 / ((54 * (n : Real) + 144) * B ^ 2))

theorem perPhaseShareFloorGen_pos {n m k : Nat} {eps B : Real} (hn : 1 ≤ n)
    (heps : 0 < eps) (hB : 0 < B) : 0 < perPhaseShareFloorGen n m k eps B := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  unfold perPhaseShareFloorGen
  refine lt_min (blockShare_pos heps) ?_
  have hden : (0 : Real) < (54 * (n : Real) + 144) * B ^ 2 := by positivity
  positivity

theorem perPhaseShareFloorGen_lt_one {n m k : Nat} {eps B : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) : perPhaseShareFloorGen n m k eps B < 1 :=
  (min_le_left _ _).trans_lt (blockShare_lt_one heps heps1)

theorem perPhaseShareFloorGen_nonneg {n m k : Nat} {eps B : Real} (hn : 1 ≤ n)
    (hB : 0 < B) : 0 ≤ perPhaseShareFloorGen n m k eps B := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  unfold perPhaseShareFloorGen blockShare Ttc.CVCorrected.correctedNu
  refine le_min (by positivity) ?_
  have hden : (0 : Real) < (54 * (n : Real) + 144) * B ^ 2 := by positivity
  positivity

/-- The arithmetic behind the floor: at `C = 1 + 2/N` the score-aware share's exponential
branch is `2 r² / ((9N + 24) e²)`, which `2 / ((9N + 24) B²)` is below whenever `r ≥ 1`,
`0 < e ≤ B`. -/
theorem perPhase_share_branch_arith {N r e B : Real}
    (hN : 0 < N) (hr : 1 ≤ r) (he0 : 0 < e) (heB : e ≤ B) :
    2 / ((54 * N + 144) * B ^ 2) ≤
      (2 / N * r ^ 2 / 6) / (3 * (e ^ 2 * (3 + 8 / N))) := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hB0 : (0 : Real) < B := lt_of_lt_of_le he0 heB
  have he2 : e ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ he0.le heB 2
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hc : (0 : Real) < 18 + 48 / N := by positivity
  have hDA : (0 : Real) < (54 * N + 144) * B ^ 2 := by positivity
  have hden : (0 : Real) < 3 * (e ^ 2 * (3 + 8 / N)) := by positivity
  rw [div_le_div_iff₀ hDA hden]
  have hkey : e ^ 2 * (18 + 48 / N) ≤ r ^ 2 * B ^ 2 * (18 + 48 / N) := by
    refine mul_le_mul_of_nonneg_right ?_ hc.le
    nlinarith [sq_nonneg B]
  calc
    2 * (3 * (e ^ 2 * (3 + 8 / N))) = e ^ 2 * (18 + 48 / N) := by
      field_simp
      ring
    _ ≤ r ^ 2 * B ^ 2 * (18 + 48 / N) := hkey
    _ = 2 / N * r ^ 2 / 6 * ((54 * N + 144) * B ^ 2) := by
      field_simp
      ring

/-- **The crux of §1.**  At the per-phase slack/boundSq pair the score-aware share of
every slow phase is bounded below by the single floor
`min (blockShare m k eps) (2 / ((54n + 144) B²))`. -/
theorem perPhaseShareFloorGen_le_scoreAwareShare
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {eps B : Real}
    {E : Nat → Real} (hE0 : ∀ i, 0 < E i) (hEB : ∀ i, E i ≤ B)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (i : Nat) :
    perPhaseShareFloorGen n m k eps B ≤
      scoreAwareShare m k eps (perPhaseSlack n chainLength K)
        (perPhaseBoundSqGen n E) i := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hratio : (1 : Real) ≤
      chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
        chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i :=
    one_le_chain_ratio_of_sigmaSq_le_succ hK hfin hball
      (slowSourceSigmaSq_pos hn hs0) (slowSourceSigmaSq_mono_succ hn hs0 i)
  unfold perPhaseShareFloorGen scoreAwareShare
  refine le_min (min_le_left _ _) ((min_le_right _ _).trans ?_)
  rw [perPhaseSlack_eq, perPhaseBoundSqGen_eq]
  exact perPhase_share_branch_arith hnR hratio (hE0 i) (hEB i)

/-! ### The two exponent bounds -/

/-- `exp (R²/(2 σ_i)) ≤ exp (8 n R²)` — the standard exponent's uniform bound. -/
theorem perPhaseExp_le {n : Nat} (hn : 1 ≤ n) {R : Real} (i : Nat) :
    perPhaseExp n R i ≤ Real.exp (8 * (n : Real) * R ^ 2) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hstart : slowSourceInitialVariance n ≤
      slowSourceSigmaSq n (slowSourceInitialVariance n) i :=
    slowSourceSigmaSq_mono_start hn hs0 i
  have hval : R ^ 2 / (2 * slowSourceInitialVariance n) = 8 * (n : Real) * R ^ 2 := by
    have hs0eq : slowSourceInitialVariance n = 1 / (16 * (n : Real)) := rfl
    rw [hs0eq]
    field_simp
    ring
  unfold perPhaseExp
  refine Real.exp_le_exp.2 ?_
  rw [← hval]
  exact div_le_div_of_nonneg_left (sq_nonneg R) (by positivity)
    (mul_le_mul_of_nonneg_left hstart (by norm_num))

/-- `exp (R²/(2 σ_i (n+1))) ≤ exp (8 R²)` — the sharp exponent's uniform bound, with **no**
`n`.  This is `Ttc.CVSharpUniformParameters.slowSharpFloor6_le_scoreAwareShare`'s exponent
computation: `σ_i ≥ s0 = 1/(16 n)` gives `2 σ_i (n+1) ≥ (n+1)/(8n) ≥ 1/8`. -/
theorem perPhaseExpSharp_le {n : Nat} (hn : 1 ≤ n) {R : Real} (i : Nat) :
    perPhaseExpSharp n R i ≤ Real.exp (8 * R ^ 2) := by
  have hnR : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hn0 : (0 : Real) < (n : Real) := by linarith
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigma : 0 < slowSourceSigmaSq n (slowSourceInitialVariance n) i :=
    slowSourceSigmaSq_pos hn hs0 i
  have hstart : slowSourceInitialVariance n ≤
      slowSourceSigmaSq n (slowSourceInitialVariance n) i :=
    slowSourceSigmaSq_mono_start hn hs0 i
  have hlow : (1 : Real) / 8 ≤
      2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i * ((n : Real) + 1) := by
    have hs0eq : slowSourceInitialVariance n = 1 / (16 * (n : Real)) := rfl
    have h1 : 2 * slowSourceInitialVariance n * ((n : Real) + 1) ≤
        2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i * ((n : Real) + 1) := by
      nlinarith
    refine le_trans ?_ h1
    rw [hs0eq, div_le_iff₀ (by norm_num : (0 : Real) < 8)]
    rw [show 2 * (1 / (16 * (n : Real))) * ((n : Real) + 1) * 8
        = ((n : Real) + 1) / (n : Real) by field_simp; ring]
    rw [le_div_iff₀ hn0]
    linarith
  unfold perPhaseExpSharp
  refine Real.exp_le_exp.2 ?_
  rw [div_le_iff₀ (by linarith :
    (0 : Real) < 2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i *
      ((n : Real) + 1))]
  nlinarith [sq_nonneg R]

/-- The floor at the **standard** exponent. -/
noncomputable def perPhaseShareFloor (n m k : Nat) (eps R : Real) : Real :=
  perPhaseShareFloorGen n m k eps (Real.exp (8 * (n : Real) * R ^ 2))

/-- The floor at the **P1-sharp** exponent — dimension-free in the exponent. -/
noncomputable def perPhaseShareFloorSharp (n m k : Nat) (eps R : Real) : Real :=
  perPhaseShareFloorGen n m k eps (Real.exp (8 * R ^ 2))

theorem perPhaseShareFloor_le_scoreAwareShare
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {eps R : Real}
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (i : Nat) :
    perPhaseShareFloor n m k eps R ≤
      scoreAwareShare m k eps (perPhaseSlack n chainLength K)
        (perPhaseBoundSq n R) i :=
  perPhaseShareFloorGen_le_scoreAwareShare hn (fun j ↦ perPhaseExp_pos j)
    (fun j ↦ perPhaseExp_le hn j) hK hball hfin i

theorem perPhaseShareFloorSharp_le_scoreAwareShare
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {eps R : Real}
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (i : Nat) :
    perPhaseShareFloorSharp n m k eps R ≤
      scoreAwareShare m k eps (perPhaseSlack n chainLength K)
        (perPhaseBoundSqSharp n R) i :=
  perPhaseShareFloorGen_le_scoreAwareShare hn (fun j ↦ perPhaseExpSharp_pos j)
    (fun j ↦ perPhaseExpSharp_le hn j) hK hball hfin i

#print axioms perPhase_share_branch_arith
#print axioms perPhaseShareFloorGen_pos
#print axioms perPhaseShareFloorGen_lt_one
#print axioms perPhaseShareFloorGen_nonneg
#print axioms perPhaseShareFloorGen_le_scoreAwareShare
#print axioms perPhaseExp_le
#print axioms perPhaseExpSharp_le
#print axioms perPhaseShareFloor_le_scoreAwareShare
#print axioms perPhaseShareFloorSharp_le_scoreAwareShare

/-! ## §2 — the crux: the first-moment budget at the per-phase pair

The per-phase analogue of
`Ttc.CVScoreAwareHalfMeanBudget.scoreAwareMixError_succ_halfSlack_mean_le_half`, stated at
the **true per-phase score sup** `S`, which is what the `B`-generic first-moment layer of
`Ttc.CVSharpFrontier` consumes.  The only link between `S` and the transport bound that
the proof uses is `S i ^ 2 ≤ 3 * E i ^ 2`. -/

/-- The arithmetic of the per-phase first-moment crux, isolated from the schedule. -/
theorem perPhase_mean_crux_arith {N s e d bs b r eta : Real}
    (hN : 1 ≤ N) (hs0 : 0 ≤ s) (he0 : 0 < e) (hd0 : 0 ≤ d) (hb0 : 0 < b)
    (hr0 : 0 < r) (hdbs : d ≤ 3 * bs) (hbs : bs ≤ b / 1024)
    (hse : s ^ 2 ≤ 3 * e ^ 2)
    (hmom : d * (e ^ 2 * (3 + 8 / N)) ≤ 2 / N * r ^ 2)
    (hetaSq : eta ^ 2 = 7 / 5 * b) (heta0 : 0 ≤ eta) :
    s * d ≤ eta * r / 2 := by
  have hN0 : (0 : Real) < N := by linarith
  have h8N : (0 : Real) ≤ 8 / N := by positivity
  have hde : (0 : Real) ≤ d * e ^ 2 := by positivity
  have hr2 : (0 : Real) ≤ r ^ 2 := sq_nonneg r
  have h2N : 2 / N ≤ 2 := by
    rw [div_le_iff₀ hN0]
    linarith
  have h1 : 3 * (d * e ^ 2) ≤ d * (e ^ 2 * (3 + 8 / N)) := by
    nlinarith [mul_nonneg hde h8N]
  have h2 : 2 / N * r ^ 2 ≤ 2 * r ^ 2 := mul_le_mul_of_nonneg_right h2N hr2
  have hds : d * s ^ 2 ≤ 2 * r ^ 2 := by
    have hstep : d * s ^ 2 ≤ d * (3 * e ^ 2) := mul_le_mul_of_nonneg_left hse hd0
    nlinarith
  have hsq : (s * d) ^ 2 ≤ 6 * bs * r ^ 2 := by
    have hstep : d * (d * s ^ 2) ≤ d * (2 * r ^ 2) :=
      mul_le_mul_of_nonneg_left hds hd0
    have hstep2 : d * (2 * r ^ 2) ≤ (3 * bs) * (2 * r ^ 2) :=
      mul_le_mul_of_nonneg_right hdbs (by positivity)
    calc
      (s * d) ^ 2 = d * (d * s ^ 2) := by ring
      _ ≤ d * (2 * r ^ 2) := hstep
      _ ≤ (3 * bs) * (2 * r ^ 2) := hstep2
      _ = 6 * bs * r ^ 2 := by ring
  have hsq' : (s * d) ^ 2 ≤ (eta * r / 2) ^ 2 := by
    have hstep : 6 * bs * r ^ 2 ≤ 6 * (b / 1024) * r ^ 2 := by
      have h6 : (6 : Real) * bs ≤ 6 * (b / 1024) := by linarith
      exact mul_le_mul_of_nonneg_right h6 hr2
    have htarget : 6 * (b / 1024) * r ^ 2 ≤ (eta * r / 2) ^ 2 := by
      have hexp : (eta * r / 2) ^ 2 = 7 / 20 * b * r ^ 2 := by
        rw [show (eta * r / 2) ^ 2 = eta ^ 2 * r ^ 2 / 4 by ring, hetaSq]
        ring
      rw [hexp]
      nlinarith [mul_nonneg hb0.le hr2]
    linarith
  have hsd0 : (0 : Real) ≤ s * d := mul_nonneg hs0 hd0
  have htarget0 : (0 : Real) ≤ eta * r / 2 := by positivity
  nlinarith [hsq', hsd0, htarget0]

/-- **The per-phase first-moment crux.**  At the `relativePhase` slack/transport pair at
`C = 1 + 2/n` and any transport exponent `E` dominating the true score sup `S` in the sense
`S² ≤ 3 E²`, the mixing error scaled by `S` fits half of the geometric-mean first-moment
allowance. -/
theorem perPhaseMixError_succ_mean_le_half
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {eps : Real}
    {E S : Nat → Real} (hE0 : ∀ i, 0 < E i) (hS0 : ∀ i, 0 ≤ S i)
    (hSE : ∀ i, S i ^ 2 ≤ 3 * E i ^ 2)
    {K : Set (State n)} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (i : Nat) :
    S i * (scoreAwareMixError (m + 1) k (eps / 2)
          (perPhaseSlack n chainLength K) (perPhaseBoundSqGen n E) i).toReal ≤
      (scoreAwareMeanEta m k eps *
        (chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
          chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i)) / 2 := by
  have hnR : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigma := slowSourceSigmaSq_pos hn hs0
  have hslackPos : ∀ j, 0 < perPhaseSlack n chainLength K j :=
    fun j ↦ perPhaseSlack_pos hn hball hfin j
  have hboundPos : ∀ j, 0 < perPhaseBoundSqGen n E j :=
    fun j ↦ perPhaseBoundSqGen_pos hn hE0 j
  have hshare := scoreAwareMixError_toReal_le_three_share
    (m := m + 1) (k := k) (eps := eps / 2)
    (slack := perPhaseSlack n chainLength K) (boundSq := perPhaseBoundSqGen n E)
    (by positivity) (by linarith) hslackPos hboundPos i
  have hdbs : (scoreAwareMixError (m + 1) k (eps / 2)
      (perPhaseSlack n chainLength K) (perPhaseBoundSqGen n E) i).toReal ≤
      3 * blockShare (m + 1) k (eps / 2) := by
    refine hshare.trans ?_
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  have hmoment := scoreAwareMixError_mul_boundSq_le_slack
    (m := m + 1) (k := k) (eps := eps / 2)
    (slack := perPhaseSlack n chainLength K) (boundSq := perPhaseBoundSqGen n E)
    (by positivity) (by linarith) hslackPos hboundPos i
  rw [perPhaseBoundSqGen_eq, perPhaseSlack_eq] at hmoment
  -- the `/6` of `perPhaseSlack` is headroom the *first*-moment crux does not need:
  -- it only wants the undivided `(2/n) r²`, so the divided slack is a fortiori inside it.
  have hslackNonneg : (0 : Real) ≤ 2 / (n : Real) *
      (chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
        chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i) ^ 2 := by
    positivity
  have hmoment' : (scoreAwareMixError (m + 1) k (eps / 2)
        (perPhaseSlack n chainLength K) (perPhaseBoundSqGen n E) i).toReal *
        (E i ^ 2 * (3 + 8 / (n : Real))) ≤
      2 / (n : Real) *
        (chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
          chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i) ^ 2 := by
    linarith
  have hbs : blockShare (m + 1) k (eps / 2) ≤ blockShare m k eps / 1024 := by
    rw [blockShare_half_accuracy (m := m + 1) (k := k) heps]
    gcongr
    exact blockShare_succ_le (m := m) (k := k) heps
  have hb0 : 0 < blockShare m k eps := blockShare_pos heps
  have hetaSq : (scoreAwareMeanEta m k eps) ^ 2 = 7 / 5 * blockShare m k eps := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    exact mul_nonneg (by norm_num) hb0.le
  exact perPhase_mean_crux_arith (N := (n : Real)) hnR (hS0 i) (hE0 i)
    ENNReal.toReal_nonneg hb0
    (div_pos (chain_pos hsigma hball hfin _) (chain_pos hsigma hball hfin _))
    hdbs hbs (hSE i) hmoment' hetaSq (scoreAwareMeanEta_nonneg m k eps)

#print axioms perPhase_mean_crux_arith
#print axioms perPhaseMixError_succ_mean_le_half

/-! ## §3 — the retry cap and the deadline cap at the per-phase floor

The per-phase analogue of `Ttc.CVSharpUniformParameters` Steps 4–6.  Everything here is
share-generic once `perPhaseShareFloorGen_le_scoreAwareShare` exists, so both exponent
instantiations are obtained by supplying their own `B`. -/

/-- Uniform logarithmic retry cap induced by the per-phase share floor. -/
noncomputable def perPhaseRetriesCapGen (n m k : Nat) (eps B : Real) : Nat :=
  16 * explicitDyadicTailIndex (perPhaseShareFloorGen n m k eps B)

/-- Every literal retry count at the per-phase pair is bounded by the single retry cap. -/
theorem scoreAwareRetries_perPhase_le
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {eps B : Real} (heps : 0 < eps)
    {E : Nat → Real} (hE0 : ∀ i, 0 < E i) (hEB : ∀ i, E i ≤ B)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (i : Nat) :
    scoreAwareRetries m k eps (perPhaseSlack n chainLength K)
        (perPhaseBoundSqGen n E) i ≤
      perPhaseRetriesCapGen n m k eps B := by
  have hB0 : 0 < B := lt_of_lt_of_le (hE0 0) (hEB 0)
  have hfloor0 := perPhaseShareFloorGen_pos (m := m) (k := k) (B := B) hn heps hB0
  have hshare0 := scoreAwareShare_pos (m := m) (k := k) heps
    (perPhaseSlack_pos (chainLength := chainLength) hn hball hfin)
    (perPhaseBoundSqGen_pos hn hE0) i
  have hfloor := perPhaseShareFloorGen_le_scoreAwareShare
    (m := m) (k := k) (chainLength := chainLength) (eps := eps) (B := B)
    hn hE0 hEB hK hball hfin i
  have hinv :
      1 / scoreAwareShare m k eps (perPhaseSlack n chainLength K)
          (perPhaseBoundSqGen n E) i ≤
        1 / perPhaseShareFloorGen n m k eps B :=
    one_div_le_one_div_of_le hfloor0 hfloor
  have hlog := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
    (by positivity) (by positivity)).2 hinv
  unfold scoreAwareRetries perPhaseRetriesCapGen explicitDyadicTailIndex
  exact Nat.mul_le_mul_left 16 (Nat.ceil_mono hlog)

/-- The logarithmic payload obtained by replacing every phase share by the per-phase
global lower bound. -/
noncomputable def perPhaseDeadlinePayload (n m k : Nat) (eps B : Real) : Real :=
  Real.log ((2 * Real.exp 1) / perPhaseShareFloorGen n m k eps B) +
    2 * Real.log (32 / perPhaseShareFloorGen n m k eps B)

/-- One literal natural deadline cap for every active phase, at the per-phase pair. -/
noncomputable def perPhaseDeadlineCap (n m k : Nat) (eps B N : Real) : Nat :=
  ⌈4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      perPhaseDeadlinePayload n m k eps B / Real.log 2 ^ 2 + 1⌉₊ + 1

/-- Replacing the actual score-aware share by the per-phase floor enlarges the exact
mixing logarithm. -/
theorem perPhaseDeadlinePayload_le
    {n m k : Nat} {eps B share : Real}
    (hf0 : 0 < perPhaseShareFloorGen n m k eps B)
    (hfs : perPhaseShareFloorGen n m k eps B ≤ share) :
    Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) ≤
      perPhaseDeadlinePayload n m k eps B := by
  have hs0 : 0 < share := hf0.trans_le hfs
  have hfirst : (2 * Real.exp 1) / share ≤
      (2 * Real.exp 1) / perPhaseShareFloorGen n m k eps B :=
    div_le_div_of_nonneg_left (by positivity) hf0 hfs
  have hsecond : 32 / share ≤ 32 / perPhaseShareFloorGen n m k eps B :=
    div_le_div_of_nonneg_left (by norm_num) hf0 hfs
  unfold perPhaseDeadlinePayload
  gcongr

theorem perPhaseDeadlinePayload_nonneg
    {n m k : Nat} {eps B : Real}
    (hf0 : 0 < perPhaseShareFloorGen n m k eps B)
    (hf1 : perPhaseShareFloorGen n m k eps B < 1) :
    0 ≤ perPhaseDeadlinePayload n m k eps B := by
  have hfirst : 1 ≤ (2 * Real.exp 1) / perPhaseShareFloorGen n m k eps B := by
    rw [le_div_iff₀ hf0]
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hsecond : 1 ≤ 32 / perPhaseShareFloorGen n m k eps B := by
    rw [le_div_iff₀ hf0]
    nlinarith
  unfold perPhaseDeadlinePayload
  exact add_nonneg (Real.log_nonneg hfirst)
    (mul_nonneg (by norm_num) (Real.log_nonneg hsecond))

/-- Every active slow source phase has the advertised explicit deadline, at the per-phase
slack/boundSq pair. -/
theorem slowScoreAwareSteps_perPhase_active_le
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {N eps B s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N)
    (hs0eq : s0 = slowSourceInitialVariance n)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {E : Nat → Real} (hE0 : ∀ i, 0 < E i) (hEB : ∀ i, E i ≤ B)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : Metric.ball 0 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hm : m = slowSourcePhases n N s0)
    {i : Nat} (hi : i + 1 < m) :
    slowScoreAwareSteps n m k (slowGlobalRadiusQ n m k eps) eps
        (perPhaseSlack n chainLength K) (perPhaseBoundSqGen n E) i 0 ≤
      perPhaseDeadlineCap n m k eps B N := by
  subst hs0eq
  have hB0 : 0 < B := lt_of_lt_of_le (hE0 0) (hEB 0)
  let share := scoreAwareShare m k eps (perPhaseSlack n chainLength K)
    (perPhaseBoundSqGen n E) i
  let floor := perPhaseShareFloorGen n m k eps B
  let A := slowRadiusTailCalls m k eps
  let sigma := slowSourceSigmaSq n (slowSourceInitialVariance n) i
  have hf0 : 0 < floor := perPhaseShareFloorGen_pos (m := m) (k := k) hn heps hB0
  have hf1 : floor < 1 := perPhaseShareFloorGen_lt_one heps heps1
  have hs0' : 0 < share := scoreAwareShare_pos (m := m) (k := k) heps
    (perPhaseSlack_pos (chainLength := chainLength) hn hball hfin)
    (perPhaseBoundSqGen_pos hn hE0) i
  have hfs : floor ≤ share := perPhaseShareFloorGen_le_scoreAwareShare
    (m := m) (k := k) (chainLength := chainLength) (eps := eps) (B := B)
    hn hE0 hEB hK hball hfin i
  have hs1 : share < 1 := scoreAwareShare_lt_one heps heps1 i
  have hA : 1 ≤ A := one_le_slowRadiusTailCalls m k eps
  have hsigma0 : 0 < sigma := slowSourceSigmaSq_pos hn hs0 i
  have hsigmaN : sigma ≤ 2 * N := by
    dsimp only [sigma]
    apply slowSourceSigmaSq_active_le_two_target hn hN hs0 hsN
    simpa only [hm] using hi
  have hcoef : sigma * (n : Real) /
      radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma ^ 2 ≤
      slowCanonicalGeometryEnvelope n m k eps N := by
    have hraw := sigmaSq_mul_n_div_globalDelta_sq_hot_le
      (N := 2 * N) hn hA hsigma0 hsigmaN
    change sigma * (n : Real) / globalLogarithmicDelta n A sigma ^ 2 ≤
      slowCanonicalGeometryEnvelope n m k eps N
    convert hraw using 1
    dsimp only [A, slowCanonicalGeometryEnvelope]
    ring
  have hpayload :
      Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) ≤
        perPhaseDeadlinePayload n m k eps B :=
    perPhaseDeadlinePayload_le hf0 hfs
  have hpayload0 : 0 ≤
      Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) := by
    have hfirst : 1 ≤ (2 * Real.exp 1) / share := by
      rw [le_div_iff₀ hs0']
      have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith
    have hsecond : 1 ≤ 32 / share := by
      rw [le_div_iff₀ hs0']
      nlinarith
    exact add_nonneg (Real.log_nonneg hfirst)
      (mul_nonneg (by norm_num) (Real.log_nonneg hsecond))
  have hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N :=
    (mul_nonneg (by
      have hlog : 0 ≤ Real.log (20 * A) := Real.log_nonneg (by nlinarith)
      positivity) (by positivity))
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  unfold adjustableSpeedyDeadlineExpression
  have heta : (scoreAwareEta m k eps (perPhaseSlack n chainLength K)
      (perPhaseBoundSqGen n E) i).toReal = share := by
    simp [scoreAwareEta, share, hs0'.le]
  have hzeta : (scoreAwareZeta m k eps (perPhaseSlack n chainLength K)
      (perPhaseBoundSqGen n E) i).toReal = share / 32 := by
    rw [scoreAwareZeta, ENNReal.toReal_ofReal]
    exact div_nonneg hs0'.le (by norm_num)
  have hwarm : slowReferenceWarm.toReal = 2 * Real.exp 1 := by
    rw [slowReferenceWarm, ENNReal.toReal_ofReal]
    positivity
  rw [ENNReal.toReal_div, hwarm, heta, hzeta]
  rw [show 1 / (share / 32) = 32 / share by field_simp]
  change 4 * 640 ^ 2 * sigma * (n : Real) *
      (Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share)) /
        (radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma * Real.log 2) ^ 2 + 1 ≤ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdelta := radiusQDelta_pos hn
    (lt_of_lt_of_le (by norm_num) (four_le_slowGlobalRadiusQ hn m k eps)) hsigma0
  have hden : 0 < radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma ^ 2 *
      Real.log 2 ^ 2 := mul_pos (sq_pos_of_pos hdelta) (sq_pos_of_pos hlog2)
  rw [show (radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma * Real.log 2) ^ 2 =
      radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma ^ 2 * Real.log 2 ^ 2 by ring]
  calc
    4 * 640 ^ 2 * sigma * (n : Real) *
          (Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share)) /
          (radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma ^ 2 * Real.log 2 ^ 2) + 1 =
        4 * 640 ^ 2 *
          (sigma * (n : Real) / radiusQDelta n
            (slowGlobalRadiusQ n m k eps) sigma ^ 2) *
          (Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share)) /
          Real.log 2 ^ 2 + 1 := by field_simp
    _ ≤ 4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
          perPhaseDeadlinePayload n m k eps B / Real.log 2 ^ 2 + 1 := by
      gcongr

/-! ### Real envelopes for the two literal natural caps -/

/-- Real upper envelope for the literal natural per-phase retry cap. -/
noncomputable def perPhaseRetryRealEnvelope (n m k : Nat) (eps B : Real) : Real :=
  16 * (Real.logb 2 (1 / perPhaseShareFloorGen n m k eps B) + 1)

/-- Real upper envelope for the literal natural per-phase mixing deadline. -/
noncomputable def perPhaseDeadlineRealEnvelope (n m k : Nat) (eps B N : Real) : Real :=
  4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      perPhaseDeadlinePayload n m k eps B / Real.log 2 ^ 2 + 3

theorem perPhaseRetriesCap_cast_le_realEnvelope
    {n m k : Nat} {eps B : Real} (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hB0 : 0 < B) :
    (perPhaseRetriesCapGen n m k eps B : Real) ≤
      perPhaseRetryRealEnvelope n m k eps B := by
  have hf0 := perPhaseShareFloorGen_pos (m := m) (k := k) (B := B) hn heps hB0
  have hf1 := perPhaseShareFloorGen_lt_one (n := n) (m := m) (k := k) (B := B) heps heps1
  have hindex := Ttc.CVAdaptive.explicitDyadicTailIndex_lt_logb_add_one hf0 hf1
  unfold perPhaseRetriesCapGen perPhaseRetryRealEnvelope
  push_cast
  linarith

theorem perPhaseDeadlineCap_cast_le_realEnvelope
    {n m k : Nat} {eps B N : Real}
    (hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N)
    (hpayload0 : 0 ≤ perPhaseDeadlinePayload n m k eps B) :
    (perPhaseDeadlineCap n m k eps B N : Real) ≤
      perPhaseDeadlineRealEnvelope n m k eps B N := by
  let x := 4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      perPhaseDeadlinePayload n m k eps B / Real.log 2 ^ 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hceil := (Nat.ceil_lt_add_one hx0).le
  unfold perPhaseDeadlineCap perPhaseDeadlineRealEnvelope
  dsimp only [x] at hceil
  push_cast
  linarith

#print axioms scoreAwareRetries_perPhase_le
#print axioms perPhaseDeadlinePayload_le
#print axioms perPhaseDeadlinePayload_nonneg
#print axioms slowScoreAwareSteps_perPhase_active_le
#print axioms perPhaseRetriesCap_cast_le_realEnvelope
#print axioms perPhaseDeadlineCap_cast_le_realEnvelope

/-! ## §3b — the frontier's `hsteps` binder, at the **actual** deadline and the `n`-aware
radius

**The second, independent gap, and it survives the §4/§4b slack repair.**  §3's
`slowScoreAwareSteps_perPhase_active_le` is stated at
`slowScoreAwareSteps n m k (slowGlobalRadiusQ n m k eps) …` — the *fixed-reference*
warmness and the *global* radius — while §6's `hsteps` binder is at
`slowCanonicalSteps slowReferenceWarm n (perPhaseQ …) …` — the *compounding actual* warm
budget and the run's own `n`-aware radius.  Wrong deadline function and wrong radius; §3
alone cannot discharge it.

This section closes the gap exactly as `Ttc.CVSharpSlowSteps` closed it for the sharp
family: three logarithmic payloads, one uniform envelope, and
`Ttc.CVSlowActualDeadline.slowCanonicalSteps_le_ceil_of_log_le`.  Every payload depends on
the schedule only through §1's share floor `perPhaseShareFloorGen` and §3's retry cap
`perPhaseRetriesCapGen`, both already proved, so nothing analytic is re-derived. -/

/-- The retry cap the frontier's literal per-phase retry family obeys.  This is exactly the
`L` of `scoreAwareRetries_perPhase_le` at the schedule's `(m + 1, eps/2)`. -/
noncomputable def perPhaseRetriesCapAt (n m k : Nat) (epsP B : Real) : Nat :=
  perPhaseRetriesCapGen n (m + 1) k (epsP / 2) B

/-- The logarithmic envelope of `1 / eta i`, at the per-phase share floor. -/
noncomputable def perPhaseElog (n m k : Nat) (epsP B : Real) : Real :=
  Real.log (1 / perPhaseShareFloorGen n (m + 1) k (epsP / 2) B)

/-- The logarithmic envelope of `1 / zeta i`.  The extra `32` is the explicit `share / 32`
in `scoreAwareZeta`. -/
noncomputable def perPhaseZlog (n m k : Nat) (epsP B : Real) : Real :=
  Real.log (32 / perPhaseShareFloorGen n (m + 1) k (epsP / 2) B)

theorem perPhaseElog_nonneg {n : Nat} (hn : 1 ≤ n) (m k : Nat) {epsP B : Real}
    (hepsP : 0 < epsP) (hepsP1 : epsP ≤ 1) (hB : 0 < B) :
    0 ≤ perPhaseElog n m k epsP B := by
  have hf0 : 0 < perPhaseShareFloorGen n (m + 1) k (epsP / 2) B :=
    perPhaseShareFloorGen_pos hn (by linarith) hB
  have hf1 : perPhaseShareFloorGen n (m + 1) k (epsP / 2) B < 1 :=
    perPhaseShareFloorGen_lt_one (by linarith) (by linarith)
  unfold perPhaseElog
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hf0]
  linarith

theorem perPhaseZlog_nonneg {n : Nat} (hn : 1 ≤ n) (m k : Nat) {epsP B : Real}
    (hepsP : 0 < epsP) (hepsP1 : epsP ≤ 1) (hB : 0 < B) :
    0 ≤ perPhaseZlog n m k epsP B := by
  have hf0 : 0 < perPhaseShareFloorGen n (m + 1) k (epsP / 2) B :=
    perPhaseShareFloorGen_pos hn (by linarith) hB
  have hf1 : perPhaseShareFloorGen n (m + 1) k (epsP / 2) B < 1 :=
    perPhaseShareFloorGen_lt_one (by linarith) (by linarith)
  unfold perPhaseZlog
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hf0]
  linarith

/-- The product route's warm payload, padded to the terminal phase `m`. -/
noncomputable def perPhaseWlogProduct (n m k : Nat) (q epsP B : Real) : Real :=
  Real.log (2 * Real.exp 1) +
    (m : Real) *
      Real.log ((Ttc.CVSlowWarmBudgetBound.slowWarmFactorEnvelope n q
        (slowSourceInitialVariance n) m (perPhaseRetriesCapAt n m k epsP B)).toReal)

/-- The refresh route's warm payload at the uniform index `m`. -/
noncomputable def perPhaseWlogRefresh (n m k : Nat) (q epsP B : Real) : Real :=
  Ttc.CVRefreshWarmRoute.slowRefreshWlog n q (slowSourceInitialVariance n) m
    (perPhaseRetriesCapAt n m k epsP B) m

/-- **The warm payload.**  Both routes are available simultaneously, so the deadline may
consume whichever is smaller. -/
noncomputable def perPhaseWlog (n m k : Nat) (q epsP B : Real) : Real :=
  min (perPhaseWlogProduct n m k q epsP B) (perPhaseWlogRefresh n m k q epsP B)

theorem perPhaseWlogProduct_nonneg (n m k : Nat) (q epsP B : Real) :
    0 ≤ perPhaseWlogProduct n m k q epsP B := by
  unfold perPhaseWlogProduct
  have h1 : 0 ≤ Real.log (2 * Real.exp 1) := by
    refine Real.log_nonneg ?_
    have he : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have h2 : 0 ≤ Real.log ((Ttc.CVSlowWarmBudgetBound.slowWarmFactorEnvelope n q
      (slowSourceInitialVariance n) m (perPhaseRetriesCapAt n m k epsP B)).toReal) :=
    Real.log_nonneg
      (Ttc.CVSlowWarmBudgetBound.one_le_slowWarmFactorEnvelope_toReal _ _ _ _ _)
  have := mul_nonneg (Nat.cast_nonneg (α := Real) m) h2
  linarith

theorem perPhaseWlogRefresh_nonneg {n : Nat} (hn : 1 ≤ n) (m k : Nat)
    (q epsP B : Real) : 0 ≤ perPhaseWlogRefresh n m k q epsP B := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have h1 : 0 ≤ (m : Real) *
      Real.log (Ttc.CVRefreshWarmRoute.slowAcceptedCap
        (perPhaseRetriesCapAt n m k epsP B)).toReal :=
    mul_nonneg (Nat.cast_nonneg m)
      (Real.log_nonneg (Ttc.CVRefreshWarmRoute.one_le_slowAcceptedCap_toReal _))
  have h2 : 0 ≤ Real.log ((m : Real) + 1) := by
    refine Real.log_nonneg ?_
    have : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
    linarith
  have h3 : 0 ≤ Real.log (2 * Real.exp 1) := by
    refine Real.log_nonneg ?_
    have he : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have h4 : 0 ≤ 1 / (32 * slowSourceInitialVariance n) := by positivity
  have h5 : 0 ≤ (n : Real) *
      Real.log (4 * max 1 (Ttc.CVRefreshWarmRoute.slowRefreshRadius n q
        (slowSourceInitialVariance n) m)) := by
    refine mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg ?_)
    have : (1 : Real) ≤ max 1 (Ttc.CVRefreshWarmRoute.slowRefreshRadius n q
        (slowSourceInitialVariance n) m) := le_max_left _ _
    linarith
  unfold perPhaseWlogRefresh Ttc.CVRefreshWarmRoute.slowRefreshWlog
  linarith

theorem perPhaseWlog_nonneg {n : Nat} (hn : 1 ≤ n) (m k : Nat) (q epsP B : Real) :
    0 ≤ perPhaseWlog n m k q epsP B :=
  le_min (perPhaseWlogProduct_nonneg n m k q epsP B)
    (perPhaseWlogRefresh_nonneg hn m k q epsP B)

/-- The per-phase deadline value the actual slow canonical schedule selects. -/
noncomputable def perPhaseStepsBound
    (n m k : Nat) (q epsP B : Real) (i : Nat) : Real :=
  Ttc.CVSlowActualDeadline.slowActualDeadlineExpression n
    (radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i))
    (slowSourceSigmaSq n (slowSourceInitialVariance n) i)
    (perPhaseWlog n m k q epsP B) (perPhaseElog n m k epsP B)
    (perPhaseZlog n m k epsP B)

/-- One real envelope valid at every phase: the variance at the terminal phase `m`
(largest) and the mixing radius at the initial variance (smallest). -/
noncomputable def perPhaseStepsEnvelope
    (n m k : Nat) (q epsP B : Real) : Real :=
  Ttc.CVSlowActualDeadline.slowActualDeadlineExpression n
    (radiusQDelta n q (slowSourceInitialVariance n))
    (slowSourceSigmaSq n (slowSourceInitialVariance n) m)
    (perPhaseWlog n m k q epsP B) (perPhaseElog n m k epsP B)
    (perPhaseZlog n m k epsP B)

theorem perPhasePayload_nonneg {n : Nat} (hn : 1 ≤ n) {m k : Nat} {q epsP B : Real}
    (hepsP : 0 < epsP) (hepsP1 : epsP ≤ 1) (hB : 0 < B) :
    0 ≤ (Real.log 2 + perPhaseWlog n m k q epsP B + perPhaseElog n m k epsP B) +
      2 * perPhaseZlog n m k epsP B := by
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 := perPhaseWlog_nonneg hn m k q epsP B
  have h2 := perPhaseElog_nonneg hn m k hepsP hepsP1 hB
  have h3 := perPhaseZlog_nonneg hn m k hepsP hepsP1 hB
  linarith

theorem perPhaseStepsBound_le_envelope {n : Nat} (hn : 1 ≤ n) {m k : Nat}
    {q epsP B : Real} (hq : 0 < q) (hepsP : 0 < epsP) (hepsP1 : epsP ≤ 1) (hB : 0 < B)
    {i : Nat} (hi : i ≤ m) :
    perPhaseStepsBound n m k q epsP B i ≤ perPhaseStepsEnvelope n m k q epsP B := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigle : slowSourceSigmaSq n (slowSourceInitialVariance n) i ≤
      slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    slowSourceSigmaSq_le_terminal hn hs0 hi
  have hd0 : 0 < radiusQDelta n q (slowSourceInitialVariance n) :=
    radiusQDelta_pos hn hq hs0
  have hdle : radiusQDelta n q (slowSourceInitialVariance n) ≤
      radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i) :=
    Ttc.CVSlowActualSteps.radiusQDelta_mono_variance n q
      (slowSourceSigmaSq_mono_start hn hs0 i)
  have hP := perPhasePayload_nonneg (n := n) hn (m := m) (k := k) (q := q) (B := B)
    hepsP hepsP1 hB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsigi : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) i :=
    (slowSourceSigmaSq_pos hn hs0 i).le
  unfold perPhaseStepsBound perPhaseStepsEnvelope
    Ttc.CVSlowActualDeadline.slowActualDeadlineExpression
  gcongr
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hsigi.trans hsigle))
    (Nat.cast_nonneg n)) hP

theorem perPhaseStepsEnvelope_nonneg {n : Nat} (hn : 1 ≤ n) {m k : Nat}
    {q epsP B : Real} (hepsP : 0 < epsP) (hepsP1 : epsP ≤ 1) (hB : 0 < B) :
    0 ≤ perPhaseStepsEnvelope n m k q epsP B := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigm : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    (slowSourceSigmaSq_pos hn hs0 m).le
  have hP := perPhasePayload_nonneg (n := n) hn (m := m) (k := k) (q := q) (B := B)
    hepsP hepsP1 hB
  unfold perPhaseStepsEnvelope Ttc.CVSlowActualDeadline.slowActualDeadlineExpression
  have hnum : 0 ≤ 4 * 640 ^ 2 * slowSourceSigmaSq n (slowSourceInitialVariance n) m *
      (n : Real) *
      ((Real.log 2 + perPhaseWlog n m k q epsP B + perPhaseElog n m k epsP B) +
        2 * perPhaseZlog n m k epsP B) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsigm) (Nat.cast_nonneg n)) hP
  have hden : 0 ≤ (radiusQDelta n q (slowSourceInitialVariance n) * Real.log 2) ^ 2 :=
    sq_nonneg _
  have := div_nonneg hnum hden
  linarith

theorem cast_perPhaseStepsCap_le (n m k : Nat) (q epsP B : Real)
    (hE : 0 ≤ perPhaseStepsEnvelope n m k q epsP B) :
    ((⌈perPhaseStepsEnvelope n m k q epsP B⌉₊ + 1 : Nat) : Real) ≤
      perPhaseStepsEnvelope n m k q epsP B + 2 :=
  Ttc.CVSpeedyDeadlineMono.cast_ceil_add_one_le _ hE

/-- **The deliverable of §3b.**  Every active phase of the *actual* slow canonical schedule
at the per-phase slack / transport pair — the one whose warmness argument is the
compounding `slowWarmBudget` and whose shares are the literal score-aware families §6's
`hQ` forces — obeys one explicit natural deadline cap.  This is the `T` of §6's `hsteps`.

The conclusion is byte-identical to `Ttc.CVSharpSlowSteps.slowCanonicalSteps_sharp_le`'s
with the two substitutions `slowSharpSlack ↦ perPhaseSlack`,
`slowSharpBoundSq ↦ perPhaseBoundSqGen` and the envelope. -/
theorem slowCanonicalSteps_perPhase_le
    {n : Nat} (hn : 1 ≤ n) (m k : Nat) {q epsP B : Real} (hq : 0 < q)
    (hepsP : 0 < epsP) (hepsP1 : epsP ≤ 1)
    {E : Nat → Real} (hE0 : ∀ j, 0 < E j) (hEB : ∀ j, E j ≤ B)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m) :
    slowCanonicalSteps slowReferenceWarm n q (slowSourceInitialVariance n) K
        (scoreAwareRetries (m + 1) k (epsP / 2)
          (perPhaseSlack n m K) (perPhaseBoundSqGen n E))
        (scoreAwareEta (m + 1) k (epsP / 2)
          (perPhaseSlack n m K) (perPhaseBoundSqGen n E))
        (scoreAwareZeta (m + 1) k (epsP / 2)
          (perPhaseSlack n m K) (perPhaseBoundSqGen n E))
        i 0 ≤
      ⌈perPhaseStepsEnvelope n m k q epsP B⌉₊ + 1 := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have heps2 : (0 : Real) < epsP / 2 := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le (hE0 0) (hEB 0)
  have hshare0 : 0 < scoreAwareShare (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i :=
    scoreAwareShare_pos heps2 (perPhaseSlack_pos hn hball hfin)
      (perPhaseBoundSqGen_pos hn hE0) i
  have hfloor0 : 0 < perPhaseShareFloorGen n (m + 1) k (epsP / 2) B :=
    perPhaseShareFloorGen_pos hn heps2 hB0
  have hfloor : perPhaseShareFloorGen n (m + 1) k (epsP / 2) B ≤
      scoreAwareShare (m + 1) k (epsP / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i :=
    perPhaseShareFloorGen_le_scoreAwareShare (chainLength := m) hn hE0 hEB hK hball hfin i
  have hW := Ttc.CVSlowWarmBudgetBound.slowWarmBudget_ne_top (q := q) hn hs0 hK
    (scoreAwareRetries (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E)) i
  have hW1 := Ttc.CVSlowWarmBudgetBound.one_le_slowWarmBudget
    (scoreAwareRetries (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E))
    n q (slowSourceInitialVariance n) K i
  have hW0 : 0 < (slowWarmBudget slowReferenceWarm n q (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E)) i).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hW1)) hW
  have hL : ∀ j, scoreAwareRetries (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) j ≤
      perPhaseRetriesCapAt n m k epsP B :=
    fun j ↦ scoreAwareRetries_perPhase_le (chainLength := m) hn heps2 hE0 hEB hK
      hball hfin j
  have hWprod : Real.log (slowWarmBudget slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E)) i).toReal ≤
      perPhaseWlogProduct n m k q epsP B := by
    refine (Ttc.CVSlowWarmBudgetBound.log_slowWarmBudget_toReal_le hn hq.le hs0 hK hL
      hi.le).trans ?_
    unfold perPhaseWlogProduct
    have hlogE : 0 ≤ Real.log ((Ttc.CVSlowWarmBudgetBound.slowWarmFactorEnvelope n q
        (slowSourceInitialVariance n) m (perPhaseRetriesCapAt n m k epsP B)).toReal) :=
      Real.log_nonneg
        (Ttc.CVSlowWarmBudgetBound.one_le_slowWarmFactorEnvelope_toReal _ _ _ _ _)
    have him : (i : Real) ≤ (m : Real) := by exact_mod_cast hi.le
    nlinarith
  have hWref : Real.log (slowWarmBudget slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E)) i).toReal ≤
      perPhaseWlogRefresh n m k q epsP B :=
    Ttc.CVRefreshWarmRoute.log_slowWarmBudget_toReal_le_refresh_uniform hn hq.le hs0 hK
      hL hi.le
  have hWlog : Real.log (slowWarmBudget slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E)) i).toReal ≤
      perPhaseWlog n m k q epsP B := le_min hWprod hWref
  have heta : (scoreAwareEta (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i).toReal =
      scoreAwareShare (m + 1) k (epsP / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i := by
    rw [scoreAwareEta, ENNReal.toReal_ofReal hshare0.le]
  have hzeta : (scoreAwareZeta (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i).toReal =
      scoreAwareShare (m + 1) k (epsP / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i / 32 := by
    rw [scoreAwareZeta, ENNReal.toReal_ofReal (by positivity)]
  have heta0 : scoreAwareEta (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i ≠ 0 := by
    rw [scoreAwareEta, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hshare0
  have hetaTop : scoreAwareEta (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i ≠ ⊤ := by
    rw [scoreAwareEta]; exact ENNReal.ofReal_ne_top
  have hElog : Real.log (1 / (scoreAwareEta (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i).toReal) ≤
      perPhaseElog n m k epsP B := by
    rw [heta]
    unfold perPhaseElog
    exact Real.log_le_log (by positivity) (one_div_le_one_div_of_le hfloor0 hfloor)
  have hZlog : Real.log (1 / (scoreAwareZeta (m + 1) k (epsP / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i).toReal) ≤
      perPhaseZlog n m k epsP B := by
    rw [hzeta, show 1 / (scoreAwareShare (m + 1) k (epsP / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i / 32) =
        32 / scoreAwareShare (m + 1) k (epsP / 2)
          (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i by field_simp]
    unfold perPhaseZlog
    exact Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_left (by norm_num) hfloor0 hfloor)
  exact Ttc.CVSlowActualDeadline.slowCanonicalSteps_le_ceil_of_log_le hn hq hs0 hW hW0
    heta0 hetaTop hWlog hElog hZlog
    (perPhaseStepsBound_le_envelope hn hq hepsP hepsP1 hB0 hi.le)

#print axioms perPhaseElog_nonneg
#print axioms perPhaseZlog_nonneg
#print axioms perPhaseWlog_nonneg
#print axioms perPhaseStepsBound_le_envelope
#print axioms perPhaseStepsEnvelope_nonneg
#print axioms cast_perPhaseStepsCap_le
#print axioms slowCanonicalSteps_perPhase_le

/-! ## §4 — the per-phase first-moment error, mixing plus radial tail

The generic form of `Ttc.CVSharpFrontier.mix_add_slowTargetError_rAware_sharpScaled_le`:
the radial-tail half never touched `boundSq`, and any per-phase sup below the loose one is
covered by `Ttc.CVRAwareGlobalRadius.slowTargetError_rAware_scaled_le` verbatim. -/

theorem mix_add_slowTargetError_rAware_genScaled_le
    {n m i : Nat} (hn : 1 ≤ n) {R s0 b target sup : Real} {mix : ENNReal}
    (hs0 : 0 < s0) (hb : 0 < b) (hi : i < m) (hmixTop : mix ≠ ⊤)
    (hsupLoose : sup ≤ Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)))
    (hmix : mix.toReal * sup ≤ target / 2)
    (hbudget : b ≤ target / 2) :
    (mix + slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal * sup ≤ target := by
  have htail0 : 0 ≤ (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal :=
    ENNReal.toReal_nonneg
  have htailLoose : (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
      Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) ≤ target / 2 :=
    slowTargetError_rAware_scaled_le hn hs0 hb hi hbudget
  have htail : (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal * sup ≤
      target / 2 := by
    refine le_trans ?_ htailLoose
    exact mul_le_mul_of_nonneg_left hsupLoose htail0
  rw [ENNReal.toReal_add hmixTop (slowTargetError_ne_top n _ m i)]
  calc
    (mix.toReal + (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal) * sup =
      mix.toReal * sup +
        (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal * sup := by ring
    _ ≤ target / 2 + target / 2 := add_le_add hmix htail
    _ = target := by ring

#print axioms mix_add_slowTargetError_rAware_genScaled_le

/-! ## §4b — the `n`-aware mean-tail floor, and the transport slack it buys

**The second half of the P2 schedule repair.**  §4's divisor `6` on `perPhaseSlack` opens
an `O(1/n)` allowance for the radial tail, but the tail budget the development ships,
`Ttc.CVSlowCanonicalUniformParameters.slowUniformMeanTailFloor n m k eps R
  = min (scoreAwareMeanEta m k eps / 4) (1 / (6 · exp (R²/(2 s₀))))`,
caps the tail's contribution at a **constant**.  Concretely
`Ttc.CVRAwareGlobalRadius.slowTargetError_rAware_scaled_le` at `target := b` gives

`targetError.toReal · exp (R²/(2 σ_i)) ≤ b`,

so with `S i ≤ exp (R²/(2 σ_i)) ≤ exp (R²/(2 s₀))` the tail contributes at most

`b · exp (R²/(2 s₀)) · (1 + 2 T) = (1 + 2 T)/6 = (3 + 8/n)/6`

at the uniform floor — an absolute constant, `0.5635…` at `n = 21`, against an available
budget of `(2/n) · r² ≥ 2/21 = 0.0952…`.  **That is the exact constant, re-derived rather
than quoted, and it is off by a factor `≈ 5.9` at `n = 21` and by `Θ(n)` thereafter — the
tail budget is *not* already `n`-aware, and Part B is therefore genuinely required.**

The repair divides the exponential branch by `n`.  The cost is a larger truncation radius,
and it is negligible: the radius is
`globalLogarithmicRadiusQ n A = √(16 + 4 log (20 A)/n)` at `A = exp(R²/(2 s₀))/(20 b)`, so
dividing `b` by `n` multiplies `A` by `n` and adds exactly `4 log n / n` to `q²` — the
trade the whole repair rests on. -/

/-- **The `n`-aware joint tail floor.**  `Ttc.CVRAwareGlobalRadius.slowCanonicalJointTailFloor`
at the canonical initial variance, with its exponential branch divided by a further `n`.
The mean branch is untouched: it is what `perPhaseMeanTailFloor_le_meanBudget` consumes,
and it was never the obstruction. -/
noncomputable def perPhaseMeanTailFloor (n m k : Nat) (eps R : Real) : Real :=
  min (scoreAwareMeanEta m k eps / 4)
    (1 / (6 * (n : Real) *
      Real.exp (R ^ 2 / (2 * slowSourceInitialVariance n))))

/-- The run-global truncation radius selected by the `n`-aware floor. -/
noncomputable def perPhaseQ (n m k : Nat) (eps R : Real) : Real :=
  rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
    (perPhaseMeanTailFloor n m k eps R)

theorem perPhaseMeanTailFloor_pos {n m k : Nat} (hn : 1 ≤ n) {eps R : Real}
    (heps : 0 < eps) : 0 < perPhaseMeanTailFloor n m k eps R := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  unfold perPhaseMeanTailFloor scoreAwareMeanEta
  refine lt_min (div_pos (Real.sqrt_pos.2
    (mul_pos (by norm_num) (blockShare_pos heps))) (by norm_num)) ?_
  positivity

/-- The frontier's `hqRAware`, definitionally. -/
theorem perPhaseQ_rAware (n m k : Nat) (eps R : Real) :
    perPhaseQ n m k eps R =
      rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
        (perPhaseMeanTailFloor n m k eps R) := rfl

theorem four_le_perPhaseQ {n : Nat} (hn : 1 ≤ n) (m k : Nat) (eps R : Real) :
    4 ≤ perPhaseQ n m k eps R :=
  four_le_globalLogarithmicRadiusQ hn (one_le_rAwareRadiusCalls _ _ _)

theorem perPhaseQ_rad {n : Nat} (hn : 1 ≤ n) (m k : Nat) (eps R : Real) (i : Nat) :
    1 ≤ perPhaseQ n m k eps R *
      Real.sqrt (slowSourceSigmaSq n (slowSourceInitialVariance n) i) *
      Real.sqrt n :=
  one_le_slow_radius hn (four_le_perPhaseQ hn m k eps R) (by rfl) i

/-- The mean branch survives the division: the `n`-aware floor is still inside half of the
first-moment transport budget, exactly as
`Ttc.CVSlowCanonicalUniformParameters.slowUniformMeanTailFloor_le_meanBudget`. -/
theorem perPhaseMeanTailFloor_le_meanBudget {n m k : Nat} (hn : 1 ≤ n)
    {eps R : Real} (heps : 0 < eps)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (i : Nat) :
    perPhaseMeanTailFloor n m k eps R ≤
      (scoreAwareMeanEta m k eps *
        (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
          chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i)) / 2 := by
  have hs0 := slowSourceInitialVariance_pos hn
  have hratio : (1 : Real) ≤
      chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
        chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i :=
    one_le_chain_ratio_of_sigmaSq_le_succ hK hfin hball
      (slowSourceSigmaSq_pos hn hs0) (slowSourceSigmaSq_mono_succ hn hs0 i)
  have heta0 := scoreAwareMeanEta_nonneg m k eps
  calc perPhaseMeanTailFloor n m k eps R ≤ scoreAwareMeanEta m k eps / 4 :=
        min_le_left _ _
    _ ≤ _ := by nlinarith

#print axioms perPhaseMeanTailFloor_pos
#print axioms four_le_perPhaseQ
#print axioms perPhaseQ_rad
#print axioms perPhaseMeanTailFloor_le_meanBudget

/-- **The crux of the repair: the transport slack of
`Ttc.CVSharpFactorSeven.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound`
holds at the per-phase pair, at the sharp exact-law factor `C = sharpExactFactor n m (i+1)`
and its transport target `T = 2C - 1 = sharpTransportedFactor n m (i+1)`.**

Both halves are paid, and neither is slack:

* **mixing.** `scoreAwareMixError_mul_boundSq_le_slack` is exactly tight at
  `mix · E² (3 + 8/n) ≤ ((2/n) r²)/6`, i.e. `mix · E² (3n + 8) ≤ r²/3`.  With
  `S² ≤ 3 E²` this gives `mix · S² (1 + 2T) ≤ (1 + 2T) r²/(3n + 8)`, which at an
  interior index is `r²/n` — **exactly half** of the interior budget `(2/n) r²`.
* **radial tail.** `slowTargetError_rAware_scaled_le` gives `tail · exp(R²/(2 σ_i)) ≤ b`,
  and `S i ≤ exp(R²/(2 σ_i)) ≤ exp(R²/(2 s₀))` turns that into
  `tail · S² (1 + 2T) ≤ (1 + 2T)/(6n)` at the `n`-aware floor.  At an interior index that
  is `(3n + 8)/(6n²) ≤ 1/n ≤ r²/n`, the other half.

The terminal index (`i + 1 = m`, where `C = 2`, `T = 3`, `1 + 2T = 7` and the budget is the
much larger `1 · r²`) is comfortable at both halves for `n ≥ 21`. -/
theorem perPhase_mix_add_tail_transport_le
    {n : Nat} (hn : 21 ≤ n) {m k : Nat} {eps R : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {E S : Nat → Real} (hE0 : ∀ j, 0 < E j) (hS0 : ∀ j, 0 ≤ S j)
    (hSE : ∀ j, S j ^ 2 ≤ 3 * E j ^ 2)
    (hSloose : ∀ j, S j ≤ Real.exp (R ^ 2 /
      (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) j)))
    {i : Nat} (hi : i < m) :
    (scoreAwareMixError (m + 1) k (eps / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i +
      slowTargetError n (perPhaseQ n m k eps R) m i).toReal *
        (S i ^ 2 * (1 + 2 * sharpTransportedFactor n m (i + 1))) ≤
      (sharpExactFactor n m (i + 1) - 1) *
        (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
          chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (21 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hnpos : (0 : Real) < (n : Real) := by linarith
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have hsigma := slowSourceSigmaSq_pos hn1 hs0
  have hr1 : (1 : Real) ≤
      chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
        chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i :=
    one_le_chain_ratio_of_sigmaSq_le_succ hK hfin hball hsigma
      (slowSourceSigmaSq_mono_succ hn1 hs0 i)
  set r := chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
    chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i with hrdef
  have hrr : (1 : Real) ≤ r ^ 2 := by nlinarith
  have hb0 : 0 < perPhaseMeanTailFloor n m k eps R :=
    perPhaseMeanTailFloor_pos (m := m) (k := k) hn1 heps
  -- the mixing half, with the `1/n` cleared
  have hmix := scoreAwareMixError_mul_boundSq_le_slack
    (m := m + 1) (k := k) (eps := eps / 2)
    (slack := perPhaseSlack n m K) (boundSq := perPhaseBoundSqGen n E)
    (by positivity) (by linarith) (fun j ↦ perPhaseSlack_pos hn1 hball hfin j)
    (fun j ↦ perPhaseBoundSqGen_pos hn1 hE0 j) i
  rw [perPhaseBoundSqGen_eq, perPhaseSlack_eq] at hmix
  set mixR := (scoreAwareMixError (m + 1) k (eps / 2)
    (perPhaseSlack n m K) (perPhaseBoundSqGen n E) i).toReal with hmixRdef
  have hmix0 : (0 : Real) ≤ mixR := ENNReal.toReal_nonneg
  have hF1 : mixR * E i ^ 2 * (3 * (n : Real) + 8) ≤ r ^ 2 / 3 := by
    have hkey := mul_le_mul_of_nonneg_left hmix hnpos.le
    have hL : (n : Real) * (mixR * (E i ^ 2 * (3 + 8 / (n : Real)))) =
        mixR * E i ^ 2 * (3 * (n : Real) + 8) := by
      field_simp
      try ring
    have hRr : (n : Real) * (2 / (n : Real) * r ^ 2 / 6) = r ^ 2 / 3 := by
      field_simp
      try ring
    rw [hL, hRr] at hkey
    exact hkey
  -- the radial-tail half
  have htail := slowTargetError_rAware_scaled_le (n := n) (m := m) (i := i)
    (R := R) (s0 := slowSourceInitialVariance n)
    (b := perPhaseMeanTailFloor n m k eps R)
    (target := perPhaseMeanTailFloor n m k eps R) hn1 hs0 hb0 hi le_rfl
  set tailR := (slowTargetError n (perPhaseQ n m k eps R) m i).toReal with htailRdef
  have htail0 : (0 : Real) ≤ tailR := ENNReal.toReal_nonneg
  set X := Real.exp (R ^ 2 /
    (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i)) with hXdef
  set X0 := Real.exp (R ^ 2 / (2 * slowSourceInitialVariance n)) with hX0def
  have hXpos : (0 : Real) < X := Real.exp_pos _
  have hX0pos : (0 : Real) < X0 := Real.exp_pos _
  have hXX0 : X ≤ X0 := by
    rw [hXdef, hX0def]
    refine Real.exp_le_exp.2 ?_
    exact div_le_div_of_nonneg_left (sq_nonneg R) (by positivity)
      (by nlinarith [initial_le_slowSourceSigmaSq hn1 hs0 i])
  have hbX0 : perPhaseMeanTailFloor n m k eps R * X0 ≤ 1 / (6 * (n : Real)) := by
    have hble : perPhaseMeanTailFloor n m k eps R ≤ 1 / (6 * (n : Real) * X0) := by
      rw [hX0def]; exact min_le_right _ _
    calc perPhaseMeanTailFloor n m k eps R * X0 ≤ (1 / (6 * (n : Real) * X0)) * X0 :=
          mul_le_mul_of_nonneg_right hble hX0pos.le
      _ = 1 / (6 * (n : Real)) := by field_simp
  -- the two `P`-generic halves
  have hA : ∀ P : Real, 0 ≤ P →
      mixR * (S i ^ 2 * P) * (3 * (n : Real) + 8) ≤ P * r ^ 2 := by
    intro P hP
    have h3n : (0 : Real) ≤ 3 * (n : Real) + 8 := by linarith
    have h1 : mixR * (S i ^ 2 * P) ≤ mixR * (3 * E i ^ 2 * P) := by
      calc mixR * (S i ^ 2 * P) = (mixR * P) * S i ^ 2 := by ring
        _ ≤ (mixR * P) * (3 * E i ^ 2) :=
            mul_le_mul_of_nonneg_left (hSE i) (mul_nonneg hmix0 hP)
        _ = mixR * (3 * E i ^ 2 * P) := by ring
    calc mixR * (S i ^ 2 * P) * (3 * (n : Real) + 8)
        ≤ mixR * (3 * E i ^ 2 * P) * (3 * (n : Real) + 8) :=
          mul_le_mul_of_nonneg_right h1 h3n
      _ = (3 * P) * (mixR * E i ^ 2 * (3 * (n : Real) + 8)) := by ring
      _ ≤ (3 * P) * (r ^ 2 / 3) := mul_le_mul_of_nonneg_left hF1 (by positivity)
      _ = P * r ^ 2 := by ring
  have hB : ∀ P : Real, 0 ≤ P →
      tailR * (S i ^ 2 * P) * (6 * (n : Real)) ≤ P := by
    intro P hP
    have hSX : S i ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (hS0 i) (hSloose i) 2
    have h1 : tailR * (S i ^ 2 * P) ≤ tailR * (X ^ 2 * P) := by
      calc tailR * (S i ^ 2 * P) = (tailR * P) * S i ^ 2 := by ring
        _ ≤ (tailR * P) * X ^ 2 :=
            mul_le_mul_of_nonneg_left hSX (mul_nonneg htail0 hP)
        _ = tailR * (X ^ 2 * P) := by ring
    have h2 : tailR * (X ^ 2 * P) ≤ (1 / (6 * (n : Real))) * P := by
      calc tailR * (X ^ 2 * P) = (tailR * X) * (X * P) := by ring
        _ ≤ perPhaseMeanTailFloor n m k eps R * (X * P) :=
            mul_le_mul_of_nonneg_right htail (by positivity)
        _ ≤ perPhaseMeanTailFloor n m k eps R * (X0 * P) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hXX0 hP) hb0.le
        _ = (perPhaseMeanTailFloor n m k eps R * X0) * P := by ring
        _ ≤ (1 / (6 * (n : Real))) * P := mul_le_mul_of_nonneg_right hbX0 hP
    have h6n : (0 : Real) < 6 * (n : Real) := by linarith
    calc tailR * (S i ^ 2 * P) * (6 * (n : Real))
        ≤ ((1 / (6 * (n : Real))) * P) * (6 * (n : Real)) :=
          mul_le_mul_of_nonneg_right (h1.trans h2) h6n.le
      _ = P := by field_simp
  rw [ENNReal.toReal_add (scoreAwareMixError_ne_top _ _ _ _ _ _)
    (slowTargetError_ne_top n _ m i)]
  rcases lt_or_ge (i + 1) m with hlt | hge
  · -- interior: `C = 1 + 2/n`, `T = 1 + 4/n`, `1 + 2T = (3n + 8)/n`, budget `(2/n) r²`
    rw [show sharpTransportedFactor n m (i + 1) = 1 + 4 / (n : Real) by
        unfold sharpTransportedFactor; rw [if_pos hlt],
      show sharpExactFactor n m (i + 1) = 1 + 2 / (n : Real) by
        unfold sharpExactFactor; rw [if_pos hlt]]
    set P := 1 + 2 * (1 + 4 / (n : Real)) with hPdef
    have hP0 : (0 : Real) < P := by rw [hPdef]; positivity
    have hPn : P * (n : Real) = 3 * (n : Real) + 8 := by
      rw [hPdef]; field_simp; ring
    have ha := hA P hP0.le
    have hb := hB P hP0.le
    have hAn : mixR * (S i ^ 2 * P) * (n : Real) ≤ r ^ 2 := by
      have h2 : P * (mixR * (S i ^ 2 * P) * (n : Real)) ≤ P * r ^ 2 := by
        calc P * (mixR * (S i ^ 2 * P) * (n : Real))
            = mixR * (S i ^ 2 * P) * (P * (n : Real)) := by ring
          _ = mixR * (S i ^ 2 * P) * (3 * (n : Real) + 8) := by rw [hPn]
          _ ≤ P * r ^ 2 := ha
      exact le_of_mul_le_mul_left h2 hP0
    have hBn : tailR * (S i ^ 2 * P) * (n : Real) ≤ r ^ 2 := by
      have h1 : (6 * (n : Real)) * (tailR * (S i ^ 2 * P) * (n : Real)) ≤
          3 * (n : Real) + 8 := by
        calc (6 * (n : Real)) * (tailR * (S i ^ 2 * P) * (n : Real))
            = (tailR * (S i ^ 2 * P) * (6 * (n : Real))) * (n : Real) := by ring
          _ ≤ P * (n : Real) := mul_le_mul_of_nonneg_right hb hnpos.le
          _ = 3 * (n : Real) + 8 := hPn
      have h2 : 3 * (n : Real) + 8 ≤ (6 * (n : Real)) * r ^ 2 := by nlinarith
      have h6n : (0 : Real) < 6 * (n : Real) := by linarith
      exact le_of_mul_le_mul_left (h1.trans h2) h6n
    have hgoal : (mixR + tailR) * (S i ^ 2 * P) * (n : Real) ≤ 2 * r ^ 2 := by
      have hexp : (mixR + tailR) * (S i ^ 2 * P) * (n : Real) =
          mixR * (S i ^ 2 * P) * (n : Real) +
            tailR * (S i ^ 2 * P) * (n : Real) := by ring
      rw [hexp]; linarith
    have hrhs : (1 + 2 / (n : Real) - 1) * r ^ 2 = 2 * r ^ 2 / (n : Real) := by
      field_simp
      try ring
    rw [hrhs, le_div_iff₀ hnpos]
    linarith [hgoal]
  · -- terminal: `C = 2`, `T = 3`, `1 + 2T = 7`, budget `1 · r²`
    rw [show sharpTransportedFactor n m (i + 1) = 3 by
        unfold sharpTransportedFactor; rw [if_neg (by omega)],
      show sharpExactFactor n m (i + 1) = 2 by
        unfold sharpExactFactor; rw [if_neg (by omega)]]
    have ha := hA (1 + 2 * 3) (by norm_num)
    have hb := hB (1 + 2 * 3) (by norm_num)
    have ha0 : (0 : Real) ≤ mixR * (S i ^ 2 * (1 + 2 * 3)) := by positivity
    have hb0' : (0 : Real) ≤ tailR * (S i ^ 2 * (1 + 2 * 3)) := by positivity
    have hA71 : mixR * (S i ^ 2 * (1 + 2 * 3)) * 71 ≤ 7 * r ^ 2 := by
      nlinarith [mul_nonneg ha0 (by linarith : (0 : Real) ≤ 3 * (n : Real) + 8 - 71)]
    have hB126 : tailR * (S i ^ 2 * (1 + 2 * 3)) * 126 ≤ 7 := by
      nlinarith [mul_nonneg hb0' (by linarith : (0 : Real) ≤ 6 * (n : Real) - 126)]
    have hexp : (mixR + tailR) * (S i ^ 2 * (1 + 2 * 3)) =
        mixR * (S i ^ 2 * (1 + 2 * 3)) + tailR * (S i ^ 2 * (1 + 2 * 3)) := by ring
    rw [hexp]
    nlinarith [hA71, hB126, hrr]

#print axioms perPhase_mix_add_tail_transport_le

/-! ## §4c — the estimator-moment binders at the per-phase pair

The per-phase analogue of `Ttc.CVSharpFrontier` §5, with **two** changes rather than one:
the stream count is `k` (the caller supplies `perPhaseRuntimeSamples`), and the operational
second-moment factor is the sharp family `sharpTransportedFactor n m j = 2 C - 1` at
`C = sharpExactFactor n m j` instead of the constant `7`.  The second change is the whole
point: it is what lets `Ttc.CVPerPhaseMomentBundle.averagedPerPhaseFactor_le_two` run at a
stream count a factor `n` below `correctedRuntimeSamples`.

Nothing analytic is re-proved.  The transport is
`Ttc.CVSharpFactorSeven.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound`
— already generic in the sup `B` and in the pair `(C, T)` — fed with §4b's
`perPhase_mix_add_tail_transport_le` in its `hslack` slot.  That slot is exactly what was
unreachable before the repair. -/

/-- The frontier's `htargetTV` at the `n`-aware radius.  This is
`Ttc.CVSlowCanonicalMomentInstantiation.slowCanonical_htargetTV` verbatim with
`slowUniformQ ↦ perPhaseQ`: the underlying
`Ttc.CVSlowSourceTargetTVAccuracy.tvLe_map_fst_tau_fullCoolLaw_slowTargetError` is
radius-generic, so nothing is re-proved. -/
theorem perPhase_htargetTV
    {k m : Nat} {Q : Nat → Kernel (State n) (ScoreSeed n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → ScoreSeed n) → Real} {estimatorEps eps R : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m estimatorEps)
    (hn : 1 ≤ n)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n (perPhaseQ n m k eps R)
        (slowSourceInitialVariance n) K i) :
    ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)
      (slowTargetError n (perPhaseQ n m k eps R) m j) := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hq4 : (4 : Real) ≤ perPhaseQ n m k eps R := four_le_perPhaseQ hn m k eps R
  have hq1 : (1 : Real) < perPhaseQ n m k eps R := by linarith
  have htau' : ∀ i, i < m → hop.tau i =
      slowLocalPairReference m n (perPhaseQ n m k eps R)
        (slowSourceInitialVariance n) K i := by
    intro i hi
    rw [htau i hi]
    exact slowLocalPairReference_succ_length_eq m n _ _ K hi
  exact tvLe_map_fst_tau_fullCoolLaw_slowTargetError hop hn hq1 hs0 hK hKc hball hfin
    (fun i _ ↦ perPhaseQ_rad hn m k eps R i) htau'

/-- **The per-index sharp operational second moment, at the per-phase schedule.**  This is
the statement `Ttc.CVPerPhaseMomentBundle.operational_phaseScore_sharpTransported_of_slack`
left open, now *proved* rather than assumed: its `hslack` binder is §4b's
`perPhase_mix_add_tail_transport_le`. -/
theorem perPhase_operational_phaseScore_sharpTransported
    (hn : 21 ≤ n) {k m : Nat}
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → ScoreSeed n) → Real} {estimatorEps eps R : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m estimatorEps)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {E S : Nat → Real} (hE0 : ∀ j, 0 < E j) (hS0 : ∀ j, 0 < S j)
    (hSbound : ∀ j x, phaseScore m
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ≤ S j)
    (hSloose : ∀ j, S j ≤ Real.exp (R ^ 2 /
      (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) j)))
    (hSE : ∀ j, S j ^ 2 ≤ 3 * E j ^ 2)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E)) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)
      (slowTargetError n (perPhaseQ n m k eps R) m j))
    (hexact : ∀ j, ∫ x, phaseScore m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      sharpExactFactor n m (j + 1) *
        (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
            (interior K) j x
          ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2)
    (i : Fin m) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → ScoreSeed n ↦
      phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
        (interior K) (i : Nat) (omega ((i : Nat) + 1)).1
    MemLp g 2 pathLaw ∧
      (∫ omega, (g omega) ^ 2 ∂pathLaw) ≤
        sharpTransportedFactor n m ((i : Nat) + 1) *
          (∫ omega, g omega ∂pathLaw) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have hmix : hop.mixError (i : Nat) = scoreAwareMixError (m + 1) k (eps / 2)
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) (i : Nat) := by
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1)]
  have htransport := perPhase_mix_add_tail_transport_le (n := n) (m := m) (k := k)
    (eps := eps) (R := R) (E := E) (S := S) (i := (i : Nat))
    hn heps heps1 hK hball hfin hE0 (fun j ↦ (hS0 j).le) hSE hSloose i.isLt
  rw [← hmix] at htransport
  have heq : sharpTransportedFactor n m ((i : Nat) + 1) -
      sharpExactFactor n m ((i : Nat) + 1) =
      sharpExactFactor n m ((i : Nat) + 1) - 1 := by
    rw [sharpTransportedFactor_eq]; ring
  exact operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound
    (C := sharpExactFactor n m ((i : Nat) + 1))
    (T := sharpTransportedFactor n m ((i : Nat) + 1))
    hop (slowSourceSigmaSq_pos hn1 hs0) hKc hball hfin
    (htargetTV (i : Nat)) (slowTargetError_ne_top n _ m (i : Nat))
    (hS0 (i : Nat)) (fun x ↦ hSbound (i : Nat) x)
    (sharpExactFactor_nonneg hn0 m ((i : Nat) + 1))
    (sharpExactFactor_le_sharpTransportedFactor hn0 m ((i : Nat) + 1))
    (hexact (i : Nat)) (by rw [heq]; exact htransport)

#print axioms perPhase_htargetTV
#print axioms perPhase_operational_phaseScore_sharpTransported

/-- The scalar sharp-transported bundle on the whole estimator prefix `j ≤ m`.  The
per-phase analogue of
`Ttc.CVSharpFactorSeven.operational_slowCanonical_positiveScalar_factorSeven_sharp_upto`,
with `7` replaced by `sharpTransportedFactor n m j`.  The `j = 0` conjunct is the constant
`1`, and `1 ≤ sharpTransportedFactor n m 0 = 1 + 4/n` needs only `0 < m`. -/
theorem perPhase_scalar_sharpTransported_upto
    (hn : 21 ≤ n) {k m : Nat} (hm : 0 < m)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → ScoreSeed n) → Real} {estimatorEps eps R : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m estimatorEps)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {E S : Nat → Real} (hE0 : ∀ j, 0 < E j) (hS0 : ∀ j, 0 < S j)
    (hSbound : ∀ j x, phaseScore m
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ≤ S j)
    (hSloose : ∀ j, S j ≤ Real.exp (R ^ 2 /
      (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) j)))
    (hSE : ∀ j, S j ^ 2 ≤ 3 * E j ^ 2)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E)) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)
      (slowTargetError n (perPhaseQ n m k eps R) m j))
    (hexact : ∀ j, ∫ x, phaseScore m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      sharpExactFactor n m (j + 1) *
        (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
            (interior K) j x
          ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega, (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        sharpTransportedFactor n m j *
          (∫ omega, positiveScalarPhaseFamilyChainLength (Seed := State n)
              m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
            ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  intro j hj
  cases j with
  | zero =>
      refine ⟨by
        simpa [positiveScalarPhaseFamilyChainLength] using
          (memLp_const (μ := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)
            (c := (1 : Real)) (p := (2 : ENNReal))), ?_⟩
      have hnR : (0 : Real) < (n : Real) := by
        have hn0 : 0 < n := by omega
        exact_mod_cast hn0
      have h1 : (1 : Real) ≤ sharpTransportedFactor n m 0 := by
        unfold sharpTransportedFactor
        rw [if_pos hm]
        have h4 : (0 : Real) < 4 / (n : Real) := by positivity
        linarith
      simpa [positiveScalarPhaseFamilyChainLength] using h1
  | succ i =>
      have hi : i < m := Nat.lt_of_succ_le hj
      change
        MemLp (fun omega : Nat → ScoreSeed n ↦
          phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
            (interior K) i (omega (i + 1)).1) 2
            (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
        ∫ omega, (phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
              (interior K) i (omega (i + 1)).1) ^ 2
            ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
          sharpTransportedFactor n m (i + 1) *
            (∫ omega, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
                (interior K) i (omega (i + 1)).1
              ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2
      exact perPhase_operational_phaseScore_sharpTransported hn hop heps heps1 hK hKc
        hball hfin hE0 hS0 hSbound hSloose hSE hmixError htargetTV hexact ⟨i, hi⟩

/-- The frontier's `hWEpos` on the estimator prefix, at the per-phase pair.  Exactly
`Ttc.CVSharpFrontier.slowSharp_hWEpos` with the per-phase slack/transport pair in place of
the sharp one: §2's first-moment crux, §4's `mix + tail` split at the true sup, and the
`B`-generic mean transport `operational_positiveStreamMean_upto_of_targetTV_bound`. -/
theorem perPhase_hWEpos
    (hn : 21 ≤ n) {k m : Nat} (hk : 0 < k)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → ScoreSeed n) → Real} {estimatorEps eps R : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m estimatorEps)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {E S : Nat → Real} (hE0 : ∀ j, 0 < E j) (hS0 : ∀ j, 0 < S j)
    (hSbound : ∀ j x, phaseScore m
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ≤ S j)
    (hSloose : ∀ j, S j ≤ Real.exp (R ^ 2 /
      (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) j)))
    (hSE : ∀ j, S j ^ 2 ≤ 3 * E j ^ 2)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E)) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)
      (slowTargetError n (perPhaseQ n m k eps R) m j)) :
    ∀ j, j ≤ m → 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n) m
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) mu0) := by
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have hmeanMix : ∀ i : Fin m,
      (hop.mixError (i : Nat)).toReal * S (i : Nat) ≤
        (scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              (i : Nat))) / 2 := by
    intro i
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1)]
    simpa only [mul_comm] using perPhaseMixError_succ_mean_le_half
      (n := n) (m := m) (k := k) (chainLength := m) (eps := eps)
      (E := E) (S := S) (K := K) (i := (i : Nat))
      hn1 hE0 (fun j ↦ (hS0 j).le) hSE heps heps1 hball hfin
  have hmeanError : ∀ i : Fin m,
      (hop.mixError (i : Nat) +
          slowTargetError n (perPhaseQ n m k eps R) m (i : Nat)).toReal *
          S (i : Nat) ≤
        scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              (i : Nat)) := by
    intro i
    exact mix_add_slowTargetError_rAware_genScaled_le hn1 hs0
      (perPhaseMeanTailFloor_pos (m := m) (k := k) hn1 heps) i.isLt
      (hop.mixError_ne_top i) (hSloose (i : Nat)) (hmeanMix i)
      (perPhaseMeanTailFloor_le_meanBudget hn1 heps hK hball hfin (i : Nat))
  exact operational_positiveStreamMean_upto_of_targetTV_bound hk hop
    (slowSourceSigmaSq_pos hn1 hs0) hK hKc hball hfin
    (scoreAwareMeanEta_nonneg m k eps)
    (Ttc.CVSlowCanonicalMomentBinders.scoreAwareMeanEta_lt_one m k heps heps1)
    hS0 hSbound htargetTV (slowTargetError_ne_top n _ m) hmeanError

#print axioms perPhase_scalar_sharpTransported_upto
#print axioms perPhase_hWEpos

/-- `Ttc.CVSlowCanonicalTailPhases.slowCanonical_clippedFamily_tail_eq_one` at an
**arbitrary** stream count.  The published version is pinned at
`k := correctedRuntimeSamples m eps`, which is exactly the count the per-phase family
replaces; its proof never uses the value of `k`, so this is that proof at a general `k`,
resting on the already `k`-generic `slowCanonical_streamAverage_tail_eq_one`. -/
theorem perPhase_clippedFamily_tail_eq_one
    (hn : 21 ≤ n) (m k : Nat) (hk : 0 < k) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {q : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (scoreScale : Real) (slack boundSq : Nat → Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    {j : Nat} (hj : m < j) :
    (fun omega ↦ slowClippedPositiveEmpiricalFamily m k eps Q (slowInitialPair n)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega)
      =ᵐ[independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)]
      fun _ ↦ (1 : Real) := by
  have htail := Ttc.CVSlowCanonicalTailPhases.slowCanonical_streamAverage_tail_eq_one
    hn m k hk hq4 hK hball scoreScale slack boundSq hQ
    (slowSourceSigmaSq n (slowSourceInitialVariance n)) hj
  have hint : ∫ z, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) z
      ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)) = 1 := by
    rw [integral_congr_ae htail]
    simp
  have halpha : (1 : Real) ≤ correctedAlpha m eps := by
    have ha := correctedAlpha_ge_hundred_thousand (m := m) heps heps1
    linarith
  filter_upwards [htail] with omega homega
  simp only [slowClippedPositiveEmpiricalFamily]
  rw [homega, hint, mul_one]
  exact min_eq_left halpha

#print axioms perPhase_clippedFamily_tail_eq_one

/-- **The five estimator-moment binders of §6, at the per-phase pair, at every `j`.**

The per-phase analogue of `Ttc.CVSharpFrontier.slowSharp_momentBinders_all`, at
`k := perPhaseRuntimeSamples n m eps` (a factor `n` below `correctedRuntimeSamples`) and at
`factor := perPhaseFactor n m k`.  The prefix `j ≤ m` comes from
`perPhase_scalar_sharpTransported_upto` (conjuncts 1, 2, 4, 5) and `perPhase_hWEpos`
(conjunct 3); the tail `m < j` comes from `Ttc.CVSlowCanonicalTailPhases`, whose two
identifications are bound-independent — past the active range the schedule is a constant
kernel into `interior K`, so the indicator is `1` and neither `slack` nor `boundSq` is ever
mentioned. -/
theorem perPhase_momentBinders_all
    (hn : 21 ≤ n) {m : Nat} (hm : 0 < m) (hnm : (n : Real) ≤ (m : Real) + 1)
    {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (scoreScale : Real)
    {E S : Nat → Real} (hE0 : ∀ j, 0 < E j) (hS0 : ∀ j, 0 < S j)
    (hSbound : ∀ j x, phaseScore m
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ≤ S j)
    (hSloose : ∀ j, S j ≤ Real.exp (R ^ 2 /
      (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) j)))
    (hSE : ∀ j, S j ^ 2 ≤ 3 * E j ^ 2)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [∀ j, IsProbabilityMeasure (slowStationaryTail n
      (perPhaseQ n m (perPhaseRuntimeSamples n m eps) eps R)
      (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1)
      (perPhaseRuntimeSamples n m eps)
      (q := perPhaseQ n m (perPhaseRuntimeSamples n m eps) eps R)
      (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num)
        (four_le_perPhaseQ (by omega : 1 ≤ n) m (perPhaseRuntimeSamples n m eps) eps R))
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm (perPhaseSlack n m K) (perPhaseBoundSqGen n E))
    (hop : IndependentStreamOperational (perPhaseRuntimeSamples n m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (perPhaseRuntimeSamples n m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (perPhaseQ n m (perPhaseRuntimeSamples n m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (perPhaseRuntimeSamples n m eps) (eps / 2)
        (perPhaseSlack n m K) (perPhaseBoundSqGen n E)) j)
    (hexact : ∀ j, ∫ x, phaseScore m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      sharpExactFactor n m (j + 1) *
        (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
            (interior K) j x
          ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    (∀ j, Integrable
      (fun omega ↦ streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (perPhaseRuntimeSamples n m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, Integrable
      (fun omega ↦ (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (perPhaseRuntimeSamples n m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, 0 < ∫ omega, streamAverage (k := perPhaseRuntimeSamples n m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, ∫ omega, (streamAverage (k := perPhaseRuntimeSamples n m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ j, ∫ omega,
        (slowClippedPositiveEmpiricalFamily m (perPhaseRuntimeSamples n m eps) eps Q
          (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n))
          K j omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      perPhaseFactor n m (perPhaseRuntimeSamples n m eps) j *
        (∫ omega, slowClippedPositiveEmpiricalFamily m
            (perPhaseRuntimeSamples n m eps) eps Q (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hn4 : 4 ≤ n := by omega
  have hnR : (4 : Real) ≤ (n : Real) := by exact_mod_cast hn4
  have hP0 : 0 < perPhaseRuntimeSamples n m eps := perPhaseRuntimeSamples_pos n m eps
  have hP2 : 2 ≤ perPhaseRuntimeSamples n m eps :=
    two_le_perPhaseRuntimeSamples hn0 heps
  have hPR : (2 : Real) ≤ (perPhaseRuntimeSamples n m eps : Real) := by exact_mod_cast hP2
  have hnk : (4 : Real) ≤ (n : Real) * (perPhaseRuntimeSamples n m eps : Real) := by
    nlinarith
  have hq4 : (4 : Real) ≤ perPhaseQ n m (perPhaseRuntimeSamples n m eps) eps R :=
    four_le_perPhaseQ hn1 m (perPhaseRuntimeSamples n m eps) eps R
  have htargetTV := perPhase_htargetTV hop hn1 hK hKc hball hfin htau
  have hscalar := perPhase_scalar_sharpTransported_upto hn hm hop heps heps1 hK hKc
    hball hfin hE0 hS0 hSbound hSloose hSE hmixError htargetTV hexact
  have hmeanPos := perPhase_hWEpos hn hP0 hop heps heps1 hK hKc hball hfin
    hE0 hS0 hSbound hSloose hSE hmixError htargetTV
  have hclip := operational_slowCanonical_clippedMoment_bundle_perPhase
    (n := n) (m := m) (eps := eps) hn4 hnm heps heps1 hK
    (Q := Q) (mu0 := slowInitialPair n)
    (V := slowClippedPositiveEmpiricalFamily m (perPhaseRuntimeSamples n m eps) eps Q
      (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K)
    hscalar hmeanPos (fun _ _ _ ↦ rfl)
  have hstream : ∀ j, j ≤ m →
      Integrable (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j))
        (independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ∧
      Integrable (fun omega ↦
        (streamAverage (k := perPhaseRuntimeSamples n m eps)
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
        (independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ∧
      ∫ omega, (streamAverage (k := perPhaseRuntimeSamples n m eps)
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
        2 * (∫ omega, streamAverage (k := perPhaseRuntimeSamples n m eps)
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2 := by
    intro j hj
    refine ⟨(memLp_streamAverage (k := perPhaseRuntimeSamples n m eps)
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n))
        (hscalar j hj).1).integrable one_le_two,
      integrable_streamAverage_sq (k := perPhaseRuntimeSamples n m eps)
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n))
        (hscalar j hj).1, ?_⟩
    refine (perPhase_streamAverage_sq_le (n := n) (m := m)
      (k := perPhaseRuntimeSamples n m eps) (j := j) hP0
      (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n))
      (measurable_positiveScalarPhaseFamilyChainLength hK j)
      (hscalar j hj).1 (hscalar j hj).2).trans ?_
    exact mul_le_mul_of_nonneg_right
      (averagedPerPhaseFactor_le_two j hnk hP2) (sq_nonneg _)
  -- the tail identifications, bound-independent
  have htail : ∀ j, m < j →
      (fun omega ↦ streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
        =ᵐ[independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) :=
    fun j hj ↦ Ttc.CVSlowCanonicalTailPhases.slowCanonical_streamAverage_tail_eq_one
      hn m (perPhaseRuntimeSamples n m eps) hP0 hq4 hK hball scoreScale
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) hQ
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) hj
  have htailSq : ∀ j, m < j →
      (fun omega ↦ (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
        =ᵐ[independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) := by
    intro j hj
    filter_upwards [htail j hj] with omega homega
    rw [homega]
    norm_num
  have hclipTail : ∀ j, m < j →
      (fun omega ↦ slowClippedPositiveEmpiricalFamily m
          (perPhaseRuntimeSamples n m eps) eps Q (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega)
        =ᵐ[independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) :=
    fun j hj ↦ perPhase_clippedFamily_tail_eq_one
      hn m (perPhaseRuntimeSamples n m eps) hP0 heps heps1 hq4 hK hball scoreScale
      (perPhaseSlack n m K) (perPhaseBoundSqGen n E) hQ hj
  have hclipTailSq : ∀ j, m < j →
      (fun omega ↦ (slowClippedPositiveEmpiricalFamily m
          (perPhaseRuntimeSamples n m eps) eps Q (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2)
        =ᵐ[independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)] fun _ ↦ (1 : Real) := by
    intro j hj
    filter_upwards [hclipTail j hj] with omega homega
    rw [homega]
    norm_num
  refine ⟨fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · rcases Nat.lt_or_ge m j with hj | hj
    · exact (integrable_const (1 : Real)).congr (htail j hj).symm
    · exact (hstream j hj).1
  · rcases Nat.lt_or_ge m j with hj | hj
    · exact (integrable_const (1 : Real)).congr (htailSq j hj).symm
    · exact (hstream j hj).2.1
  · rcases Nat.lt_or_ge m j with hj | hj
    · rw [integral_congr_ae (htail j hj)]
      simp
    · exact hmeanPos j hj
  · rcases Nat.lt_or_ge m j with hj | hj
    · rw [integral_congr_ae (htail j hj), integral_congr_ae (htailSq j hj)]
      simp
    · exact (hstream j hj).2.2
  · rcases Nat.lt_or_ge m j with hj | hj
    · rw [integral_congr_ae (hclipTail j hj), integral_congr_ae (hclipTailSq j hj)]
      have hf1 : (1 : Real) ≤ perPhaseFactor n m (perPhaseRuntimeSamples n m eps) j :=
        one_le_perPhaseFactor j
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_pow]
      linarith
    · exact (hclip j hj).2

#print axioms perPhase_momentBinders_all

/-! ## §5 — THE DELIVERABLE: the frontier certificate at the per-phase pair

This is
`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`
with its two schedule binders replaced,

* `hslackDef : slack = perPhaseSlack n m K` in place of
  `slack = fun j ↦ phaseMomentSlackSeven m σ K C j / 2`,
* `hboundDef : boundSq = perPhaseBoundSqGen n E` in place of
  `boundSq = phaseScoreTransportBoundSqSeven R σ`,

and with the **same conclusion, character for character**.  The comparison-constant
binders `C`, `hC1`, `hC7` of the original are gone — `C` is pinned to `1 + 2/n` inside
`perPhaseSlack`.  What replaces them is the abstract exponent/sup pair `E`, `S`: `E` is the
transport exponent the schedule declares, `S` the true per-phase score sup, linked by
`hSE : S i ^ 2 ≤ 3 * E i ^ 2`.  Taking `S := E := exp (R²/(2 σ_i))` recovers the
standard-exponent family; taking `E := exp (R²/(2 σ_i (n+1)))` and `S := sharpPhaseSup`
gives the combined P1 + P2 family. -/

theorem exists_sourceReferenceTVOneRunCertificate_slowCanonical_perPhase
    (hn : 21 ≤ n) (m k : Nat) (hm : 0 < m) (hk : 1 ≤ k)
    {q eps beta requested R meanTailFloor : Real} (hq4 : 4 ≤ q)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hbeta : 0 ≤ beta)
    (haccuracyBudget : eps + beta + eps * beta ≤ requested)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
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
    {factor : Nat → Real} {E S : Nat → Real}
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2) slack boundSq) j)
    (hslackDef : slack = perPhaseSlack n m K)
    (hboundDef : boundSq = perPhaseBoundSqGen n E)
    (hE0 : ∀ i, 0 < E i) (hS0 : ∀ i, 0 < S i)
    (hSbound : ∀ i x, phaseScore m
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) i x ≤ S i)
    (hSloose : ∀ i, S i ≤ Real.exp (R ^ 2 /
      (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i)))
    (hSE : ∀ i, S i ^ 2 ≤ 3 * E i ^ 2)
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
  -- the per-phase first-moment budget, through the crux of §2
  have hmeanMix : ∀ i : Fin m,
      (hop.mixError (i : Nat)).toReal * S (i : Nat) ≤
        (scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              (i : Nat))) / 2 := by
    intro i
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1), hslackDef, hboundDef]
    simpa only [mul_comm] using
      perPhaseMixError_succ_mean_le_half (n := n) (m := m) (k := k)
        (chainLength := m) (eps := eps) (E := E) (S := S) (K := K) (i := (i : Nat))
        hn1 hE0 (fun j ↦ (hS0 j).le) hSE heps heps1 hball hfin
  have hmeanError : ∀ i : Fin m,
      (hop.mixError (i : Nat) + slowTargetError n q m (i : Nat)).toReal * S (i : Nat) ≤
        scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i : Nat)) := by
    intro i
    have hc := mix_add_slowTargetError_rAware_genScaled_le hn1
      hs0 hmeanTailFloor i.isLt (hop.mixError_ne_top i)
      (hSloose (i : Nat)) (hmeanMix i) (hmeanTailBudget i)
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
    (B := S) hS0 hSbound
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

#print axioms exists_sourceReferenceTVOneRunCertificate_slowCanonical_perPhase

/-! ## §6 — the canonical instantiation at the `n`-aware stream count

The per-phase analogue of `Ttc.CVSharpFrontier.exists_slowOneRunCertificate_canonical_sharp`
at `k := perPhaseRuntimeSamples n (slowCanonicalPhases n R2) eps` — a factor `n` below
`correctedRuntimeSamples`.  `Ttc.CVSlowOneRunValid.canonical_hq0` and
`canonical_isProbabilityMeasure_slowStationaryTail` are pinned at `correctedRuntimeSamples`,
so the two `k`-generic replacements come first. -/

theorem perPhase_canonical_hq0 (hn : 21 ≤ n) (R2 eps R : Real) :
    (0 : Real) < perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (perPhaseRuntimeSamples n
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R :=
  lt_of_lt_of_le (by norm_num) (four_le_perPhaseQ (by omega : 1 ≤ n) _ _ eps R)

theorem perPhase_canonical_isProbabilityMeasure_slowStationaryTail
    (hn : 21 ≤ n) {R2 eps R : Real} {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K) (j : Nat) :
    IsProbabilityMeasure (slowStationaryTail n
      (perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) :=
  isProbabilityMeasure_slowStationaryTail (by omega) (perPhase_canonical_hq0 hn R2 eps R)
    (Ttc.CVSlowOneRunValid.canonical_hs0 hn) hK hKc hball
    (fun r ↦ one_le_slow_radius (by omega)
      (four_le_perPhaseQ (by omega : 1 ≤ n) _ _ eps R) (by rfl) r) j

/-- **The slow canonical one-run certificate at the per-phase slack / transport pair, at
the `n`-aware stream count.**

The per-phase analogue of `Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical`,
with `k := perPhaseRuntimeSamples n (slowCanonicalPhases n R2) eps` in place of
`correctedRuntimeSamples (slowCanonicalPhases n R2) eps` (an `n`-fold saving,
`Ttc.CVPerPhaseMomentBundle.perPhaseRuntimeSamples_lt_correctedRuntimeSamples`),
`slack := perPhaseSlack n (slowCanonicalPhases n R2) K`,
`boundSq := perPhaseBoundSqGen n E`, and
`factor := perPhaseFactor n (slowCanonicalPhases n R2) (perPhaseRuntimeSamples …)` in
place of the uniform `fun _ ↦ 1 + 8 / (correctedRuntimeSamples …)`.

`hfactor0` and `hprefix` are free here (`perPhaseFactor_nonneg`,
`perPhase_prefixMomentRatio_le` + `perPhaseRuntimeSamples_budget`); the residual binder
list is otherwise exactly the original's. -/
theorem exists_slowOneRunCertificate_canonical_perPhase
    (hn : 21 ≤ n) {eps R R2 : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {E S : Nat → Real} (hE0 : ∀ i, 0 < E i) (hS0 : ∀ i, 0 < S i)
    (hSbound : ∀ i x, phaseScore (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) i x ≤ S i)
    (hSloose : ∀ i, S i ≤ Real.exp (R ^ 2 /
      (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i)))
    (hSE : ∀ i, S i ^ 2 ≤ 3 * E i ^ 2)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n)
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
      (perPhaseRuntimeSamples n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
      (q := perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (perPhase_canonical_hq0 hn R2 eps R)
      (Ttc.CVSlowOneRunValid.canonical_hs0 hn) K hK 0 slowReferenceWarm
      (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
      (perPhaseBoundSqGen n E))
    (hWint : ∀ j, Integrable
      (fun omega ↦ streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hW2int : ∀ j, Integrable
      (fun omega ↦ (streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hWEpos : ∀ j, 0 < ∫ omega, streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hrawSecond : ∀ j, ∫ omega, (streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    (hphaseMoment : ∀ j, ∫ omega,
          (slowClippedPositiveEmpiricalFamily
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      perPhaseFactor n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) j *
        (∫ omega, slowClippedPositiveEmpiricalFamily
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    {runtimeConstant : Real} (T L : Nat)
    (hsteps : ∀ i, i < Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 →
      slowCanonicalSteps slowReferenceWarm n
        (perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
        (slowSourceInitialVariance n) K
        (scoreAwareRetries (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
          (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
          (perPhaseBoundSqGen n E))
        (scoreAwareEta (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
          (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
          (perPhaseBoundSqGen n E))
        (scoreAwareZeta (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
          (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
          (perPhaseBoundSqGen n E))
        i 0 ≤ T)
    (hretries : ∀ i, i < Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 →
      scoreAwareRetries (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
        (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
        (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
        (perPhaseBoundSqGen n E) i ≤ L)
    (hscalar : ((perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps : Nat) : ENNReal) *
        ((Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 : Nat) : ENNReal) *
          ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R
        (slowAccuracyRequested (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps)) :
    ∃ reference : Measure
        (Fin (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) →
          HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (@independentHeterogeneousRetainedPathLaw _ _ _ _
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (slowCanonicalCostedActiveSchedule (by omega : 1 ≤ n)
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
            (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
            (q := perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
              (perPhaseRuntimeSamples n
                (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
            (eps := eps / 2) (s0 := slowSourceInitialVariance n)
            (perPhase_canonical_hq0 hn R2 eps R)
            (Ttc.CVSlowOneRunValid.canonical_hs0 hn) K hK 0 slowReferenceWarm
            (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
            (perPhaseBoundSqGen n E))
          (by
            letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
                (perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
                  (perPhaseRuntimeSamples n
                    (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
                (slowSourceInitialVariance n) K j) := fun j ↦
              perPhase_canonical_isProbabilityMeasure_slowStationaryTail
                hn hK hKc hball j
            intro i; infer_instance)
          (slowInitialPair n) (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ gaussianScorePrefixReadout
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
          (chain (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0)
          (independentStoredScorePrefixCurrent
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) omega))
        runtimeConstant n R
        (slowAccuracyRequested (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps)
        ((1 - slowAccuracyRequested (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps) *
            (volume K).toReal)
        ((1 + slowAccuracyRequested (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps) *
            (volume K).toReal) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  haveI : IsProbabilityMeasure (slowInitialPair n) :=
    Ttc.CVSlowOneRunValid.canonical_isProbabilityMeasure_slowInitialPair hn
  haveI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) := fun j ↦
    perPhase_canonical_isProbabilityMeasure_slowStationaryTail hn hK hKc hball j
  have hq4 : (4 : Real) ≤ perPhaseQ n
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (perPhaseRuntimeSamples n
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R :=
    four_le_perPhaseQ hn1 _ _ eps R
  have hP0 : 0 < perPhaseRuntimeSamples n
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps :=
    perPhaseRuntimeSamples_pos _ _ _
  have hslack := perPhaseSlack_pos (n := n)
    (chainLength := Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) hn1 hball hfin
  have hbound := perPhaseBoundSqGen_pos (n := n) (E := E) hn1 hE0
  obtain ⟨hop, htau, hmixError⟩ :=
    Ttc.CVSlowCanonicalHopAssembly.exists_slowCanonicalHop_literal hn
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (perPhaseRuntimeSamples n
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
      hP0 hq4 heps heps1 hK hKc hball hfin (0 : Real) hslack hbound hQ
  exact exists_sourceReferenceTVOneRunCertificate_slowCanonical_perPhase
    hn (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
    (perPhaseRuntimeSamples n
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
    (Ttc.CVSlowOneRunValid.slowCanonicalPhases_pos n R2) hP0
    hq4 heps heps1 (scoreAwareAccuracyBeta_nonneg _ _ heps)
    (slowAccuracyBudget_le _ _ eps)
    hK hKc hball hfin
    (perPhaseMeanTailFloor_pos hn1 heps)
    (perPhaseQ_rAware n _ _ eps R)
    (fun i ↦ perPhaseQ_rad hn1 _ _ eps R i)
    (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
    (perPhaseBoundSqGen n E)
    hslack hbound (0 : Real) hQ _ rfl hop htau hmixError rfl rfl
    hE0 hS0 hSbound hSloose hSE
    (fun i ↦ perPhaseMeanTailFloor_le_meanBudget hn1 heps hK hball hfin (i : Nat))
    hWint hW2int hWEpos hrawSecond
    (fun j ↦ perPhaseFactor_nonneg j) hphaseMoment
    (fun i hi ↦ perPhase_prefixMomentRatio_le hn0 hP0 heps heps1
      (perPhaseRuntimeSamples_budget hn0 heps) hi)
    (chain (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0)
    (volume K).toReal
    (Ttc.CVSlowOneRunValid.canonical_chain_zero_nonneg hn R2 hball hfin)
    ENNReal.toReal_nonneg
    rfl (Ttc.CVSlowOneRunValid.slowCanonical_volumeTarget_eq n R2 K).symm (le_refl _)
    T L hsteps hretries hscalar

#print axioms perPhase_canonical_hq0
#print axioms perPhase_canonical_isProbabilityMeasure_slowStationaryTail
#print axioms exists_slowOneRunCertificate_canonical_perPhase

/-! ## §7 — the two instantiations of the `(E, S)` data

`perPhaseBoundSq n R` and `perPhaseBoundSqSharp n R` are `perPhaseBoundSqGen n E` at
`E := perPhaseExp n R` and `E := perPhaseExpSharp n R` **by definition**, so §5 and §6 are
already the frontier and the canonical certificate at both families; all that is left is
to discharge their `(hE0, hS0, hSbound, hSloose, hSE)` data, which is what the two theorems
below do.  The standard family takes `S := E`; the combined P1 + P2 family takes
`S := Ttc.CVSharpFactorSeven.sharpPhaseSup`, and is the only one carrying the terminal side
condition `hR2`, exactly as in `Ttc.CVSharpFrontier`. -/

/-- The `(E, S)` data of the **standard-exponent** family, at `S := E := exp (R²/(2 σ_i))`.
Feed the four conjuncts to `exists_sourceReferenceTVOneRunCertificate_slowCanonical_perPhase`
or `exists_slowOneRunCertificate_canonical_perPhase` at `E := S := perPhaseExp n R`. -/
theorem perPhaseStandard_supData {n : Nat} (hn : 1 ≤ n) (m : Nat) {R : Real}
    {K : Set (State n)} (hKR : K ⊆ closedBall (0 : State n) R) :
    (∀ i, 0 < perPhaseExp n R i) ∧
    (∀ i x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
      (interior K) i x ≤ perPhaseExp n R i) ∧
    (∀ i, perPhaseExp n R i ≤ Real.exp (R ^ 2 /
      (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i))) ∧
    (∀ i, perPhaseExp n R i ^ 2 ≤ 3 * perPhaseExp n R i ^ 2) := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  refine ⟨fun i ↦ perPhaseExp_pos i, fun i x ↦ ?_, fun i ↦ le_rfl, fun i ↦ ?_⟩
  · exact phaseScore_le (slowSourceSigmaSq_pos hn hs0)
      (interior_subset.trans hKR) i x
  · nlinarith [sq_nonneg (perPhaseExp n R i)]

/-- The `(E, S)` data of the **combined P1 + P2** family, at
`E := exp (R²/(2 σ_i (n+1)))` and `S := Ttc.CVSharpFactorSeven.sharpPhaseSup`.  The link
`S² ≤ 3 E²` is `sharpPhaseSup_sq_mul_le_three_mul` divided by `15`, and it is the only
place the terminal binder `hR2` is used. -/
theorem perPhaseSharp_supData {n : Nat} (hn : 1 ≤ n) (m : Nat) {R : Real}
    {K : Set (State n)} (hKR : K ⊆ closedBall (0 : State n) R)
    (hR2 : ∀ i : Nat, m ≤ i + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) i) :
    (∀ i, 0 < perPhaseExpSharp n R i) ∧
    (∀ i, 0 < sharpPhaseSup n R
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) m i) ∧
    (∀ i x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
      (interior K) i x ≤ sharpPhaseSup n R
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) m i) ∧
    (∀ i, sharpPhaseSup n R
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) m i ≤
      Real.exp (R ^ 2 /
        (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) i))) ∧
    (∀ i, sharpPhaseSup n R
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) m i ^ 2 ≤
      3 * perPhaseExpSharp n R i ^ 2) := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  refine ⟨fun i ↦ perPhaseExpSharp_pos i, fun i ↦ sharpPhaseSup_pos m i,
    fun i x ↦ phaseScore_le_sharpPhaseSup hn hs0 (interior_subset.trans hKR) x,
    fun i ↦ sharpPhaseSup_le_loose (slowSourceSigmaSq_pos hn hs0 i), fun i ↦ ?_⟩
  have hcrux := sharpPhaseSup_sq_mul_le_three_mul (n := n) (m := m) (i := i)
    hn hs0 (fun h ↦ hR2 i h)
  have hbound : phaseScoreTransportBoundSqSharp n R
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) i =
      perPhaseExpSharp n R i ^ 2 * 15 := by
    unfold phaseScoreTransportBoundSqSharp perPhaseExpSharp
    ring
  rw [hbound] at hcrux
  linarith

#print axioms perPhaseStandard_supData
#print axioms perPhaseSharp_supData

/-! ## §8 — the quantified payoff, machine-checked

Two comparisons against `Ttc.CVSlowUniformShareBounds`, the stack at the slack/boundSq pair
the frontier currently forces (`slack = phaseMomentSlackSeven … / 2`,
`boundSq = phaseScoreTransportBoundSqSeven R σ`, floor branch `1 / (18 exp (R²/(2 s0))²)`):

* at the **same** transport exponent the per-phase floor is smaller by *exactly*
  `(54n + 144)/36`, and the retry cap therefore grows by at most an additive
  `16 ⌈log₂((54n + 144)/36)⌉` — logarithmic in `n` against a multiplicative `n` saving in the
  stream count;
* at the **sharp** exponent the per-phase floor is *larger* than the current one for
  `2 ≤ n`, `1 ≤ R`, so the combined P1 + P2 family costs nothing at all in retries. -/

/-- `R²/(2 s0) = 8 n R²` at the canonical initial variance `s0 = 1/(16 n)`. -/
theorem slowSourceInitialVariance_exponent {n : Nat} (hn : 1 ≤ n) (R : Real) :
    R ^ 2 / (2 * slowSourceInitialVariance n) = 8 * (n : Real) * R ^ 2 := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hs0eq : slowSourceInitialVariance n = 1 / (16 * (n : Real)) := rfl
  rw [hs0eq]
  field_simp
  ring

/-- Uniform logarithmic retry cap at the **standard** per-phase exponent. -/
noncomputable def perPhaseRetriesCap (n m k : Nat) (eps R : Real) : Nat :=
  perPhaseRetriesCapGen n m k eps (Real.exp (8 * (n : Real) * R ^ 2))

/-- Uniform logarithmic retry cap at the **P1-sharp** per-phase exponent. -/
noncomputable def perPhaseRetriesCapSharp (n m k : Nat) (eps R : Real) : Nat :=
  perPhaseRetriesCapGen n m k eps (Real.exp (8 * R ^ 2))

/-- **The floor comparison, at the same transport exponent.**  The per-phase share floor is
below the one the frontier currently forces by *exactly* the factor `(54n + 144)/36`. -/
theorem perPhaseShareFloor_ge_ratio {n : Nat} (hn : 2 ≤ n) (m k : Nat) {eps : Real}
    (heps : 0 < eps) (R : Real) :
    Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
        (slowSourceInitialVariance n) ≤
      ((54 * (n : Real) + 144) / 36) * perPhaseShareFloor n m k eps R := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hc1 : (1 : Real) ≤ (54 * (n : Real) + 144) / 36 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 36)]
    linarith
  have hd0 : (0 : Real) < 54 * (n : Real) + 144 := by linarith
  have hB0 : (0 : Real) ≤ blockShare m k eps := (blockShare_pos heps).le
  have hE0 : (0 : Real) < Real.exp (8 * (n : Real) * R ^ 2) ^ 2 := by positivity
  have hcy : ((54 * (n : Real) + 144) / 36) *
      (2 / ((54 * (n : Real) + 144) * Real.exp (8 * (n : Real) * R ^ 2) ^ 2)) =
      1 / (18 * Real.exp (8 * (n : Real) * R ^ 2) ^ 2) := by
    field_simp
    ring
  unfold Ttc.CVSlowUniformShareBounds.slowUniformShareFloor perPhaseShareFloor
    perPhaseShareFloorGen
  rw [slowSourceInitialVariance_exponent hn1 R]
  rcases min_cases (blockShare m k eps)
      (2 / ((54 * (n : Real) + 144) * Real.exp (8 * (n : Real) * R ^ 2) ^ 2)) with
    ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]
    exact (min_le_left _ _).trans (le_mul_of_one_le_left hB0 hc1)
  · rw [h1, hcy]
    exact min_le_right _ _

/-- **The retry cap grows only additively in `log n`.**  At the same transport exponent the
per-phase retry cap exceeds the one the frontier currently forces by at most
`16 ⌈log₂((54n + 144)/36)⌉` — against a base of order `16 · 16 n R² / log 2`, i.e. nothing. -/
theorem perPhaseRetriesCap_le_add_log {n : Nat} (hn : 2 ≤ n) {m k : Nat} {eps : Real}
    (heps : 0 < eps) (R : Real) :
    perPhaseRetriesCap n m k eps R ≤
      Ttc.CVSlowUniformShareBounds.slowUniformRetriesCap m k eps R
        (slowSourceInitialVariance n) +
      16 * ⌈Real.logb 2 ((54 * (n : Real) + 144) / 36)⌉₊ := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hc1 : (1 : Real) ≤ (54 * (n : Real) + 144) / 36 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 36)]
    linarith
  have hc0 : (0 : Real) < (54 * (n : Real) + 144) / 36 := by linarith
  have hfloorU0 := Ttc.CVSlowUniformShareBounds.slowUniformShareFloor_pos
    (m := m) (k := k) (R := R) (s0 := slowSourceInitialVariance n) heps
  have hfloorP0 : 0 < perPhaseShareFloor n m k eps R :=
    perPhaseShareFloorGen_pos hn1 heps (by positivity)
  have hcmp := perPhaseShareFloor_ge_ratio hn m k heps R
  -- `1 / floorP ≤ c * (1 / floorU)`
  have hstep : 1 / (((54 * (n : Real) + 144) / 36) * perPhaseShareFloor n m k eps R) ≤
      1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
        (slowSourceInitialVariance n) :=
    one_div_le_one_div_of_le hfloorU0 hcmp
  have hinv : 1 / perPhaseShareFloor n m k eps R ≤
      ((54 * (n : Real) + 144) / 36) *
        (1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
          (slowSourceInitialVariance n)) := by
    have hrw : 1 / (((54 * (n : Real) + 144) / 36) * perPhaseShareFloor n m k eps R) =
        (1 / ((54 * (n : Real) + 144) / 36)) * (1 / perPhaseShareFloor n m k eps R) := by
      field_simp
    rw [hrw] at hstep
    have := mul_le_mul_of_nonneg_left hstep hc0.le
    calc
      1 / perPhaseShareFloor n m k eps R
          = ((54 * (n : Real) + 144) / 36) *
            ((1 / ((54 * (n : Real) + 144) / 36)) *
              (1 / perPhaseShareFloor n m k eps R)) := by
            field_simp
      _ ≤ ((54 * (n : Real) + 144) / 36) *
            (1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
              (slowSourceInitialVariance n)) := this
  have hlog : Real.logb 2 (1 / perPhaseShareFloor n m k eps R) ≤
      Real.logb 2 ((54 * (n : Real) + 144) / 36) +
        Real.logb 2 (1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
          (slowSourceInitialVariance n)) := by
    have hmono := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
      (by positivity) (by positivity)).2 hinv
    rw [Real.logb_mul (ne_of_gt hc0) (by positivity)] at hmono
    exact hmono
  have hceil : ⌈Real.logb 2 (1 / perPhaseShareFloor n m k eps R)⌉₊ ≤
      ⌈Real.logb 2 ((54 * (n : Real) + 144) / 36)⌉₊ +
        ⌈Real.logb 2 (1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
          (slowSourceInitialVariance n))⌉₊ :=
    (Nat.ceil_mono hlog).trans (Nat.ceil_add_le _ _)
  unfold perPhaseRetriesCap perPhaseRetriesCapGen
    Ttc.CVSlowUniformShareBounds.slowUniformRetriesCap explicitDyadicTailIndex
  have hfloorEq : perPhaseShareFloorGen n m k eps (Real.exp (8 * (n : Real) * R ^ 2)) =
      perPhaseShareFloor n m k eps R := rfl
  rw [hfloorEq]
  omega

/-- **The combined P1 + P2 family costs nothing at all.**  At the sharp transport exponent
the per-phase share floor is *larger* than the one the frontier currently forces, for
`2 ≤ n` and `1 ≤ R` (both hypotheses are forced: `ball 0 1 ⊆ K ⊆ closedBall 0 R` gives
`1 ≤ R` downstream, and at `n = 1` the two exponents agree). -/
theorem perPhaseShareFloorSharp_ge_slowUniformShareFloor
    {n : Nat} (hn : 2 ≤ n) (m k : Nat) (eps : Real) {R : Real} (hR : 1 ≤ R) :
    Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
        (slowSourceInitialVariance n) ≤ perPhaseShareFloorSharp n m k eps R := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hRsq : (1 : Real) ≤ R ^ 2 := by nlinarith
  have hsplit : Real.exp (8 * (n : Real) * R ^ 2) =
      Real.exp (8 * R ^ 2) * Real.exp (8 * ((n : Real) - 1) * R ^ 2) := by
    rw [← Real.exp_add]
    ring_nf
  have hbig : (54 * (n : Real) + 144) / 36 ≤
      Real.exp (8 * ((n : Real) - 1) * R ^ 2) ^ 2 := by
    have h8 : (8 : Real) * ((n : Real) - 1) * R ^ 2 ≥ 8 * ((n : Real) - 1) := by
      nlinarith
    have hle := Real.add_one_le_exp (8 * ((n : Real) - 1) * R ^ 2)
    have hpos := Real.exp_pos (8 * ((n : Real) - 1) * R ^ 2)
    have hlow : (1 : Real) + 8 * ((n : Real) - 1) ≤
        Real.exp (8 * ((n : Real) - 1) * R ^ 2) := by linarith
    have hone : (1 : Real) ≤ Real.exp (8 * ((n : Real) - 1) * R ^ 2) := by linarith
    nlinarith
  unfold Ttc.CVSlowUniformShareBounds.slowUniformShareFloor perPhaseShareFloorSharp
    perPhaseShareFloorGen
  rw [slowSourceInitialVariance_exponent hn1 R]
  refine le_min (min_le_left _ _) ((min_le_right _ _).trans ?_)
  rw [hsplit, mul_pow]
  rw [div_le_div_iff₀
    (by positivity : (0 : Real) < 18 *
      (Real.exp (8 * R ^ 2) ^ 2 * Real.exp (8 * ((n : Real) - 1) * R ^ 2) ^ 2))
    (by positivity : (0 : Real) < (54 * (n : Real) + 144) * Real.exp (8 * R ^ 2) ^ 2)]
  nlinarith [Real.exp_pos (8 * R ^ 2), sq_nonneg (Real.exp (8 * R ^ 2)),
    Real.exp_pos (8 * ((n : Real) - 1) * R ^ 2)]

/-- **The retry-cap payoff of the combined family**: a larger share floor means fewer
dyadic retry shells, so the combined P1 + P2 retry cap is *below* the one the frontier
currently forces. -/
theorem perPhaseRetriesCapSharp_le_slowUniformRetriesCap
    {n : Nat} (hn : 2 ≤ n) {m k : Nat} {eps R : Real} (heps : 0 < eps) (hR : 1 ≤ R) :
    perPhaseRetriesCapSharp n m k eps R ≤
      Ttc.CVSlowUniformShareBounds.slowUniformRetriesCap m k eps R
        (slowSourceInitialVariance n) := by
  have hn1 : 1 ≤ n := by omega
  have hfloorU0 := Ttc.CVSlowUniformShareBounds.slowUniformShareFloor_pos
    (m := m) (k := k) (R := R) (s0 := slowSourceInitialVariance n) heps
  have hfloorS0 : 0 < perPhaseShareFloorSharp n m k eps R :=
    perPhaseShareFloorGen_pos hn1 heps (by positivity)
  have hcmp := perPhaseShareFloorSharp_ge_slowUniformShareFloor hn m k eps hR
  have hinv : 1 / perPhaseShareFloorSharp n m k eps R ≤
      1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
        (slowSourceInitialVariance n) :=
    one_div_le_one_div_of_le hfloorU0 hcmp
  have hlog := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
    (by positivity) (by positivity)).2 hinv
  unfold perPhaseRetriesCapSharp perPhaseRetriesCapGen
    Ttc.CVSlowUniformShareBounds.slowUniformRetriesCap explicitDyadicTailIndex
  exact Nat.mul_le_mul_left 16 (Nat.ceil_mono hlog)

#print axioms slowSourceInitialVariance_exponent
#print axioms perPhaseShareFloor_ge_ratio
#print axioms perPhaseRetriesCap_le_add_log
#print axioms perPhaseShareFloorSharp_ge_slowUniformShareFloor
#print axioms perPhaseRetriesCapSharp_le_slowUniformRetriesCap


/-! ## §9 — reachability: §6's estimator-moment binders, discharged

The point of §4b and §4c.  Before the repair `exists_slowOneRunCertificate_canonical_perPhase`
was *unreachable at its own declared schedule*: its `hphaseMoment` binder can only come from
`Ttc.CVPerPhaseMomentBundle.operational_slowCanonical_clippedMoment_bundle_perPhase`, whose
`hscalar` slot is at `sharpTransportedFactor`, which in turn can only come from the
transport bridge
`Ttc.CVSharpFactorSeven.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound`,
whose `hslack` binder carries **mixing error plus target error** against a budget that the
undivided `perPhaseSlack = (2/n)·r²` already exhausted with the mixing error alone.

§4b's `perPhase_mix_add_tail_transport_le` closes that, and this section carries the
consequence all the way to §6's binder list at the combined P1 + P2 family. -/

/-- The canonical chain's **sharp exact-law** second moment at the recursion's index.  This
is P2's `Ttc.CVPerPhaseSamples.slowSource_phaseScore_sq_moment_sharp` read on the canonical
schedule: `slowCanonicalPhases n R2` is definitionally
`slowSourcePhases n (max 1 R2) s₀ + 1`, which is exactly that theorem's `m`. -/
theorem perPhase_canonical_hexact (hn : 21 ≤ n) {R R2 : Real} (hR2 : R ^ 2 ≤ R2)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R) (j : Nat) :
    ∫ x, phaseScore (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ^ 2
      ∂(coolLaw (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      sharpExactFactor n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) (j + 1) *
        (∫ x, phaseScore (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x
          ∂(coolLaw (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2 :=
  slowSource_phaseScore_sq_moment_sharpExact (by omega : 3 ≤ n)
    (Ttc.CVSlowOneRunValid.canonicalN_pos R2)
    (slowSourceInitialVariance_pos (by omega : 1 ≤ n))
    (Ttc.CVSlowOneRunValid.slowSourceInitialVariance_le_canonicalN hn R2)
    (hR2.trans (le_max_right 1 R2)) hK hKc hball hfin hKR j

/-- The terminal binder of §7's sharp `(E, S)` data, at **every natural index**.
`Ttc.CVSharpFrontier.canonical_hR2_sharp` gives it on `Fin m`; the variance schedule is
increasing, so it extends past `m` for free. -/
theorem perPhase_canonical_hR2 (hn : 21 ≤ n) {R R2 : Real} (hR2 : R ^ 2 ≤ R2) :
    ∀ i : Nat, Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 ≤ i + 1 →
      R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) i := by
  intro i hterm
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have hterm2 : slowSourcePhases n (max 1 R2) (slowSourceInitialVariance n) + 1 ≤ i + 1 :=
    hterm
  have hbase : R ^ 2 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n)
      (slowSourcePhases n (max 1 R2) (slowSourceInitialVariance n)) :=
    (hR2.trans (le_max_right 1 R2)).trans
      (target_le_slowSourceSigmaSq_terminal hn1
        (Ttc.CVSlowOneRunValid.canonicalN_pos R2) hs0
        (Ttc.CVSlowOneRunValid.slowSourceInitialVariance_le_canonicalN hn R2))
  exact hbase.trans (slowSourceSigmaSq_le_terminal hn1 hs0 (by omega))

/-- **The five estimator-moment binders of §6, discharged at the combined P1 + P2 family.**

`E := perPhaseExpSharp n R = exp (R²/(2 σ_i (n+1)))`, `S := sharpPhaseSup n R σ m` — §7's
`perPhaseSharp_supData`.  Everything else is §4c's `perPhase_momentBinders_all` fed with
§9's `perPhase_canonical_hexact`.

Its fifth conjunct is **character for character** §6's `hphaseMoment` binder. -/
theorem perPhase_canonical_momentBinders_sharp
    (hn : 21 ≤ n) {eps R R2 : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hnm : (n : Real) ≤
      ((Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 : Nat) : Real) + 1)
    (hR2 : R ^ 2 ≤ R2)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n)
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
      (perPhaseRuntimeSamples n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
      (q := perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (perPhase_canonical_hq0 hn R2 eps R)
      (Ttc.CVSlowOneRunValid.canonical_hs0 hn) K hK 0 slowReferenceWarm
      (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
      (perPhaseBoundSqGen n (perPhaseExpSharp n R))) :
    (∀ j, Integrable
      (fun omega ↦ streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, Integrable
      (fun omega ↦ (streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, 0 < ∫ omega, streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, ∫ omega, (streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage
        (k := perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ j, ∫ omega,
          (slowClippedPositiveEmpiricalFamily
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      perPhaseFactor n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) j *
        (∫ omega, slowClippedPositiveEmpiricalFamily
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  haveI : IsProbabilityMeasure (slowInitialPair n) :=
    Ttc.CVSlowOneRunValid.canonical_isProbabilityMeasure_slowInitialPair hn
  haveI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) := fun j ↦
    perPhase_canonical_isProbabilityMeasure_slowStationaryTail hn hK hKc hball j
  obtain ⟨hE0, hS0, hSbound, hSloose, hSE⟩ :=
    perPhaseSharp_supData (n := n) hn1
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) hKR
      (perPhase_canonical_hR2 hn hR2)
  have hq4 : (4 : Real) ≤ perPhaseQ n
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (perPhaseRuntimeSamples n
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R :=
    four_le_perPhaseQ hn1 _ _ eps R
  obtain ⟨hop, htau, hmixError⟩ :=
    Ttc.CVSlowCanonicalHopAssembly.exists_slowCanonicalHop_literal hn
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (perPhaseRuntimeSamples n
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
      (perPhaseRuntimeSamples_pos _ _ _) hq4 heps heps1 hK hKc hball hfin (0 : Real)
      (perPhaseSlack_pos hn1 hball hfin) (perPhaseBoundSqGen_pos hn1 hE0) hQ
  exact perPhase_momentBinders_all hn
    (Ttc.CVSlowOneRunValid.slowCanonicalPhases_pos n R2) hnm heps heps1
    hK hKc hball hfin (0 : Real) hE0 hS0 hSbound hSloose hSE hQ hop htau hmixError
    (perPhase_canonical_hexact hn hR2 hK hKc hball hfin hKR)

/-- **§6's `hphaseMoment` binder, discharged.**  This is exactly the fifth conjunct above,
and its statement is character for character the `hphaseMoment` binder of
`exists_slowOneRunCertificate_canonical_perPhase` at
`E := perPhaseExpSharp n R`.  Together with the four binders beside it, §6 is reachable. -/
theorem perPhase_canonical_hphaseMoment
    (hn : 21 ≤ n) {eps R R2 : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hnm : (n : Real) ≤
      ((Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 : Nat) : Real) + 1)
    (hR2 : R ^ 2 ≤ R2)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n)
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
      (perPhaseRuntimeSamples n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
      (q := perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (perPhase_canonical_hq0 hn R2 eps R)
      (Ttc.CVSlowOneRunValid.canonical_hs0 hn) K hK 0 slowReferenceWarm
      (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
      (perPhaseBoundSqGen n (perPhaseExpSharp n R))) :
    ∀ j, ∫ omega,
          (slowClippedPositiveEmpiricalFamily
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      perPhaseFactor n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) j *
        (∫ omega, slowClippedPositiveEmpiricalFamily
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2 :=
  (perPhase_canonical_momentBinders_sharp hn heps heps1 hnm hR2 hK hKc hball hfin
    hKR hQ).2.2.2.2

#print axioms perPhase_canonical_hexact
#print axioms perPhase_canonical_hR2
#print axioms perPhase_canonical_momentBinders_sharp
#print axioms perPhase_canonical_hphaseMoment

/-- **§6's `hsteps` binder, at the literal per-phase canonical schedule.**  §3b's envelope
instantiated at the schedule §6 actually declares: the `n`-aware radius `perPhaseQ`, the
schedule accuracy `eps`, and the combined P1 + P2 exponent bound `B = exp (8 R²)`
(§1's `perPhaseExpSharp_le`, dimension-free).  Its conclusion is character for character
§6's `hsteps` binder at `T := ⌈perPhaseStepsEnvelope …⌉₊ + 1`, which is what closes the
second gap at the place it actually bites. -/
theorem perPhase_canonical_hsteps
    (hn : 21 ≤ n) {eps R R2 : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    ∀ i, i < Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 →
      slowCanonicalSteps slowReferenceWarm n
        (perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
        (slowSourceInitialVariance n) K
        (scoreAwareRetries (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
          (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
          (perPhaseBoundSqGen n (perPhaseExpSharp n R)))
        (scoreAwareEta (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
          (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
          (perPhaseBoundSqGen n (perPhaseExpSharp n R)))
        (scoreAwareZeta (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2 + 1)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) (eps / 2)
          (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
          (perPhaseBoundSqGen n (perPhaseExpSharp n R)))
        i 0 ≤
      ⌈perPhaseStepsEnvelope n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
          (perPhaseRuntimeSamples n
            (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps)
          (perPhaseQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
            (perPhaseRuntimeSamples n
              (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
          eps (Real.exp (8 * R ^ 2))⌉₊ + 1 := by
  intro i hi
  have hn1 : 1 ≤ n := by omega
  exact slowCanonicalSteps_perPhase_le hn1 _ _
    (lt_of_lt_of_le (by norm_num) (four_le_perPhaseQ hn1 _ _ eps R)) heps heps1
    (fun j ↦ perPhaseExpSharp_pos j) (fun j ↦ perPhaseExpSharp_le hn1 j)
    hK hball hfin hi

#print axioms perPhase_canonical_hsteps

end Ttc.CVPerPhaseFrontier

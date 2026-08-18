/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVPerPhaseMomentBundle
import Ttc.Exec.CVSlowUniformShareBounds
import Ttc.Exec.CVSharpFrontier

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

so that `slack / (3 · boundSq) = 2 r² / ((9n + 24) · (E i)²)`, against the current
schedule's `r² / (18 · exp (R²/(2 σ_i))²)`.  The retry cap and deadline payload depend on
the share only *logarithmically*, so at the same exponent that costs an additive
`log₂((9n+24)/36)` (§7 proves this), while `k` drops by a factor `n`.

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

/-- The schedule's mixing slack at the per-phase family: `(2/n) · r²`. -/
noncomputable def perPhaseSlack (n chainLength : Nat) (K : Set (State n)) : Nat → Real :=
  relativePhaseSlack chainLength
    (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (perPhaseC n)

theorem perPhaseSlack_pos {n chainLength : Nat} (hn : 1 ≤ n)
    {K : Set (State n)} (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : Nat) :
    0 < perPhaseSlack n chainLength K i := by
  unfold perPhaseSlack
  exact relativePhaseSlack_pos
    (slowSourceSigmaSq_pos hn (slowSourceInitialVariance_pos hn)) hball hfin
    (one_lt_perPhaseC hn) i

/-- The literal closed form of the slack: `(2/n) · r²`. -/
theorem perPhaseSlack_eq {n chainLength : Nat} (K : Set (State n)) (i : Nat) :
    perPhaseSlack n chainLength K i =
      (2 / (n : Real)) *
        (chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i + 1) /
          chain chainLength (slowSourceSigmaSq n (slowSourceInitialVariance n)) K i) ^ 2 := by
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

`slack i / (3 · boundSq i) = ((2/n) r²) / (3 (E i)² (3 + 8/n)) = 2 r² / ((9n + 24) (E i)²)`
with `r ≥ 1`, so any uniform upper bound `B` on `E` gives the single floor

`min (blockShare m k eps) (2 / ((9n + 24) B²))`.

At the standard exponent `B = exp (R²/(2 s0)) = exp (8 n R²)`; at the sharp exponent
`B = exp (8 R²)`, dimension-free, exactly as in `Ttc.CVSharpUniformParameters`. -/

/-- One lower share valid simultaneously at every slow phase, at the per-phase
slack/boundSq pair with per-phase exponents bounded by `B`. -/
noncomputable def perPhaseShareFloorGen (n m k : Nat) (eps B : Real) : Real :=
  min (blockShare m k eps) (2 / ((9 * (n : Real) + 24) * B ^ 2))

theorem perPhaseShareFloorGen_pos {n m k : Nat} {eps B : Real} (hn : 1 ≤ n)
    (heps : 0 < eps) (hB : 0 < B) : 0 < perPhaseShareFloorGen n m k eps B := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  unfold perPhaseShareFloorGen
  refine lt_min (blockShare_pos heps) ?_
  have hden : (0 : Real) < (9 * (n : Real) + 24) * B ^ 2 := by positivity
  positivity

theorem perPhaseShareFloorGen_lt_one {n m k : Nat} {eps B : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) : perPhaseShareFloorGen n m k eps B < 1 :=
  (min_le_left _ _).trans_lt (blockShare_lt_one heps heps1)

theorem perPhaseShareFloorGen_nonneg {n m k : Nat} {eps B : Real} (hn : 1 ≤ n)
    (hB : 0 < B) : 0 ≤ perPhaseShareFloorGen n m k eps B := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  unfold perPhaseShareFloorGen blockShare Ttc.CVCorrected.correctedNu
  refine le_min (by positivity) ?_
  have hden : (0 : Real) < (9 * (n : Real) + 24) * B ^ 2 := by positivity
  positivity

/-- The arithmetic behind the floor: at `C = 1 + 2/N` the score-aware share's exponential
branch is `2 r² / ((9N + 24) e²)`, which `2 / ((9N + 24) B²)` is below whenever `r ≥ 1`,
`0 < e ≤ B`. -/
theorem perPhase_share_branch_arith {N r e B : Real}
    (hN : 0 < N) (hr : 1 ≤ r) (he0 : 0 < e) (heB : e ≤ B) :
    2 / ((9 * N + 24) * B ^ 2) ≤
      (2 / N * r ^ 2) / (3 * (e ^ 2 * (3 + 8 / N))) := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hB0 : (0 : Real) < B := lt_of_lt_of_le he0 heB
  have he2 : e ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ he0.le heB 2
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hc : (0 : Real) < 18 + 48 / N := by positivity
  have hDA : (0 : Real) < (9 * N + 24) * B ^ 2 := by positivity
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
    _ = 2 / N * r ^ 2 * ((9 * N + 24) * B ^ 2) := by
      field_simp
      ring

/-- **The crux of §1.**  At the per-phase slack/boundSq pair the score-aware share of
every slow phase is bounded below by the single floor
`min (blockShare m k eps) (2 / ((9n + 24) B²))`. -/
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
    hdbs hbs (hSE i) hmoment hetaSq (scoreAwareMeanEta_nonneg m k eps)

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
    (0 : Real) < slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (perPhaseRuntimeSamples n
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R :=
  lt_of_lt_of_le (by norm_num) (four_le_slowUniformQ (by omega : 1 ≤ n) _ _ eps R)

theorem perPhase_canonical_isProbabilityMeasure_slowStationaryTail
    (hn : 21 ≤ n) {R2 eps R : Real} {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K) (j : Nat) :
    IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) :=
  isProbabilityMeasure_slowStationaryTail (by omega) (perPhase_canonical_hq0 hn R2 eps R)
    (Ttc.CVSlowOneRunValid.canonical_hs0 hn) hK hKc hball
    (fun r ↦ one_le_slow_radius (by omega)
      (four_le_slowUniformQ (by omega : 1 ≤ n) _ _ eps R) (by rfl) r) j

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
      (q := slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
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
        (slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
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
            (q := slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
              (perPhaseRuntimeSamples n
                (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
            (eps := eps / 2) (s0 := slowSourceInitialVariance n)
            (perPhase_canonical_hq0 hn R2 eps R)
            (Ttc.CVSlowOneRunValid.canonical_hs0 hn) K hK 0 slowReferenceWarm
            (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
            (perPhaseBoundSqGen n E))
          (by
            letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
                (slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
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
      (slowUniformQ n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n
          (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) := fun j ↦
    perPhase_canonical_isProbabilityMeasure_slowStationaryTail hn hK hKc hball j
  have hq4 : (4 : Real) ≤ slowUniformQ n
      (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2)
      (perPhaseRuntimeSamples n
        (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) eps) eps R :=
    four_le_slowUniformQ hn1 _ _ eps R
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
    (slowUniformMeanTailFloor_pos heps)
    (slowUniformQ_rAware n _ _ eps R)
    (fun i ↦ slowUniformQ_rad hn1 _ _ eps R i)
    (perPhaseSlack n (Ttc.CVSlowOneRunValid.slowCanonicalPhases n R2) K)
    (perPhaseBoundSqGen n E)
    hslack hbound (0 : Real) hQ _ rfl hop htau hmixError rfl rfl
    hE0 hS0 hSbound hSloose hSE
    (fun i ↦ slowUniformMeanTailFloor_le_meanBudget hn1 heps hK hball hfin (i : Nat))
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
  `(9n + 24)/36`, and the retry cap therefore grows by at most an additive
  `16 ⌈log₂((9n + 24)/36)⌉` — logarithmic in `n` against a multiplicative `n` saving in the
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
below the one the frontier currently forces by *exactly* the factor `(9n + 24)/36`. -/
theorem perPhaseShareFloor_ge_ratio {n : Nat} (hn : 2 ≤ n) (m k : Nat) {eps : Real}
    (heps : 0 < eps) (R : Real) :
    Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
        (slowSourceInitialVariance n) ≤
      ((9 * (n : Real) + 24) / 36) * perPhaseShareFloor n m k eps R := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hc1 : (1 : Real) ≤ (9 * (n : Real) + 24) / 36 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 36)]
    linarith
  have hd0 : (0 : Real) < 9 * (n : Real) + 24 := by linarith
  have hB0 : (0 : Real) ≤ blockShare m k eps := (blockShare_pos heps).le
  have hE0 : (0 : Real) < Real.exp (8 * (n : Real) * R ^ 2) ^ 2 := by positivity
  have hcy : ((9 * (n : Real) + 24) / 36) *
      (2 / ((9 * (n : Real) + 24) * Real.exp (8 * (n : Real) * R ^ 2) ^ 2)) =
      1 / (18 * Real.exp (8 * (n : Real) * R ^ 2) ^ 2) := by
    field_simp
    ring
  unfold Ttc.CVSlowUniformShareBounds.slowUniformShareFloor perPhaseShareFloor
    perPhaseShareFloorGen
  rw [slowSourceInitialVariance_exponent hn1 R]
  rcases min_cases (blockShare m k eps)
      (2 / ((9 * (n : Real) + 24) * Real.exp (8 * (n : Real) * R ^ 2) ^ 2)) with
    ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]
    exact (min_le_left _ _).trans (le_mul_of_one_le_left hB0 hc1)
  · rw [h1, hcy]
    exact min_le_right _ _

/-- **The retry cap grows only additively in `log n`.**  At the same transport exponent the
per-phase retry cap exceeds the one the frontier currently forces by at most
`16 ⌈log₂((9n + 24)/36)⌉` — against a base of order `16 · 16 n R² / log 2`, i.e. nothing. -/
theorem perPhaseRetriesCap_le_add_log {n : Nat} (hn : 2 ≤ n) {m k : Nat} {eps : Real}
    (heps : 0 < eps) (R : Real) :
    perPhaseRetriesCap n m k eps R ≤
      Ttc.CVSlowUniformShareBounds.slowUniformRetriesCap m k eps R
        (slowSourceInitialVariance n) +
      16 * ⌈Real.logb 2 ((9 * (n : Real) + 24) / 36)⌉₊ := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hc1 : (1 : Real) ≤ (9 * (n : Real) + 24) / 36 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 36)]
    linarith
  have hc0 : (0 : Real) < (9 * (n : Real) + 24) / 36 := by linarith
  have hfloorU0 := Ttc.CVSlowUniformShareBounds.slowUniformShareFloor_pos
    (m := m) (k := k) (R := R) (s0 := slowSourceInitialVariance n) heps
  have hfloorP0 : 0 < perPhaseShareFloor n m k eps R :=
    perPhaseShareFloorGen_pos hn1 heps (by positivity)
  have hcmp := perPhaseShareFloor_ge_ratio hn m k heps R
  -- `1 / floorP ≤ c * (1 / floorU)`
  have hstep : 1 / (((9 * (n : Real) + 24) / 36) * perPhaseShareFloor n m k eps R) ≤
      1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
        (slowSourceInitialVariance n) :=
    one_div_le_one_div_of_le hfloorU0 hcmp
  have hinv : 1 / perPhaseShareFloor n m k eps R ≤
      ((9 * (n : Real) + 24) / 36) *
        (1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
          (slowSourceInitialVariance n)) := by
    have hrw : 1 / (((9 * (n : Real) + 24) / 36) * perPhaseShareFloor n m k eps R) =
        (1 / ((9 * (n : Real) + 24) / 36)) * (1 / perPhaseShareFloor n m k eps R) := by
      field_simp
    rw [hrw] at hstep
    have := mul_le_mul_of_nonneg_left hstep hc0.le
    calc
      1 / perPhaseShareFloor n m k eps R
          = ((9 * (n : Real) + 24) / 36) *
            ((1 / ((9 * (n : Real) + 24) / 36)) *
              (1 / perPhaseShareFloor n m k eps R)) := by
            field_simp
      _ ≤ ((9 * (n : Real) + 24) / 36) *
            (1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
              (slowSourceInitialVariance n)) := this
  have hlog : Real.logb 2 (1 / perPhaseShareFloor n m k eps R) ≤
      Real.logb 2 ((9 * (n : Real) + 24) / 36) +
        Real.logb 2 (1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
          (slowSourceInitialVariance n)) := by
    have hmono := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
      (by positivity) (by positivity)).2 hinv
    rw [Real.logb_mul (ne_of_gt hc0) (by positivity)] at hmono
    exact hmono
  have hceil : ⌈Real.logb 2 (1 / perPhaseShareFloor n m k eps R)⌉₊ ≤
      ⌈Real.logb 2 ((9 * (n : Real) + 24) / 36)⌉₊ +
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
  have hbig : (9 * (n : Real) + 24) / 36 ≤
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
    (by positivity : (0 : Real) < (9 * (n : Real) + 24) * Real.exp (8 * R ^ 2) ^ 2)]
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

end Ttc.CVPerPhaseFrontier

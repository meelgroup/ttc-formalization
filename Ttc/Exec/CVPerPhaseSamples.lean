/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVCorrectedRuntime
import Ttc.Exec.CVSlowGaussianPhaseMoment
import Ttc.Exec.CVSourceSampleCountAudit

/-!
# `n`-aware per-phase stream provisioning (P2)

## The question

The slow canonical estimator declares

  `Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps = ⌈100000·(m+1)/eps²⌉₊ + 1`

(`Ttc/Volume/CVCorrectedRuntime.lean:156`), i.e. `k ∝ m`.  With `m ≈ n·log(nR²)` this
makes `m·k = Θ(n²·log²/eps²)`, a factor `n` above what the variance analysis needs.
Is that factor removable?

## Step 1 — the audit

**Where `Ttc.CVCorrected.CorrectedSampleBudget` (`Ttc/Volume/CVCorrectedParameters.lean:42`)
is consumed.**  Its *entire* mathematical content is one prefix-product bound:

* `Ttc.CVCorrected.phaseMomentRatio_pow_le` (`Ttc/Volume/CVCorrectedParameters.lean:108`)
  turns the budget into `(1 + 8/k)^i ≤ 1 + eps²/6250` for `i ≤ m`.
* `Ttc.CVCorrected.prefixSecondMean_le_concrete` (`:144`) is its only caller.
* `Ttc.CVCorrected.corrected_parameter_bundle` (`:173`) uses the budget hypothesis `hk`
  at exactly two places — lines `199` and `247` — both of them
  `prefixSecondMean_le_concrete`.  Nothing else in the bundle sees `k`:
  `correctedAlpha` (`:29`) and `correctedNu` (`:32`) are `k`-free.
* Downstream, `Ttc.CVCorrected.corrected_lem_accuracy_concrete` (`:299`) takes the
  budget and the uniform `hratio : ∫ V_j² ≤ (1 + 8/k)·(∫ V_j)²` and passes both to the
  bundle.  The slow canonical chain supplies both from
  `Ttc.CVSlowCanonicalPhaseMomentPackage.corrected_factorEight_prefix_bundle`
  (`Ttc/Exec/CVSlowCanonicalPhaseMomentPackage.lean:186`).

**The shape of the constraint the recursion actually imposes.**  It is *per-phase*, not
aggregate.  `Ttc.CVSourceSampleCountAudit.weighted_phaseFactors_discharge_recursion_scalars`
(`Ttc/Exec/CVSourceSampleCountAudit.lean:102`) proves the recursion's two scalar
obligations from an arbitrary factor family `factor : ℕ → ℝ`, reading it only through

  `hprefix : ∀ i ≤ m, (1 + 2ν·α⁴·i) · prefixMomentRatio factor i ≤ 2`
  `hfinal  : (1 + 2ν·α⁴·m) · prefixMomentRatio factor m ≤ q·(1 - m/α)²`

with `prefixMomentRatio c i = ∏_{j<i} c (j+1)`
(`Arlib/Probability/AccuracySecondMoment.lean:232`).  So a per-phase variance factor
*can* be inserted; the aggregate `m/eps²` shape is not what the recursion needs.

**Is `8/k` a clipping artifact?**  No.  Its provenance is
`raw factor c` → `averaged 1 + (c-1)/k`
(`Ttc.CVIndependentStreamMoments.integral_streamAverage_sq_le`) →
`clipped c/(1 - 1/(2α))²` (`Ttc.CVSourceWeightedClipping.clipped_sq_moment_le_factor`,
`Ttc/Exec/CVSourceWeightedClipping.lean:33`, which is **generic in `c`**).  The `8`
comes from the *raw* factor `c = 2`, via
`Ttc.CVCorrectedClippingArithmetic.six_over_clipping_sq_le_eight_of_nearby` at `c = 7`
in the operational route and `c = 2` in the canonical one.  Clipping only inflates `c-1`
by a bounded constant; it does not create the `Θ(1)` per-phase term.

**Where the factor `n` is actually lost.**  At
`Ttc/Exec/CVSlowGaussianPhaseMoment.lean:53-57`.  The interior branch of
`slowSource_phaseScore_interior_sq_moment_le_two` (`:31`) obtains the *sharp* fixed-rate
factor `1 + 2/n` from `Arlib.GaussianCooling.coolLaw_sq_moment_le`
(`Arlib/Convexity/GaussianCooling/PhaseVar.lean:513`) and then relaxes it to `2` with
`2/n ≤ 1`.  That single relaxation, before any averaging or clipping, is the whole of
the over-provisioning.  The hybrid route never performs it: it keeps the sharp cold
factor `1 + 2/(k·n)` in `Ttc.CVHybridSchedule.phaseVarFactor`
(`Ttc/Volume/CVHybridVarianceBudget.lean:29`), only *relaxing* it to `1 + 8/k` when it
wants to reuse the uniform bundle
(`Ttc.CVHybridCorrected.phaseVarFactor_le_one_add_eight_div`,
`Ttc/Volume/CVHybridCorrectedAccuracy.lean:34`), and correspondingly declares the
`n`-aware count `Ttc.CVHybridSchedule.estimatorSamples`
(`Ttc/Volume/CVHybridParameters.lean:25`), which is `Θ((c/n + J)/eps²)`.

## Step 2 — the verdict and what is landed here

**The factor `n` is removable.**  The recursion admits per-phase factors, the sharp
per-phase factor at the slow route's rate `α = 1/n` is `1 + 2/n` (interior) and a
constant only at the single terminal phase, and the resulting budget is

  `PerPhaseSampleBudget n m k eps : 100000·(m + n) ≤ k·n·eps²`,

met by `perPhaseRuntimeSamples n m eps = ⌈100000·(m+n)/(n·eps²)⌉₊ + 1`.

Landed:

* `perPhaseFactor` / `perPhase_prefixMomentRatio_le` — the `n`-aware factor family and
  the prefix bound `≤ 1 + eps²/6250` the recursion consumes.
* `perPhaseRuntimeSamples`, `perPhaseRuntimeSamples_budget`,
  `perPhaseRuntimeSamples_saving` (`n·new ≤ 3·old` for `n ≤ m+1`) and
  `perPhaseRuntimeSamples_le_correctedRuntimeSamples`.
* `uniform_prefix_forces_k_ge` — the matching lower bound: the *uniform* `1 + 8/k` shape
  forces `k ≥ 50000·m/eps²` whatever the cooling rate, so the saving is genuinely due to
  sharpening the per-phase factor and not to looser arithmetic.
* `perPhaseSampleBudget_of_correctedSampleBudget` — the new budget is weaker than the old.
* `slowSource_phaseScore_sq_moment_sharp` — the sharp raw factor `1 + 2/n`, on the actual
  slow canonical schedule, i.e. `slowSource_phaseScore_interior_sq_moment_le_two` with
  the relaxation removed.
* `perPhaseRuntime_interior_clipping` / `perPhaseRuntime_terminal_clipping` — the
  clipping normalisation still fits at the *smaller* sample count (this could have
  failed: `correctedAlpha` is not shrunk along with `k`).
* `perPhase_recursion_scalars` — both scalar obligations of the corrected accuracy
  recursion, discharged at the `n`-aware budget with the `n`-aware factors.

## Scope, stated honestly (`CLAUDE.md` §11)

Nothing here rewires the slow canonical chain; no existing file is modified.  What
remains for full integration is re-instantiating the *stream and clipped moment bundles*
— `Ttc.CVSlowCanonicalMomentBinders.slowCanonical_momentBinders`
(`Ttc/Exec/CVSlowCanonicalMomentBinders.lean:281`) and the
`corrected_factorEight_prefix_bundle` it feeds — at `perPhaseFactor` instead of the
uniform `1 + 8/k`, together with the concrete-parameter lemmas that mention
`correctedRuntimeSamples` by name (notably
`Ttc.CVGaussianScoreAwareMeanBudget.scoreAwareMeanGamma_corrected_le_one`
(`Ttc/Exec/CVGaussianScoreAwareMeanBudget.lean:56`), whose proof extracts the m-scaled
`100000·(m+1) ≤ k` from the old budget — a lossy route, since the quantity it bounds is
`Θ(m²·ν/k)` with `ν = Θ(eps¹⁰/m⁵)`, but a real re-proof obligation).  Those are
existing-file changes outside this file's write scope.

**Regime caveat.**  The `n`-fold saving is claimed for `n ≤ m + 1`, which the canonical
slow schedule satisfies with room to spare (`m = slowCanonicalPhases n R2 ≈ n·log(nR²)`).
Outside that regime the `+ n` term dominates the budget and there is nothing to save.

## Semantic `def`s (`CLAUDE.md` §11)

`perPhaseFactor`, `PerPhaseSampleBudget` and `perPhaseRuntimeSamples` are closed-form
abbreviations and assert no property; everything claimed of them is proved below.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVPerPhaseSamples

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowGaussianPhaseMoment

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The `n`-aware per-phase relative second-moment factor family.

The split at `j = m` mirrors exactly the branch of
`Ttc.CVSlowGaussianPhaseMoment.slowSource_phaseScore_interior_sq_moment_le_two`: the
recursion's phase `j` is the schedule's phase `j - 1`, which is *interior*
(`(j-1)+1 < m`) precisely when `j < m`.  That index alignment is definitional —
`Ttc.CVRelativeMeanClippingAssembly.positiveScalarPhaseFamilyChainLength`
(`Ttc/Exec/CVRelativeMeanClippingAssembly.lean:289`) is
`| i + 1 => scalarPhaseScore chainLength sigmaSq K i`, and `prefixMomentRatio`,
`prefixSecondMean`, `prefixMean`, `phaseProduct` all read `c (j+1)` over
`Finset.range i`.  Interior phases at cooling rate `1/n` have raw
factor `1 + 2/n` (`Arlib.GaussianCooling.coolLaw_sq_moment_le`), hence averaged factor
`1 + 2/(n·k)`; the single terminal phase has raw factor `exp(R²/(2σ²)) ≤ 2`, hence
averaged factor `1 + 1/k`.  Both are relaxed here to the `8`-shape used by the existing
clipped assembly. -/
noncomputable def perPhaseFactor (n m k : Nat) (j : Nat) : Real :=
  if j < m then 1 + 8 / ((n : Real) * k) else 1 + 8 / (k : Real)

theorem perPhaseFactor_nonneg {n m k : Nat} (j : Nat) :
    0 ≤ perPhaseFactor n m k j := by
  unfold perPhaseFactor
  split <;> positivity

theorem one_le_perPhaseFactor {n m k : Nat} (j : Nat) :
    1 ≤ perPhaseFactor n m k j := by
  unfold perPhaseFactor
  split
  · have : (0 : Real) ≤ 8 / ((n : Real) * k) := by positivity
    linarith
  · have : (0 : Real) ≤ 8 / (k : Real) := by positivity
    linarith

/-! ## The prefix product of the per-phase factors -/

/-- **Every prefix read by the corrected recursion carries at most one terminal factor.**

`prefixMomentRatio c i = ∏_{j < i} c (j+1)` reads the factors `c 1, …, c i`, so for
`i ≤ m` exactly the last one (`j + 1 = m`, and only when `i = m`) is terminal. -/
theorem prefixMomentRatio_perPhaseFactor_le_pow {n m k i : Nat} (hi : i ≤ m) :
    prefixMomentRatio (perPhaseFactor n m k) i ≤
      (1 + 8 / ((n : Real) * k)) ^ m * (1 + 8 / (k : Real)) := by
  have hint0 : (0 : Real) ≤ 8 / ((n : Real) * k) := by positivity
  have hterm1 : (1 : Real) ≤ 1 + 8 / (k : Real) := by
    have : (0 : Real) ≤ 8 / (k : Real) := by positivity
    linarith
  have hbase : (1 : Real) ≤ 1 + 8 / ((n : Real) * k) := by linarith
  rcases lt_or_eq_of_le hi with hlt | heq
  · -- every factor read is interior
    have hall : ∀ j ∈ Finset.range i,
        perPhaseFactor n m k (j + 1) = 1 + 8 / ((n : Real) * k) := by
      intro j hj
      have hji : j < i := Finset.mem_range.mp hj
      unfold perPhaseFactor
      rw [if_pos (show j + 1 < m by omega)]
    have hprod : prefixMomentRatio (perPhaseFactor n m k) i =
        (1 + 8 / ((n : Real) * k)) ^ i := by
      unfold prefixMomentRatio
      rw [Finset.prod_congr rfl hall, Finset.prod_const, Finset.card_range]
    rw [hprod]
    have hmono : (1 + 8 / ((n : Real) * k)) ^ i ≤ (1 + 8 / ((n : Real) * k)) ^ m :=
      pow_le_pow_right₀ hbase hi
    nlinarith [pow_nonneg (by linarith : (0 : Real) ≤ 1 + 8 / ((n : Real) * k)) m]
  · -- the last factor read is the terminal one
    subst heq
    match i with
    | 0 =>
      simpa only [prefixMomentRatio_zero, pow_zero, one_mul] using hterm1
    | (M + 1) =>
      have hall : ∀ j ∈ Finset.range M,
          perPhaseFactor n (M + 1) k (j + 1) = 1 + 8 / ((n : Real) * k) := by
        intro j hj
        have hjM : j < M := Finset.mem_range.mp hj
        unfold perPhaseFactor
        rw [if_pos (show j + 1 < M + 1 by omega)]
      have hlast : perPhaseFactor n (M + 1) k (M + 1) = 1 + 8 / (k : Real) := by
        unfold perPhaseFactor
        rw [if_neg (show ¬ M + 1 < M + 1 by omega)]
      have hprod : prefixMomentRatio (perPhaseFactor n (M + 1) k) (M + 1) =
          (1 + 8 / ((n : Real) * k)) ^ M * (1 + 8 / (k : Real)) := by
        unfold prefixMomentRatio
        rw [Finset.prod_range_succ, Finset.prod_congr rfl hall, Finset.prod_const,
          Finset.card_range, hlast]
      rw [hprod]
      have hmono : (1 + 8 / ((n : Real) * k)) ^ M ≤ (1 + 8 / ((n : Real) * k)) ^ (M + 1) :=
        pow_le_pow_right₀ hbase (Nat.le_succ M)
      nlinarith

/-! ## The `n`-aware sample budget -/

/-- **The `n`-aware replacement for `Ttc.CVCorrected.CorrectedSampleBudget`.**

`CorrectedSampleBudget m k ε` is `100000·(m+1) ≤ k·ε²` — it contains no `n`, i.e. it is
provisioned as if every phase contributed an *absolute constant* relative variance.  At
the slow route's cooling rate `α = 1/n` the interior per-phase contribution is `Θ(1/n)`
(`Arlib.GaussianCooling.coolLaw_sq_moment_le` gives the raw factor `1 + 2/n`), and a
single terminal phase contributes a constant.  That is exactly the shape below:

  `100000·(m + n) ≤ k·n·ε²`,

i.e. `k ≳ (m/n + 1)/ε²` instead of `k ≳ m/ε²`. -/
def PerPhaseSampleBudget (n m k : Nat) (eps : Real) : Prop :=
  100000 * ((m : Real) + (n : Real)) ≤ (k : Real) * (n : Real) * eps ^ 2

/-- **The budget closes the prefix product.**  The `n`-aware budget forces every prefix
of the per-phase factors below the same `1 + ε²/6250` the corrected recursion consumes
(`Ttc.CVCorrected.prefixSecondMean_le_concrete`). -/
theorem perPhase_pow_mul_le {n m k : Nat} {eps : Real}
    (hn : 0 < n) (hk : 0 < k) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hbudget : PerPhaseSampleBudget n m k eps) :
    (1 + 8 / ((n : Real) * k)) ^ m * (1 + 8 / (k : Real)) ≤ 1 + eps ^ 2 / 6250 := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hmR : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have heps2 : (0 : Real) < eps ^ 2 := by positivity
  have heps2le : eps ^ 2 ≤ 1 := by nlinarith
  have hnk : (0 : Real) < (n : Real) * (k : Real) := mul_pos hnR hkR
  -- the exponent bound: `8m/(nk) + 8/k ≤ ε²/12500`
  have hexpArg : (m : Real) * (8 / ((n : Real) * k)) + 8 / (k : Real)
      ≤ eps ^ 2 / 12500 := by
    rw [PerPhaseSampleBudget] at hbudget
    have hkey : (m : Real) * (8 / ((n : Real) * k)) + 8 / (k : Real)
        = (8 * ((m : Real) + (n : Real))) / ((n : Real) * (k : Real)) := by
      field_simp
    rw [hkey, div_le_div_iff₀ hnk (by norm_num : (0 : Real) < 12500)]
    nlinarith
  have hint0 : (0 : Real) ≤ 8 / ((n : Real) * k) := by positivity
  have hterm0 : (0 : Real) ≤ 8 / (k : Real) := by positivity
  calc
    (1 + 8 / ((n : Real) * k)) ^ m * (1 + 8 / (k : Real))
        ≤ Real.exp ((m : Real) * (8 / ((n : Real) * k))) * Real.exp (8 / (k : Real)) := by
          apply mul_le_mul (one_add_pow_le_exp hint0 m)
            (by linarith [Real.add_one_le_exp (8 / (k : Real))])
            (by linarith) (Real.exp_pos _).le
    _ = Real.exp ((m : Real) * (8 / ((n : Real) * k)) + 8 / (k : Real)) := by
          rw [← Real.exp_add]
    _ ≤ Real.exp (eps ^ 2 / 12500) := Real.exp_le_exp.mpr hexpArg
    _ ≤ 1 + 2 * (eps ^ 2 / 12500) := by
          apply exp_le_one_add_two_mul (by positivity)
          nlinarith
    _ = 1 + eps ^ 2 / 6250 := by ring

/-- **The `n`-aware analogue of `Ttc.CVCorrected.phaseMomentRatio_pow_le`.**

This is the exact premise the corrected recursion consumes: see
`Ttc.CVSourceSampleCountAudit.weighted_phaseFactors_discharge_recursion_scalars`, whose
`hprefix`/`hfinal` obligations read only `prefixMomentRatio factor i`, and
`Ttc.CVCorrected.prefixSecondMean_le_concrete`, which uses `CorrectedSampleBudget` for
nothing else. -/
theorem perPhase_prefixMomentRatio_le {n m k i : Nat} {eps : Real}
    (hn : 0 < n) (hk : 0 < k) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hbudget : PerPhaseSampleBudget n m k eps) (hi : i ≤ m) :
    prefixMomentRatio (perPhaseFactor n m k) i ≤ 1 + eps ^ 2 / 6250 :=
  (prefixMomentRatio_perPhaseFactor_le_pow hi).trans
    (perPhase_pow_mul_le hn hk heps heps1 hbudget)

/-! ## The `n`-aware stream count -/

/-- **The `n`-aware replacement for `Ttc.CVCorrectedRuntime.correctedRuntimeSamples`.**

`correctedRuntimeSamples m eps = ⌈100000·(m+1)/eps²⌉₊ + 1` is `k ∝ m/eps²`; this is
`k ∝ (m/n + 1)/eps²`.  A closed-form abbreviation and nothing more: everything claimed
of it is proved below. -/
noncomputable def perPhaseRuntimeSamples (n m : Nat) (eps : Real) : Nat :=
  ⌈100000 * ((m : Real) + (n : Real)) / ((n : Real) * eps ^ 2)⌉₊ + 1

theorem perPhaseRuntimeSamples_pos (n m : Nat) (eps : Real) :
    0 < perPhaseRuntimeSamples n m eps := by
  simp [perPhaseRuntimeSamples]

/-- **The declared count meets the declared budget** — the analogue of
`Ttc.CVCorrectedRuntime.correctedRuntimeSamples_budget`. -/
theorem perPhaseRuntimeSamples_budget {n m : Nat} {eps : Real}
    (hn : 0 < n) (heps : 0 < eps) :
    PerPhaseSampleBudget n m (perPhaseRuntimeSamples n m eps) eps := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have he2 : (0 : Real) < eps ^ 2 := by positivity
  have hden : (0 : Real) < (n : Real) * eps ^ 2 := by positivity
  have hceil := Nat.le_ceil (100000 * ((m : Real) + (n : Real)) / ((n : Real) * eps ^ 2))
  rw [div_le_iff₀ hden] at hceil
  unfold PerPhaseSampleBudget perPhaseRuntimeSamples
  push_cast
  nlinarith

theorem perPhaseRuntimeSamples_cast_lt {n m : Nat} {eps : Real} :
    (perPhaseRuntimeSamples n m eps : Real)
      < 100000 * ((m : Real) + (n : Real)) / ((n : Real) * eps ^ 2) + 2 := by
  have harg : (0 : Real)
      ≤ 100000 * ((m : Real) + (n : Real)) / ((n : Real) * eps ^ 2) := by positivity
  have hceil := Nat.ceil_lt_add_one harg
  rw [perPhaseRuntimeSamples]
  push_cast
  linarith

/-! ## The quantified `n`-fold saving

The saving is claimed in the regime `n ≤ m + 1`, which the canonical slow schedule
satisfies with room to spare: there `m = slowCanonicalPhases n R2 ≈ n·log(nR²) ≥ n`.
Outside that regime the `+ n` term in the budget dominates and there is nothing to
save — indeed at `m = 0` the two counts agree up to constants. -/

/-- **The `n`-fold saving, quantified.**  `n · perPhaseRuntimeSamples ≤ 3 ·
correctedRuntimeSamples` whenever `n ≤ m+1`: the per-phase provisioning is smaller by a
factor `n/3`. -/
theorem perPhaseRuntimeSamples_saving {n m : Nat} {eps : Real}
    (hn : 0 < n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (n : Real) * (perPhaseRuntimeSamples n m eps : Real)
      ≤ 3 * (correctedRuntimeSamples m eps : Real) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hmR : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have he2 : (0 : Real) < eps ^ 2 := by positivity
  have he2le : eps ^ 2 ≤ 1 := by nlinarith
  have hden : (0 : Real) < (n : Real) * eps ^ 2 := by positivity
  have hP0 : (0 : Real) ≤ (perPhaseRuntimeSamples n m eps : Real) := Nat.cast_nonneg _
  have hC0 : (0 : Real) ≤ (correctedRuntimeSamples m eps : Real) := Nat.cast_nonneg _
  -- upper bound on the new count, denominators cleared
  have hPlt := perPhaseRuntimeSamples_cast_lt (n := n) (m := m) (eps := eps)
  have hPmul : (perPhaseRuntimeSamples n m eps : Real) * ((n : Real) * eps ^ 2)
      < 100000 * ((m : Real) + (n : Real)) + 2 * ((n : Real) * eps ^ 2) := by
    have hstep := mul_lt_mul_of_pos_right hPlt hden
    have hexp : (100000 * ((m : Real) + (n : Real)) / ((n : Real) * eps ^ 2) + 2)
        * ((n : Real) * eps ^ 2)
        = 100000 * ((m : Real) + (n : Real)) + 2 * ((n : Real) * eps ^ 2) := by
      field_simp
    linarith [hexp ▸ hstep]
  -- lower bound on the old count, denominators cleared
  have hClow : 100000 * ((m : Real) + 1) ≤ (correctedRuntimeSamples m eps : Real) * eps ^ 2 := by
    have h := correctedRuntimeSamples_budget (m := m) (eps := eps) heps
    rw [Ttc.CVCorrected.CorrectedSampleBudget] at h
    exact h
  -- `2n ≤ C`
  have h2n : 2 * (n : Real) ≤ (correctedRuntimeSamples m eps : Real) := by
    nlinarith
  -- multiply the target by `eps ^ 2` and cancel
  have hgoal : (n : Real) * (perPhaseRuntimeSamples n m eps : Real) * eps ^ 2
      ≤ 3 * (correctedRuntimeSamples m eps : Real) * eps ^ 2 := by
    nlinarith
  nlinarith

/-- **The new count never exceeds the old one** (for `n ≥ 3`, `n ≤ m+1`). -/
theorem perPhaseRuntimeSamples_le_correctedRuntimeSamples {n m : Nat} {eps : Real}
    (hn : 3 ≤ n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    perPhaseRuntimeSamples n m eps ≤ correctedRuntimeSamples m eps := by
  have hnR : (3 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hsav := perPhaseRuntimeSamples_saving (n := n) (m := m) (eps := eps)
    (by omega) hnm heps heps1
  have hP0 : (0 : Real) ≤ (perPhaseRuntimeSamples n m eps : Real) := Nat.cast_nonneg _
  have : (perPhaseRuntimeSamples n m eps : Real)
      ≤ (correctedRuntimeSamples m eps : Real) := by nlinarith
  exact_mod_cast this

/-! ## The saving is real: the uniform factor genuinely forces `k ≳ m/eps²`

The two statements below are the two-sided form of the audit's verdict.  The first shows
that the *uniform* `1 + 8/k` shape — the one `Ttc.CVCorrected.phaseMomentRatio_pow_le`
consumes — admits no `n`-aware improvement at all: it forces `k ≥ 50000·m/eps²`
regardless of the cooling rate.  The second shows the new budget is strictly weaker than
the old one, so nothing is lost by adopting it. -/

/-- **Lower bound for the uniform shape.**  If the uniform per-phase factor `1 + 8/k`
has to satisfy the corrected recursion's prefix constraint `(1+8/k)^m ≤ 1 + eps²/6250`,
then `k ≥ 50000·m/eps²` — i.e. `k ∝ m` is *forced*, and the factor `n` can only be
removed by sharpening the per-phase factor itself, which is exactly what
`perPhaseFactor` does. -/
theorem uniform_prefix_forces_k_ge {m k : Nat} {eps : Real} (hk : 0 < k)
    (h : (1 + 8 / (k : Real)) ^ m ≤ 1 + eps ^ 2 / 6250) :
    50000 * (m : Real) ≤ (k : Real) * eps ^ 2 := by
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have h8 : (0 : Real) ≤ 8 / (k : Real) := by positivity
  have hbern : 1 + (m : Real) * (8 / (k : Real)) ≤ (1 + 8 / (k : Real)) ^ m :=
    one_add_mul_le_pow (a := 8 / (k : Real)) (by linarith) m
  have hstep : (m : Real) * (8 / (k : Real)) ≤ eps ^ 2 / 6250 := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ hkR (by norm_num : (0 : Real) < 6250)] at hstep
  linarith

/-- **The new budget is weaker than the old one.**  For `2 ≤ n ≤ m+1`, every `k` meeting
`Ttc.CVCorrected.CorrectedSampleBudget` already meets `PerPhaseSampleBudget`; the
converse fails by a factor `n` (`perPhaseRuntimeSamples_saving`). -/
theorem perPhaseSampleBudget_of_correctedSampleBudget {n m k : Nat} {eps : Real}
    (hn : 2 ≤ n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (hbudget : Ttc.CVCorrected.CorrectedSampleBudget m k eps) :
    PerPhaseSampleBudget n m k eps := by
  have hnR : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hmR : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hkR : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
  have he2 : (0 : Real) ≤ eps ^ 2 := sq_nonneg eps
  rw [Ttc.CVCorrected.CorrectedSampleBudget] at hbudget
  unfold PerPhaseSampleBudget
  nlinarith [mul_nonneg hkR he2]

/-! ## Where the factor `n` is actually lost

`Ttc.CVSlowGaussianPhaseMoment.slowSource_phaseScore_interior_sq_moment_le_two`
(`Ttc/Exec/CVSlowGaussianPhaseMoment.lean:31`) proves the raw per-phase relative second
moment on the slow canonical schedule.  Its *interior* branch obtains the sharp
fixed-rate factor `1 + 2/n` from `Arlib.GaussianCooling.coolLaw_sq_moment_le`
(`Arlib/Convexity/GaussianCooling/PhaseVar.lean:513`) and then, at lines 53-57, relaxes
it to `2` using `2/n ≤ 1`.  *That single relaxation is where the factor `n` is thrown
away* — before any clipping, averaging, or budget arithmetic.

The theorem below is that lemma with the relaxation removed: the sharp factor is
dischargeable on the actual slow canonical schedule, with exactly the same hypotheses.
It is the machine-checked witness for the audit verdict. -/

/-- **The sharp raw per-phase factor on the slow canonical schedule.**  Interior phases
pay `1 + 2/n`, not `2`; only the single terminal phase pays a constant.

This is `Ttc.CVSlowGaussianPhaseMoment.slowSource_phaseScore_interior_sq_moment_le_two`
without the `1 + 2/n ≤ 2` relaxation, and it implies it (`if` branch `≤ 2` in both
cases, for `n ≥ 3`). -/
theorem slowSource_phaseScore_sq_moment_sharp
    {n : Nat} (hn : 3 ≤ n) {N s0 R : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hsN : s0 ≤ N) (hR2 : R ^ 2 ≤ N)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R) (i : Nat) :
    let m := slowSourcePhases n N s0 + 1
    let sigmaSq := slowSourceSigmaSq n s0
    ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2 ∂(coolLaw m sigmaSq K i) ≤
      (if i + 1 < m then 1 + 2 / (n : Real) else 2) *
        (∫ x, phaseScore m sigmaSq (interior K) i x
          ∂(coolLaw m sigmaSq K i)) ^ 2 := by
  dsimp only
  have hn1 : 1 ≤ n := by omega
  have hsigma : ∀ j, 0 < slowSourceSigmaSq n s0 j := slowSourceSigmaSq_pos hn1 hs0
  rw [integral_phaseScore_interior_sq_eq hKc, integral_phaseScore_interior_eq hKc]
  by_cases hi : i + 1 < slowSourcePhases n N s0 + 1
  · rw [if_pos hi]
    exact coolLaw_sq_moment_le hsigma hKc hK hball hfin hi hn
      (slowSourceSigmaSq_succ n s0 i)
  · rw [if_neg hi]
    have hterm : slowSourcePhases n N s0 + 1 ≤ i + 1 := not_lt.mp hi
    have hmIndex : slowSourcePhases n N s0 ≤ i := by omega
    have hterminal := target_le_slowSourceSigmaSq_terminal hn1 hN hs0 hsN
    have hmono := sigmaSq_mono_of_fixedRate hsigma (by omega : 0 < n)
      (slowSourceSigmaSq_succ n s0) hmIndex
    have hRsig : R ^ 2 ≤ slowSourceSigmaSq n s0 i :=
      hR2.trans (hterminal.trans hmono)
    have hraw := coolLaw_sq_moment_le_terminal_paper hsigma hK hball hfin hKR
      hterm hRsig
    exact hraw.trans (mul_le_mul_of_nonneg_right exp_half_le_two (sq_nonneg _))

/-! ## The clipping normalisation still fits at the smaller sample count

Averaging `k` independent streams turns a raw factor `c` into `1 + (c-1)/k`
(`Ttc.CVIndependentStreamMoments.integral_streamAverage_sq_le`), so the sharp raw
factors above become `1 + 2/(n·k)` (interior) and `1 + 1/k` (terminal).  Clipping at
level `correctedAlpha m eps` divides by `(1 - 1/(2α))²`
(`Ttc.CVSourceWeightedClipping.clippedFactor`, which is generic in the factor).  The
lemmas below check that the `8`-shape of `perPhaseFactor` absorbs that division *at the
new, smaller sample count* — the one place where shrinking `k` could have broken the
existing assembly, since `correctedAlpha` is not shrunk with it. -/

/-- Generic clipping absorption: a raw-averaged factor `1 + 2/x` survives division by
`(1 - 1/(2α))²` inside `1 + 8/x`, provided `x ≤ 5α` and `α ≥ 10`.  This is the sharp
analogue of
`Ttc.CVCorrectedClippingArithmetic.six_over_clipping_sq_le_eight_of_nearby`. -/
theorem two_over_clipping_sq_le_eight_of_nearby {x alpha : Real}
    (halpha : 10 ≤ alpha) (hx : 0 < x) (hxa : x ≤ 5 * alpha) :
    (1 + 2 / x) / (1 - 1 / (2 * alpha)) ^ 2 ≤ 1 + 8 / x := by
  have ha0 : 0 < alpha := by linarith
  have hd0 : 0 < 1 - 1 / (2 * alpha) := by
    rw [sub_pos, div_lt_one (by positivity)]
    linarith
  rw [div_le_iff₀ (sq_pos_of_pos hd0)]
  field_simp
  nlinarith [sq_nonneg (x - alpha), mul_pos hx ha0, sq_nonneg alpha]

/-- The truncation level `correctedAlpha m eps` still dominates `n · k` at the new
sample count, for `n ≤ m + 1`. -/
theorem nmul_perPhaseRuntimeSamples_le_five_correctedAlpha {n m : Nat} {eps : Real}
    (hn : 0 < n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (n : Real) * (perPhaseRuntimeSamples n m eps : Real) ≤ 5 * correctedAlpha m eps := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hmR : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have he2 : (0 : Real) < eps ^ 2 := by positivity
  have he2le : eps ^ 2 ≤ 1 := by nlinarith
  have hden : (0 : Real) < (n : Real) * eps ^ 2 := by positivity
  have hPlt := perPhaseRuntimeSamples_cast_lt (n := n) (m := m) (eps := eps)
  have hPmul : (perPhaseRuntimeSamples n m eps : Real) * ((n : Real) * eps ^ 2)
      < 100000 * ((m : Real) + (n : Real)) + 2 * ((n : Real) * eps ^ 2) := by
    have hstep := mul_lt_mul_of_pos_right hPlt hden
    have hexp : (100000 * ((m : Real) + (n : Real)) / ((n : Real) * eps ^ 2) + 2)
        * ((n : Real) * eps ^ 2)
        = 100000 * ((m : Real) + (n : Real)) + 2 * ((n : Real) * eps ^ 2) := by
      field_simp
    linarith [hexp ▸ hstep]
  have halpha : correctedAlpha m eps * eps ^ 2 = 100000 * ((m : Real) + 1) := by
    rw [correctedAlpha]
    field_simp
  -- compare after multiplying by `eps ^ 2`
  have hgoal : (n : Real) * (perPhaseRuntimeSamples n m eps : Real) * eps ^ 2
      ≤ 5 * correctedAlpha m eps * eps ^ 2 := by nlinarith
  nlinarith

/-- **The interior clipped factor at the new sample count is exactly the interior
`perPhaseFactor`.** -/
theorem perPhaseRuntime_interior_clipping {n m : Nat} {eps : Real}
    (hn : 0 < n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (1 + 2 / ((n : Real) * (perPhaseRuntimeSamples n m eps : Real))) /
        (1 - 1 / (2 * correctedAlpha m eps)) ^ 2 ≤
      1 + 8 / ((n : Real) * (perPhaseRuntimeSamples n m eps : Real)) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hPpos : (0 : Real) < (perPhaseRuntimeSamples n m eps : Real) := by
    exact_mod_cast perPhaseRuntimeSamples_pos n m eps
  refine two_over_clipping_sq_le_eight_of_nearby ?_ (by positivity) ?_
  · exact (show (10 : Real) ≤ 100000 by norm_num).trans
      (Ttc.CVCorrectedClippingArithmetic.correctedAlpha_ge_hundred_thousand
        (m := m) heps heps1)
  · exact nmul_perPhaseRuntimeSamples_le_five_correctedAlpha hn hnm heps heps1

/-- **The terminal clipped factor at the new sample count is bounded by the terminal
`perPhaseFactor`.** -/
theorem perPhaseRuntime_terminal_clipping {n m : Nat} {eps : Real}
    (hn : 0 < n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (1 + 2 / (perPhaseRuntimeSamples n m eps : Real)) /
        (1 - 1 / (2 * correctedAlpha m eps)) ^ 2 ≤
      1 + 8 / (perPhaseRuntimeSamples n m eps : Real) := by
  have hnR : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hPpos : (0 : Real) < (perPhaseRuntimeSamples n m eps : Real) := by
    exact_mod_cast perPhaseRuntimeSamples_pos n m eps
  refine two_over_clipping_sq_le_eight_of_nearby ?_ hPpos ?_
  · exact (show (10 : Real) ≤ 100000 by norm_num).trans
      (Ttc.CVCorrectedClippingArithmetic.correctedAlpha_ge_hundred_thousand
        (m := m) heps heps1)
  · have h := nmul_perPhaseRuntimeSamples_le_five_correctedAlpha hn hnm heps heps1
    nlinarith

/-! ## The corrected recursion's scalar obligations, at the `n`-aware budget

`Ttc.CVSourceSampleCountAudit.weighted_phaseFactors_discharge_recursion_scalars`
(`Ttc/Exec/CVSourceSampleCountAudit.lean:102`) shows the corrected accuracy recursion
consumes *only* `prefixMomentRatio factor i` — never a uniform factor.  Composing it
with the prefix bound above gives the full scalar bundle at the `n`-aware budget. -/

theorem prefixMomentRatio_perPhaseFactor_nonneg (n m k i : Nat) :
    0 ≤ prefixMomentRatio (perPhaseFactor n m k) i := by
  unfold prefixMomentRatio
  exact Finset.prod_nonneg fun j _ ↦ perPhaseFactor_nonneg _

/-- The `hprefix` obligation, at the concrete corrected scalars. -/
theorem perPhase_prefix_coefficient_le {n m k i : Nat} {eps : Real}
    (hn : 0 < n) (hk : 0 < k) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hbudget : PerPhaseSampleBudget n m k eps) (hi : i ≤ m) :
    (1 + 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (i : Real)) *
        prefixMomentRatio (perPhaseFactor n m k) i ≤ 2 := by
  have he2le : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg eps]
  have ha1 := one_le_correctedAlpha (m := m) heps heps1
  have hCi := correctedNu_alpha_four_mul_le (m := m) (r := i) heps
    (hi.trans (Nat.le_succ m))
  have hC0 : (0 : Real) ≤ 1 + 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (i : Real) := by
    have hterm : (0 : Real) ≤ 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (i : Real) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (correctedNu_nonneg (m := m) (ε := eps)))
          (pow_nonneg (le_trans (by norm_num) ha1) 4))
        (Nat.cast_nonneg i)
    linarith
  have hP := perPhase_prefixMomentRatio_le hn hk heps heps1 hbudget hi
  have hP0 := prefixMomentRatio_perPhaseFactor_nonneg n m k i
  calc
    _ ≤ (1 + eps ^ 2 / 50000) * (1 + eps ^ 2 / 6250) :=
        mul_le_mul (by linarith) hP hP0 (by positivity)
    _ ≤ 2 := by nlinarith [sq_nonneg (eps ^ 2)]

/-- The `hfinal` obligation, at the concrete corrected scalars. -/
theorem perPhase_prefix_final_le {n m k : Nat} {eps : Real}
    (hn : 0 < n) (hk : 0 < k) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hbudget : PerPhaseSampleBudget n m k eps) :
    (1 + 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (m : Real)) *
        prefixMomentRatio (perPhaseFactor n m k) m ≤
      correctedQ eps * (1 - (m : Real) / correctedAlpha m eps) ^ 2 := by
  have he2 : (0 : Real) < eps ^ 2 := by positivity
  have he2le : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg eps]
  have ha1 := one_le_correctedAlpha (m := m) heps heps1
  have ht := phase_div_correctedAlpha_le (m := m) heps
  have hCm := correctedNu_alpha_four_mul_le (m := m) (r := m) heps (Nat.le_succ m)
  have hC0 : (0 : Real) ≤ 1 + 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (m : Real) := by
    have hterm : (0 : Real) ≤ 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (m : Real) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (correctedNu_nonneg (m := m) (ε := eps)))
          (pow_nonneg (le_trans (by norm_num) ha1) 4))
        (Nat.cast_nonneg m)
    linarith
  have hP := perPhase_prefixMomentRatio_le hn hk heps heps1 hbudget (le_refl m)
  have hP0 := prefixMomentRatio_perPhaseFactor_nonneg n m k m
  have ht0 : (0 : Real) ≤ (m : Real) / correctedAlpha m eps := by positivity
  have hsquare : (1 - eps ^ 2 / 100000) ^ 2 ≤ (1 - (m : Real) / correctedAlpha m eps) ^ 2 := by
    apply (sq_le_sq₀ (by nlinarith) (by nlinarith)).2
    nlinarith
  have hnum : (1 + eps ^ 2 / 50000) * (1 + eps ^ 2 / 6250) ≤
      (1 + eps ^ 2 / 1000) * (1 - eps ^ 2 / 100000) ^ 2 := by
    nlinarith [sq_nonneg (eps ^ 2), mul_nonneg (sq_nonneg eps) (sub_nonneg.mpr he2le)]
  calc
    _ ≤ (1 + eps ^ 2 / 50000) * (1 + eps ^ 2 / 6250) :=
        mul_le_mul (by linarith) hP hP0 (by positivity)
    _ ≤ (1 + eps ^ 2 / 1000) * (1 - eps ^ 2 / 100000) ^ 2 := hnum
    _ ≤ correctedQ eps * (1 - (m : Real) / correctedAlpha m eps) ^ 2 := by
        rw [correctedQ]
        exact mul_le_mul_of_nonneg_left hsquare (by positivity)

variable {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}

/-- **P2, landed.**  Both scalar obligations of the corrected accuracy recursion hold at
the `n`-aware budget with the `n`-aware per-phase factors.

This is the exact analogue of the two nontrivial conclusions of
`Ttc.CVCorrected.corrected_parameter_bundle` (`AccuracyLowerScalar` and the final
relative second moment), with `Ttc.CVCorrected.CorrectedSampleBudget` — which forces
`k ≳ m/eps²` (`uniform_prefix_forces_k_ge`) — replaced by `PerPhaseSampleBudget`, which
needs only `k ≳ (m/n + 1)/eps²`. -/
theorem perPhase_recursion_scalars [MeasureTheory.IsProbabilityMeasure mu]
    (V : Nat → Omega → Real) {n m k : Nat} {eps : Real}
    (hn : 0 < n) (hk : 0 < k) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hbudget : PerPhaseSampleBudget n m k eps)
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hratio : ∀ j, (∫ omega, (V j omega) ^ 2 ∂mu) ≤
      perPhaseFactor n m k j * (∫ omega, V j omega ∂mu) ^ 2) :
    AccuracyLowerScalar mu V (correctedAlpha m eps) (correctedNu m eps) m ∧
      (1 + 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (m : Real)) *
          prefixSecondMean mu V m ≤
        correctedQ eps * (1 - (m : Real) / correctedAlpha m eps) ^ 2 *
          (prefixMean mu V m) ^ 2 :=
  Ttc.CVSourceSampleCountAudit.weighted_phaseFactors_discharge_recursion_scalars
    (mu := mu) V (perPhaseFactor n m k)
    (correctedNu_nonneg (m := m) (ε := eps)) hV0
    (fun j ↦ perPhaseFactor_nonneg j) hratio
    (corrected_covariance_scalar (m := m) heps heps1)
    (fun _ hi ↦ perPhase_prefix_coefficient_le hn hk heps heps1 hbudget hi)
    (perPhase_prefix_final_le hn hk heps heps1 hbudget)

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms perPhaseFactor_nonneg
#print axioms one_le_perPhaseFactor
#print axioms prefixMomentRatio_perPhaseFactor_le_pow
#print axioms perPhase_pow_mul_le
#print axioms perPhase_prefixMomentRatio_le
#print axioms perPhaseRuntimeSamples_pos
#print axioms perPhaseRuntimeSamples_budget
#print axioms perPhaseRuntimeSamples_cast_lt
#print axioms perPhaseRuntimeSamples_saving
#print axioms perPhaseRuntimeSamples_le_correctedRuntimeSamples
#print axioms uniform_prefix_forces_k_ge
#print axioms perPhaseSampleBudget_of_correctedSampleBudget
#print axioms slowSource_phaseScore_sq_moment_sharp
#print axioms two_over_clipping_sq_le_eight_of_nearby
#print axioms nmul_perPhaseRuntimeSamples_le_five_correctedAlpha
#print axioms perPhaseRuntime_interior_clipping
#print axioms perPhaseRuntime_terminal_clipping
#print axioms prefixMomentRatio_perPhaseFactor_nonneg
#print axioms perPhase_prefix_coefficient_le
#print axioms perPhase_prefix_final_le
#print axioms perPhase_recursion_scalars

end Ttc.CVPerPhaseSamples

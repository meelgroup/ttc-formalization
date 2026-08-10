/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Runtime
import Ttc.Coupling.Family

/-!
# The absorption loop's level tail, and the level budget

`alg:ttc` lines 39–42 halve the rate until `Nᵢ + |𝒳| ≤ Thresh`.  `Ttc.absorbLevel`
models that loop by its **exit level**, and `Model/Pseudocode` deviation (b) records
what happens when no such level exists: `Nat.sInf ∅ = 0`, the loop "does not move",
and nothing can be said about the Poisson draw handed to `GenerateSamples`.  That is
why `Ttc.runCost_le` carries `Ttc.Terminates` and why `Model/Theorem`'s runtime
conjunct carries `Ttc.ttcTerminates`.

This file removes that hypothesis, almost surely, and prices the interrupt
truncation that would remove it pointwise.

## The one fact that does the work

Under `Ttc.trajLaw θ` the level-`j` count vector is `⨂ₛ Pois(θₛ/2ʲ)`
(`Ttc.map_trajLaw_eval`), so

* `Pr[ ω j = 0 ] = e^(−Λ/2ʲ)` with `Λ = ∑ₛ θₛ` (`Ttc.trajLaw_eval_eq_zero`), hence
  `Pr[ ω j ≠ 0 ] ≤ Λ/2ʲ` (`Ttc.trajLaw_eval_ne_zero_le`);
* summing the geometric series, `Pr[ ∃ j ≥ Lb, ω j ≠ 0 ] ≤ 2Λ/2^Lb`
  (`Ttc.trajLaw_exists_ne_zero_le`).

Both summands of the absorption guard — `Ttc.trajPois` and the cardinality of
`Ttc.trajThin` — are read off the level's count vector, so **at a level the family
has left empty the guard fails** (`Ttc.not_guard_of_eval_eq_zero`), needing only
`0 ≤ Thresh`.  Nothing about the cube, the entry state or the entry level enters.

## The level budget

`Ttc.BudgetMet P O Lb` says every absorption loop — at *any* cube, from *any* entry
state, at *any* entry level — exits within `Lb` levels of where it started.  It is a
property of the oracle answers, never assumed: on `Ttc.Vanish L Lb` (the family is
empty from level `Lb` on) it is **proved** (`Ttc.budgetMet_of_vanish`), and

```
Pr[ ¬ BudgetMet P (trajOracles …) Lb ] ≤ 2Λ / 2^Lb        (Ttc.trajLaw_not_budgetMet_le)
```

so `Lb ≥ log₂(2Λ/δ')` buys the budget for a `δ'` slice.  On the event the truncation
is **inert**: `Ttc.absorbLevel_le_of_budgetMet` shows the untruncated exit level is
already at most `j₁ + Lb`.

## What follows: the `∀ᵐ` cost bound is unconditional

`2Λ/2^Lb → 0`, so `Ttc.Terminates` holds `trajLaw`-almost surely
(`Ttc.trajLaw_ae_terminates`) — with no truncation, no budget and no hypothesis on
the run — and `Ttc.trajLaw_ae_runCost_le` is `thm:runtime`'s bound
`m·(C_vol + C_sample·Thresh)` with the `Ttc.Terminates` guard gone.

The **pointwise** `∀ ω` bound is a different matter and is genuinely false: `ω`
ranges over all of `ℕ → Fin L → ℕ`, and a trajectory that is constantly a large
vector keeps the guard true at every level, so `Ttc.absorbLevel` degenerates to the
entry level and the Poisson draw handed to `GenerateSamples` is unbounded.  Only an
interrupt truncation can fix that, and `Ttc.trajLaw_not_budgetMet_le` is the tail
bound such a truncation costs.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Multiset
open scoped NNReal ENNReal

variable {L : ℕ}

/-- **The level-`j` count vector is the zero vector with probability `e^(−Λ/2ʲ)`.** -/
theorem trajLaw_eval_eq_zero {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (j : ℕ) :
    trajLaw θ {ω : ℕ → (Fin L → ℕ) | ω j = 0}
      = ENNReal.ofReal (Real.exp (-((∑ s, θ s) / 2 ^ j))) := by
  have hmeas : MeasurableSet ({0} : Set (Fin L → ℕ)) := MeasurableSet.singleton 0
  have hpre : {ω : ℕ → (Fin L → ℕ) | ω j = 0}
      = (fun ω : ℕ → (Fin L → ℕ) => ω j) ⁻¹' {0} := rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply j) hmeas, map_trajLaw_eval hθ j,
    levelLaw, pi_poisson_singleton]
  congr 1
  have hpt : ∀ s : Fin L, poissonPMF (((θ s / 2 ^ j).toNNReal : ℝ)) ((0 : Fin L → ℕ) s)
      = Real.exp (-(θ s / 2 ^ j)) := by
    intro s
    have hs : (0:ℝ) ≤ θ s / 2 ^ j := by have := hθ s; positivity
    rw [Pi.zero_apply, poissonPMF_def, Real.coe_toNNReal _ hs]
    simp
  rw [Finset.prod_congr rfl (fun s _ => hpt s), ← Real.exp_sum]
  congr 1
  simp [Finset.sum_div]

/-- **The level-`j` count vector is nonzero with probability at most `Λ/2ʲ`.** -/
theorem trajLaw_eval_ne_zero_le {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (j : ℕ) :
    trajLaw θ {ω : ℕ → (Fin L → ℕ) | ω j ≠ 0}
      ≤ ENNReal.ofReal ((∑ s, θ s) / 2 ^ j) := by
  have hΛ : (0 : ℝ) ≤ ∑ s, θ s := Finset.sum_nonneg fun s _ => hθ s
  have hx : (0 : ℝ) ≤ (∑ s, θ s) / 2 ^ j := by positivity
  have hmeas : MeasurableSet {ω : ℕ → (Fin L → ℕ) | ω j = 0} :=
    (measurable_pi_apply j) (MeasurableSet.singleton 0)
  have hcompl : {ω : ℕ → (Fin L → ℕ) | ω j ≠ 0} = {ω : ℕ → (Fin L → ℕ) | ω j = 0}ᶜ := rfl
  rw [hcompl, measure_compl hmeas (measure_ne_top _ _), trajLaw_eval_eq_zero hθ j, measure_univ]
  -- `1 − e^(−x) ≤ x` for `x ≥ 0`, in `ℝ≥0∞`
  refine tsub_le_iff_right.2 ?_
  have hexp : (1 : ℝ) ≤ (∑ s, θ s) / 2 ^ j + Real.exp (-((∑ s, θ s) / 2 ^ j)) := by
    have := Real.add_one_le_exp (-((∑ s, θ s) / 2 ^ j))
    linarith
  calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    _ ≤ ENNReal.ofReal ((∑ s, θ s) / 2 ^ j + Real.exp (-((∑ s, θ s) / 2 ^ j))) :=
        ENNReal.ofReal_le_ofReal hexp
    _ = ENNReal.ofReal ((∑ s, θ s) / 2 ^ j)
          + ENNReal.ofReal (Real.exp (-((∑ s, θ s) / 2 ^ j))) :=
        ENNReal.ofReal_add hx (Real.exp_nonneg _)

/-- **The level process is eventually zero, quantitatively**: the probability that
*some* level at or above `Lb` still carries a point is at most `2Λ/2^Lb`. -/
theorem trajLaw_exists_ne_zero_le {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (Lb : ℕ) :
    trajLaw θ {ω : ℕ → (Fin L → ℕ) | ∃ j, Lb ≤ j ∧ ω j ≠ 0}
      ≤ ENNReal.ofReal (2 * (∑ s, θ s) / 2 ^ Lb) := by
  have hΛ : (0 : ℝ) ≤ ∑ s, θ s := Finset.sum_nonneg fun s _ => hθ s
  have hcover : {ω : ℕ → (Fin L → ℕ) | ∃ j, Lb ≤ j ∧ ω j ≠ 0}
      ⊆ ⋃ k : ℕ, {ω : ℕ → (Fin L → ℕ) | ω (Lb + k) ≠ 0} := by
    rintro ω ⟨j, hj, hne⟩
    exact Set.mem_iUnion.2 ⟨j - Lb, by simpa [Nat.add_sub_cancel' hj] using hne⟩
  refine le_trans (measure_mono hcover) ?_
  refine le_trans (measure_iUnion_le _) ?_
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [show (1 / 2 : ℝ) = ((2 : ℝ))⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  have hterm : ∀ k : ℕ, trajLaw θ {ω : ℕ → (Fin L → ℕ) | ω (Lb + k) ≠ 0}
      ≤ ENNReal.ofReal ((∑ s, θ s) / 2 ^ Lb) * (2 : ℝ≥0∞)⁻¹ ^ k := by
    intro k
    refine le_trans (trajLaw_eval_ne_zero_le hθ (Lb + k)) (le_of_eq ?_)
    have hrw : (∑ s, θ s) / 2 ^ (Lb + k) = ((∑ s, θ s) / 2 ^ Lb) * (1 / 2 : ℝ) ^ k := by
      rw [pow_add, ← div_div, one_div, inv_pow, div_eq_mul_inv]
    rw [hrw, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1 / 2), hhalf]
  refine le_trans (ENNReal.tsum_le_tsum hterm) (le_of_eq ?_)
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    show (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ from
      ENNReal.sub_eq_of_eq_add (by simp) (ENNReal.inv_two_add_inv_two).symm,
    inv_inv]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-! ## The absorption loop's exit level, on a vanishing trajectory -/

variable {n : ℕ} {ι : Type*}

/-- **A level whose count vector is `0` fails the absorption guard.** Both summands
of `alg:ttc` line 39's test are read off the level's count vector, so at a level the
family has left empty the test is `Thresh < 0 + 0`, which `0 ≤ Thresh` refutes. -/
theorem not_guard_of_eval_eq_zero {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (P : Params) (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    {ω : ℕ → (Fin L → ℕ)} (hT : 0 ≤ P.thresh) (i : ι) (lam : ℝ) (X : Multiset (Space n))
    (j₀ j' : ℕ) (hω : ω j' = 0) :
    ¬ P.thresh < ((trajOracles hpt vol covered mem ω).pois i j' lam : ℝ)
      + (card ((trajOracles hpt vol covered mem ω).thin j₀ j' X) : ℝ) := by
  have hp : (trajOracles hpt vol covered mem ω).pois i j' lam = 0 := by
    show trajPois (mem i) (ω j') = 0
    simp [trajPois, hω]
  have ht : card ((trajOracles hpt vol covered mem ω).thin j₀ j' X) = 0 := by
    show card (trajThin pt (ω j') X) = 0
    simp [trajThin, hω]
  rw [hp, ht]
  push_cast
  linarith

/-- **The trajectories on which every absorption loop exits within `Lb` extra
levels**: the level process is empty from level `Lb` on. -/
def Vanish (L Lb : ℕ) : Set (ℕ → (Fin L → ℕ)) := {ω | ∀ j, Lb ≤ j → ω j = 0}

/-- **`Ttc.Vanish` fails with probability at most `2Λ/2^Lb`.** -/
theorem trajLaw_compl_vanish_le {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (Lb : ℕ) :
    trajLaw θ (Vanish L Lb)ᶜ ≤ ENNReal.ofReal (2 * (∑ s, θ s) / 2 ^ Lb) := by
  have hset : (Vanish L Lb)ᶜ = {ω : ℕ → (Fin L → ℕ) | ∃ j, Lb ≤ j ∧ ω j ≠ 0} := by
    ext ω
    simp only [Vanish, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, exists_prop]
  rw [hset]
  exact trajLaw_exists_ne_zero_le hθ Lb

/-! ## The level budget

`Ttc.BudgetMet P O Lb` is the event that **every** absorption loop the run can
possibly perform — at any cube, from any entry state, at any entry level — exits
within `Lb` levels of where it started.  It is a property of the oracle answers, not
an assumption about them: `Ttc.budgetMet_of_vanish` proves it on `Ttc.Vanish`, and
`Ttc.trajLaw_not_budgetMet_le` bounds the probability that it fails. -/

/-- **The level budget is met**: every absorption loop finds a level at which the
guard fails within `Lb` levels of its entry level `j₁`. -/
def BudgetMet (P : Params) (O : Oracles n ι) (Lb : ℕ) : Prop :=
  ∀ (i : ι) (t : ℝ) (X : Multiset (Space n)) (j₀ j₁ : ℕ),
    ∃ j', j₁ ≤ j' ∧ j' ≤ j₁ + Lb ∧
      ¬ P.thresh < (O.pois i j' (t * (1 / 2 : ℝ) ^ j') : ℝ) + (card (O.thin j₀ j' X) : ℝ)

/-- **On `Ttc.Vanish`, the level budget `Lb` is met.** The level `j₁ + Lb` is at or
above `Lb`, so the family is empty there and the guard fails. -/
theorem budgetMet_of_vanish {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (P : Params) (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    {ω : ℕ → (Fin L → ℕ)} (hT : 0 ≤ P.thresh) {Lb : ℕ} (hω : ω ∈ Vanish L Lb) :
    BudgetMet P (trajOracles hpt vol covered mem ω) Lb := by
  intro i t X j₀ j₁
  exact ⟨j₁ + Lb, Nat.le_add_right _ _, le_rfl,
    not_guard_of_eval_eq_zero hpt P vol covered mem hT i _ X j₀ _
      (hω _ (Nat.le_add_left _ _))⟩

/-- **The level budget fails with probability at most `2Λ/2^Lb`.**

This is the tail bound the interrupt truncation costs: choosing
`Lb ≥ log₂(2Λ/δ')` makes it at most `δ'`.  Uniform over cubes, entry states and
entry levels — one event of the trajectory law covers the whole run. -/
theorem trajLaw_not_budgetMet_le {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (P : Params) (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (hT : 0 ≤ P.thresh) (Lb : ℕ) :
    trajLaw θ {ω : ℕ → (Fin L → ℕ) |
        ¬ BudgetMet P (trajOracles hpt vol covered mem ω) Lb}
      ≤ ENNReal.ofReal (2 * (∑ s, θ s) / 2 ^ Lb) := by
  refine le_trans (measure_mono ?_) (trajLaw_compl_vanish_le hθ Lb)
  intro ω hω
  exact fun hv => hω (budgetMet_of_vanish hpt P vol covered mem hT hv)

/-! ## What the budget buys: termination, and the exit level -/

/-- **The budget implies the absorption loop exits** — `Ttc.AbsorbExits`, the
hypothesis `thm:runtime` leaves unstated, for every cube and every entry state. -/
theorem absorbExits_of_budgetMet {P : Params} {O : Oracles n ι} {Lb : ℕ}
    (h : BudgetMet P O Lb) (i : ι) (t : ℝ) (X : Multiset (Space n)) (j₀ j₁ : ℕ) :
    AbsorbExits P O i t X j₀ j₁ := by
  obtain ⟨j', hj₁, _, hguard⟩ := h i t X j₀ j₁
  exact ⟨j', hj₁, hguard⟩

/-- **The budget bounds the exit level**: `Ttc.absorbLevel` never runs past
`j₁ + Lb`.  This is why truncating the loop at that level changes nothing on the
event — the honesty companion to the truncation. -/
theorem absorbLevel_le_of_budgetMet {P : Params} {O : Oracles n ι} {Lb : ℕ}
    (h : BudgetMet P O Lb) (i : ι) (t : ℝ) (X : Multiset (Space n)) (j₀ j₁ : ℕ) :
    absorbLevel P O i t X j₀ j₁ ≤ j₁ + Lb := by
  obtain ⟨j', hj₁, hj₂, hguard⟩ := h i t X j₀ j₁
  refine max_le (Nat.le_add_right _ _) (le_trans (Nat.sInf_le ⟨hj₁, hguard⟩) hj₂)

/-- **The budget implies `Ttc.Terminates`** — the hypothesis of `Ttc.runCost_le`. -/
theorem terminates_of_budgetMet {P : Params} {O : Oracles n ι} {Lb : ℕ}
    (h : BudgetMet P O Lb) (cubes : List ι) : Terminates P O cubes :=
  fun st i _ => absorbExits_of_budgetMet h i (O.vol i) (dropCovered O i st.X) st.level _

/-! ## Termination holds almost surely

`2Λ/2^Lb → 0`, so the budget is met for *some* `Lb` almost surely, and therefore
`Ttc.Terminates` — the hypothesis `Ttc.runCost_le` carries — holds `trajLaw`-almost
surely.  This is what makes the cost bound's `∀ᵐ` form unconditional **without any
change to `Model/Pseudocode`**; the pointwise `∀ ω` form is genuinely false and does
need the truncation. -/

/-- `2Λ/2^Lb → 0` in `ℝ≥0∞`. -/
theorem tendsto_geom_bound (Λ : ℝ) :
    Filter.Tendsto (fun Lb : ℕ => ENNReal.ofReal (2 * Λ / 2 ^ Lb)) Filter.atTop (nhds 0) := by
  have hreal : Filter.Tendsto (fun Lb : ℕ => 2 * Λ / 2 ^ Lb) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1/2:ℝ) < 1)).const_mul (2 * Λ)
    rw [mul_zero] at h
    refine h.congr fun Lb => ?_
    rw [one_div, inv_pow, ← div_eq_mul_inv]
  simpa using ENNReal.tendsto_ofReal hreal

/-- **`Ttc.Terminates` holds `trajLaw`-almost surely.**

Every absorption loop of the run exits, at every cube and from every entry state,
outside a null set.  Nothing is assumed about the run: the only inputs are that the
level-`0` rates are nonnegative and that `Thresh` is. -/
theorem trajLaw_ae_terminates {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (P : Params) (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (hT : 0 ≤ P.thresh) (cubes : List ι) :
    ∀ᵐ ω ∂(trajLaw θ), Terminates P (trajOracles hpt vol covered mem ω) cubes := by
  rw [MeasureTheory.ae_iff]
  refine le_antisymm ?_ bot_le
  refine ge_of_tendsto' (tendsto_geom_bound (∑ s, θ s)) fun Lb => ?_
  refine le_trans (measure_mono ?_) (trajLaw_compl_vanish_le hθ Lb)
  intro ω hω hv
  exact hω (terminates_of_budgetMet (budgetMet_of_vanish hpt P vol covered mem hT hv) cubes)

/-- **Some level budget is met, almost surely.** The quantitative form is
`Ttc.trajLaw_not_budgetMet_le`; this is its Borel–Cantelli-free limit. -/
theorem trajLaw_ae_exists_budgetMet {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (P : Params) (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (hT : 0 ≤ P.thresh) :
    ∀ᵐ ω ∂(trajLaw θ), ∃ Lb, BudgetMet P (trajOracles hpt vol covered mem ω) Lb := by
  rw [MeasureTheory.ae_iff]
  refine le_antisymm ?_ bot_le
  refine ge_of_tendsto' (tendsto_geom_bound (∑ s, θ s)) fun Lb => ?_
  refine le_trans (measure_mono ?_) (trajLaw_compl_vanish_le hθ Lb)
  intro ω hω hv
  exact hω ⟨Lb, budgetMet_of_vanish hpt P vol covered mem hT hv⟩

/-! ## The cost bound, almost surely and unconditionally

`Ttc.runCost_le` (`Runtime`) needs `Ttc.Terminates`; the previous section supplies
it almost surely.  Together they give `alg:ttc`'s charged cost bound with **no
hypothesis about the run at all** — the `∀ᵐ` shape the headline asks for. -/

/-- **The charged cost, bounded under the level budget.** -/
theorem runCost_le_of_budgetMet {P : Params} {O : Oracles n ι} {Lb : ℕ}
    (h : BudgetMet P O Lb) (cVol cSample : ℕ) (ρ : ℤ) (cubes : List ι) (thr : ℕ)
    (hthr : (thr : ℝ) = P.thresh) :
    runCost P O cVol cSample ρ cubes ≤ cubes.length * (cVol + cSample * thr) :=
  runCost_le P O cVol cSample ρ cubes thr hthr (terminates_of_budgetMet h cubes)

/-- **`thm:runtime`'s cost bound, `trajLaw`-almost surely and with no termination
hypothesis.**

`m` iterations, one `Vol_ED` call each and at most `Thresh` samples each, on every
trajectory outside a null set.  The `Ttc.Terminates` guard that
`Ttc.runCost_le` carries is discharged here by `Ttc.trajLaw_ae_terminates`, so
nothing about the run is assumed. -/
theorem trajLaw_ae_runCost_le {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (P : Params) (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (hT : 0 ≤ P.thresh)
    (cVol cSample : ℕ) (ρ : ℤ) (cubes : List ι) (thr : ℕ) (hthr : (thr : ℝ) = P.thresh) :
    ∀ᵐ ω ∂(trajLaw θ),
      runCost P (trajOracles hpt vol covered mem ω) cVol cSample ρ cubes
        ≤ cubes.length * (cVol + cSample * thr) := by
  filter_upwards [trajLaw_ae_terminates hpt P vol covered mem hθ hT cubes] with ω hω
  exact runCost_le P _ cVol cSample ρ cubes thr hthr hω

end Ttc

/-! ## Axiom check -/

#print axioms Ttc.trajLaw_eval_eq_zero
#print axioms Ttc.trajLaw_eval_ne_zero_le
#print axioms Ttc.trajLaw_exists_ne_zero_le
#print axioms Ttc.not_guard_of_eval_eq_zero
#print axioms Ttc.trajLaw_compl_vanish_le
#print axioms Ttc.budgetMet_of_vanish
#print axioms Ttc.trajLaw_not_budgetMet_le
#print axioms Ttc.absorbExits_of_budgetMet
#print axioms Ttc.absorbLevel_le_of_budgetMet
#print axioms Ttc.terminates_of_budgetMet
#print axioms Ttc.tendsto_geom_bound
#print axioms Ttc.trajLaw_ae_terminates
#print axioms Ttc.trajLaw_ae_exists_budgetMet
#print axioms Ttc.runCost_le_of_budgetMet
#print axioms Ttc.trajLaw_ae_runCost_le

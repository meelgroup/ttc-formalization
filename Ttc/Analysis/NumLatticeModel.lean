/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.RunCoupling
import Ttc.Model.ProblemSetting

/-!
# `lem:numlattice` from the model, not from an assumption

`Ttc.traj_numlattice_le` proves the paper's bound for a run driven by the coupled
family. This file transports it to a run on an *arbitrary* probability space,
given only that the space **is** the family: a map `e` reading each `ω` as a
trajectory, whose law is `Ttc.trajLaw θ`, along which the oracles factor.

`Ttc.TtcProb` used to assert this shape as a `numlattice_union` **field**. It no
longer does: the structure carries the model data instead, and the field has been
deleted in favour of `Ttc.TtcProb.numlattice_union` at the end of this file.

No measurability of the failure event is needed: `Measure.le_map_apply` bounds the
measure of a preimage by the pushforward of the set, which is all the direction of
the inequality requires.
-/

namespace Ttc

open MeasureTheory

/-- **`lem:numlattice`, transported off the trajectory space.**

`hlo`/`hhi` are what `lem:lattice` supplies (already proved); `hsmall`, `hrate`
and `hlamStar` are conditions on `Thresh` and the volume estimates; `hall`/`hcov`
say the cubes cover the lattice points and the oracle's coverage test agrees with
cube membership. Nothing probabilistic is assumed. -/
theorem numlattice_union_of_model
    {A : Type*} {n : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Params) (ε δ Lval : ℝ) (fuel : ℕ) (ρ : ℤ) (D : DNF A)
    (O : Ω → Oracles n (Cube A))
    {Lidx : ℕ} {pt : Fin Lidx → Space n} (hpt : Function.Injective pt)
    {θ : Fin Lidx → ℝ} (hθ0 : ∀ s, 0 ≤ θ s) (hθ : 0 < ∑ s, θ s)
    {vol : Cube A → ℝ} {covered : Space n → Cube A → Bool} {mem : Cube A → Fin Lidx → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s)
    (hall : ∀ s, (D.any fun i => mem i s) = true)
    (e : Ω → (ℕ → Fin Lidx → ℕ)) (he : AEMeasurable e μ)
    (hlaw : μ.map e = trajLaw θ)
    (hO : ∀ ω, O ω = trajOracles hpt vol covered mem (e ω))
    (jstar : ℕ) (hj1 : 1 ≤ jstar)
    (hsmall : ∀ i ∈ D, ¬ (P.thresh / vol i ≤ (1 / 2 : ℝ) ^ (jstar - 1)))
    (hrate : 2 * totalRate θ (jstar - 1) ≤ P.thresh)
    (hlamStar : (1 - P.epsPrime) * P.thresh / 8 ≤ totalRate θ (jstar - 1))
    (hep0 : 0 < P.epsPrime) (hep1 : P.epsPrime ≤ 1)
    (hlo : (1 - ε / 3) * Lval ≤ (1 - P.epsPrime) * (∑ s, θ s))
    (hhi : (1 + P.epsPrime) * (∑ s, θ s) ≤ (1 + ε / 3) * Lval)
    (hm : 1 ≤ P.m) (hδ : 0 ≤ δ) :
    ∃ (jstar' : ℕ) (lamStar : ℝ),
      (1 - P.epsPrime) * P.thresh / 8 ≤ lamStar ∧
      (μ {ω | ¬ ((1 - ε / 3) * Lval ≤ ttcOutput P O fuel ρ D ω ∧
                 ttcOutput P O fuel ρ D ω ≤ (1 + ε / 3) * Lval)}).toReal
        ≤ (∑ t ∈ Finset.range jstar',
              2 * Real.exp (-(P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
            + P.m * Real.exp (-(P.thresh / 6)) + δ / 2 := by
  classical
  refine ⟨jstar, totalRate θ (jstar - 1), hlamStar, ?_⟩
  set S : Set (ℕ → (Fin Lidx → ℕ)) :=
    {t | ¬ ((1 - ε / 3) * Lval ≤ run P (trajOracles hpt vol covered mem t) fuel ρ D ∧
            run P (trajOracles hpt vol covered mem t) fuel ρ D ≤ (1 + ε / 3) * Lval)} with hS
  -- the failure event is the pullback of the trajectory-space one
  have hset : {ω | ¬ ((1 - ε / 3) * Lval ≤ ttcOutput P O fuel ρ D ω ∧
      ttcOutput P O fuel ρ D ω ≤ (1 + ε / 3) * Lval)} = e ⁻¹' S := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hS, ttcOutput, hO ω]
  have h1 : μ {ω | ¬ ((1 - ε / 3) * Lval ≤ ttcOutput P O fuel ρ D ω ∧
      ttcOutput P O fuel ρ D ω ≤ (1 + ε / 3) * Lval)} ≤ trajLaw θ S := by
    rw [hset, ← hlaw]
    exact Measure.le_map_apply he S
  have hmain : (trajLaw θ).real S
      ≤ (∑ t ∈ Finset.range jstar,
            2 * Real.exp (-(P.epsPrime ^ 2 * (totalRate θ (jstar - 1) * 2 ^ t) / 3)))
          + Real.exp (-(P.thresh / 6)) :=
    traj_numlattice_le hθ0 hθ hep0 hep1 hlo hhi hpt hcov P fuel ρ D hall jstar hj1 hsmall hrate
  have hexp : (0:ℝ) ≤ Real.exp (-(P.thresh / 6)) := (Real.exp_pos _).le
  calc (μ {ω | ¬ ((1 - ε / 3) * Lval ≤ ttcOutput P O fuel ρ D ω ∧
        ttcOutput P O fuel ρ D ω ≤ (1 + ε / 3) * Lval)}).toReal
      ≤ (trajLaw θ S).toReal := ENNReal.toReal_mono (measure_ne_top _ _) h1
    _ ≤ (∑ t ∈ Finset.range jstar,
            2 * Real.exp (-(P.epsPrime ^ 2 * (totalRate θ (jstar - 1) * 2 ^ t) / 3)))
          + Real.exp (-(P.thresh / 6)) := hmain
    _ ≤ _ := by
        have hmexp : Real.exp (-(P.thresh / 6)) ≤ P.m * Real.exp (-(P.thresh / 6)) :=
          le_mul_of_one_le_left hexp (by exact_mod_cast hm)
        linarith

/-! ## The window, from `lem:lattice`

`Ttc.numlattice_union_of_model` wants the family's total rate `∑θ` pinned inside
`(1±ε/3)·L` after the `(1±ε')` slack of the epoch estimate is spent.
`lem:lattice` gives `∑θ` inside `(1±c)·L`; this is the arithmetic that combines
the two. The budget condition is `(1−ε')(1−c) ≥ 1−ε/3` and `(1+ε')(1+c) ≤ 1+ε/3`,
i.e. the two error sources together must still fit in `ε/3`.
-/

/-- **The two-sided window composes.** -/
theorem window_of_two_sided {epsP ε c Lval S : ℝ}
    (hL : 0 ≤ Lval) (hep0 : 0 ≤ epsP) (hep1 : epsP ≤ 1)
    (hlo' : (1 - c) * Lval ≤ S) (hhi' : S ≤ (1 + c) * Lval)
    (hA : 1 - ε / 3 ≤ (1 - epsP) * (1 - c))
    (hB : (1 + epsP) * (1 + c) ≤ 1 + ε / 3) :
    (1 - ε / 3) * Lval ≤ (1 - epsP) * S ∧ (1 + epsP) * S ≤ (1 + ε / 3) * Lval := by
  constructor
  · calc (1 - ε / 3) * Lval ≤ ((1 - epsP) * (1 - c)) * Lval := by nlinarith
      _ = (1 - epsP) * ((1 - c) * Lval) := by ring
      _ ≤ (1 - epsP) * S := by nlinarith
  · calc (1 + epsP) * S ≤ (1 + epsP) * ((1 + c) * Lval) := by nlinarith
      _ = ((1 + epsP) * (1 + c)) * Lval := by ring
      _ ≤ (1 + ε / 3) * Lval := by nlinarith

/-- **The exact case.** When the rates reproduce the lattice count exactly — the
ideal instance of CLAUDE.md §13, with every error coefficient `0` — the window
holds as soon as `ε' ≤ ε/3`. -/
theorem window_of_exact {epsP ε Lval S : ℝ} (hL : 0 ≤ Lval) (hep0 : 0 ≤ epsP)
    (hep1 : epsP ≤ 1) (hS : S = Lval) (hbudget : epsP ≤ ε / 3) :
    (1 - ε / 3) * Lval ≤ (1 - epsP) * S ∧ (1 + epsP) * S ≤ (1 + ε / 3) * Lval := by
  refine window_of_two_sided (c := 0) hL hep0 hep1 (by rw [hS]; linarith) (by rw [hS]; linarith)
    (by nlinarith) (by nlinarith)

/-! ## The epoch index exists

`Ttc.numlattice_union_of_model` needs a `j*` whose rate sits in the window
`[(1−ε')·Thresh/8, Thresh/2]`. That window has ratio at least `4`, so a power of
two always lands in it — provided the instance is big enough that the level-`0`
rate clears the bottom of the window at all. "Big enough" is the only real demand
the estimate makes on the input, and it is exactly the paper's regime: the
sketch is worth running only when the count exceeds the threshold.
-/

/-- **A suitable epoch index exists.** Take the first level at which the rate has
fallen to `Thresh/2`; minimality keeps it above `Thresh/4`, which clears
`(1−ε')·Thresh/8`. -/
theorem exists_epoch {S Thresh epsP : ℝ} (hT : 0 < Thresh)
    (hep : 0 ≤ epsP) (hbig : (1 - epsP) * Thresh / 8 ≤ S) :
    ∃ jstar : ℕ, 1 ≤ jstar ∧ 2 * (S / 2 ^ (jstar - 1)) ≤ Thresh ∧
      (1 - epsP) * Thresh / 8 ≤ S / 2 ^ (jstar - 1) := by
  classical
  have hex : ∃ k : ℕ, S / 2 ^ k ≤ Thresh / 2 := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (S / (Thresh / 2)) (by norm_num : (1:ℝ) < 2)
    refine ⟨k, ?_⟩
    have hpow : (0:ℝ) < 2 ^ k := by positivity
    rw [div_le_iff₀ hpow]
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < Thresh / 2)] at hk
    linarith
  set k := Nat.find hex with hk
  have hkspec : S / 2 ^ k ≤ Thresh / 2 := Nat.find_spec hex
  refine ⟨k + 1, Nat.le_add_left 1 k, ?_, ?_⟩
  · simpa using by linarith [hkspec]
  · simp only [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · simpa [hk0] using hbig
    · -- minimality: the previous level was still above `Thresh/2`
      have hprev : ¬ (S / 2 ^ (k - 1) ≤ Thresh / 2) := Nat.find_min hex (by omega)
      rw [not_le] at hprev
      have hsplit : k = (k - 1) + 1 := by omega
      have hpow : (0:ℝ) < 2 ^ (k - 1) := by positivity
      have hrw : S / 2 ^ k = (S / 2 ^ (k - 1)) / 2 := by
        rw [show (2:ℝ) ^ k = 2 ^ (k - 1) * 2 from by rw [← pow_succ, ← hsplit]]
        rw [div_div]
      rw [hrw]
      have : (1 - epsP) * Thresh / 8 ≤ Thresh / 4 := by nlinarith
      linarith

/-! ## The self-coupled instance

The witness takes `Ω` to BE the trajectory space, so the identification is the
identity and `law_eq` is `Measure.map_id`. This is the form
`Ttc.TtcProb`'s witness plugs in.
-/

/-- **`hsmall` from the epoch bound.** Once the level-`j*−1` rate is below
`Thresh/2`, no cube's rate can still trigger a `halveDown` at that level. -/
theorem rate_small_of_epoch {S Thresh v : ℝ} (hv : 0 < v) (hvS : v ≤ S) {jstar : ℕ}
    (hep : 2 * (S / 2 ^ (jstar - 1)) ≤ Thresh) :
    ¬ (Thresh / v ≤ (1 / 2 : ℝ) ^ (jstar - 1)) := by
  have hpow : (0:ℝ) < 2 ^ (jstar - 1) := by positivity
  rw [not_le, one_div, inv_pow, lt_div_iff₀ hv, inv_mul_eq_div, div_lt_iff₀ hpow]
  have h1 : S / 2 ^ (jstar - 1) ≤ Thresh / 2 := by linarith
  rw [div_le_iff₀ hpow] at h1
  nlinarith

/-- **`lem:numlattice` for a run whose sample space is the family itself.** -/
theorem numlattice_union_of_traj
    {A : Type*} {n : ℕ}
    (P : Params) (ε δ Lval : ℝ) (fuel : ℕ) (ρ : ℤ) (D : DNF A)
    {Lidx : ℕ} {pt : Fin Lidx → Space n} (hpt : Function.Injective pt)
    {θ : Fin Lidx → ℝ} (hθ0 : ∀ s, 0 ≤ θ s) (hθ : 0 < ∑ s, θ s)
    {vol : Cube A → ℝ} {covered : Space n → Cube A → Bool} {mem : Cube A → Fin Lidx → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s)
    (hall : ∀ s, (D.any fun i => mem i s) = true)
    (jstar : ℕ) (hj1 : 1 ≤ jstar)
    (hsmall : ∀ i ∈ D, ¬ (P.thresh / vol i ≤ (1 / 2 : ℝ) ^ (jstar - 1)))
    (hrate : 2 * totalRate θ (jstar - 1) ≤ P.thresh)
    (hlamStar : (1 - P.epsPrime) * P.thresh / 8 ≤ totalRate θ (jstar - 1))
    (hep0 : 0 < P.epsPrime) (hep1 : P.epsPrime ≤ 1)
    (hlo : (1 - ε / 3) * Lval ≤ (1 - P.epsPrime) * (∑ s, θ s))
    (hhi : (1 + P.epsPrime) * (∑ s, θ s) ≤ (1 + ε / 3) * Lval)
    (hm : 1 ≤ P.m) (hδ : 0 ≤ δ) :
    ∃ (jstar' : ℕ) (lamStar : ℝ),
      (1 - P.epsPrime) * P.thresh / 8 ≤ lamStar ∧
      ((trajLaw θ) {ω | ¬ ((1 - ε / 3) * Lval ≤
            ttcOutput P (fun t => trajOracles hpt vol covered mem t) fuel ρ D ω ∧
          ttcOutput P (fun t => trajOracles hpt vol covered mem t) fuel ρ D ω
            ≤ (1 + ε / 3) * Lval)}).toReal
        ≤ (∑ t ∈ Finset.range jstar',
              2 * Real.exp (-(P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
            + P.m * Real.exp (-(P.thresh / 6)) + δ / 2 :=
  numlattice_union_of_model (trajLaw θ) P ε δ Lval fuel ρ D _ hpt hθ0 hθ hcov hall
    (fun ω => ω) aemeasurable_id (Measure.map_id) (fun _ => rfl)
    jstar hj1 hsmall hrate hlamStar hep0 hep1 hlo hhi hm hδ

/-! ## The field, as a theorem

This is what replaced `numlattice_union` in `Ttc.TtcProb`. The statement is
verbatim the field that used to be assumed; the proof is
`Ttc.numlattice_union_of_model` fed from the sampler description.
-/

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

theorem epsPrime_pos : 0 < T.P.epsPrime := by
  rw [Params.epsPrime, T.eps_eq]; linarith [T.hε0]

theorem epsPrime_le_one' : T.P.epsPrime ≤ 1 := by
  rw [Params.epsPrime, T.eps_eq]; linarith [T.hε1, T.hε0]

theorem epsPrime_le_third : T.P.epsPrime ≤ T.ε / 3 := by
  rw [Params.epsPrime, T.eps_eq]; linarith [T.hε0]

/-- **`Thresh` is positive**, from the algorithm's own formula: `δ ≤ 1` makes
`log(24/δ) ≥ log 24 > 0` and `ε' = ε/12 ∈ (0, 1/12]` keeps the denominator
positive. Not an assumption. -/
theorem thresh_pos : 0 < T.P.thresh := by
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  have hd : T.P.δ = T.δ := T.delta_eq
  have hlog : 0 < Real.log (24 / T.P.δ) := by
    refine Real.log_pos ?_
    rw [hd]
    rw [lt_div_iff₀ T.hδ0]
    linarith [T.hδ1]
  have hep0 := T.epsPrime_pos
  have hep1 : T.P.epsPrime ≤ 1 / 12 := by
    rw [Params.epsPrime, T.eps_eq]; linarith [T.hε1]
  have hden : 0 < (1 - T.P.epsPrime) * T.P.epsPrime ^ 2 := by
    have : T.P.epsPrime < 1 := by linarith
    positivity
  positivity

/-- **The total rate is positive** — derived, not assumed: `big` bounds it below
by `(1−ε')·Thresh/8`, and `Thresh > 0` with `ε' ≤ 1/12` makes that positive. -/
theorem theta_pos : 0 < ∑ s, T.θ s := by
  have hT := T.thresh_pos
  have hep1 : T.P.epsPrime ≤ 1 / 12 := by
    rw [Params.epsPrime, T.eps_eq]; linarith [T.hε1]
  have hb := T.big
  nlinarith

/-- Each cube's rate is at most the total: `vol_eq` sums a subset of nonnegative
rates. -/
theorem vol_le_total {i : Cube A} (hi : i ∈ T.D) : T.vol i ≤ ∑ s, T.θ s := by
  classical
  rw [← T.vol_eq i hi]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun s _ _ => T.θ_nonneg s)

/-- **`lem:numlattice`'s epoch bound — proved, not assumed.** -/
theorem numlattice_union :
    ∃ (jstar : ℕ) (lamStar : ℝ),
      (1 - T.P.epsPrime) * T.P.thresh / 8 ≤ lamStar ∧
      (T.μ {ω | ¬ ((1 - T.ε / 3) * T.L ≤ ttcOutput T.P T.O T.fuel T.ρ T.D ω ∧
                 ttcOutput T.P T.O T.fuel T.ρ T.D ω ≤ (1 + T.ε / 3) * T.L)}).toReal
        ≤ (∑ t ∈ Finset.range jstar,
              2 * Real.exp (-(T.P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
            + T.P.m * Real.exp (-(T.P.thresh / 6)) + T.δ / 2 := by
  obtain ⟨hlo, hhi⟩ := window_of_exact (ε := T.ε)
    (le_of_lt (T.rate_eq_L ▸ T.theta_pos)) (T.epsPrime_pos).le (T.epsPrime_le_one')
    T.rate_eq_L (T.epsPrime_le_third)
  -- the epoch index is *derived*, not a field
  obtain ⟨jstar, hj1, hrate, hlam⟩ := exists_epoch (S := ∑ s, T.θ s)
    (Thresh := T.P.thresh) (epsP := T.P.epsPrime) T.thresh_pos
    (T.epsPrime_pos).le T.big
  haveI := T.isProb
  exact numlattice_union_of_model (mΩ := T.mΩ)
    T.μ T.P T.ε T.δ T.L T.fuel T.ρ T.D T.O
    T.ptE_inj T.θ_nonneg T.theta_pos T.cover_eq T.cover_all
    T.toTraj T.toTraj_meas T.law_eq T.oracle_eq
    jstar hj1
    (fun i hi => rate_small_of_epoch (T.vol_pos i hi) (T.vol_le_total hi) hrate)
    hrate hlam
    (T.epsPrime_pos) (T.epsPrime_le_one') hlo hhi T.P.hm T.hδ0.le

end TtcProb

end Ttc

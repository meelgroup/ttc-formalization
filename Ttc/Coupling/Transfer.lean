/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Coupling.Run
import Ttc.TtcProb
import Ttc.Volume.Bridge
import Ttc.Lattice.Assembled
import Ttc.Sampler.Bridge

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
    (P : Params) (ε δ Lval : ℝ) (ρ : ℤ) (D : DNF A)
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
    (hlo : (1 - ε / 2) * Lval ≤ (1 - P.epsPrime) * (∑ s, θ s))
    (hhi : (1 + P.epsPrime) * (∑ s, θ s) ≤ (1 + ε / 2) * Lval)
    (hm : 1 ≤ P.m) (hδ : 0 ≤ δ) :
    ∃ (jstar' : ℕ) (lamStar : ℝ),
      (1 - P.epsPrime) * P.thresh / 8 ≤ lamStar ∧
      (μ {ω | ¬ ((1 - ε / 2) * Lval ≤ run P (O ω) ρ D ∧
                 run P (O ω) ρ D ≤ (1 + ε / 2) * Lval)}).toReal
        ≤ (∑ t ∈ Finset.range jstar',
              2 * Real.exp (-(P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
            + P.m * Real.exp (-(P.thresh / 6)) + δ / 2 := by
  classical
  refine ⟨jstar, totalRate θ (jstar - 1), hlamStar, ?_⟩
  set S : Set (ℕ → (Fin Lidx → ℕ)) :=
    {t | ¬ ((1 - ε / 2) * Lval ≤ run P (trajOracles hpt vol covered mem t) ρ D ∧
            run P (trajOracles hpt vol covered mem t) ρ D ≤ (1 + ε / 2) * Lval)} with hS
  -- the failure event is the pullback of the trajectory-space one
  have hset : {ω | ¬ ((1 - ε / 2) * Lval ≤ run P (O ω) ρ D ∧
      run P (O ω) ρ D ≤ (1 + ε / 2) * Lval)} = e ⁻¹' S := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hS, hO ω]
  have h1 : μ {ω | ¬ ((1 - ε / 2) * Lval ≤ run P (O ω) ρ D ∧
      run P (O ω) ρ D ≤ (1 + ε / 2) * Lval)} ≤ trajLaw θ S := by
    rw [hset, ← hlaw]
    exact Measure.le_map_apply he S
  have hmain : (trajLaw θ).real S
      ≤ (∑ t ∈ Finset.range jstar,
            2 * Real.exp (-(P.epsPrime ^ 2 * (totalRate θ (jstar - 1) * 2 ^ t) / 3)))
          + Real.exp (-(P.thresh / 6)) :=
    traj_numlattice_le hθ0 hθ hep0 hep1 hlo hhi hpt hcov P ρ D hall jstar hj1 hsmall hrate
  have hexp : (0:ℝ) ≤ Real.exp (-(P.thresh / 6)) := (Real.exp_pos _).le
  calc (μ {ω | ¬ ((1 - ε / 2) * Lval ≤ run P (O ω) ρ D ∧
        run P (O ω) ρ D ≤ (1 + ε / 2) * Lval)}).toReal
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
`(1±ε/2)·L` after the `(1±ε')` slack of the epoch estimate is spent. The Invariant
gives `∑θ` inside `[clo·L, chi·L]`; this is the arithmetic that combines the two.
The budget condition is `ε'·clo ≥ 1−ε/2` and `(1+ε')·chi ≤ 1+ε/2`, i.e. all the
error sources together must still fit in `ε/2`.

The window is stated with **two** constants rather than one `(1±c)`, because with
an almost-uniform sampler it is genuinely asymmetric: `clo = (1−ε')²(1−η)` and
`chi = (1+ε')²(1+η)` are not reflections of each other.
-/

/-- **The two-sided window composes.** -/
theorem window_of_two_sided {epsP ε clo chi Lval S : ℝ}
    (hL : 0 ≤ Lval) (hep0 : 0 ≤ epsP) (hep1 : epsP ≤ 1)
    (hlo' : clo * Lval ≤ S) (hhi' : S ≤ chi * Lval)
    (hA : 1 - ε / 2 ≤ (1 - epsP) * clo)
    (hB : (1 + epsP) * chi ≤ 1 + ε / 2) :
    (1 - ε / 2) * Lval ≤ (1 - epsP) * S ∧ (1 + epsP) * S ≤ (1 + ε / 2) * Lval := by
  constructor
  · calc (1 - ε / 2) * Lval ≤ ((1 - epsP) * clo) * Lval := by nlinarith
      _ = (1 - epsP) * (clo * Lval) := by ring
      _ ≤ (1 - epsP) * S := by nlinarith
  · calc (1 + epsP) * S ≤ (1 + epsP) * (chi * Lval) := by nlinarith
      _ = ((1 + epsP) * chi) * Lval := by ring
      _ ≤ (1 + ε / 2) * Lval := by nlinarith

/-- **The exact case.** When the rates reproduce the lattice count exactly — the
ideal instance of CLAUDE.md §13, with every error coefficient `0` — the window
holds as soon as `ε' ≤ ε/2`. -/
theorem window_of_exact {epsP ε Lval S : ℝ} (hL : 0 ≤ Lval) (hep0 : 0 ≤ epsP)
    (hep1 : epsP ≤ 1) (hS : S = Lval) (hbudget : epsP ≤ ε / 2) :
    (1 - ε / 2) * Lval ≤ (1 - epsP) * S ∧ (1 + epsP) * S ≤ (1 + ε / 2) * Lval := by
  refine window_of_two_sided (clo := 1) (chi := 1) hL hep0 hep1
    (by rw [hS]; linarith) (by rw [hS]; linarith) (by nlinarith) (by nlinarith)

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
`Thresh/2`, no cube's rate can still trigger the first loop at that level. -/
theorem rate_small_of_epoch {S Thresh v : ℝ} (hv : 0 < v) (hvS : v < 2 * S) {jstar : ℕ}
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
    (P : Params) (ε δ Lval : ℝ) (ρ : ℤ) (D : DNF A)
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
    (hlo : (1 - ε / 2) * Lval ≤ (1 - P.epsPrime) * (∑ s, θ s))
    (hhi : (1 + P.epsPrime) * (∑ s, θ s) ≤ (1 + ε / 2) * Lval)
    (hm : 1 ≤ P.m) (hδ : 0 ≤ δ) :
    ∃ (jstar' : ℕ) (lamStar : ℝ),
      (1 - P.epsPrime) * P.thresh / 8 ≤ lamStar ∧
      ((trajLaw θ) {ω | ¬ ((1 - ε / 2) * Lval ≤
            run P (trajOracles hpt vol covered mem ω) ρ D ∧
          run P (trajOracles hpt vol covered mem ω) ρ D
            ≤ (1 + ε / 2) * Lval)}).toReal
        ≤ (∑ t ∈ Finset.range jstar',
              2 * Real.exp (-(P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
            + P.m * Real.exp (-(P.thresh / 6)) + δ / 2 :=
  numlattice_union_of_model (trajLaw θ) P ε δ Lval ρ D _ hpt hθ0 hθ hcov hall
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

/-- The enumeration's range is exactly `Sol(F) ∩ 𝕃ⁿ` — `ptE_mem` gives one
inclusion, `ptE_onto` the other. -/
theorem sol_lattice_eq_range :
    sol T.M T.φ ∩ fineLattice n (latticeScale T.ρ) = Set.range T.ptE := by
  ext x
  constructor
  · intro hx; obtain ⟨s, hs⟩ := T.ptE_onto x hx; exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩; exact T.ptE_mem s

/-- **`Lidx` is the paper's `|Sol(F) ∩ 𝕃ⁿ|`.** Forced by the bijection, not
assumed — this is what `ptE_inj`/`ptE_mem`/`ptE_onto` buy. -/
theorem Lidx_eq : T.Lidx = latticeCount T.M T.φ T.ρ := by
  rw [latticeCount, T.sol_lattice_eq_range, ← Set.image_univ,
    Set.ncard_image_of_injective _ T.ptE_inj, Set.ncard_univ]
  simp

/-- Hence `L = Lidx / 10^(ρ·n)`. -/
theorem L_eq_Lidx : T.L = (T.Lidx : ℝ) / (latticeScale T.ρ) ^ n := by
  rw [T.L_eq, normalisedCount, T.Lidx_eq]

/-- `η = ε/8 ∈ (0, 1/8]`. -/
theorem eta_pos : 0 < T.P.eta := by
  rw [Params.eta, T.eps_eq]; linarith [T.hε0]

theorem eta_le : T.P.eta ≤ 1 / 8 := by
  rw [Params.eta, T.eps_eq]; linarith [T.hε1]

/-- **Rates are nonnegative** — derived from the Invariant's lower half. -/
theorem theta_nonneg (s : Fin T.Lidx) : 0 ≤ T.θ s := by
  refine le_trans ?_ (T.theta_lo s)
  have h1 : T.P.epsPrime ≤ 1 / 12 := by
    rw [Params.epsPrime, T.eps_eq]; linarith [T.hε1]
  have h2 := T.eta_le
  have hls : (0:ℝ) < latticeScale T.ρ := by rw [latticeScale]; positivity
  have hpow : (0:ℝ) < (latticeScale T.ρ) ^ n := by positivity
  have : (0:ℝ) ≤ (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) := by
    nlinarith [T.epsPrime_pos, T.eta_pos, sq_nonneg (1 - T.P.epsPrime)]
  positivity

/-- **The total rate, windowed** — the paper's Invariant summed over the lattice
points. This is what replaces the exact `∑θ = L`. The `(1−ε')` appears **squared**:
once for `Vol_ED`, once for the almost-uniformity of `GenerateSamples`
(`eq:sampler`). -/
theorem sum_theta_lo : (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) * T.L ≤ ∑ s, T.θ s := by
  have hls : (0:ℝ) < latticeScale T.ρ := by rw [latticeScale]; positivity
  have hpow : (0:ℝ) < (latticeScale T.ρ) ^ n := by positivity
  calc (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) * T.L
      = (T.Lidx : ℝ) * ((1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) / (latticeScale T.ρ) ^ n) := by
        rw [T.L_eq_Lidx]; field_simp; try ring
    _ = ∑ _s : Fin T.Lidx, (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) / (latticeScale T.ρ) ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ s, T.θ s := Finset.sum_le_sum fun s _ => T.theta_lo s

theorem sum_theta_hi : ∑ s, T.θ s ≤ (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) * T.L := by
  have hls : (0:ℝ) < latticeScale T.ρ := by rw [latticeScale]; positivity
  have hpow : (0:ℝ) < (latticeScale T.ρ) ^ n := by positivity
  calc ∑ s, T.θ s
      ≤ ∑ _s : Fin T.Lidx, (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) / (latticeScale T.ρ) ^ n :=
        Finset.sum_le_sum fun s _ => T.theta_hi s
    _ = (T.Lidx : ℝ) * ((1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) / (latticeScale T.ρ) ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) * T.L := by
        rw [T.L_eq_Lidx]; field_simp; try ring

/-- `L` is positive: the total rate is, and it is sandwiched by `L`. -/
theorem L_pos : 0 < T.L := by
  have h := T.sum_theta_hi
  have hpos := T.theta_pos
  have hk : 0 < (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) := by
    have := T.epsPrime_pos; have := T.eta_pos; positivity
  rcases le_or_gt T.L 0 with hL | hL
  · have hneg : 0 ≤ ((1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta)) * (-T.L) :=
      mul_nonneg hk.le (neg_nonneg.2 hL)
    nlinarith
  · exact hL

/-- **Every enumerated point is covered by some cube** — derived from `isDNF`,
not assumed. `ptE s` lies in `Sol(F)`, so the formula holds there; `D` is a DNF of
the formula, so some cube of `D` holds there; and `memPt_eq` turns that into
membership. -/
theorem cover_all (s : Fin T.Lidx) : (T.D.any fun i => T.memPt i s) = true := by
  have hφ : T.φ.holds (induced T.M (T.ptE s)) := (T.ptE_mem s).1
  obtain ⟨c, hcD, hc⟩ := (T.isDNF (induced T.M (T.ptE s))).2 hφ
  exact List.any_eq_true.2 ⟨c, hcD, (T.memPt_eq c hcD s).2 hc⟩

/-- A cube of the DNF sits inside the solution set. -/
theorem region_subset_sol {i : Cube A} (hi : i ∈ T.D) : region T.M i ⊆ sol T.M T.φ := by
  intro x hx
  exact (T.isDNF (induced T.M x)).1 ⟨i, hi, hx⟩

/-- The solution set has finite volume — else `volSol` would be `0`, contradicting
`lem:lattice`'s lower bound together with `L > 0`. -/
theorem volSol_ne_top : volume (sol T.M T.φ) ≠ ⊤ := by
  intro htop
  have hlo := T.lattice_lo
  rw [volSol, htop, ENNReal.toReal_top] at hlo
  have h1 : T.ε / 8 ≤ 1 / 8 := by linarith [T.hε1]
  nlinarith [T.L_pos, T.hε0]

/-- **A single cube's estimate cannot exceed twice the whole instance's rate.**
`Vol_ED` overestimates by at most `(1+ε')`, the cube sits inside `Sol(F)`, and
`lem:lattice` bounds `Vol(Sol(F))` by `(1+η)L` — while the Invariant bounds `∑θ`
below by `(1−ε')²(1−η)L`. The ratio is under `2` for every `ε ≤ 1`: at the worst
case `ε = 1` it is `(13/12)(9/8) / (2·(11/12)²(7/8)) ≈ 0.83`. -/
theorem vol_lt_two_total {i : Cube A} (hi : i ∈ T.D) : T.vol i < 2 * ∑ s, T.θ s := by
  have hmono : (volume (region T.M i)).toReal ≤ volSol T.M T.φ := by
    rw [volSol]
    exact ENNReal.toReal_mono T.volSol_ne_top (measure_mono (T.region_subset_sol hi))
  have hV := T.lattice_hi
  have hvol := T.volED_hi i hi
  have hsum := T.sum_theta_lo
  have hep : T.P.epsPrime = T.ε / 12 := by rw [Params.epsPrime, T.eps_eq]
  have hη : T.P.eta = T.ε / 8 := by rw [Params.eta, T.eps_eq]
  rw [hep] at hvol
  rw [hep, hη] at hsum
  have hL := T.L_pos
  -- the coefficient comparison, isolated from the `L`-scaling
  have hcoeff : (1 + T.ε / 12) * (1 + T.ε / 8) < 2 * ((1 - T.ε / 12) ^ 2 * (1 - T.ε / 8)) := by
    have h0 := T.hε0
    have h1 := T.hε1
    have h2 : T.ε ^ 2 ≤ T.ε := by nlinarith
    have h3 : T.ε ^ 3 ≤ T.ε := by nlinarith
    have h3nn : (0:ℝ) ≤ T.ε ^ 3 := by positivity
    nlinarith
  nlinarith [T.hε0, T.hε1]

/-- **`lem:numlattice`'s epoch bound — proved, not assumed.** -/
theorem numlattice_union :
    ∃ (jstar : ℕ) (lamStar : ℝ),
      (1 - T.P.epsPrime) * T.P.thresh / 8 ≤ lamStar ∧
      (T.μ {ω | ¬ ((1 - T.ε / 2) * T.L ≤ ttcOutput T.P T.O T.toDNF T.ρ T.φ ω ∧
                 ttcOutput T.P T.O T.toDNF T.ρ T.φ ω ≤ (1 + T.ε / 2) * T.L)}).toReal
        ≤ (∑ t ∈ Finset.range jstar,
              2 * Real.exp (-(T.P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
            + T.P.m * Real.exp (-(T.P.thresh / 6)) + T.δ / 2 := by
  -- the accuracy window, from the paper's Invariant rather than an exact equality
  have hep : T.P.epsPrime = T.ε / 12 := by rw [Params.epsPrime, T.eps_eq]
  have hη : T.P.eta = T.ε / 8 := by rw [Params.eta, T.eps_eq]
  have hLpos := T.L_pos
  -- the budget: `(1±ε')` for the concentration, `(1±ε')` for `Vol_ED`, `(1±ε')` for
  -- the sampler (`eq:sampler`) and `(1±η)` for `lem:lattice` — four factors, which
  -- is why the window is `ε/2` and not the pre-`eq:sampler` `ε/3`.
  have he0 := T.hε0
  have he1 := T.hε1
  have h2 : T.ε ^ 2 ≤ T.ε := by nlinarith
  have h3 : T.ε ^ 3 ≤ T.ε := by nlinarith
  have h4 : T.ε ^ 4 ≤ T.ε := by nlinarith
  have h3nn : (0:ℝ) ≤ T.ε ^ 3 := by positivity
  have h4nn : (0:ℝ) ≤ T.ε ^ 4 := by positivity
  have hA : 1 - T.ε / 2 ≤ (1 - T.P.epsPrime) * ((1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta)) := by
    rw [hep, hη]
    have hexp : (1 - T.ε / 12) * ((1 - T.ε / 12) ^ 2 * (1 - T.ε / 8))
        = 1 - (3/8) * T.ε + (5/96) * T.ε ^ 2 - (11/3456) * T.ε ^ 3
            + (1/13824) * T.ε ^ 4 := by ring
    rw [hexp]; nlinarith
  have hB : (1 + T.P.epsPrime) * ((1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta)) ≤ 1 + T.ε / 2 := by
    rw [hep, hη]
    have hexp : (1 + T.ε / 12) * ((1 + T.ε / 12) ^ 2 * (1 + T.ε / 8))
        = 1 + (3/8) * T.ε + (5/96) * T.ε ^ 2 + (11/3456) * T.ε ^ 3
            + (1/13824) * T.ε ^ 4 := by ring
    rw [hexp]; nlinarith
  obtain ⟨hlo, hhi⟩ := window_of_two_sided (ε := T.ε) hLpos.le (T.epsPrime_pos).le
    (T.epsPrime_le_one') T.sum_theta_lo T.sum_theta_hi hA hB
  -- the epoch index is *derived*, not a field
  obtain ⟨jstar, hj1, hrate, hlam⟩ := exists_epoch (S := ∑ s, T.θ s)
    (Thresh := T.P.thresh) (epsP := T.P.epsPrime) T.thresh_pos
    (T.epsPrime_pos).le T.big
  haveI := T.isProb
  exact numlattice_union_of_model (mΩ := T.mΩ)
    T.μ T.P T.ε T.δ T.L T.ρ T.D T.O
    T.ptE_inj T.theta_nonneg T.theta_pos T.cover_eq T.cover_all
    T.toTraj T.toTraj_meas T.law_eq T.oracle_eq
    jstar hj1
    (fun i hi => rate_small_of_epoch (T.vol_pos i hi) (T.vol_lt_two_total hi) hrate)
    hrate hlam
    (T.epsPrime_pos) (T.epsPrime_le_one') hlo hhi T.P.hm T.hδ0.le

end TtcProb

end Ttc

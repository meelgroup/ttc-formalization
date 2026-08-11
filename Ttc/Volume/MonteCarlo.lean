/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.TtcProb
import Ttc.Model.Pseudocode
import Arlib.Convexity.GaussianCooling.Unblock
import Arlib.Probability.UniformOn
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# `Volume/MonteCarlo`: the volume oracle, constructed

`Ttc.VolumeAlgorithm n` (`Volume/Oracle`) was, until this file, an *assumption*:
a field of `Ttc.TtcProb` with no witness that constructs its estimate from randomness.
This file constructs one, `Ttc.VolumeAlgorithm.monteCarlo`, with no hypotheses at all.

## What the algorithm is

Plain **hit-and-miss Monte Carlo**.  The coins are an i.i.d. sequence of points drawn
uniformly from the unit ball, `Ω = ℕ → Space n` under `Measure.infinitePi`.  Given a
body `K`, the algorithm

1. manufactures a radius `R` with `K ⊆ ball 0 R`, from convexity, the inscribed unit ball
   and finiteness of the volume, via `Arlib.Convexity.exists_closedBall_superset_of_convex`;
2. rescales the coins, `x ↦ R • x`, so that they are uniform on `ball 0 R ⊇ K`;
3. counts how many of the first `N` land in `K`, and returns
   `Vol(ball 0 R) · (count / N)`.

`N` is chosen from `(K, ε, p)` — the interface permits this, since `est` is applied to all
three — as `⌈(ε²·p·q)⁻¹⌉ + 1`, where `q = Vol(K)/Vol(ball 0 R)` is the hitting probability.
Correctness is Chebyshev on the i.i.d. Bernoulli(`q`) counts, using
`ProbabilityTheory.IndepFun.variance_sum` and `ProbabilityTheory.meas_ge_le_variance_div_sq`.

## Honest scope

The sample count is `N = Θ(R^n/(ε²·p))`, i.e. **exponential in the dimension `n`** — and
`R` is itself `Θ(Vol K / Vol(ball 0 (1/2)))`, so the bound is very bad indeed.  This is
admissible only because `Ttc.VolumeAlgorithm` has **no complexity field**: it asserts
accuracy and measurability, and nothing about running time.  Consequently:

**This is emphatically not Cousins–Vempala Theorem 1.1.**  CV Theorem 1.1 is an
`O*(n³)` algorithm; nothing here is polynomial in `n`, and no claim about running time is
made or proved anywhere in this file.  What is proved is exactly the proposition
`Ttc.VolumeAlgorithm n` states, no more.

Note in the other direction that `Ttc.VolumeAlgorithm.correct` is *strictly stronger* than
CV Theorem 1.1's accuracy claim, which additionally assumes `E_K(‖X‖²) = O(n)`: this
construction discharges the interface on bodies CV alone would not cover.  So the
`Ttc.TtcProb.volAlg` field is now inhabited unconditionally, while the *efficient* oracle
of `Ttc/Volume/CousinsVempala.lean` remains open.

## The measurability subtlety

`Ttc.VolumeAlgorithm.est_meas` must hold for **every** `K : Set (Space n)`, including
non-measurable ones; only `correct` gets `Convex ℝ K`, and Mathlib v4.32 offers just
`Convex.nullMeasurableSet`, not `MeasurableSet`.  So `fun ω ↦ #{i | R • ω i ∈ K}` is not
measurable in general.

The fix is to define the estimator against the **measurable hull**
`MeasureTheory.toMeasurable volume K` rather than `K` (`Ttc.MonteCarlo.target`).  That
makes `Ttc.MonteCarlo.measurableSet_target` — and hence `est_meas` — hold for *every* set
whatsoever, with no hypothesis.  Correctness survives because of
`Ttc.MonteCarlo.volume_hull_inter_ball`: the hull has the same volume as `K` and contains
it, so intersecting it back with the enclosing ball recovers `volume K` on the nose.  No
almost-everywhere argument is needed; the identity is exact.

## Where the definitions live

The estimator's **definitions** — `rad`, `target`, `hitData`, `scale`, `nSamp`, `ind`,
`score`, `est`, and `Ttc.mcVol` itself — are in
[`Ttc/Model/Pseudocode.lean`](../Model/Pseudocode.lean), the audit surface.  This
file holds every **theorem** about them, and the coin space they are averaged over.

The split is not cosmetic: it is what keeps this development's own probability space out of
the algorithm's definitional closure.  The sample count `nSamp` is defined from
`Ttc.MonteCarlo.hitData`, the hitting probability written out in Lebesgue volume, rather
than from `Ttc.MonteCarlo.hit`, which is `(coinLaw n (target K)).toReal`.  The two are equal
whenever `K ⊆ Metric.ball 0 (rad K)` — `Ttc.MonteCarlo.hit_eq_hitData` — which is what
`correct` establishes for itself, so nothing about the estimator changes; `coinLaw` and
`coins` simply no longer appear in what `Ttc.mcVol` *unfolds to*.  Mathlib's Lebesgue
`volume` does, irreducibly: `scale` is the enclosing ball's volume and `target` is a
measurable hull.  See `Model/Pseudocode`'s docstring.

## Main declarations

* `Ttc.MonteCarlo.coinLaw`, `Ttc.MonteCarlo.coins` — the uniform law on the unit ball and
  its countable i.i.d. power.
* `Ttc.MonteCarlo.exists_ball_superset` — the enclosing radius `Ttc.MonteCarlo.rad` exists.
* `Ttc.MonteCarlo.measurableSet_target` — the hull `Ttc.MonteCarlo.target`, pulled back
  along the rescaling, is measurable unconditionally.
* `Ttc.MonteCarlo.volume_hull_inter_ball`, `Ttc.MonteCarlo.hit_eq`,
  `Ttc.MonteCarlo.scale_mul_hit` — the geometry: the hitting probability is
  `Vol K / Vol(ball 0 R)`, exactly.
* `Ttc.MonteCarlo.hit_eq_hitData` — the sample count's arithmetic hitting probability is
  the coin law's.
* `Ttc.MonteCarlo.measurable_est` — the estimator `Ttc.MonteCarlo.est` is measurable.
* `Ttc.MonteCarlo.integral_est`, `Ttc.MonteCarlo.variance_est` — unbiasedness and the
  Bernoulli variance.
* `Ttc.MonteCarlo.correct` — Chebyshev, in the exact shape `VolumeAlgorithm.correct` wants.
* `Ttc.VolumeAlgorithm.monteCarlo` — **the term**.
* `Ttc.MonteCarlo.est_ne_volume` — **the anti-cheat** (`CLAUDE.md` §11): a body satisfying
  every hypothesis of `correct`, together with coins on which the estimate differs from
  the true volume.  Without it the construction could be the exact oracle in disguise,
  which is precisely what it is meant to replace.
-/

namespace Ttc.MonteCarlo

open MeasureTheory ProbabilityTheory

variable {n : ℕ}

/-! ## The coins

`K`-independent by necessity: `Ω` and `μ` are fields of `VolumeAlgorithm`, fixed before any
body is seen.  So the coins are uniform on the *unit* ball, and the body-dependent radius
enters through a rescaling inside `est`. -/

theorem volume_unitBall_ne_zero : volume (Metric.ball (0 : Space n) 1) ≠ 0 :=
  (Metric.measure_ball_pos volume 0 one_pos).ne'

theorem volume_unitBall_ne_top : volume (Metric.ball (0 : Space n) 1) ≠ ⊤ :=
  measure_ball_lt_top.ne

theorem volume_unitBall_toReal_pos : 0 < (volume (Metric.ball (0 : Space n) 1)).toReal :=
  ENNReal.toReal_pos volume_unitBall_ne_zero volume_unitBall_ne_top

instance instIsProbabilityMeasureCoinLaw : IsProbabilityMeasure (coinLaw n) :=
  Arlib.isProbabilityMeasure_uniformOn volume volume_unitBall_ne_zero volume_unitBall_ne_top

instance instIsProbabilityMeasureCoins : IsProbabilityMeasure (coins n) := by
  unfold coins; infer_instance

/-! ## The enclosing radius

`correct` hands over exactly three facts about `K` — convex, contains the unit ball, finite
volume — and `Arlib.Convexity.exists_closedBall_superset_of_convex` turns them into a
radius.  `rad` takes the *least* such radius, plus one, totally: it is defined (as `1`) even
when no radius exists, so that `est` is a total function and `est_meas` needs no hypothesis.

Both facts below come out of `sInf` rather than `Exists.choose_spec`: positivity because the
valid radii are bounded below by `0`, and the enclosure because `‖x‖` is a lower bound for
every valid radius, hence at most their infimum — which is where the `+ 1` in `rad`'s body
earns its keep, reopening the ball.  Unlike `Exists.choose`, `sInf` also admits an
*upper* bound; that is
`Ttc.MonteCarlo.radMin_le_of_subset_closedBall` in `Ttc/Volume/RadBound.lean`. -/

theorem rad_pos (K : Set (Space n)) : 0 < rad K := by
  classical
  rw [rad]
  split_ifs with h
  · have hnn : 0 ≤ sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} :=
      le_csInf h fun _ hR => hR.1.le
    linarith
  · exact one_pos

theorem rad_ne_zero (K : Set (Space n)) : rad K ≠ 0 := (rad_pos K).ne'

theorem rad_pow_pos (K : Set (Space n)) (m : ℕ) : 0 < rad K ^ m := pow_pos (rad_pos K) m

theorem subset_ball_rad {K : Set (Space n)}
    (h : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R) :
    K ⊆ Metric.ball (0 : Space n) (rad K) := by
  classical
  intro x hx
  rw [rad, if_pos h, mem_ball_zero_iff]
  have hle : ‖x‖ ≤ sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} :=
    le_csInf h fun R hR => (mem_ball_zero_iff.mp (hR.2 hx)).le
  linarith

/-- **The radius exists**, from exactly the hypotheses `VolumeAlgorithm.correct` supplies.
`Arlib` produces a *closed* ball; a `+1` opens it. -/
theorem exists_ball_superset {K : Set (Space n)} (hK : Convex ℝ K)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R := by
  obtain ⟨R, hR, hsub⟩ := Arlib.Convexity.exists_closedBall_superset_of_convex hK hball hfin
  exact ⟨R + 1, by linarith, hsub.trans (Metric.closedBall_subset_ball (by linarith))⟩

/-! ## The target set

`target K` is the set the *coins* are tested against: the measurable hull of `K`, pulled
back along `x ↦ rad K • x`.  Two properties matter, and they are the two halves of the
subtlety in the module docstring: it is measurable for **every** `K` (so `est_meas` is
unconditional), and — once `K` really is enclosed by `ball 0 (rad K)` — its intersection
with the unit ball has volume exactly `(rad K)⁻ⁿ · Vol K`. -/

/-- **Measurable, with no hypothesis on `K`.**  This is what makes
`Ttc.VolumeAlgorithm.est_meas` provable: it is quantified over every `K`, and a convex set
is only `NullMeasurableSet` in Mathlib v4.32, never `MeasurableSet`. -/
theorem measurableSet_target (K : Set (Space n)) : MeasurableSet (target K) :=
  (measurableSet_toMeasurable _ _).preimage (measurable_const_smul _)

theorem target_inter_unitBall (K : Set (Space n)) :
    target K ∩ Metric.ball (0 : Space n) 1
      = (fun x : Space n => rad K • x) ⁻¹'
          (toMeasurable volume K ∩ Metric.ball (0 : Space n) (rad K)) := by
  have hr : (0 : ℝ) < rad K := rad_pos K
  ext x
  simp only [target, Set.mem_inter_iff, Set.mem_preimage, mem_ball_zero_iff, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, mul_lt_iff_lt_one_right hr]

/-- **The hull costs nothing.**  `toMeasurable volume K` has the same volume as `K` and
contains it; intersecting it back with a ball that already contains `K` recovers `volume K`
*exactly*.  This is why replacing `K` by its hull — forced by `est_meas` — does not damage
`correct`, and no almost-everywhere argument is needed. -/
theorem volume_hull_inter_ball {K : Set (Space n)} {R : ℝ}
    (hsub : K ⊆ Metric.ball (0 : Space n) R) :
    volume (toMeasurable volume K ∩ Metric.ball (0 : Space n) R) = volume K := by
  refine le_antisymm ?_ ?_
  · exact le_trans (measure_mono Set.inter_subset_left) (measure_toMeasurable K).le
  · exact measure_mono (Set.subset_inter (subset_toMeasurable _ _) hsub)

/-! ## The estimator -/

/-- The hitting probability: the chance that one rescaled coin lands in `K`. -/
noncomputable def hit (K : Set (Space n)) : ℝ := (coinLaw n (target K)).toReal

theorem scale_pos (K : Set (Space n)) : 0 < scale K := by
  rw [scale]; exact mul_pos (rad_pow_pos K n) volume_unitBall_toReal_pos

theorem nSamp_pos (K : Set (Space n)) (ε pf : ℝ) : 0 < nSamp K ε pf := Nat.succ_pos _

theorem nSamp_cast_pos (K : Set (Space n)) (ε pf : ℝ) : (0 : ℝ) < (nSamp K ε pf : ℝ) := by
  exact_mod_cast nSamp_pos K ε pf

theorem measurable_ind (K : Set (Space n)) : Measurable (ind K) :=
  measurable_one.indicator (measurableSet_target K)

theorem ind_sq (K : Set (Space n)) (x : Space n) : ind K x ^ 2 = ind K x := by
  by_cases hx : x ∈ target K
  · rw [ind, Set.indicator_of_mem hx]; norm_num
  · rw [ind, Set.indicator_of_notMem hx]; norm_num

theorem norm_ind_le (K : Set (Space n)) (x : Space n) : ‖ind K x‖ ≤ 1 := by
  by_cases hx : x ∈ target K
  · rw [ind, Set.indicator_of_mem hx]; norm_num
  · rw [ind, Set.indicator_of_notMem hx]; norm_num

theorem measurable_score (K : Set (Space n)) (i : ℕ) : Measurable (score K i) :=
  (measurable_ind K).comp (measurable_pi_apply i)

/-- **`est` is measurable for every `K` whatsoever** — no convexity, no measurability of
`K`.  This is `Ttc.VolumeAlgorithm.est_meas`. -/
theorem measurable_est (K : Set (Space n)) (ε pf : ℝ) : Measurable (est K ε pf) :=
  measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_score K i)

/-! ## The geometry: the hitting probability is the volume ratio -/

theorem coinLaw_target (K : Set (Space n)) :
    coinLaw n (target K)
      = volume (target K ∩ Metric.ball (0 : Space n) 1)
          / volume (Metric.ball (0 : Space n) 1) :=
  Arlib.uniformOn_apply volume measurableSet_ball (measurableSet_target K)

theorem volume_target_inter_unitBall {K : Set (Space n)}
    (hsub : K ⊆ Metric.ball (0 : Space n) (rad K)) :
    volume (target K ∩ Metric.ball (0 : Space n) 1)
      = ENNReal.ofReal ((rad K ^ n)⁻¹) * volume K := by
  have habs : |((rad K) ^ Module.finrank ℝ (Space n))⁻¹| = (rad K ^ n)⁻¹ := by
    rw [finrank_euclideanSpace_fin]
    exact abs_of_nonneg (le_of_lt (inv_pos.mpr (rad_pow_pos K n)))
  rw [target_inter_unitBall, Measure.addHaar_preimage_smul volume (rad_ne_zero K) _, habs,
    volume_hull_inter_ball hsub]

/-- **The hitting probability, exactly.** `q = Vol K / Vol(ball 0 (rad K))`, written out. -/
theorem hit_eq {K : Set (Space n)} (hsub : K ⊆ Metric.ball (0 : Space n) (rad K)) :
    hit K = (rad K ^ n)⁻¹ * (volume K).toReal
      / (volume (Metric.ball (0 : Space n) 1)).toReal := by
  rw [hit, coinLaw_target, volume_target_inter_unitBall hsub, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (rad_pow_pos K n)))]

/-- **Data equals law.**  `Ttc.MonteCarlo.hitData`, the arithmetic hitting probability that
`Ttc.MonteCarlo.nSamp` is *defined* from, is the coin law's own hitting probability
`Ttc.MonteCarlo.hit` — whenever `K` is enclosed by `Metric.ball 0 (rad K)`, which is exactly
the situation `Ttc.MonteCarlo.correct` establishes for itself
(`Ttc.MonteCarlo.subset_ball_rad`).

This lemma is the entire content of the data/law split described in
`Ttc/Model/Pseudocode.lean`: the sample count is arithmetic in Lebesgue volume, the coin law
`Ttc.MonteCarlo.coinLaw` enters only through theorems, and the estimator's *definition*
therefore names no measure this development constructs. -/
theorem hit_eq_hitData {K : Set (Space n)} (hsub : K ⊆ Metric.ball (0 : Space n) (rad K)) :
    hit K = hitData K := hit_eq hsub

/-- **The estimator is unbiased**, at the level of one sample: `scale · q = Vol K`. -/
theorem scale_mul_hit {K : Set (Space n)} (hsub : K ⊆ Metric.ball (0 : Space n) (rad K)) :
    scale K * hit K = (volume K).toReal := by
  have hr : (rad K ^ n : ℝ) ≠ 0 := (rad_pow_pos K n).ne'
  have hu : (volume (Metric.ball (0 : Space n) 1)).toReal ≠ 0 :=
    volume_unitBall_toReal_pos.ne'
  rw [scale, hit_eq hsub]
  field_simp

theorem hit_pos {K : Set (Space n)} (hsub : K ⊆ Metric.ball (0 : Space n) (rad K))
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) : 0 < hit K := by
  rw [hit_eq hsub]
  exact div_pos (mul_pos (inv_pos.mpr (rad_pow_pos K n)) (ENNReal.toReal_pos hK0 hKtop))
    volume_unitBall_toReal_pos

/-! ## The probability: i.i.d. Bernoulli, and Chebyshev -/

/-- **The scores are independent** — this is what the infinite product measure buys. -/
theorem iIndepFun_score (K : Set (Space n)) : iIndepFun (score K) (coins n) :=
  iIndepFun_infinitePi (X := fun _ : ℕ => ind K) (fun _ => measurable_ind K)

theorem memLp_score (K : Set (Space n)) (i : ℕ) : MemLp (score K i) 2 (coins n) :=
  MemLp.of_bound (measurable_score K i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => norm_ind_le K (ω i))

theorem integral_score (K : Set (Space n)) (i : ℕ) :
    ∫ ω, score K i ω ∂(coins n) = hit K := by
  have hmap : Measure.map (fun ω : ℕ → Space n => ω i) (coins n) = coinLaw n :=
    Measure.infinitePi_map_eval (fun _ : ℕ => coinLaw n) i
  have hcomp : ∫ x, ind K x ∂(coinLaw n) = ∫ ω, ind K (ω i) ∂(coins n) := by
    rw [← hmap]
    exact integral_map (measurable_pi_apply i).aemeasurable
      (measurable_ind K).aestronglyMeasurable
  simp only [score]
  rw [← hcomp, ind, integral_indicator_one (measurableSet_target K), hit, measureReal_def]

theorem integral_score_sq (K : Set (Space n)) (i : ℕ) :
    ∫ ω, (score K i ω) ^ 2 ∂(coins n) = hit K := by
  have h : ∀ ω : ℕ → Space n, (score K i ω) ^ 2 = score K i ω := fun ω => ind_sq K (ω i)
  simp only [h]
  exact integral_score K i

theorem variance_score (K : Set (Space n)) (i : ℕ) :
    variance (score K i) (coins n) = hit K - hit K ^ 2 := by
  have hsq : ∫ ω, ((score K i) ^ 2) ω ∂(coins n) = ∫ ω, (score K i ω) ^ 2 ∂(coins n) := by
    simp
  rw [variance_eq_sub (memLp_score K i), hsq, integral_score_sq, integral_score]

/-- The unnormalised count: how many of the first `N` rescaled coins land in `K`. -/
noncomputable def count (K : Set (Space n)) (N : ℕ) : (ℕ → Space n) → ℝ :=
  ∑ i ∈ Finset.range N, score K i

theorem memLp_count (K : Set (Space n)) (N : ℕ) : MemLp (count K N) 2 (coins n) :=
  memLp_finsetSum' _ fun i _ => memLp_score K i

theorem integral_count (K : Set (Space n)) (N : ℕ) :
    ∫ ω, count K N ω ∂(coins n) = N * hit K := by
  simp only [count, Finset.sum_apply]
  rw [integral_finsetSum _ fun i _ => (memLp_score K i).integrable one_le_two]
  simp [integral_score]

/-- **The variance of the count**, `N·q(1−q)` — this is where independence is used. -/
theorem variance_count (K : Set (Space n)) (N : ℕ) :
    variance (count K N) (coins n) = N * (hit K - hit K ^ 2) := by
  simp only [count]
  rw [IndepFun.variance_sum (fun i _ => memLp_score K i)
    (fun i _ j _ hij => (iIndepFun_score K).indepFun hij)]
  simp [variance_score]
  ring

theorem est_eq_smul_count (K : Set (Space n)) (ε pf : ℝ) :
    est K ε pf = (scale K / (nSamp K ε pf : ℝ)) • count K (nSamp K ε pf) := by
  funext ω
  simp [est, count, Finset.sum_apply]

theorem memLp_est (K : Set (Space n)) (ε pf : ℝ) : MemLp (est K ε pf) 2 (coins n) := by
  rw [est_eq_smul_count]
  exact (memLp_count K _).const_smul _

/-- **Unbiasedness**: the expected estimate is the true volume. -/
theorem integral_est {K : Set (Space n)} (hsub : K ⊆ Metric.ball (0 : Space n) (rad K))
    (ε pf : ℝ) : ∫ ω, est K ε pf ω ∂(coins n) = (volume K).toReal := by
  have hN : ((nSamp K ε pf : ℝ)) ≠ 0 := (nSamp_cast_pos K ε pf).ne'
  rw [est_eq_smul_count]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, integral_count, ← scale_mul_hit hsub]
  field_simp

theorem variance_est (K : Set (Space n)) (ε pf : ℝ) :
    variance (est K ε pf) (coins n)
      = (scale K / (nSamp K ε pf : ℝ)) ^ 2 * ((nSamp K ε pf : ℝ) * (hit K - hit K ^ 2)) := by
  rw [est_eq_smul_count, variance_smul, variance_count]

/-! ## Relative error, unpacked -/

theorem abs_le_of_notMem_relErr {ε b x : ℝ} (h : x ∉ relErr ε b) : ε * b ≤ |x - b| := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨h1, h2⟩ := abs_lt.mp hlt
  exact h (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)

/-! ## The theorem -/

/-- **The Monte Carlo estimator is correct**, in exactly the shape
`Ttc.VolumeAlgorithm.correct` demands: outside a set of measure `pf`, the estimate lies
within a relative `ε` of `Vol K`. -/
theorem correct (K : Set (Space n)) (ε pf : ℝ) (hε : 0 < ε) (hp : 0 < pf) (_hp1 : pf < 1)
    (hK : Convex ℝ K) (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    1 - pf ≤ (coins n {ω | est K ε pf ω ∈ relErr ε (volume K).toReal}).toReal := by
  classical
  -- the enclosing radius
  have hsub : K ⊆ Metric.ball (0 : Space n) (rad K) :=
    subset_ball_rad (exists_ball_superset hK hball hfin)
  -- `K` has positive finite volume
  have hK0 : volume K ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 one_pos) (measure_mono hball))
  have hVpos : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hfin
  have hqpos : 0 < hit K := hit_pos hsub hK0 hfin
  have hNpos : (0 : ℝ) < (nSamp K ε pf : ℝ) := nSamp_cast_pos K ε pf
  have hspos : 0 < scale K := scale_pos K
  have hscale : scale K * hit K = (volume K).toReal := scale_mul_hit hsub
  -- the sample count really is large enough
  have hNbig : (ε ^ 2 * pf * hit K)⁻¹ ≤ (nSamp K ε pf : ℝ) := by
    have h1 : (ε ^ 2 * pf * hit K)⁻¹ ≤ (⌈(ε ^ 2 * pf * hit K)⁻¹⌉₊ : ℝ) := Nat.le_ceil _
    rw [nSamp, ← hit_eq_hitData hsub]
    push_cast
    linarith
  have hkey : (1 - hit K) / ((nSamp K ε pf : ℝ) * ε ^ 2 * hit K) ≤ pf := by
    have hden : (0 : ℝ) < (nSamp K ε pf : ℝ) * ε ^ 2 * hit K := by positivity
    rw [div_le_iff₀ hden]
    have hpos : (0 : ℝ) < ε ^ 2 * pf * hit K := by positivity
    have h1 : (1 : ℝ) ≤ (nSamp K ε pf : ℝ) * (ε ^ 2 * pf * hit K) := by
      have := mul_le_mul_of_nonneg_right hNbig hpos.le
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    have h2 : pf * ((nSamp K ε pf : ℝ) * ε ^ 2 * hit K)
        = (nSamp K ε pf : ℝ) * (ε ^ 2 * pf * hit K) := by ring
    rw [h2]
    linarith
  -- Chebyshev
  have hmean : ∫ ω, est K ε pf ω ∂(coins n) = (volume K).toReal := integral_est hsub ε pf
  have hcheb := meas_ge_le_variance_div_sq (μ := coins n) (memLp_est K ε pf)
    (c := ε * (volume K).toReal) (by positivity)
  rw [hmean] at hcheb
  -- the variance, computed
  have hvar : variance (est K ε pf) (coins n) / (ε * (volume K).toReal) ^ 2
      = (1 - hit K) / ((nSamp K ε pf : ℝ) * ε ^ 2 * hit K) := by
    have hs : scale K ≠ 0 := hspos.ne'
    have hN : ((nSamp K ε pf : ℝ)) ≠ 0 := hNpos.ne'
    have hq : hit K ≠ 0 := hqpos.ne'
    have he : ε ≠ 0 := hε.ne'
    rw [variance_est, ← hscale]
    field_simp
  rw [hvar] at hcheb
  -- transfer to the good set
  have hbadsub : {ω | est K ε pf ω ∈ relErr ε (volume K).toReal}ᶜ
      ⊆ {ω | ε * (volume K).toReal ≤ |est K ε pf ω - (volume K).toReal|} := by
    intro ω hω
    exact abs_le_of_notMem_relErr hω
  have hSmeas : MeasurableSet {ω | est K ε pf ω ∈ relErr ε (volume K).toReal} :=
    (measurable_est K ε pf) measurableSet_Icc
  have hbad : coins n {ω | est K ε pf ω ∈ relErr ε (volume K).toReal}ᶜ ≤ ENNReal.ofReal pf :=
    le_trans (measure_mono hbadsub) (le_trans hcheb (ENNReal.ofReal_le_ofReal hkey))
  have hsum : coins n {ω | est K ε pf ω ∈ relErr ε (volume K).toReal}
      + coins n {ω | est K ε pf ω ∈ relErr ε (volume K).toReal}ᶜ = 1 := by
    rw [measure_add_measure_compl hSmeas, measure_univ]
  have hsumR : (coins n {ω | est K ε pf ω ∈ relErr ε (volume K).toReal}).toReal
      + (coins n {ω | est K ε pf ω ∈ relErr ε (volume K).toReal}ᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum,
      ENNReal.toReal_one]
  have hbadR : (coins n {ω | est K ε pf ω ∈ relErr ε (volume K).toReal}ᶜ).toReal ≤ pf := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    rwa [ENNReal.toReal_ofReal hp.le] at this
  linarith

end Ttc.MonteCarlo

namespace Ttc

open MeasureTheory

/-- **The volume oracle, constructed.**

A term of `Ttc.VolumeAlgorithm n` with no hypotheses: hit-and-miss Monte Carlo on i.i.d.
uniform draws from the unit ball, rescaled to an enclosing ball of `K`.  See the module
docstring of `Ttc/Volume/MonteCarlo.lean` — in particular, the sample count is exponential
in `n`, and this is **not** Cousins–Vempala Theorem 1.1. -/
noncomputable def VolumeAlgorithm.monteCarlo (n : ℕ) : VolumeAlgorithm n where
  Ω := ℕ → Space n
  mΩ := inferInstance
  μ := MonteCarlo.coins n
  isProb := MonteCarlo.instIsProbabilityMeasureCoins
  est := MonteCarlo.est
  est_meas := MonteCarlo.measurable_est
  correct := fun K ε pf hε hp hp1 hK hball hfin =>
    MonteCarlo.correct K ε pf hε hp hp1 hK hball hfin

end Ttc

namespace Ttc.MonteCarlo

open MeasureTheory
open scoped Pointwise

/-! ## Anti-cheat: the estimate is not the exact volume

`CLAUDE.md` §11.  The construction this file replaces had an `est` that was `rfl`-equal to
`(volume K).toReal` — the exact oracle in disguise.  What follows exhibits a body
satisfying **every** hypothesis of `correct`, together with coins on which the estimate is
`0` while the true volume is not, so no such identification is possible. -/

/-- The measurable hull of the unit ball does not swallow the whole space: the doubled ball
would then fit inside a set of the unit ball's own volume. -/
theorem exists_notMem_hull_unitBall {n : ℕ} (hn : n ≠ 0) :
    ∃ v : Space n, v ∉ toMeasurable volume (Metric.ball (0 : Space n) 1) := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hle : volume ((2 : ℝ) • Metric.ball (0 : Space n) 1)
      ≤ volume (Metric.ball (0 : Space n) 1) := by
    rw [← measure_toMeasurable (Metric.ball (0 : Space n) 1)]
    exact measure_mono fun x _ => hcon x
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin] at hle
  have h2 : ((2 : ℝ) ^ n) * (volume (Metric.ball (0 : Space n) 1)).toReal
      ≤ (volume (Metric.ball (0 : Space n) 1)).toReal := by
    have := ENNReal.toReal_mono volume_unitBall_ne_top hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)] at this
  have hu : 0 < (volume (Metric.ball (0 : Space n) 1)).toReal := volume_unitBall_toReal_pos
  have hpow : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn)
  norm_num at hpow
  nlinarith

/-- **The anti-cheat.**  There is a body meeting every hypothesis of
`Ttc.VolumeAlgorithm.correct` — convex, containing the unit ball, of finite volume — and a
sequence of coins on which `Ttc.VolumeAlgorithm.monteCarlo` returns something *other* than
the true volume.  In particular `est` is not the exact volume oracle in disguise. -/
theorem est_ne_volume {n : ℕ} (hn : n ≠ 0) :
    ∃ (K : Set (Space n)) (ε pf : ℝ) (ω : ℕ → Space n),
      0 < ε ∧ 0 < pf ∧ pf < 1 ∧ Convex ℝ K ∧ Metric.ball (0 : Space n) 1 ⊆ K ∧
      volume K ≠ ⊤ ∧ est K ε pf ω ≠ (volume K).toReal := by
  obtain ⟨v, hv⟩ := exists_notMem_hull_unitBall hn
  refine ⟨Metric.ball (0 : Space n) 1, 1, 1 / 2,
    fun _ => (rad (Metric.ball (0 : Space n) 1))⁻¹ • v, one_pos, by norm_num, by norm_num,
    convex_ball _ _, subset_rfl, volume_unitBall_ne_top, ?_⟩
  have hzero : est (Metric.ball (0 : Space n) 1) 1 (1 / 2)
      (fun _ => (rad (Metric.ball (0 : Space n) 1))⁻¹ • v) = 0 := by
    have hs : ∀ i ∈ Finset.range (nSamp (Metric.ball (0 : Space n) 1) 1 (1 / 2)),
        score (Metric.ball (0 : Space n) 1) i
          (fun _ => (rad (Metric.ball (0 : Space n) 1))⁻¹ • v) = 0 := by
      intro i _
      have hmem : ((fun _ => (rad (Metric.ball (0 : Space n) 1))⁻¹ • v : ℕ → Space n) i)
          ∉ target (Metric.ball (0 : Space n) 1) := by
        rw [target, Set.mem_preimage]
        simpa [smul_inv_smul₀ (rad_ne_zero (Metric.ball (0 : Space n) 1))] using hv
      rw [score, ind, Set.indicator_of_notMem hmem]
    rw [est, Finset.sum_congr rfl hs]
    simp
  rw [hzero]
  exact fun h => absurd h.symm volume_unitBall_toReal_pos.ne'

/-- The anti-cheat, restated on the constructed structure itself: the `est` *field* of
`Ttc.VolumeAlgorithm.monteCarlo` is not the exact volume oracle. -/
theorem monteCarlo_est_ne_volume {n : ℕ} (hn : n ≠ 0) :
    ∃ (K : Set (Space n)) (ε pf : ℝ) (ω : (Ttc.VolumeAlgorithm.monteCarlo n).Ω),
      0 < ε ∧ 0 < pf ∧ pf < 1 ∧ Convex ℝ K ∧ Metric.ball (0 : Space n) 1 ⊆ K ∧
      volume K ≠ ⊤ ∧ (Ttc.VolumeAlgorithm.monteCarlo n).est K ε pf ω ≠ (volume K).toReal :=
  est_ne_volume hn

/-! ### Axiom audit

Every declaration in this file is `sorry`-free and depends only on Lean's three standard
axioms.  Re-check with `lake build Ttc.Volume.MonteCarlo`.  The definitions this file is
*about* — `rad`, `target`, `hitData`, `scale`, `nSamp`, `ind`, `score`, `est` — are checked
where they are defined, in `Ttc/Model/Pseudocode.lean`. -/

#print axioms Ttc.MonteCarlo.volume_unitBall_ne_zero
#print axioms Ttc.MonteCarlo.volume_unitBall_ne_top
#print axioms Ttc.MonteCarlo.volume_unitBall_toReal_pos
#print axioms Ttc.MonteCarlo.coinLaw
#print axioms Ttc.MonteCarlo.instIsProbabilityMeasureCoinLaw
#print axioms Ttc.MonteCarlo.coins
#print axioms Ttc.MonteCarlo.instIsProbabilityMeasureCoins
#print axioms Ttc.MonteCarlo.rad_pos
#print axioms Ttc.MonteCarlo.rad_ne_zero
#print axioms Ttc.MonteCarlo.rad_pow_pos
#print axioms Ttc.MonteCarlo.subset_ball_rad
#print axioms Ttc.MonteCarlo.exists_ball_superset
#print axioms Ttc.MonteCarlo.measurableSet_target
#print axioms Ttc.MonteCarlo.target_inter_unitBall
#print axioms Ttc.MonteCarlo.volume_hull_inter_ball
#print axioms Ttc.MonteCarlo.hit
#print axioms Ttc.MonteCarlo.scale_pos
#print axioms Ttc.MonteCarlo.nSamp_pos
#print axioms Ttc.MonteCarlo.nSamp_cast_pos
#print axioms Ttc.MonteCarlo.measurable_ind
#print axioms Ttc.MonteCarlo.ind_sq
#print axioms Ttc.MonteCarlo.norm_ind_le
#print axioms Ttc.MonteCarlo.measurable_score
#print axioms Ttc.MonteCarlo.measurable_est
#print axioms Ttc.MonteCarlo.coinLaw_target
#print axioms Ttc.MonteCarlo.volume_target_inter_unitBall
#print axioms Ttc.MonteCarlo.hit_eq
#print axioms Ttc.MonteCarlo.hitData
#print axioms Ttc.MonteCarlo.hit_eq_hitData
#print axioms Ttc.MonteCarlo.scale_mul_hit
#print axioms Ttc.MonteCarlo.hit_pos
#print axioms Ttc.MonteCarlo.iIndepFun_score
#print axioms Ttc.MonteCarlo.memLp_score
#print axioms Ttc.MonteCarlo.integral_score
#print axioms Ttc.MonteCarlo.integral_score_sq
#print axioms Ttc.MonteCarlo.variance_score
#print axioms Ttc.MonteCarlo.count
#print axioms Ttc.MonteCarlo.memLp_count
#print axioms Ttc.MonteCarlo.integral_count
#print axioms Ttc.MonteCarlo.variance_count
#print axioms Ttc.MonteCarlo.est_eq_smul_count
#print axioms Ttc.MonteCarlo.memLp_est
#print axioms Ttc.MonteCarlo.integral_est
#print axioms Ttc.MonteCarlo.variance_est
#print axioms Ttc.MonteCarlo.abs_le_of_notMem_relErr
#print axioms Ttc.MonteCarlo.correct
#print axioms Ttc.VolumeAlgorithm.monteCarlo
#print axioms Ttc.MonteCarlo.exists_notMem_hull_unitBall
#print axioms Ttc.MonteCarlo.est_ne_volume
#print axioms Ttc.MonteCarlo.monteCarlo_est_ne_volume

end Ttc.MonteCarlo

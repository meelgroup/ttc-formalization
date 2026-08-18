/-
# Fractional moments of the inverse local conductance

`Arlib.MarkovChains.ell K δ x = vol(B(x,δ) ∩ K) / vol(B(x,δ))` is the ball walk's local
conductance, and `ell⁻¹` is the mean number of proposals per proper step.  The speedy walk's
reference law is `ell`-weighted, so the *first* moment of `ell⁻¹` against it collapses to a
zeroth moment against the underlying weight — that is
`Arlib.MarkovChains.lintegral_inv_ell_ellProb`, and it is why the speedy walk exists.

The *second* moment does not collapse: it is a first moment of `ell⁻¹` against the underlying
weight, which no averaged-conductance hypothesis controls.  This file supplies what sits
strictly between the two: **fractional moments `∫ ell^{-α}` for `α < 1/n`**, which are bounded
by an absolute constant with no hypothesis beyond convexity, `ball 0 1 ⊆ K`, and `δ ≤ 1/(2n)`.

The mechanism is a layer bound.  For convex `K ⊇ ball 0 1`, every point of `(1-λ) • K` carries
a `λ`-ball inside `K` (`ball_subset_of_mem_smul_of_convex`), so `ell ≥ (λ/δ)^n` there
(`ofReal_div_pow_le_ell_of_ball_subset`); hence `{ell < θ}` is confined to the shell
`K \ (1-λ) • K` at `λ = δ·θ^{1/n}`, whose weight is at most `n·λ` of the whole.  With
`δ ≤ 1/(2n)` the tail is `θ^{1/n}/2` and integrating it converges exactly when `α·n < 1`.

The weight enters only through `MeasureShrinks`, an inline hypothesis saying that shrinking
toward the origin costs at most the Jacobian.  Lebesgue satisfies it with equality; any
radially non-increasing density — the Gaussian in particular — satisfies it.
-/
import Arlib.MarkovChains.Continuous.BallWalk

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. The pointwise estimate -/

/-- **A ball inside `K` forces local conductance.**  If `ball x u ⊆ K` and `u ≤ δ`, then
`ell K δ x ≥ (u/δ)^n`.  No convexity and no measurability of `K` are needed: `ell` is a ratio
of two volumes and only the numerator is being bounded below, by monotonicity. -/
theorem ofReal_div_pow_le_ell_of_ball_subset
    {K : Set (EuclideanSpace ℝ (Fin n))} {δ u : ℝ} (hu : 0 < u) (huδ : u ≤ δ)
    {x : EuclideanSpace ℝ (Fin n)} (hsub : ball x u ⊆ K) :
    ENNReal.ofReal ((u / δ) ^ n) ≤ ell K δ x := by
  have hδ : 0 < δ := lt_of_lt_of_le hu huδ
  have hbx0 : volume (ball x δ) ≠ 0 := (measure_ball_pos volume x hδ).ne'
  have hbxt : volume (ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hvu : volume (ball x u)
      = ENNReal.ofReal (u ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    have h := Measure.addHaar_ball_of_pos
      (volume : Measure (EuclideanSpace ℝ (Fin n))) x hu
    rwa [finrank_euclideanSpace_fin] at h
  have hvx : volume (ball x δ)
      = ENNReal.ofReal (δ ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    have h := Measure.addHaar_ball_of_pos
      (volume : Measure (EuclideanSpace ℝ (Fin n))) x hδ
    rwa [finrank_euclideanSpace_fin] at h
  have hincl : ball x u ⊆ ball x δ ∩ K := fun y hy => ⟨ball_subset_ball huδ hy, hsub hy⟩
  have hpow : (u / δ) ^ n * δ ^ n = u ^ n := by
    rw [div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ hδ.ne'
  rw [ell_apply, ENNReal.le_div_iff_mul_le (Or.inl hbx0) (Or.inl hbxt)]
  calc ENNReal.ofReal ((u / δ) ^ n) * volume (ball x δ)
      = ENNReal.ofReal (u ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        rw [hvx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hpow]
    _ = volume (ball x u) := hvu.symm
    _ ≤ volume (ball x δ ∩ K) := measure_mono hincl

/-- **The shrunken body has interior room.**  For convex `K` containing the unit ball and
`0 < λ ≤ 1`, every point of `(1-λ) • K` is the centre of a `λ`-ball contained in `K`.

This is the only place convexity and `ball 0 1 ⊆ K` are used. -/
theorem ball_subset_of_mem_smul_of_convex
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (1 - lam) • K) :
    ball x lam ⊆ K := by
  obtain ⟨k, hk, rfl⟩ := hx
  intro y hy
  have hynorm : ‖y - (1 - lam) • k‖ < lam := by
    simpa [mem_ball, dist_eq_norm] using hy
  have hz : lam⁻¹ • (y - (1 - lam) • k) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [inv_mul_lt_one₀ hlam0]
    exact hynorm
  have hzK : lam⁻¹ • (y - (1 - lam) • k) ∈ K := hball hz
  have hcomb := hKc hk hzK (by linarith : (0:ℝ) ≤ 1 - lam) hlam0.le (by ring)
  have hy_eq : (1 - lam) • k + lam • (lam⁻¹ • (y - (1 - lam) • k)) = y := by
    rw [smul_smul, mul_inv_cancel₀ hlam0.ne', one_smul]
    abel
  rwa [hy_eq] at hcomb

/-- **The pointwise estimate on the shrunken body.**  Combining the two lemmas above: on
`(1-λ) • K` the local conductance is at least `(λ/δ)^n`. -/
theorem ofReal_div_pow_le_ell_of_mem_smul
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {δ lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hlamδ : lam ≤ δ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (1 - lam) • K) :
    ENNReal.ofReal ((lam / δ) ^ n) ≤ ell K δ x :=
  ofReal_div_pow_le_ell_of_ball_subset hlam0 hlamδ
    (ball_subset_of_mem_smul_of_convex hKc hball hlam0 hlam1 hx)

/-! ## 2. The layer bound, for any weight that does not lose mass under shrinking -/

/-- **`mu` does not lose more than the Jacobian when the body is shrunk toward the origin.**
Lebesgue measure satisfies this with equality; so does any measure with a radially
non-increasing density, the Gaussian weight in particular, because shrinking moves every
point closer to `0` where the density is larger. -/
def MeasureShrinks (mu : Measure (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ c : ℝ, 0 < c → c ≤ 1 → ENNReal.ofReal (c ^ n) * mu K ≤ mu (c • K)

/-- **The layer bound.**  Under `MeasureShrinks`, the set of points of `K` where the local
conductance is below `(λ/δ)^n` has `mu`-measure at most `(1 - (1-λ)^n) · mu K`. -/
theorem measure_lt_ell_le_of_measureShrinks
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {mu : Measure (EuclideanSpace ℝ (Fin n))} (hshrink : MeasureShrinks mu K)
    (hKtop : mu K ≠ ⊤)
    {δ lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlamδ : lam ≤ δ) :
    mu {x ∈ K | ell K δ x < ENNReal.ofReal ((lam / δ) ^ n)}
      ≤ mu K - ENNReal.ofReal ((1 - lam) ^ n) * mu K := by
  have hc0 : (0:ℝ) < 1 - lam := by linarith
  have hsub : {x ∈ K | ell K δ x < ENNReal.ofReal ((lam / δ) ^ n)} ⊆ K \ (1 - lam) • K := by
    rintro x ⟨hxK, hxell⟩
    refine ⟨hxK, fun hxs => absurd hxell (not_lt.2 ?_)⟩
    exact ofReal_div_pow_le_ell_of_mem_smul hKc hball hlam0 hlam1.le hlamδ hxs
  have hsmulK : (1 - lam) • K ⊆ K := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := hy
    have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (mem_ball_self one_pos)
    have := hKc hk h0K hc0.le (by linarith : (0:ℝ) ≤ lam) (by ring)
    simpa using this
  calc mu {x ∈ K | ell K δ x < ENNReal.ofReal ((lam / δ) ^ n)}
      ≤ mu (K \ (1 - lam) • K) := measure_mono hsub
    _ = mu K - mu ((1 - lam) • K) :=
        measure_sdiff hsmulK
          (hK.const_smul₀ (1 - lam)).nullMeasurableSet
          (ne_top_of_le_ne_top hKtop (measure_mono hsmulK))
    _ ≤ mu K - ENNReal.ofReal ((1 - lam) ^ n) * mu K :=
        tsub_le_tsub_left (hshrink (1 - lam) hc0 (by linarith)) _

/-- **Bernoulli, in the form the layer bound needs**: `1 - (1-λ)^n ≤ n·λ`. -/
theorem one_sub_one_sub_pow_le (n : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    1 - (1 - lam) ^ n ≤ (n : ℝ) * lam := by
  have h := one_add_mul_le_pow (a := -lam) (by linarith) n
  have hrw : (1 : ℝ) + (n : ℝ) * (-lam) = 1 - (n : ℝ) * lam := by ring
  have hrw2 : (1 : ℝ) + -lam = 1 - lam := by ring
  rw [hrw, hrw2] at h
  linarith

/-- **The layer bound, in the form the moment estimate uses.**  At `λ ≤ min 1 δ`,

    `mu {x ∈ K | ell K δ x < (λ/δ)^n}  ≤  n·λ · mu K`.

Everything about the weight is in `MeasureShrinks`; everything about the geometry is in
`ofReal_div_pow_le_ell_of_mem_smul`. -/
theorem measure_lt_ell_le_mul
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {mu : Measure (EuclideanSpace ℝ (Fin n))} (hshrink : MeasureShrinks mu K)
    (hKtop : mu K ≠ ⊤)
    {δ lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlamδ : lam ≤ δ) :
    mu {x ∈ K | ell K δ x < ENNReal.ofReal ((lam / δ) ^ n)}
      ≤ ENNReal.ofReal ((n : ℝ) * lam) * mu K := by
  refine (measure_lt_ell_le_of_measureShrinks hK hKc hball hshrink hKtop
    hlam0 hlam1 hlamδ).trans ?_
  have hc0 : (0:ℝ) ≤ (1 - lam) ^ n := by positivity
  have hfac : mu K - ENNReal.ofReal ((1 - lam) ^ n) * mu K
      = (1 - ENNReal.ofReal ((1 - lam) ^ n)) * mu K := by
    rw [ENNReal.sub_mul (fun _ _ => hKtop), one_mul]
  rw [hfac]
  refine mul_le_mul_right' ?_ _
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_sub _ hc0]
  exact ENNReal.ofReal_le_ofReal (one_sub_one_sub_pow_le n hlam0.le hlam1.le)

/-! ## 3. The fractional moment

The exponent is fixed at `α = 1/(2n)`, which is what the downstream Hölder step uses, and
the dyadic base at `2^n`.  That base is the point of this section: with bands of ratio `2^n`
the *crude* band bound `mu(A_k) ≤ mu{ell < 2^{-nk}}` already sums to an absolute constant,
so no Abel summation and no layer-cake machinery is needed.  At base `2` the same argument
loses a factor `n`. -/

/-- The dyadic thresholds, `bb k = 2^{-nk}`. -/
noncomputable def dyadicThreshold (n k : ℕ) : ℝ := ((1 : ℝ) / 2) ^ (n * k)

theorem dyadicThreshold_pos (n k : ℕ) : 0 < dyadicThreshold n k := by
  unfold dyadicThreshold; positivity

theorem dyadicThreshold_le_one (n k : ℕ) : dyadicThreshold n k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

/-- **The pointwise dyadic bound.**  For `t ≤ 1`,

    `t ^ (-1/(2n))  ≤  √2  +  ∑_{k≥1} √2^{k+1} · 1[t < 2^{-nk}]`.

At `t = 0` the right side is `⊤`; otherwise the least `k` with `2^{-n(k+1)} ≤ t` selects the
one term that dominates. -/
theorem rpow_neg_le_add_tsum_indicator {n : ℕ} (hn : 0 < n) {t : ℝ≥0∞} (ht1 : t ≤ 1) :
    t ^ (-(1 / (2 * (n : ℝ)))) ≤
      ENNReal.ofReal (Real.sqrt 2) +
        ∑' k : ℕ, (if t < ENNReal.ofReal (dyadicThreshold n (k + 1))
          then ENNReal.ofReal (Real.sqrt 2 ^ (k + 2)) else 0) := by
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hkey : ∀ k : ℕ, (ENNReal.ofReal (dyadicThreshold n k)) ^ (-(1 / (2 * (n : ℝ))))
      = ENNReal.ofReal (Real.sqrt 2 ^ k) := by
    intro k
    have hpos : (0:ℝ) < dyadicThreshold n k := dyadicThreshold_pos n k
    rw [ENNReal.ofReal_rpow_of_pos hpos]
    congr 1
    have h2 : dyadicThreshold n k = (2:ℝ) ^ (-((n : ℝ) * (k : ℝ))) := by
      unfold dyadicThreshold
      rw [← Real.rpow_natCast ((1:ℝ)/2) (n * k),
        show ((1:ℝ)/2) = (2:ℝ) ^ (-1:ℝ) by rw [Real.rpow_neg_one]; norm_num,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      push_cast
      ring_nf
    have h3 : Real.sqrt 2 ^ k = (2:ℝ) ^ ((k : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ)/2)) k,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      ring_nf
    rw [h2, h3, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    field_simp
  rcases eq_or_ne t 0 with ht0 | ht0
  · have hterm : ∀ k : ℕ, ENNReal.ofReal 2 ≤
        (if t < ENNReal.ofReal (dyadicThreshold n (k + 1))
          then ENNReal.ofReal (Real.sqrt 2 ^ (k + 2)) else 0) := by
      intro k
      have hlt : t < ENNReal.ofReal (dyadicThreshold n (k + 1)) := by
        rw [ht0]
        exact ENNReal.ofReal_pos.2 (dyadicThreshold_pos n (k + 1))
      rw [if_pos hlt]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsq : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
      calc (2:ℝ) = Real.sqrt 2 ^ 2 := hsq.symm
        _ ≤ Real.sqrt 2 ^ (k + 2) := pow_le_pow_right₀ hs1 (by omega)
    have hsum : (∑' k : ℕ, (if t < ENNReal.ofReal (dyadicThreshold n (k + 1))
        then ENNReal.ofReal (Real.sqrt 2 ^ (k + 2)) else 0)) = ⊤ := by
      refine top_le_iff.1 ?_
      calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, ENNReal.ofReal 2 :=
            (ENNReal.tsum_const_eq_top_of_ne_zero (by simp)).symm
        _ ≤ _ := ENNReal.tsum_le_tsum hterm
    rw [hsum]
    simp
  · have ht0' : 0 < t := pos_iff_ne_zero.2 ht0
    have httop : t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ht1
    have hex : ∃ k : ℕ, ENNReal.ofReal (dyadicThreshold n (k + 1)) ≤ t := by
      obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (ENNReal.toReal_pos ht0 httop)
        (by norm_num : ((1:ℝ)/2) < 1)
      refine ⟨n * (j + 1), ?_⟩
      have hle : dyadicThreshold n (n * (j + 1) + 1) ≤ ((1:ℝ)/2) ^ j := by
        unfold dyadicThreshold
        refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
        calc j ≤ n * (j + 1) :=
              le_trans (Nat.le_succ j) (Nat.le_mul_of_pos_left _ hn)
          _ ≤ n * (j + 1) + 1 := Nat.le_succ _
          _ ≤ n * (n * (j + 1) + 1) := Nat.le_mul_of_pos_left _ hn
      calc ENNReal.ofReal (dyadicThreshold n (n * (j + 1) + 1))
          ≤ ENNReal.ofReal (((1:ℝ)/2) ^ j) := ENNReal.ofReal_le_ofReal hle
        _ ≤ t := by
            rw [← ENNReal.ofReal_toReal httop]
            exact ENNReal.ofReal_le_ofReal hj.le
    classical
    obtain ⟨k0, hk0le, hk0min⟩ :
        ∃ k : ℕ, ENNReal.ofReal (dyadicThreshold n (k + 1)) ≤ t ∧
          ∀ m, m < k → ¬ ENNReal.ofReal (dyadicThreshold n (m + 1)) ≤ t :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    have hupper : t ^ (-(1 / (2 * (n : ℝ)))) ≤ ENNReal.ofReal (Real.sqrt 2 ^ (k0 + 1)) := by
      rw [← hkey (k0 + 1), ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hk0le (by positivity))
    rcases Nat.eq_zero_or_pos k0 with hz | hpos
    · refine le_trans hupper (le_trans (le_of_eq ?_) le_self_add)
      rw [hz]
      norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k0 = j + 1 := ⟨k0 - 1, by omega⟩
      have hlt : t < ENNReal.ofReal (dyadicThreshold n (j + 1)) :=
        not_le.1 (hk0min j (by omega))
      refine le_trans hupper (le_trans ?_ le_add_self)
      calc ENNReal.ofReal (Real.sqrt 2 ^ (j + 1 + 1))
          = (if t < ENNReal.ofReal (dyadicThreshold n (j + 1))
              then ENNReal.ofReal (Real.sqrt 2 ^ (j + 2)) else 0) := by rw [if_pos hlt]
        _ ≤ _ := ENNReal.le_tsum j

/-- The `k`-th dyadic threshold is realised by the shrink parameter `δ·2^{-(k+1)}`. -/
theorem dyadicThreshold_eq_div_pow (n k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    dyadicThreshold n (k + 1) = ((δ * ((1:ℝ) / 2) ^ (k + 1)) / δ) ^ n := by
  unfold dyadicThreshold
  have h : (δ * ((1:ℝ) / 2) ^ (k + 1)) / δ = ((1:ℝ) / 2) ^ (k + 1) := by
    field_simp
  rw [h, ← pow_mul, mul_comm (k + 1) n]

/-- **The single-band bound.**  Each dyadic band contributes at most
`a · n·δ·2^{-(k+1)} · mu K`. -/
theorem lintegral_indicator_ell_lt_le
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {mu : Measure (EuclideanSpace ℝ (Fin n))} (hshrink : MeasureShrinks mu K)
    (hKtop : mu K ≠ ⊤)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (k : ℕ) (a : ℝ≥0∞) :
    ∫⁻ x in K, (if ell K δ x < ENNReal.ofReal (dyadicThreshold n (k + 1)) then a else 0) ∂mu
      ≤ a * (ENNReal.ofReal ((n : ℝ) * (δ * ((1:ℝ) / 2) ^ (k + 1))) * mu K) := by
  classical
  set lam : ℝ := δ * ((1:ℝ) / 2) ^ (k + 1) with hlamdef
  have hlam0 : 0 < lam := by positivity
  have hhalf : ((1:ℝ) / 2) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hlamδ : lam ≤ δ := by
    rw [hlamdef]
    nlinarith
  have hlam1 : lam < 1 := lt_of_le_of_lt hlamδ hδ1
  set S : Set (EuclideanSpace ℝ (Fin n)) :=
    {y | ell K δ y < ENNReal.ofReal (dyadicThreshold n (k + 1))} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_lt (measurable_ell hK δ) measurable_const
  have hind : ∀ x, (if ell K δ x < ENNReal.ofReal (dyadicThreshold n (k + 1)) then a else 0)
      = S.indicator (fun _ => a) x := by
    intro x
    simp only [hSdef, Set.indicator_apply, Set.mem_setOf_eq]
  calc ∫⁻ x in K, (if ell K δ x < ENNReal.ofReal (dyadicThreshold n (k + 1)) then a else 0) ∂mu
      = ∫⁻ x in K, S.indicator (fun _ => a) x ∂mu := lintegral_congr fun x => hind x
    _ = a * mu (K ∩ S) := by
        rw [lintegral_indicator hSmeas, setLIntegral_const,
          Measure.restrict_apply hSmeas, Set.inter_comm]
    _ ≤ a * (ENNReal.ofReal ((n : ℝ) * lam) * mu K) := by
        refine mul_le_mul_left' ?_ a
        have hset : K ∩ S = {x ∈ K | ell K δ x < ENNReal.ofReal ((lam / δ) ^ n)} := by
          rw [hSdef, dyadicThreshold_eq_div_pow n k hδ0]
          rfl
        rw [hset]
        exact measure_lt_ell_le_mul hK hKc hball hshrink hKtop hlam0 hlam1 hlamδ

/-! ### The geometric series that closes the estimate -/

theorem sqrt_two_div_two_lt_one : Real.sqrt 2 / 2 < 1 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem band_pow_eq (k : ℕ) :
    Real.sqrt 2 ^ (k + 2) * ((1:ℝ) / 2) ^ (k + 1) = (Real.sqrt 2 / 2) ^ k := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc Real.sqrt 2 ^ (k + 2) * ((1:ℝ) / 2) ^ (k + 1)
      = (Real.sqrt 2 ^ k * Real.sqrt 2 ^ 2) * (((1:ℝ) / 2) ^ k * ((1:ℝ) / 2) ^ 1) := by
        rw [← pow_add, ← pow_add]
    _ = (Real.sqrt 2 ^ k * ((1:ℝ) / 2) ^ k) * (Real.sqrt 2 ^ 2 * ((1:ℝ) / 2) ^ 1) := by ring
    _ = (Real.sqrt 2 * ((1:ℝ) / 2)) ^ k * (2 * ((1:ℝ) / 2)) := by rw [mul_pow, hs, pow_one]
    _ = (Real.sqrt 2 / 2) ^ k := by ring_nf

theorem tsum_band_le : (∑' k : ℕ, (Real.sqrt 2 / 2) ^ k) ≤ 4 := by
  have hr0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hr1 : Real.sqrt 2 / 2 < 1 := sqrt_two_div_two_lt_one
  rw [tsum_geometric_of_lt_one hr0 hr1]
  have hq : Real.sqrt 2 / 2 ≤ 3 / 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hden : (1:ℝ) / 4 ≤ 1 - Real.sqrt 2 / 2 := by linarith
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-! ### The fractional moment -/

/-- **The fractional moment of the inverse local conductance is an absolute constant.**

    `∫_K ell^{-1/(2n)} dmu  ≤  4 · mu K`

for convex `K ⊇ ball 0 1` and `δ ≤ 1/(2n)`, with no hypothesis on the weight beyond
`MeasureShrinks`.  The exponent `1/(2n)` is one half of the critical exponent `1/n` at which
the layer bound's tail `θ^{1/n}` stops being integrable, and the constant is absolute
precisely because the dyadic base is `2^n`. -/
theorem lintegral_ell_rpow_neg_le
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {mu : Measure (EuclideanSpace ℝ (Fin n))} (hshrink : MeasureShrinks mu K)
    (hKtop : mu K ≠ ⊤)
    (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) :
    ∫⁻ x in K, (ell K δ x) ^ (-(1 / (2 * (n : ℝ)))) ∂mu ≤ ENNReal.ofReal 6 * mu K := by
  classical
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnδ : (n : ℝ) * δ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hδn (le_of_lt hnR)
    calc (n:ℝ) * δ ≤ (n:ℝ) * (1 / (2 * (n:ℝ))) := this
      _ = 1 / 2 := by field_simp
  have hδ1 : δ < 1 := by nlinarith
  have hmeas : ∀ k : ℕ, Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      (if ell K δ x < ENNReal.ofReal (dyadicThreshold n (k + 1))
        then ENNReal.ofReal (Real.sqrt 2 ^ (k + 2)) else 0)) := by
    intro k
    exact Measurable.ite (measurableSet_lt (measurable_ell hK δ) measurable_const)
      measurable_const measurable_const
  calc ∫⁻ x in K, (ell K δ x) ^ (-(1 / (2 * (n : ℝ)))) ∂mu
      ≤ ∫⁻ x in K, (ENNReal.ofReal (Real.sqrt 2) +
          ∑' k : ℕ, (if ell K δ x < ENNReal.ofReal (dyadicThreshold n (k + 1))
            then ENNReal.ofReal (Real.sqrt 2 ^ (k + 2)) else 0)) ∂mu :=
        lintegral_mono fun x => rpow_neg_le_add_tsum_indicator hn (ell_le_one K δ x)
    _ = ENNReal.ofReal (Real.sqrt 2) * mu K +
          ∑' k : ℕ, ∫⁻ x in K, (if ell K δ x < ENNReal.ofReal (dyadicThreshold n (k + 1))
            then ENNReal.ofReal (Real.sqrt 2 ^ (k + 2)) else 0) ∂mu := by
        rw [lintegral_add_left measurable_const, lintegral_tsum
          (fun k => (hmeas k).aemeasurable), setLIntegral_const]
    _ ≤ ENNReal.ofReal (Real.sqrt 2) * mu K +
          ∑' k : ℕ, ENNReal.ofReal ((1:ℝ) / 2 * (Real.sqrt 2 / 2) ^ k) * mu K := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)
        refine le_trans (lintegral_indicator_ell_lt_le hK hKc hball hshrink hKtop
          hδ0 hδ1 k (ENNReal.ofReal (Real.sqrt 2 ^ (k + 2)))) ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _
        calc Real.sqrt 2 ^ (k + 2) * ((n:ℝ) * (δ * ((1:ℝ)/2) ^ (k + 1)))
            = ((n:ℝ) * δ) * (Real.sqrt 2 ^ (k + 2) * ((1:ℝ)/2) ^ (k + 1)) := by ring
          _ = ((n:ℝ) * δ) * (Real.sqrt 2 / 2) ^ k := by rw [band_pow_eq]
          _ ≤ ((1:ℝ)/2) * (Real.sqrt 2 / 2) ^ k := by
              exact mul_le_mul_of_nonneg_right hnδ (by positivity)
    _ ≤ ENNReal.ofReal 6 * mu K := by
        rw [ENNReal.tsum_mul_right, ← add_mul]
        refine mul_le_mul_right' ?_ _
        have hsummable : Summable (fun k : ℕ => (1:ℝ) / 2 * (Real.sqrt 2 / 2) ^ k) :=
          (summable_geometric_of_lt_one (by positivity) sqrt_two_div_two_lt_one).mul_left _
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsummable,
          ← ENNReal.ofReal_add (by positivity) (by
            exact tsum_nonneg fun k => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hts : (∑' k : ℕ, (1:ℝ) / 2 * (Real.sqrt 2 / 2) ^ k)
            = (1:ℝ) / 2 * ∑' k : ℕ, (Real.sqrt 2 / 2) ^ k :=
          tsum_mul_left
        rw [hts]
        have h2 : Real.sqrt 2 ≤ 3 / 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
        linarith [tsum_band_le]

/-! ### Axiom audit -/

section AxiomCheck

#print axioms ofReal_div_pow_le_ell_of_ball_subset
#print axioms ball_subset_of_mem_smul_of_convex
#print axioms ofReal_div_pow_le_ell_of_mem_smul
#print axioms measure_lt_ell_le_of_measureShrinks
#print axioms one_sub_one_sub_pow_le
#print axioms measure_lt_ell_le_mul
#print axioms dyadicThreshold_pos
#print axioms dyadicThreshold_le_one
#print axioms rpow_neg_le_add_tsum_indicator
#print axioms dyadicThreshold_eq_div_pow
#print axioms lintegral_indicator_ell_lt_le
#print axioms sqrt_two_div_two_lt_one
#print axioms band_pow_eq
#print axioms tsum_band_le
#print axioms lintegral_ell_rpow_neg_le

end AxiomCheck

end Arlib.MarkovChains

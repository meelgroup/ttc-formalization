import Kr25Ssmxt.Analysis.OracleContracts
import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.KV97HitAndRunSampling
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Geometry of the sampler's unit-inball chart

The normalized finite-facet body is the exact inverse image of the KV97
inflated decimal-scaled body. This equality is the geometric bridge needed
before the normalized walk can replace the current absolute-diameter walk.
-/

namespace Kr25Ssmxt

open Set
open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace

private theorem volume_preimage_samplerChart {n : Nat} {γ : Real} (hγ : 0 < γ)
    (cen : EuclideanSpace Real (Fin n)) (A : Set (EuclideanSpace Real (Fin n))) :
    volume ((fun z : EuclideanSpace Real (Fin n) => γ • z + cen) ⁻¹' A) =
      ENNReal.ofReal ((γ ^ n)⁻¹) * volume A := by
  have hpre : (fun z : EuclideanSpace Real (Fin n) => γ • z + cen) ⁻¹' A =
      (fun z : EuclideanSpace Real (Fin n) => γ • z) ⁻¹'
        ((fun z : EuclideanSpace Real (Fin n) => z + cen) ⁻¹' A) := rfl
  rw [hpre, Measure.addHaar_preimage_smul volume hγ.ne', measure_preimage_add_right,
    finrank_euclideanSpace_fin, abs_of_pos (by positivity : (0 : Real) < (γ ^ n)⁻¹)]

private theorem map_uniformOn_samplerChart {n : Nat} {γ : Real} (hγ : 0 < γ)
    (cen : EuclideanSpace Real (Fin n))
    {A : Set (EuclideanSpace Real (Fin n))} (hA : MeasurableSet A) :
    Measure.map (fun z : EuclideanSpace Real (Fin n) => γ • z + cen)
      (ArlibCommunity.Foundations.Convex.uniformOn volume ((fun z : EuclideanSpace Real (Fin n) => γ • z + cen) ⁻¹' A)) =
        ArlibCommunity.Foundations.Convex.uniformOn volume A := by
  have hS : Measurable (fun z : EuclideanSpace Real (Fin n) => γ • z + cen) := by fun_prop
  ext t ht
  rw [Measure.map_apply hS ht, ArlibCommunity.Foundations.Convex.uniformOn_apply volume (hA.preimage hS)
    (ht.preimage hS), ArlibCommunity.Foundations.Convex.uniformOn_apply volume hA ht, ← Set.preimage_inter,
    volume_preimage_samplerChart hγ, volume_preimage_samplerChart hγ]
  exact ENNReal.mul_div_mul_left _ _
    ((ENNReal.ofReal_pos.2 (by positivity : 0 < (γ ^ n)⁻¹)).ne') ENNReal.ofReal_ne_top

theorem PolytopeData.normalizedHitAndRunBody_eq_preimage {n : Nat}
    (P : PolytopeData n) (b : Nat) (eta : Real) :
    P.normalizedHitAndRunBody b eta =
      P.samplerChart b ⁻¹' hitAndRunBody P b eta := by
  have hG : 0 < P.scaledInradius b :=
    mul_pos (by unfold decimalScale; positivity) P.inradius_pos
  ext y
  change (∀ i, ⟪P.arlibNormal i, y⟫_Real ≤
      (hitAndRunOffset P b eta i -
        ⟪P.arlibNormal i, P.scaledIncenter b⟫_Real) / P.scaledInradius b) ↔
    ∀ i, ⟪P.arlibNormal i, P.samplerChart b y⟫_Real ≤
      hitAndRunOffset P b eta i
  constructor
  · intro hy i
    have hi := (le_div_iff₀ hG).mp (hy i)
    dsimp only [PolytopeData.samplerChart]
    simp only [inner_add_right, real_inner_smul_right]
    nlinarith
  · intro hy i
    apply (le_div_iff₀ hG).mpr
    have hi := hy i
    dsimp only [PolytopeData.samplerChart] at hi
    simp only [inner_add_right, real_inner_smul_right] at hi
    nlinarith

theorem PolytopeData.normalizedHitAndRun_unitBall {n : Nat}
    (P : PolytopeData n) (b : Nat) (eta : Real) :
    Metric.closedBall (0 : EuclideanSpace Real (Fin n)) 1 ⊆
      P.normalizedHitAndRunBody b eta := by
  have hG : 0 < P.scaledInradius b :=
    mul_pos (by unfold decimalScale; positivity) P.inradius_pos
  rw [P.normalizedHitAndRunBody_eq_preimage b eta]
  intro y hy
  have hy' : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hy
  have hdist : dist (P.samplerChart b y) (P.scaledIncenter b) ≤
      P.scaledInradius b := by
    simp only [PolytopeData.samplerChart, dist_eq_norm, add_sub_cancel_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hG]
    nlinarith
  have hscaled : P.samplerChart b y ∈ P.scaledBody b := by
    apply P.scaledBody_inball b
    exact Metric.mem_closedBall.mpr hdist
  exact ArlibCommunity.Algorithms.KV97.body_subset_inflated P.arlibNormal (P.scaledOffset b)
    (P.presentation.facetCount : Real) ArlibCommunity.Algorithms.KV97.cOf_nonneg hscaled

theorem PolytopeData.normalizedHitAndRun_bounded {n : Nat}
    (P : PolytopeData n) (b : Nat) (eta : Real) :
    Bornology.IsBounded (P.normalizedHitAndRunBody b eta) := by
  have hG : 0 < P.scaledInradius b :=
    mul_pos (by unfold decimalScale; positivity) P.inradius_pos
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp (P.hitAndRunBody_bounded b eta)
  apply Metric.isBounded_iff.mpr
  refine ⟨D / P.scaledInradius b, ?_⟩
  intro x hx y hy
  have hx' : P.samplerChart b x ∈ hitAndRunBody P b eta := by
    rwa [P.normalizedHitAndRunBody_eq_preimage b eta] at hx
  have hy' : P.samplerChart b y ∈ hitAndRunBody P b eta := by
    rwa [P.normalizedHitAndRunBody_eq_preimage b eta] at hy
  have hdist := hD hx' hy'
  have heq : dist (P.samplerChart b x) (P.samplerChart b y) =
      P.scaledInradius b * dist x y := by
    simp [PolytopeData.samplerChart, dist_add_right, dist_smul₀,
      Real.norm_eq_abs, abs_of_pos hG]
  rw [heq] at hdist
  exact (le_div_iff₀ hG).2 (by nlinarith)

/-- The scaled body has the diameter certified by the preprocessing outer radius. -/
theorem PolytopeData.scaledBody_dist_le_outerRadius {n : Nat}
    (P : PolytopeData n) (b : Nat) :
    ∀ x ∈ P.scaledBody b, ∀ y ∈ P.scaledBody b,
      dist x y ≤ 2 * decimalScale b * P.outerRadius := by
  intro x hx y hy
  rw [← P.image_decimalScale_eq_scaledBody b] at hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hs : 0 ≤ decimalScale b := (decimalScale_pos b).le
  have hxn : ‖decimalScale b • toEuclidean x₀‖ ≤
      decimalScale b * P.outerRadius := by
    simpa only [toEuclidean, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] using
      mul_le_mul_of_nonneg_left (P.outer_bound x₀ hx₀) hs
  have hyn : ‖decimalScale b • toEuclidean y₀‖ ≤
      decimalScale b * P.outerRadius := by
    simpa only [toEuclidean, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] using
      mul_le_mul_of_nonneg_left (P.outer_bound y₀ hy₀) hs
  have htriangle : dist (decimalScale b • toEuclidean x₀)
      (decimalScale b • toEuclidean y₀) ≤
      ‖decimalScale b • toEuclidean x₀‖ +
        ‖decimalScale b • toEuclidean y₀‖ := by
    simpa [dist_eq_norm] using
      (norm_sub_le (decimalScale b • toEuclidean x₀)
        (decimalScale b • toEuclidean y₀))
  linarith

/-- Inflation and normalization leave only the radius ratio in the diameter. -/
theorem PolytopeData.normalizedHitAndRun_diameter_le {n : Nat}
    (P : PolytopeData n) (b : Nat) (eta : Real) :
    Metric.diam (P.normalizedHitAndRunBody b eta) ≤
      (1 + ArlibCommunity.Algorithms.KV97.kappaOf (ArlibCommunity.Algorithms.KV97.cOf eta)
        (P.presentation.facetCount : Real) / P.scaledInradius b) *
        (2 * P.outerRadius / P.inradius) := by
  have hG : 0 < P.scaledInradius b :=
    mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (P.scaledIncenter b) (P.scaledInradius b) ⊆
      P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  let κ := ArlibCommunity.Algorithms.KV97.kappaOf (ArlibCommunity.Algorithms.KV97.cOf eta)
    (P.presentation.facetCount : Real)
  let C := (1 + κ / P.scaledInradius b) * (2 * P.outerRadius / P.inradius)
  have hκ : 0 ≤ κ := ArlibCommunity.Algorithms.KV97.kappaOf_nonneg ArlibCommunity.Algorithms.KV97.cOf_nonneg
  have hdist : ∀ x ∈ P.normalizedHitAndRunBody b eta,
      ∀ y ∈ P.normalizedHitAndRunBody b eta, dist x y ≤ C := by
    intro x hx y hy
    have hx' : P.samplerChart b x ∈ hitAndRunBody P b eta := by
      rwa [P.normalizedHitAndRunBody_eq_preimage b eta] at hx
    have hy' : P.samplerChart b y ∈ hitAndRunBody P b eta := by
      rwa [P.normalizedHitAndRunBody_eq_preimage b eta] at hy
    have hbound := dist_le_of_mem_inflated hG ArlibCommunity.Algorithms.KV97.cOf_nonneg hbaseball
      (P.scaledBody_dist_le_outerRadius b)
      (P.samplerChart b x) hx' (P.samplerChart b y) hy'
    have heq : dist (P.samplerChart b x) (P.samplerChart b y) =
        P.scaledInradius b * dist x y := by
      simp [PolytopeData.samplerChart, dist_add_right, dist_smul₀,
        Real.norm_eq_abs, abs_of_pos hG]
    rw [heq] at hbound
    have hscale : 0 < decimalScale b := decimalScale_pos b
    calc
      dist x y ≤ ((1 + κ / P.scaledInradius b) *
          (2 * decimalScale b * P.outerRadius)) / P.scaledInradius b :=
        (le_div_iff₀ hG).2 (by simpa only [mul_comm] using hbound)
      _ = C := by
        simp only [C, PolytopeData.scaledInradius]
        field_simp
        <;> ring
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (add_nonneg zero_le_one (div_nonneg hκ hG.le))
      (div_nonneg (mul_nonneg (by norm_num) P.outerRadius_nonneg) P.inradius_pos.le)
  exact Metric.diam_le_of_forall_dist_le hC hdist

/-! ## The paper's walk length `T` and accuracy `ν`

`normalizedHitAndRunSteps` and `hitAndRunTolerance` are the paper's parameters
(`eq:sampler-parameters`), computed from `γ`, the enclosing radius, `b`, `ε`, `n` and the
facet count only. Under the precision hypothesis of Corollary `cor:linf` this `T` is at least
arlib-community's proved mixing deadline at the true diameter and warmness of the walk's
body, and this `ν` is at most the inverse-volume accuracy KV97 rounding needs. -/

theorem PolytopeData.inradius_le_outerRadius {n : Nat}
    (P : PolytopeData n) (hn : 0 < n) : P.inradius ≤ P.outerRadius := by
  let e : Point n := Pi.single ⟨0, hn⟩ (1 : Real)
  have he : ‖e‖ = 1 := by simp [e, Pi.norm_single]
  have heE : ‖toEuclidean e‖ = 1 := by
    simp [toEuclidean, e]
  let x : Point n := P.incenter + P.inradius • e
  let y : Point n := P.incenter - P.inradius • e
  have hx : x ∈ P.carrier := by
    apply P.inball
    change ‖(WithLp.toLp 2 (x - P.incenter) : EuclideanSpace Real (Fin n))‖ ≤ P.inradius
    have hxc : x - P.incenter = P.inradius • e := by simp [x]
    rw [hxc, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos P.inradius_pos]
    change P.inradius * ‖toEuclidean e‖ ≤ _
    rw [heE, mul_one]
  have hy : y ∈ P.carrier := by
    apply P.inball
    change ‖(WithLp.toLp 2 (y - P.incenter) : EuclideanSpace Real (Fin n))‖ ≤ P.inradius
    have hyc : y - P.incenter = -(P.inradius • e) := by simp [y]
    rw [hyc, WithLp.toLp_neg, norm_neg, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos P.inradius_pos]
    change P.inradius * ‖toEuclidean e‖ ≤ _
    rw [heE, mul_one]
  have hxR := P.outer_bound x hx
  have hyR := P.outer_bound y hy
  have hxy : dist (toEuclidean x) (toEuclidean y) = 2 * P.inradius := by
    have heq : toEuclidean x - toEuclidean y =
        (2 * P.inradius) • toEuclidean e := by
      ext i
      simp [x, y, toEuclidean, PiLp.smul_apply, PiLp.add_apply]
      ring
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by nlinarith [P.inradius_pos] : 0 < 2 * P.inradius), heE]
    ring
  have htri : dist (toEuclidean x) (toEuclidean y) ≤
      ‖toEuclidean x‖ + ‖toEuclidean y‖ := by
    simpa [dist_eq_norm] using norm_sub_le (toEuclidean x) (toEuclidean y)
  change ‖toEuclidean x‖ ≤ P.outerRadius at hxR
  change ‖toEuclidean y‖ ≤ P.outerRadius at hyR
  linarith

/-- The precision requirement dominates both `16 / ε` and `128 κ`. -/
theorem samplerRadiusRequirement_ge {n : Nat} (P : PolytopeData n) (hn : 0 < n)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    16 / eta ≤ samplerRadiusRequirement P eta ∧
      128 * P.samplerKappa eta ≤ samplerRadiusRequirement P eta := by
  let r : Real := P.presentation.facetCount
  let L : Real := Real.log (32 * r / eta)
  have hr : 1 ≤ r := by
    have hfac : 1 ≤ P.presentation.facetCount := by
      have := P.facets_pos
      omega
    change (1 : Real) ≤ (P.presentation.facetCount : Real)
    exact_mod_cast hfac
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
  have hfour : 4 / eta ≤ 32 * r / eta :=
    div_le_div_of_nonneg_right (by nlinarith) heta0.le
  have hrx : r ≤ 32 * r / eta := by
    apply (le_div_iff₀ heta0).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ r) (sub_nonneg.mpr heta1)]
  have h32 : (32 : Real) ≤ 32 * r / eta := by
    apply (le_div_iff₀ heta0).2
    nlinarith
  have hL1 : 1 ≤ L := by
    have he : Real.exp 1 ≤ 32 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : Real) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 32 := Real.log_le_log (Real.exp_pos 1) he
      _ ≤ L := Real.log_le_log (by norm_num) h32
  have hL : 0 ≤ L := by linarith
  have hsqrtL : 1 ≤ Real.sqrt L := by
    rw [show (1 : Real) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL1
  have hc : ArlibCommunity.Algorithms.KV97.cOf eta ≤ Real.sqrt (2 * L) := by
    unfold ArlibCommunity.Algorithms.KV97.cOf
    apply Real.sqrt_le_sqrt
    gcongr
    exact Real.log_le_log (by positivity) hfour
  have hrroot : Real.sqrt (2 * Real.log r) ≤ Real.sqrt (2 * L) := by
    apply Real.sqrt_le_sqrt
    gcongr
    exact Real.log_le_log (by linarith) hrx
  have hroot : Real.sqrt (2 * L) ≤ 2 * Real.sqrt L := by
    have h1 := Real.sq_sqrt (by positivity : 0 ≤ 2 * L)
    have h2 := Real.sq_sqrt hL
    have h3 := Real.sqrt_nonneg (2 * L)
    have h4 := Real.sqrt_nonneg L
    nlinarith
  have hκ : P.samplerKappa eta ≤ 4 * Real.sqrt L := by
    unfold PolytopeData.samplerKappa ArlibCommunity.Algorithms.KV97.kappaOf
    change ArlibCommunity.Algorithms.KV97.cOf eta + Real.sqrt (2 * Real.log r) ≤ _
    linarith
  have hreq : samplerRadiusRequirement P eta = (512 * (n : Real) / eta) * Real.sqrt L := rfl
  have h512 : 512 ≤ 512 * (n : Real) / eta := (le_div_iff₀ heta0).2 (by nlinarith)
  rw [hreq]
  constructor
  · have h1 : 16 / eta ≤ 512 * (n : Real) / eta :=
      div_le_div_of_nonneg_right (by nlinarith) heta0.le
    calc 16 / eta ≤ 512 * (n : Real) / eta := h1
      _ = 512 * (n : Real) / eta * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrtL (by positivity)
  · have := mul_le_mul_of_nonneg_right h512 (Real.sqrt_nonneg L)
    nlinarith

/-- The sampler's radii under the precision hypothesis: `16/ε ≤ γ/h`, `128 κ ≤ γ/h`,
`γ/h ≤ R₀/h ≤ R'₀/h`. -/
theorem PolytopeData.samplerRadii {n : Nat} (hn : 0 < n) (P : PolytopeData n) (b : Nat)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hprec : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius) :
    16 / eta ≤ P.scaledInradius b ∧
      128 * P.samplerKappa eta ≤ P.scaledInradius b ∧
      P.scaledInradius b ≤ decimalScale b * P.outerRadius ∧
      decimalScale b * P.outerRadius ≤ P.samplerOuterRadius b eta := by
  obtain ⟨h16, h128⟩ := samplerRadiusRequirement_ge P hn heta0 heta1
  have hγ : P.scaledInradius b = decimalScale b * P.inradius := rfl
  have hκ0 : 0 ≤ P.samplerKappa eta :=
    ArlibCommunity.Algorithms.KV97.kappaOf_nonneg ArlibCommunity.Algorithms.KV97.cOf_nonneg
  have hpos : 0 < P.scaledInradius b := mul_pos (decimalScale_pos b) P.inradius_pos
  refine ⟨by rw [hγ]; exact h16.trans hprec, by rw [hγ]; exact h128.trans hprec, ?_, ?_⟩
  · rw [hγ]
    exact mul_le_mul_of_nonneg_left (P.inradius_le_outerRadius hn) (decimalScale_pos b).le
  · unfold PolytopeData.samplerOuterRadius
    have : 0 ≤ P.samplerKappa eta / P.scaledInradius b := div_nonneg hκ0 hpos.le
    have hR : 0 ≤ decimalScale b * P.outerRadius :=
      mul_nonneg (decimalScale_pos b).le P.outerRadius_nonneg
    nlinarith

/-- The inflated body `P'` has diameter at most `2 R'₀ / h`. -/
theorem PolytopeData.hitAndRunBody_dist_le_samplerOuterRadius {n : Nat}
    (P : PolytopeData n) (b : Nat) (eta : Real) :
    ∀ x ∈ hitAndRunBody P b eta, ∀ y ∈ hitAndRunBody P b eta,
      dist x y ≤ 2 * P.samplerOuterRadius b eta := by
  have hG : 0 < P.scaledInradius b := mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (P.scaledIncenter b) (P.scaledInradius b) ⊆
      P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  intro x hx y hy
  have h := dist_le_of_mem_inflated hG ArlibCommunity.Algorithms.KV97.cOf_nonneg hbaseball
    (P.scaledBody_dist_le_outerRadius b) x hx y hy
  unfold PolytopeData.samplerOuterRadius PolytopeData.samplerKappa
  calc dist x y ≤ _ := h
    _ = _ := by ring

/-- A set of diameter at most `d` has volume at most `dⁿ` (it lies in a box of side `d`). -/
theorem euclidean_volume_le_ofReal_pow_of_dist_le {n : Nat}
    {A : Set (EuclideanSpace Real (Fin n))} {d : Real}
    (h : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) :
    volume A ≤ ENNReal.ofReal d ^ n := by
  let e := (MeasurableEquiv.toLp 2 (Fin n → Real)).symm
  have hpres : MeasurePreserving e volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  have hA : volume A = volume (e '' A) := by
    rw [← hpres.measure_preimage_equiv (e '' A), e.preimage_image]
  have hlip : LipschitzWith 1 (fun x : EuclideanSpace Real (Fin n) => e x) :=
    PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => Real)
  have hdiam : Metric.ediam (e '' A) ≤ ENNReal.ofReal d := by
    calc Metric.ediam (e '' A) ≤ 1 * Metric.ediam A := hlip.ediam_image_le A
      _ = Metric.ediam A := one_mul _
      _ ≤ ENNReal.ofReal d := Metric.ediam_le fun x hx y hy => by
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal (h x hx y hy)
  rw [hA]
  calc volume (e '' A) ≤ Metric.ediam (e '' A) ^ Fintype.card (Fin n) :=
        Real.volume_pi_le_diam_pow _
    _ ≤ ENNReal.ofReal d ^ n := by
        rw [Fintype.card_fin]
        gcongr

theorem PolytopeData.normalizedHitAndRun_warmness_ge_one {n : Nat}
    (P : PolytopeData n) (b : Nat) (eta : Real) :
    1 ≤ (volume (P.normalizedHitAndRunBody b eta) /
      volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal := by
  let B := Metric.ball (0 : EuclideanSpace Real (Fin n)) 1
  let K := P.normalizedHitAndRunBody b eta
  have hB0 : volume B ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hKtop : volume K ≠ ⊤ := (P.normalizedHitAndRun_bounded b eta).measure_lt_top.ne
  have hsubset : B ⊆ K :=
    Metric.ball_subset_closedBall.trans (P.normalizedHitAndRun_unitBall b eta)
  have hreal : (volume B).toReal ≤ (volume K).toReal :=
    ENNReal.toReal_mono hKtop (measure_mono hsubset)
  have hBreal : 0 < (volume B).toReal := ENNReal.toReal_pos hB0 hBtop
  rw [ENNReal.toReal_div]
  exact (one_le_div hBreal).2 hreal

theorem PolytopeData.normalizedHitAndRun_warmness_le_diameter_pow
    {n : Nat} (hn : 0 < n) (P : PolytopeData n) (b : Nat)
    (eta R : Real) (hR : 0 ≤ R)
    (hdiam : Metric.diam (P.normalizedHitAndRunBody b eta) ≤ R) :
    (volume (P.normalizedHitAndRunBody b eta) /
      volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal ≤
        (R + 1) ^ n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let K := P.normalizedHitAndRunBody b eta
  let B := Metric.ball (0 : EuclideanSpace Real (Fin n)) 1
  let BR := Metric.ball (0 : EuclideanSpace Real (Fin n)) (R + 1)
  have h0 : (0 : EuclideanSpace Real (Fin n)) ∈ K := by
    apply P.normalizedHitAndRun_unitBall b eta
    simp [Metric.mem_closedBall]
  have hsubset : K ⊆ BR := by
    intro x hx
    have hdist := Metric.dist_le_diam_of_mem (P.normalizedHitAndRun_bounded b eta)
      hx h0
    change dist x 0 ≤ Metric.diam K at hdist
    have : ‖x‖ < R + 1 := by
      simpa [dist_zero_right] using lt_of_le_of_lt (hdist.trans hdiam) (by linarith)
    simpa [BR, Metric.mem_ball, dist_zero_right] using this
  have hBRtop : volume BR ≠ ⊤ := measure_ball_lt_top.ne
  have hB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hBreal : 0 < (volume B).toReal := ENNReal.toReal_pos hB0 hBtop
  have hvol : (volume K).toReal ≤ (volume BR).toReal :=
    ENNReal.toReal_mono hBRtop (measure_mono hsubset)
  have hball : (volume BR).toReal = (R + 1) ^ n * (volume B).toReal := by
    dsimp only [BR, B]
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ R + 1)]
    norm_num
  rw [ENNReal.toReal_div]
  exact (div_le_iff₀ hBreal).2 (by rw [hball] at hvol; linarith)

/-- The arithmetic of `log (M/ν) ≤ 3n log (2R'₀/h)` (proof of Corollary `cor:linf`),
with arlib-community's `2^64 n² D² log (8M/ν²)` deadline in place of `[LV04]`'s. -/
private theorem deadline_le_walkLength {n : Nat} (hn : 21 ≤ n)
    {a S M ν eta D : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (ha1 : 1 ≤ a) (haS : a ≤ S) (hS : 32 / eta ≤ 2 * S)
    (hM1 : 1 ≤ M) (hM : M ≤ (2 * a + 1) ^ n)
    (hν : ν = eta / (16 * (2 * S) ^ n))
    (hD0 : 0 ≤ D) (hD : D ≤ 2 * a) :
    2 ^ 64 * (n : Real) ^ 2 * D ^ 2 * Real.log (8 * M / ν ^ 2) ≤
      2 ^ 68 * (n : Real) ^ 3 * a ^ 2 * Real.log (2 * S) := by
  have hnR : (21 : Real) ≤ n := by exact_mod_cast hn
  have h32 : (32 : Real) ≤ 2 * S := by
    have : (32 : Real) ≤ 32 / eta := (le_div_iff₀ heta0).2 (by linarith)
    linarith
  have hS0 : 0 < 2 * S := by linarith
  let L := Real.log (2 * S)
  have hL1 : 1 ≤ L := by
    have he : Real.exp 1 ≤ 2 * S := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : Real) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos 1) he
  have h8 : Real.log 8 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have h16 : Real.log 16 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have heta : -Real.log eta ≤ L := by
    have h1 : Real.log (32 / eta) ≤ L := Real.log_le_log (by positivity) hS
    rw [Real.log_div (by norm_num) heta0.ne'] at h1
    have : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
    linarith
  have hetaneg : 0 ≤ -Real.log eta := by
    have := Real.log_nonpos heta0.le heta1
    linarith
  have hM0 : 0 < M := by linarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlogM : Real.log M ≤ (n : Real) * (L + 1 / 2) := by
    have h3 : 2 * a + 1 ≤ (3 / 2) * (2 * S) := by linarith
    have hpow : M ≤ ((3 / 2) * (2 * S)) ^ n :=
      hM.trans (pow_le_pow_left₀ (by linarith) h3 n)
    have hlog := Real.log_le_log hM0 hpow
    rw [Real.log_pow, Real.log_mul (by norm_num) hS0.ne'] at hlog
    have h32' : Real.log (3 / 2) ≤ 1 / 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : Real) < 3 / 2 by norm_num)
      linarith
    have hn0 : (0 : Real) ≤ n := by positivity
    nlinarith
  have hνpos : 0 < ν := by rw [hν]; positivity
  have hX : Real.log (8 * M / ν ^ 2) =
      Real.log 8 + Real.log M + 2 * Real.log 16 + 2 * (n : Real) * L - 2 * Real.log eta := by
    have hSn : 0 < (2 * S) ^ n := pow_pos hS0 n
    rw [Real.log_div (by positivity : (8 : Real) * M ≠ 0) (pow_pos hνpos 2).ne',
      Real.log_mul (by norm_num) hM0.ne', Real.log_pow, hν,
      Real.log_div heta0.ne' (mul_pos (by norm_num) hSn).ne',
      Real.log_mul (by norm_num) hSn.ne', Real.log_pow]
    simp only [L]
    push_cast
    ring
  have hX0 : 0 ≤ Real.log (8 * M / ν ^ 2) := by
    rw [hX]
    have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    have : 0 ≤ (n : Real) * L := by positivity
    linarith
  have hXle : Real.log (8 * M / ν ^ 2) ≤ 4 * (n : Real) * L := by
    rw [hX]
    nlinarith
  have hD2 : D ^ 2 ≤ 4 * a ^ 2 := by nlinarith
  have hn2 : (0 : Real) ≤ (n : Real) ^ 2 := by positivity
  calc 2 ^ 64 * (n : Real) ^ 2 * D ^ 2 * Real.log (8 * M / ν ^ 2) ≤
        2 ^ 64 * (n : Real) ^ 2 * (4 * a ^ 2) * (4 * (n : Real) * L) := by
        gcongr
    _ = 2 ^ 68 * (n : Real) ^ 3 * a ^ 2 * L := by ring

/-- The paper's walk length is at least arlib-community's mixing deadline. -/
theorem PolytopeData.hitAndRun_deadline_le_steps {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat) {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hprec : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius) :
    ArlibCommunity.Algorithms.HitAndRun.deadline n
      (Metric.diam (P.normalizedHitAndRunBody b eta))
      (volume (P.normalizedHitAndRunBody b eta) /
        volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal
      (hitAndRunTolerance P b eta) ≤ (normalizedHitAndRunSteps P b eta : Real) := by
  obtain ⟨h16, -, hγR, hRS⟩ := P.samplerRadii (by omega) b heta0 heta1 hprec
  have hγ : 0 < P.scaledInradius b := mul_pos (decimalScale_pos b) P.inradius_pos
  have hγ1 : 1 ≤ P.scaledInradius b := by
    have : (1 : Real) ≤ 16 / eta := (le_div_iff₀ heta0).2 (by linarith)
    linarith
  have hγS : P.scaledInradius b ≤ P.samplerOuterRadius b eta := hγR.trans hRS
  have hS0 : 0 ≤ P.samplerOuterRadius b eta := hγ.le.trans hγS
  have ha1 : 1 ≤ P.samplerOuterRadius b eta / P.scaledInradius b :=
    (one_le_div hγ).2 hγS
  have haS : P.samplerOuterRadius b eta / P.scaledInradius b ≤
      P.samplerOuterRadius b eta := div_le_self hS0 hγ1
  have hS : 32 / eta ≤ 2 * P.samplerOuterRadius b eta := by
    have : 32 / eta = 2 * (16 / eta) := by ring
    linarith
  have hD := P.normalizedHitAndRun_diameter_le b eta
  have hDa : Metric.diam (P.normalizedHitAndRunBody b eta) ≤
      2 * (P.samplerOuterRadius b eta / P.scaledInradius b) := by
    refine hD.trans (le_of_eq ?_)
    have hd := decimalScale_pos b
    have hi := P.inradius_pos
    unfold PolytopeData.samplerOuterRadius PolytopeData.samplerKappa
    simp only [PolytopeData.scaledInradius]
    field_simp
  have hD0 : 0 ≤ Metric.diam (P.normalizedHitAndRunBody b eta) := Metric.diam_nonneg
  have hM := P.normalizedHitAndRun_warmness_le_diameter_pow (by omega) b eta _
    (by positivity : (0 : Real) ≤
      2 * (P.samplerOuterRadius b eta / P.scaledInradius b)) hDa
  have hM1 := P.normalizedHitAndRun_warmness_ge_one b eta
  have hmain := deadline_le_walkLength hn heta0 heta1 ha1 haS hS hM1 hM rfl hD0 hDa
  unfold ArlibCommunity.Algorithms.HitAndRun.deadline
  refine hmain.trans ?_
  unfold normalizedHitAndRunSteps hitAndRunWalkConstant
  exact Nat.le_ceil _

/-- The paper's walk from the uniform inball start is `ν`-close to uniform on `P'`, and
`ν` is within the inverse-volume accuracy required by KV97 rounding. -/
theorem PolytopeData.normalizedHitAndRun_tvLe {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat) {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hprec : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius) :
    ArlibCommunity.Foundations.Convex.TVLe (normalizedHitAndRunContinuousLaw P b eta)
      (ArlibCommunity.Foundations.Convex.uniformOn volume (hitAndRunBody P b eta))
      (ENNReal.ofReal ((eta / 8) /
        (volume (hitAndRunBody P b eta)).toReal)) := by
  haveI : NeZero n := ⟨by omega⟩
  let K := P.normalizedHitAndRunBody b eta
  have hG : 0 < P.scaledInradius b :=
    mul_pos (by unfold decimalScale; positivity) P.inradius_pos
  have hbounded : Bornology.IsBounded K := P.normalizedHitAndRun_bounded b eta
  have hV : 0 < (volume (hitAndRunBody P b eta)).toReal := by
    have hbaseball : Metric.ball (P.scaledIncenter b) (P.scaledInradius b) ⊆
        P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
    have hfin : volume (P.scaledBody b) ≠ ⊤ :=
      (P.scaledBody_bounded b).measure_lt_top.ne
    simpa [hitAndRunBody, PolytopeData.scaledIncenter, PolytopeData.scaledInradius]
      using (ArlibCommunity.Algorithms.KV97.toReal_volume_inflated_pos hG ArlibCommunity.Algorithms.KV97.cOf_nonneg
        hbaseball hfin)
  obtain ⟨h16, -, hγR, hRS⟩ := P.samplerRadii (by omega) b heta0 heta1 hprec
  let S := P.samplerOuterRadius b eta
  have hS1 : 1 ≤ 2 * S := by
    have : (1 : Real) ≤ 16 / eta := (le_div_iff₀ heta0).2 (by linarith)
    have : P.scaledInradius b ≤ S := hγR.trans hRS
    linarith
  have hpow1 : 1 ≤ (2 * S) ^ n := one_le_pow₀ hS1
  let eps : Real := hitAndRunTolerance P b eta
  have heps : eps = eta / (16 * (2 * S) ^ n) := rfl
  have heps0 : 0 < eps := by rw [heps]; positivity
  have heps1 : eps ≤ 1 := by
    rw [heps, div_le_one (by positivity)]
    nlinarith
  have hvolS : (volume (hitAndRunBody P b eta)).toReal ≤ (2 * S) ^ n := by
    have h := euclidean_volume_le_ofReal_pow_of_dist_le
      (P.hitAndRunBody_dist_le_samplerOuterRadius b eta)
    have h' := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) h
    rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)] at h'
  have hepsle : eps ≤ (eta / 8) / (volume (hitAndRunBody P b eta)).toReal := by
    rw [heps, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hmix : ArlibCommunity.Foundations.Convex.TVLe
      (ArlibCommunity.Foundations.MarkovChainTheory.iterate
        (ArlibCommunity.Foundations.MarkovChainTheory.lazy (ArlibCommunity.Foundations.MarkovChainTheory.hitAndRun K))
        (ArlibCommunity.Foundations.Convex.uniformOn volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1))
        (normalizedHitAndRunSteps P b eta))
      (ArlibCommunity.Foundations.Convex.uniformOn volume K) (ENNReal.ofReal eps) := by
    apply tvLe_iterate_lazy_hitAndRun_from_unit_inball hn
      (ArlibCommunity.Foundations.Convex.Polytope.convex_body P.arlibNormal (P.normalizedHitAndRunOffset b eta))
      (ArlibCommunity.Foundations.Convex.Polytope.isClosed_body P.arlibNormal (P.normalizedHitAndRunOffset b eta))
      (ArlibCommunity.Foundations.Convex.Polytope.measurableSet_body P.arlibNormal
        (P.normalizedHitAndRunOffset b eta))
      hbounded (P.normalizedHitAndRun_unitBall b eta)
      (fun _ hx _ hy => Metric.dist_le_diam_of_mem hbounded hx hy)
      heps0 heps1
    exact P.hitAndRun_deadline_le_steps hn b heta0 heta1 hprec
  have hfiniteStep := ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep_eq_step
    P.arlibNormal (P.normalizedHitAndRunOffset b eta) hbounded
  have hmapped := hmix.map (show Measurable (P.samplerChart b) by
    unfold PolytopeData.samplerChart
    fun_prop)
  have htarget : (ArlibCommunity.Foundations.Convex.uniformOn volume K).map (P.samplerChart b) =
      ArlibCommunity.Foundations.Convex.uniformOn volume (hitAndRunBody P b eta) := by
    change (ArlibCommunity.Foundations.Convex.uniformOn volume (P.normalizedHitAndRunBody b eta)).map
      (P.samplerChart b) = ArlibCommunity.Foundations.Convex.uniformOn volume (hitAndRunBody P b eta)
    rw [P.normalizedHitAndRunBody_eq_preimage b eta]
    exact map_uniformOn_samplerChart hG (P.scaledIncenter b)
      (ArlibCommunity.Algorithms.KV97.measurableSet_inflated P.arlibNormal (P.scaledOffset b)
        (ArlibCommunity.Algorithms.KV97.cOf eta) (P.presentation.facetCount : Real))
  have hmix' := hmapped.mono (ENNReal.ofReal_mono hepsle)
  rw [htarget] at hmix'
  unfold normalizedHitAndRunContinuousLaw
  rw [hfiniteStep]
  simpa only [K, PolytopeData.normalizedHitAndRunBody,
    ArlibCommunity.Algorithms.HitAndRun.step] using hmix'

/-- The finite-step normalized walk is a probability law before rounding. -/
theorem normalizedHitAndRunContinuousLaw_isProbabilityMeasure {n : Nat}
    (hn : 0 < n) (P : PolytopeData n) (b : Nat) (eta : Real) :
    IsProbabilityMeasure (normalizedHitAndRunContinuousLaw P b eta) := by
  letI : NeZero n := ⟨by omega⟩
  let mu0 : Measure (EuclideanSpace Real (Fin n)) :=
    ArlibCommunity.Foundations.Convex.uniformOn volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)
  have hball0 : volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hballtop : volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  letI : IsProbabilityMeasure mu0 :=
    ArlibCommunity.Foundations.Convex.isProbabilityMeasure_uniformOn volume hball0 hballtop
  letI : IsMarkovKernel
      (ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep
        P.arlibNormal (P.normalizedHitAndRunOffset b eta)) := by
    unfold ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep
    infer_instance
  dsimp only [normalizedHitAndRunContinuousLaw,
    ArlibCommunity.Algorithms.HitAndRun.run,
    ArlibCommunity.Algorithms.HitAndRun.lazyStep,
    ArlibCommunity.Algorithms.HitAndRun.step]
  exact Measure.isProbabilityMeasure_map (by
    unfold PolytopeData.samplerChart
    fun_prop)

/-- The normalized sampler discharges the same KV97 pointwise contract. -/
theorem PolytopeData.normalizedHitAndRun_latticePointLaw {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat)
    {eta : Real}
    (hprec : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty) :
    AlmostUniformPointwise
      (normalizedHitAndRunPointLaw hn P b eta hprec heta0 heta1 hfinite hnonempty)
      (codedLatticePoints P b) eta := by
  letI : NeZero n := ⟨by omega⟩
  let mu := normalizedHitAndRunContinuousLaw P b eta
  let mu0 : Measure (EuclideanSpace Real (Fin n)) :=
    ArlibCommunity.Foundations.Convex.uniformOn volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)
  have hball0 : volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hballtop : volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  letI : IsProbabilityMeasure mu0 :=
    ArlibCommunity.Foundations.Convex.isProbabilityMeasure_uniformOn volume hball0 hballtop
  letI : IsMarkovKernel
      (ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep
        P.arlibNormal (P.normalizedHitAndRunOffset b eta)) := by
    unfold ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep
    infer_instance
  letI : IsProbabilityMeasure mu := by
    dsimp only [mu, normalizedHitAndRunContinuousLaw,
      ArlibCommunity.Algorithms.HitAndRun.run,
      ArlibCommunity.Algorithms.HitAndRun.lazyStep,
      ArlibCommunity.Algorithms.HitAndRun.step]
    exact Measure.isProbabilityMeasure_map (by
      unfold PolytopeData.samplerChart
      fun_prop)
  change AlmostUniformPointwise (acceptedRoundedLatticeLaw mu P b)
    (codedLatticePoints P b) eta
  apply almostUniform_acceptedRoundedLatticeLaw_of_tvLe P b heta0 heta1
    hfinite hnonempty mu
  simpa [mu, hitAndRunBody] using P.normalizedHitAndRun_tvLe hn b heta0 heta1 hprec

/-- Forgetting the number of rejection attempts recovers the conditional
rounded point law used by the paper sampler. -/
theorem acceptedRoundedWithAttempts_fst {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) (P : PolytopeData n) (b : Nat) :
    (acceptedRoundedWithAttempts mu P b).map Prod.fst =
      acceptedRoundedLatticeLaw mu P b := by
  letI : IsProbabilityMeasure
      (ProbabilityTheory.geometricMeasure (roundedAcceptanceProbability mu P b)) :=
    ProbabilityTheory.isProbabilityMeasure_geometricMeasure
  unfold acceptedRoundedWithAttempts
  rw [Measure.map_map measurable_fst (by fun_prop)]
  change (Measure.prod
    (ProbabilityTheory.geometricMeasure (roundedAcceptanceProbability mu P b))
    (acceptedRoundedLatticeLaw mu P b)).map Prod.snd =
      acceptedRoundedLatticeLaw mu P b
  simpa using Measure.map_snd_prod

/-- In the certified probability regime the totalized parameter is exactly
the chance that a rounded proposal passes the membership test. -/
theorem roundedAcceptanceProbability_val_eq {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) (P : PolytopeData n) (b : Nat)
    [IsProbabilityMeasure (kv97RoundedMeasureLaw mu)] :
    (roundedAcceptanceProbability mu P b : Real) =
      (kv97RoundedMeasureLaw mu).real (acceptedIntegers P b) := by
  unfold roundedAcceptanceProbability
  simp only [Subtype.coe_mk]
  rw [max_eq_right measureReal_nonneg, min_eq_right measureReal_le_one]

theorem normalizedHitAndRunPointWithCostLaw_fst {n : Nat}
    (P : PolytopeData n) (b : Nat) (eta : Real) :
    (normalizedHitAndRunPointWithCostLaw P b eta).map Prod.fst =
      acceptedRoundedLatticeLaw (normalizedHitAndRunContinuousLaw P b eta) P b := by
  unfold normalizedHitAndRunPointWithCostLaw
  rw [Measure.map_map measurable_fst (by fun_prop)]
  simpa only [Function.comp_def] using
    acceptedRoundedWithAttempts_fst (normalizedHitAndRunContinuousLaw P b eta) P b

/-- Summing retry costs across independent requests preserves the paper
batch law after the cost coordinate is forgotten. -/
theorem normalizedHitAndRunBatchWithCostLaw_fst {n : Nat}
    (P : PolytopeData n) (count b : Nat) (eta : Real)
    [IsProbabilityMeasure
      (acceptedRoundedLatticeLaw (normalizedHitAndRunContinuousLaw P b eta) P b)] :
    (normalizedHitAndRunBatchWithCostLaw P count b eta).map Prod.fst =
      iidSampleBatchLaw (acceptedRoundedLatticeLaw
        (normalizedHitAndRunContinuousLaw P b eta) P b) := by
  let μ := normalizedHitAndRunPointWithCostLaw P b eta
  let ν := acceptedRoundedLatticeLaw (normalizedHitAndRunContinuousLaw P b eta) P b
  have hmarginal : μ.map Prod.fst = ν :=
    normalizedHitAndRunPointWithCostLaw_fst P b eta
  have hsigma : ∀ i : Fin count, SigmaFinite (μ.map Prod.fst) := fun _ => by
    rw [hmarginal]
    infer_instance
  have hpi : (Measure.pi (fun _ : Fin count => μ)).map
      (fun draws i => (draws i).1) = Measure.pi (fun _ : Fin count => ν) := by
    rw [Measure.pi_map_pi (hμ := hsigma) (fun _ => measurable_fst.aemeasurable)]
    simp only [hmarginal]
  unfold normalizedHitAndRunBatchWithCostLaw iidSampleBatchLaw
  rw [Measure.map_map measurable_fst (by fun_prop)]
  change (Measure.pi (fun _ : Fin count => μ)).map
      (fun draws i => (draws i).1) = Measure.pi (fun _ : Fin count => ν)
  exact hpi

end Kr25Ssmxt

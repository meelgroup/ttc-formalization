import Kr25Ssmxt.Analysis.RuntimeBudgets
import Kr25Ssmxt.Analysis.EuclideanInball
import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.PrecisionAdequateSplit
import Kr25Ssmxt.Analysis.HitAndRunSamplingOracle
import Kr25Ssmxt.Analysis.CV18RoundnessBound

/-! Runtime geometry of the normalized Hit-and-Run walk. -/

namespace Kr25Ssmxt

open Real
open MeasureTheory

theorem euclidean_unitBall_volume_le_two_pow (n : Nat) :
    volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) ≤
      (2 : ENNReal) ^ n := by
  let B := Metric.ball (0 : EuclideanSpace Real (Fin n)) 1
  have hpre : (toEuclidean : Point n → EuclideanSpace Real (Fin n)) ⁻¹' B ⊆
      Metric.closedBall (0 : Point n) 1 := by
    intro x hx
    have hnorm : ‖x‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : Real) ≤ 1)).2
      intro i
      have hi := PiLp.norm_apply_le (toEuclidean x) i
      have hxnorm : ‖toEuclidean x‖ < 1 := by
        simpa [B, Metric.mem_ball, dist_zero_right] using hx
      simpa [toEuclidean] using hi.trans hxnorm.le
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  have heq : volume B =
      volume ((toEuclidean : Point n → EuclideanSpace Real (Fin n)) ⁻¹' B) := by
    exact ((PiLp.volume_preserving_toLp (Fin n)).measure_preimage
      measurableSet_ball.nullMeasurableSet).symm
  calc
    volume B = volume ((toEuclidean : Point n → EuclideanSpace Real (Fin n)) ⁻¹' B) := heq
    _ ≤ volume (Metric.closedBall (0 : Point n) 1) := measure_mono hpre
    _ = (2 : ENNReal) ^ n := by
      rw [Real.volume_pi_closedBall (0 : Point n) (by norm_num)]
      simp

theorem euclidean_unitBall_log_volume_le_two_dim (n : Nat) (hn : 1 ≤ n) :
    Real.log (1 +
      (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal) ≤
      2 * (n : Real) := by
  have hvol := euclidean_unitBall_volume_le_two_pow n
  have hfin : (2 : ENNReal) ^ n ≠ ⊤ := by simp
  have hreal := ENNReal.toReal_mono hfin hvol
  have hball :
      (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal ≤
        (2 : Real) ^ n := by simpa using hreal
  have hpow : (1 : Real) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hbound : 1 +
      (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal ≤
        2 ^ (n + 1) := by
    rw [pow_succ]
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : Real) < 1 +
    (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal) hbound
  rw [Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hnreal : (1 : Real) ≤ n := by exact_mod_cast hn
  push_cast at hlog
  nlinarith

theorem PolytopeData.kv97_kappa_le_samplerRadiusRequirement {n : Nat}
    (P : PolytopeData n) (hn : 0 < n) {eta : Real}
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta)
        (P.presentation.facetCount : Real) ≤
      samplerRadiusRequirement P eta := by
  let r : Real := P.presentation.facetCount
  let L : Real := Real.log (32 * r / eta)
  have hr : 1 ≤ r := by
    have hfac : 1 ≤ P.presentation.facetCount := by
      have := P.facets_pos
      omega
    change (1 : Real) ≤ (P.presentation.facetCount : Real)
    exact_mod_cast hfac
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
  have hx0 : 0 < 32 * r / eta := by positivity
  have hfour : 4 / (eta / 4) ≤ 32 * r / eta := by
    rw [show 4 / (eta / 4) = 16 / eta by field_simp; ring]
    exact div_le_div_of_nonneg_right (by nlinarith) heta0.le
  have hrx : r ≤ 32 * r / eta := by
    apply (le_div_iff₀ heta0).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ r) (sub_nonneg.mpr heta1)]
  have hlog4 : 0 ≤ Real.log (4 / eta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ heta0).2
    linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (le_trans hr hrx)
  have hc : samplerC eta ≤ Real.sqrt (2 * L) := by
    unfold samplerC ArlibCommunity.Algorithms.KV97.cOf
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
  have hfactor : 4 ≤ 512 * (n : Real) / eta := by
    apply (le_div_iff₀ heta0).2
    nlinarith
  unfold ArlibCommunity.Algorithms.KV97.kappaOf samplerRadiusRequirement
  change samplerC eta + Real.sqrt (2 * Real.log r) ≤
    (512 * (n : Real) / eta) * Real.sqrt L
  have hκ : samplerC eta + Real.sqrt (2 * Real.log r) ≤
      4 * Real.sqrt L := by linarith
  exact hκ.trans (mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg L))

theorem PolytopeData.normalizedHitAndRun_diameter_le_four_ratio
    {n : Nat} (P : PolytopeData n) (hn : 0 < n) (b : Nat)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hprecision : samplerRadiusRequirement P eta ≤
      decimalScale b * P.inradius) :
    Metric.diam (P.normalizedHitAndRunBody b eta) ≤
      4 * P.outerRadius / P.inradius := by
  have hκ : ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta)
      (P.presentation.facetCount : Real) ≤ P.scaledInradius b := by
    exact (P.kv97_kappa_le_samplerRadiusRequirement hn heta0 heta1).trans
      (by simpa only [PolytopeData.scaledInradius] using hprecision)
  have hγ : 0 < P.scaledInradius b :=
    mul_pos (decimalScale_pos b) P.inradius_pos
  have hκratio : ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta)
      (P.presentation.facetCount : Real) / P.scaledInradius b ≤ 1 :=
    (div_le_iff₀ hγ).2 (by simpa using hκ)
  have hR : 0 ≤ P.outerRadius / P.inradius :=
    div_nonneg P.outerRadius_nonneg P.inradius_pos.le
  calc
    Metric.diam (P.normalizedHitAndRunBody b eta) ≤
        (1 + ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta)
          (P.presentation.facetCount : Real) / P.scaledInradius b) *
          (2 * P.outerRadius / P.inradius) :=
      P.normalizedHitAndRun_diameter_le b eta
    _ ≤ 4 * P.outerRadius / P.inradius := by
      calc
        _ ≤ 2 * (2 * P.outerRadius / P.inradius) :=
          mul_le_mul_of_nonneg_right (by linarith)
            (div_nonneg (mul_nonneg (by norm_num) P.outerRadius_nonneg)
              P.inradius_pos.le)
        _ = 4 * P.outerRadius / P.inradius := by ring

theorem PolytopeData.hitAndRunBody_norm_le_five_scaled_outer
    {n : Nat} (P : PolytopeData n) (hn : 0 < n) (b : Nat)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hprecision : samplerRadiusRequirement P eta ≤
      decimalScale b * P.inradius) :
    ∀ x ∈ hitAndRunBody P b eta,
      ‖x‖ ≤ 5 * decimalScale b * P.outerRadius := by
  have hκ : ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta)
      (P.presentation.facetCount : Real) ≤ P.scaledInradius b :=
    (P.kv97_kappa_le_samplerRadiusRequirement hn heta0 heta1).trans
      (by simpa only [PolytopeData.scaledInradius] using hprecision)
  have hγ : 0 < P.scaledInradius b :=
    mul_pos (decimalScale_pos b) P.inradius_pos
  have hκratio : ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta)
      (P.presentation.facetCount : Real) / P.scaledInradius b ≤ 1 :=
    (div_le_iff₀ hγ).2 (by simpa using hκ)
  have hbaseball : Metric.ball (P.scaledIncenter b) (P.scaledInradius b) ⊆
      P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  have hcenterBody : P.scaledIncenter b ∈ P.scaledBody b :=
    P.scaledBody_inball b (by
      simp [PolytopeData.scaledIncenter, PolytopeData.scaledInradius,
        Metric.mem_closedBall, mul_nonneg (decimalScale_pos b).le P.inradius_pos.le])
  have hcenterInflated : P.scaledIncenter b ∈ hitAndRunBody P b eta := by
    exact ArlibCommunity.Algorithms.KV97.body_subset_inflated P.arlibNormal (P.scaledOffset b)
      (P.presentation.facetCount : Real) ArlibCommunity.Algorithms.KV97.cOf_nonneg hcenterBody
  have hcenterNorm : ‖P.scaledIncenter b‖ ≤
      decimalScale b * P.outerRadius := by
    have hmem : P.incenter ∈ P.carrier := P.incenter_mem_carrier
    have hnorm : ‖toEuclidean P.incenter‖ ≤ P.outerRadius :=
      P.outer_bound P.incenter hmem
    dsimp [PolytopeData.scaledIncenter]
    simpa only [norm_smul, Real.norm_eq_abs,
      abs_of_pos (decimalScale_pos b)] using
      mul_le_mul_of_nonneg_left hnorm (decimalScale_pos b).le
  intro x hx
  have hdist := dist_le_of_mem_inflated hγ ArlibCommunity.Algorithms.KV97.cOf_nonneg
    hbaseball (P.scaledBody_dist_le_outerRadius b) x hx
    (P.scaledIncenter b) hcenterInflated
  have hbound : dist x (P.scaledIncenter b) ≤
      4 * decimalScale b * P.outerRadius := by
    have hR : 0 ≤ decimalScale b * P.outerRadius :=
      mul_nonneg (decimalScale_pos b).le P.outerRadius_nonneg
    calc
      _ ≤ (1 + ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta)
        (P.presentation.facetCount : Real) / P.scaledInradius b) *
        (2 * decimalScale b * P.outerRadius) := hdist
      _ ≤ 2 * (2 * decimalScale b * P.outerRadius) := by
        apply mul_le_mul_of_nonneg_right (by linarith)
        nlinarith
      _ = _ := by ring
  have htriangle : ‖x‖ ≤ dist x (P.scaledIncenter b) +
      ‖P.scaledIncenter b‖ := by
    simpa [dist_eq_norm] using (norm_add_le (x - P.scaledIncenter b)
      (P.scaledIncenter b))
  linarith

theorem PolytopeData.hitAndRunBody_volume_le_scaled_outer_ball
    {n : Nat} (P : PolytopeData n) (hn : 0 < n) (b : Nat)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hprecision : samplerRadiusRequirement P eta ≤
      decimalScale b * P.inradius) :
    volume (hitAndRunBody P b eta) ≤
      volume (Metric.ball (0 : EuclideanSpace Real (Fin n))
        (5 * decimalScale b * P.outerRadius + 1)) := by
  apply measure_mono
  intro x hx
  have hnorm := P.hitAndRunBody_norm_le_five_scaled_outer hn b heta0 heta1
    hprecision x hx
  have hlt : ‖x‖ < 5 * decimalScale b * P.outerRadius + 1 := by linarith
  simpa [Metric.mem_ball, dist_zero_right] using hlt

theorem PolytopeData.hitAndRunBody_volume_toReal_le_scaled_outer_pow
    {n : Nat} (P : PolytopeData n) (hn : 0 < n) (b : Nat)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hprecision : samplerRadiusRequirement P eta ≤
      decimalScale b * P.inradius) :
    (volume (hitAndRunBody P b eta)).toReal ≤
      (5 * decimalScale b * P.outerRadius + 1) ^ n *
        (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let R : Real := 5 * decimalScale b * P.outerRadius + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    have hmul : 0 ≤ decimalScale b * P.outerRadius :=
      mul_nonneg (decimalScale_pos b).le P.outerRadius_nonneg
    linarith
  have hV := P.hitAndRunBody_volume_le_scaled_outer_ball hn b heta0 heta1
    hprecision
  have hballtop : volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) R) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hreal := ENNReal.toReal_mono hballtop hV
  have hball :
      (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) R)).toReal =
        R ^ n * (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal := by
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal hR]
    norm_num
  simpa only [R] using hreal.trans_eq hball

theorem PolytopeData.log_scaled_outer_ball_radius_le
    {n : Nat} (P : PolytopeData n) (b : Nat) :
    Real.log (5 * decimalScale b * P.outerRadius + 1) ≤
      (b : Real) * Real.log 10 + Real.log (6 * max 1 P.outerRadius) := by
  have hscale : 1 ≤ decimalScale b := by
    unfold decimalScale
    exact one_le_pow₀ (by norm_num)
  have hR : 1 ≤ max 1 P.outerRadius := le_max_left _ _
  have hRle : P.outerRadius ≤ max 1 P.outerRadius := le_max_right _ _
  have hrad : 0 < 5 * decimalScale b * P.outerRadius + 1 := by
    have := P.outerRadius_nonneg
    positivity
  have hupper : 5 * decimalScale b * P.outerRadius + 1 ≤
      decimalScale b * (6 * max 1 P.outerRadius) := by
    have hmul : decimalScale b * P.outerRadius ≤
        decimalScale b * max 1 P.outerRadius :=
      mul_le_mul_of_nonneg_left hRle (decimalScale_pos b).le
    have hone : 1 ≤ decimalScale b * max 1 P.outerRadius := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hscale)
        (sub_nonneg.mpr hR)]
    nlinarith
  have hlog := Real.log_le_log hrad hupper
  have hright : Real.log (decimalScale b * (6 * max 1 P.outerRadius)) =
      (b : Real) * Real.log 10 + Real.log (6 * max 1 P.outerRadius) := by
    rw [Real.log_mul (decimalScale_pos b).ne' (by positivity :
      (6 * max 1 P.outerRadius) ≠ 0)]
    simp [decimalScale, Real.log_pow]
  exact hlog.trans_eq hright

theorem Decomposition.component_outerRadius_le_theorem3OuterRadiusMax
    {n k : Nat} {F : LRAFormula n k} (D : Decomposition F)
    (i : Fin D.componentCount) :
    (D.component i).outerRadius ≤ TTCRuntime.theorem3OuterRadiusMax D := by
  have hle : Real.toNNReal (D.component i).outerRadius ≤
      (Finset.univ.sup fun j : Fin D.componentCount =>
        Real.toNNReal (D.component j).outerRadius : NNReal) :=
    Finset.le_sup (f := fun j : Fin D.componentCount =>
      Real.toNNReal (D.component j).outerRadius) (Finset.mem_univ i)
  calc
    (D.component i).outerRadius =
        (Real.toNNReal (D.component i).outerRadius : Real) :=
      (Real.coe_toNNReal _ (D.component i).outerRadius_nonneg).symm
    _ ≤ TTCRuntime.theorem3OuterRadiusMax D := by
      unfold TTCRuntime.theorem3OuterRadiusMax
      exact_mod_cast hle

theorem Decomposition.log_scaled_outer_ball_radius_le_global
    {n k : Nat} {F : LRAFormula n k} (D : Decomposition F)
    (i : Fin D.componentCount) (b : Nat) :
    Real.log (5 * decimalScale b * (D.component i).outerRadius + 1) ≤
      (b : Real) * Real.log 10 +
        Real.log (6 * max 1 (TTCRuntime.theorem3OuterRadiusMax D)) := by
  have hlocal := (D.component i).log_scaled_outer_ball_radius_le b
  have hmax : max 1 (D.component i).outerRadius ≤
      max 1 (TTCRuntime.theorem3OuterRadiusMax D) := by
    gcongr
    exact D.component_outerRadius_le_theorem3OuterRadiusMax i
  have hpos : 0 < 6 * max 1 (D.component i).outerRadius := by
    have := le_max_left (1 : Real) (D.component i).outerRadius
    positivity
  have hlog : Real.log (6 * max 1 (D.component i).outerRadius) ≤
      Real.log (6 * max 1 (TTCRuntime.theorem3OuterRadiusMax D)) :=
    Real.log_le_log hpos (by gcongr)
  linarith

theorem log_six_max_one (R : Real) (hR : 0 ≤ R) :
    Real.log (6 * max 1 R) = Real.log 6 + max 0 (Real.log R) := by
  rw [Real.log_mul (by norm_num) (by
    have := le_max_left (1 : Real) R
    positivity : max 1 R ≠ 0)]
  by_cases hR1 : R ≤ 1
  · rw [max_eq_left hR1]
    have hlog : Real.log R ≤ 0 := by
      by_cases hz : R = 0
      · simp [hz]
      · have hpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
        simpa using Real.log_le_log hpos hR1
    simp [hlog]
  · have hone : 1 ≤ R := by linarith
    rw [max_eq_right hone]
    have hlog : 0 ≤ Real.log R := Real.log_nonneg hone
    simp [hlog]

theorem Decomposition.log_scaled_outer_ball_radius_le_precisionScale
    {n k : Nat} {F : LRAFormula n k} (D : Decomposition F)
    (i : Fin D.componentCount) (b : Nat) :
    Real.log (5 * decimalScale b * (D.component i).outerRadius + 1) ≤
      (b : Real) * Real.log 10 + Real.log 6 +
        max 0 (Real.log (TTCRuntime.theorem3OuterRadiusMax D)) := by
  have hR : 0 ≤ TTCRuntime.theorem3OuterRadiusMax D := by
    unfold TTCRuntime.theorem3OuterRadiusMax
    positivity
  have h := D.log_scaled_outer_ball_radius_le_global i b
  rw [log_six_max_one _ hR] at h
  linarith

theorem Decomposition.normalizedHitAndRun_diameter_le_four_rho
    {n k : Nat} {F : LRAFormula n k} (hn : 0 < n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    Metric.diam ((D.component i).normalizedHitAndRunBody b p.ε') ≤
      4 * TTCRuntime.Rho D := by
  let P := D.component i
  have heta0 : 0 < p.ε' := by
    dsimp [ApproxParams.ε']
    positivity [p.epsilon_pos]
  have heta1 : p.ε' ≤ 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have hprec : samplerRadiusRequirement P p.ε' ≤
      decimalScale b * P.inradius := by
    simpa only [P, decimalScale] using
      (le_max_right _ _).trans (hprecision.split i)
  have hD := P.normalizedHitAndRun_diameter_le_four_ratio hn b heta0 heta1 hprec
  have hratio : P.outerRadius / P.inradius ≤ TTCRuntime.Rho D := by
    have hnonneg : 0 ≤ P.outerRadius / P.inradius :=
      div_nonneg P.outerRadius_nonneg P.inradius_pos.le
    have hle : Real.toNNReal (P.outerRadius / P.inradius) ≤
        (Finset.univ.sup fun j : Fin D.componentCount =>
          Real.toNNReal ((D.component j).outerRadius / (D.component j).inradius) :
            NNReal) := Finset.le_sup (f := fun j : Fin D.componentCount =>
              Real.toNNReal ((D.component j).outerRadius / (D.component j).inradius))
              (Finset.mem_univ i)
    have hleR : P.outerRadius / P.inradius ≤
        ((Finset.univ.sup fun j : Fin D.componentCount =>
          Real.toNNReal ((D.component j).outerRadius / (D.component j).inradius) :
            NNReal) : Real) := by
      calc
        P.outerRadius / P.inradius =
            (Real.toNNReal (P.outerRadius / P.inradius) : Real) :=
          (Real.coe_toNNReal _ hnonneg).symm
        _ ≤ _ := by exact_mod_cast hle
    exact hleR.trans (le_max_right _ _)
  calc
    _ ≤ 4 * P.outerRadius / P.inradius := by simpa only [P] using hD
    _ = 4 * (P.outerRadius / P.inradius) := by ring
    _ ≤ 4 * TTCRuntime.Rho D := by gcongr

/-- The paper's walk length `T = ⌈C n³ (R'₀/γ)² log (2R'₀/h)⌉` within the per-component
sampler allowance. `R₀ = BoundingRadius ≤ 2√n R` gives `(R'₀/γ)² ≤ 5n ρ²`, and
`log (2R'₀/h) ≤ b log 10 + log 6 + log n + log⁺ R_max`. -/
theorem Decomposition.normalizedHitAndRunSteps_le_explicitEnvelope
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    normalizedHitAndRunSteps (D.component i) b p.ε' ≤
      Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
        (TTCRuntime.Rho D) ^ 2 *
        TTCRuntime.theorem3SamplerLogEnvelope n b
          (TTCRuntime.Rho D)
          (TTCRuntime.theorem3OuterRadiusMax D) p.ε') := by
  let P := D.component i
  have heta0 : 0 < p.ε' := by
    dsimp [ApproxParams.ε']
    positivity [p.epsilon_pos]
  have heta1 : p.ε' ≤ 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have hprec : samplerRadiusRequirement P p.ε' ≤ decimalScale b * P.inradius := by
    simpa only [P, decimalScale] using (le_max_right _ _).trans (hprecision.split i)
  obtain ⟨h16, h128, hγR, hRS⟩ := P.samplerRadii (by omega) b heta0 heta1 hprec
  have hd := decimalScale_pos b
  have hγ : 0 < P.scaledInradius b := mul_pos hd P.inradius_pos
  have hκ0 : 0 ≤ P.samplerKappa p.ε' :=
    ArlibCommunity.Algorithms.KV97.kappaOf_nonneg ArlibCommunity.Algorithms.KV97.cOf_nonneg
  have hκ : P.samplerKappa p.ε' / P.scaledInradius b ≤ 1 / 128 := by
    rw [div_le_div_iff₀ hγ (by norm_num)]
    linarith
  have hκ' : 0 ≤ P.samplerKappa p.ε' / P.scaledInradius b := div_nonneg hκ0 hγ.le
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsqrt1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : Real) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn1
  have hsqrtsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
  have hratio0 : 0 ≤ P.outerRadius / P.inradius :=
    div_nonneg P.outerRadius_nonneg P.inradius_pos.le
  have hratio : P.outerRadius / P.inradius ≤ TTCRuntime.Rho D := by
    have hle : Real.toNNReal (P.outerRadius / P.inradius) ≤
        (Finset.univ.sup fun j : Fin D.componentCount =>
          Real.toNNReal ((D.component j).outerRadius / (D.component j).inradius) :
            NNReal) := Finset.le_sup (f := fun j : Fin D.componentCount =>
              Real.toNNReal ((D.component j).outerRadius / (D.component j).inradius))
              (Finset.mem_univ i)
    have hleR : P.outerRadius / P.inradius ≤
        ((Finset.univ.sup fun j : Fin D.componentCount =>
          Real.toNNReal ((D.component j).outerRadius / (D.component j).inradius) :
            NNReal) : Real) := by
      calc
        P.outerRadius / P.inradius =
            (Real.toNNReal (P.outerRadius / P.inradius) : Real) :=
          (Real.coe_toNNReal _ hratio0).symm
        _ ≤ _ := by exact_mod_cast hle
    exact hleR.trans (le_max_right _ _)
  have hR0 := P.boundingRadius_le
  have hR00 := P.boundingRadius_nonneg
  have hRγ : P.BoundingRadius / P.inradius ≤ 2 * Real.sqrt n * TTCRuntime.Rho D := by
    rw [div_le_iff₀ P.inradius_pos]
    have h1 : P.outerRadius ≤ TTCRuntime.Rho D * P.inradius := by
      rwa [div_le_iff₀ P.inradius_pos] at hratio
    have h2 : 0 ≤ 2 * Real.sqrt n := by positivity
    nlinarith
  have ha : P.samplerOuterRadius b p.ε' / P.scaledInradius b =
      (1 + P.samplerKappa p.ε' / P.scaledInradius b) * (P.BoundingRadius / P.inradius) := by
    have hi := P.inradius_pos
    unfold PolytopeData.samplerOuterRadius
    rw [show P.scaledInradius b = decimalScale b * P.inradius from rfl]
    field_simp
  have ha2 : (P.samplerOuterRadius b p.ε' / P.scaledInradius b) ^ 2 ≤
      5 * (n : Real) * (TTCRuntime.Rho D) ^ 2 := by
    rw [ha]
    have hc0 : 0 ≤ P.BoundingRadius / P.inradius := div_nonneg hR00 P.inradius_pos.le
    have h1 : (1 + P.samplerKappa p.ε' / P.scaledInradius b) *
        (P.BoundingRadius / P.inradius) ≤
        (129 / 128) * (2 * Real.sqrt n * TTCRuntime.Rho D) := by
      calc _ ≤ (129 / 128) * (P.BoundingRadius / P.inradius) := by
            apply mul_le_mul_of_nonneg_right _ hc0
            linarith
        _ ≤ _ := by gcongr
    have h0 : 0 ≤ (1 + P.samplerKappa p.ε' / P.scaledInradius b) *
        (P.BoundingRadius / P.inradius) := by positivity
    have hsq := pow_le_pow_left₀ h0 h1 2
    have hrho0 : 0 ≤ TTCRuntime.Rho D := le_trans zero_le_one (le_max_left _ _)
    calc _ ≤ ((129 / 128) * (2 * Real.sqrt n * TTCRuntime.Rho D)) ^ 2 := hsq
      _ = (129 / 128) ^ 2 * 4 * (Real.sqrt n ^ 2) * (TTCRuntime.Rho D) ^ 2 := by ring
      _ ≤ 5 * (n : Real) * (TTCRuntime.Rho D) ^ 2 := by
          rw [hsqrtsq]
          have : (0 : Real) ≤ n * (TTCRuntime.Rho D) ^ 2 := by positivity
          nlinarith
  let Rmax := TTCRuntime.theorem3OuterRadiusMax D
  have hRmax : P.outerRadius ≤ Rmax := D.component_outerRadius_le_theorem3OuterRadiusMax i
  have hRmax0 : 0 ≤ Rmax := P.outerRadius_nonneg.trans hRmax
  have hS1 : 1 ≤ 2 * P.samplerOuterRadius b p.ε' := by
    have : (1 : Real) ≤ 16 / p.ε' := (le_div_iff₀ heta0).2 (by linarith)
    linarith
  have h2S : 2 * P.samplerOuterRadius b p.ε' ≤
      decimalScale b * ((n : Real) * (6 * max 1 Rmax)) := by
    have hR1 : P.outerRadius ≤ max 1 Rmax := hRmax.trans (le_max_right _ _)
    have hsn : Real.sqrt n ≤ n := by nlinarith
    have hB : P.BoundingRadius ≤ 2 * (n : Real) * max 1 Rmax := by
      have h1 : 2 * Real.sqrt n * P.outerRadius ≤ 2 * (n : Real) * P.outerRadius :=
        mul_le_mul_of_nonneg_right (by linarith) P.outerRadius_nonneg
      have h2 : 2 * (n : Real) * P.outerRadius ≤ 2 * (n : Real) * max 1 Rmax :=
        mul_le_mul_of_nonneg_left hR1 (by positivity)
      linarith
    have hdB : decimalScale b * P.BoundingRadius ≤ decimalScale b * (2 * (n : Real) * max 1 Rmax) :=
      mul_le_mul_of_nonneg_left hB hd.le
    have hdB0 : 0 ≤ decimalScale b * P.BoundingRadius := mul_nonneg hd.le hR00
    unfold PolytopeData.samplerOuterRadius
    nlinarith
  have hL : Real.log (2 * P.samplerOuterRadius b p.ε') ≤
      (b : Real) * Real.log 10 + Real.log 6 + Real.log n + max 0 (Real.log Rmax) := by
    refine (Real.log_le_log (by linarith) h2S).trans_eq ?_
    have h6 : (0 : Real) < 6 * max 1 Rmax := by
      have := le_max_left (1 : Real) Rmax
      positivity
    rw [Real.log_mul hd.ne' (by positivity), Real.log_mul (by positivity) h6.ne',
      log_six_max_one _ hRmax0]
    simp [decimalScale, Real.log_pow]
    ring
  have hL0 : 0 ≤ Real.log (2 * P.samplerOuterRadius b p.ε') := Real.log_nonneg hS1
  have hX0 : 0 ≤ (b : Real) * Real.log 10 + Real.log 6 + Real.log n +
      max 0 (Real.log Rmax) := by linarith
  unfold normalizedHitAndRunSteps hitAndRunWalkConstant TTCRuntime.theorem3SamplerLogEnvelope
  apply Nat.ceil_mono
  calc (2 : Real) ^ 68 * (n : Real) ^ 3 *
        (P.samplerOuterRadius b p.ε' / P.scaledInradius b) ^ 2 *
        Real.log (2 * P.samplerOuterRadius b p.ε') ≤
      (2 : Real) ^ 68 * (n : Real) ^ 3 * (5 * (n : Real) * (TTCRuntime.Rho D) ^ 2) *
        ((b : Real) * Real.log 10 + Real.log 6 + Real.log n + max 0 (Real.log Rmax)) := by
        gcongr
    _ = _ := by ring

theorem TTCRuntime.expectedComponentBudgetLinearPrecision_le_geometric
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    TTCRuntime.expectedComponentBudgetLinearPrecision hn p
      D.componentCount b cv18NonQueryFactor (D.component i) ≤
      TTCRuntime.expectedComponentBudgetGeometric hn D p b
        cv18NonQueryFactor i := by
  have hsteps := D.normalizedHitAndRunSteps_le_explicitEnvelope
    hn b p hprecision i
  unfold TTCRuntime.expectedComponentBudgetLinearPrecision
    TTCRuntime.expectedComponentBudgetGeometric
  dsimp only
  gcongr
  unfold TTCRuntime.samplingAttemptOperations
  gcongr

/-- The sampler envelope is at most `n² · (1 + b + log⁺ R_max)` times the sampler log
factor of `polylogFactors`. -/
theorem theorem3_samplerLogEnvelope_le_dimension_precision_polylog
    (n b : Nat) (hn : 1 ≤ n) (rho R eta : Real)
    (hrho : 1 ≤ rho) (heta : 0 < eta) :
    TTCRuntime.theorem3SamplerLogEnvelope n b rho R eta ≤
      (n : Real) ^ 2 * TTCRuntime.theorem3PrecisionScale b R *
        (5 * (Real.log 8 + Real.log (4 * rho + 1) +
          2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / eta) + 2) +
          Real.log n)) := by
  let F := Real.log 8 + Real.log (4 * rho + 1) +
    2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / eta) + 2)
  let Lp := max 0 (Real.log R)
  have hb : 0 ≤ (b : Real) := by positivity
  have hLp : 0 ≤ Lp := le_max_left _ _
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hr : 0 ≤ Real.log (4 * rho + 1) := Real.log_nonneg (by linarith)
  have h10 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  have h6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have he : 0 ≤ Real.log (1 + 8 / eta) := by
    apply Real.log_nonneg
    have : 0 ≤ 8 / eta := div_nonneg (by norm_num) heta.le
    linarith
  have hF10 : Real.log 10 ≤ F := by dsimp [F]; linarith
  have hF6 : Real.log 6 ≤ F := by dsimp [F]; linarith
  have hF1 : 1 ≤ F := by dsimp [F]; linarith
  have hkey : (b : Real) * Real.log 10 + Real.log 6 + Real.log n + Lp ≤
      (1 + b + Lp) * (F + Real.log n) := by
    have e1 : (b : Real) * Real.log 10 ≤ b * F := mul_le_mul_of_nonneg_left hF10 hb
    have e2 : Lp ≤ Lp * F := le_mul_of_one_le_right hLp hF1
    have e3 : 0 ≤ ((b : Real) + Lp) * Real.log n := by positivity
    have hexp : (1 + b + Lp) * (F + Real.log n) =
        F + Real.log n + b * F + Lp * F + ((b : Real) + Lp) * Real.log n := by ring
    rw [hexp]
    linarith
  unfold TTCRuntime.theorem3SamplerLogEnvelope TTCRuntime.theorem3PrecisionScale
  change 5 * (n : Real) ^ 2 * ((b : Real) * Real.log 10 + Real.log 6 + Real.log n + Lp) ≤
    (n : Real) ^ 2 * (1 + b + Lp) * (5 * (F + Real.log n))
  have hn2 : (0 : Real) ≤ 5 * (n : Real) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hkey hn2
  linarith

theorem Decomposition.normalizedHitAndRunSteps_le_theorem3_polylog
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    normalizedHitAndRunSteps (D.component i) b p.ε' ≤
      Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 4 *
        (TTCRuntime.Rho D) ^ 2 *
        TTCRuntime.theorem3PrecisionScale b
          (TTCRuntime.theorem3OuterRadiusMax D) *
        (5 * (Real.log 8 + Real.log (4 * TTCRuntime.Rho D + 1) +
          2 * (Real.log 10 + Real.log 6 + 1 +
            Real.log (1 + 8 / p.ε') + 2) + Real.log n))) := by
  have hstep := D.normalizedHitAndRunSteps_le_explicitEnvelope hn b p hprecision i
  have henv := theorem3_samplerLogEnvelope_le_dimension_precision_polylog
    n b (by omega : 1 ≤ n) (TTCRuntime.Rho D)
    (TTCRuntime.theorem3OuterRadiusMax D) p.ε'
    (by unfold TTCRuntime.Rho; exact le_max_left _ _)
    (by dsimp [ApproxParams.ε']; positivity [p.epsilon_pos])
  apply hstep.trans
  apply Nat.ceil_mono
  have hfactor : 0 ≤ (2 : Real) ^ 68 * (n : Real) ^ 2 *
      (TTCRuntime.Rho D) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left henv hfactor
  nlinarith [sq_nonneg (n : Real)]

end Kr25Ssmxt

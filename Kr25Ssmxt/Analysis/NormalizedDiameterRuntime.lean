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

theorem PolytopeData.normalizedHitAndRun_deadline_log_nonneg {n : Nat}
    (P : PolytopeData n) (b : Nat) {eta : Real} (heta0 : 0 < eta) :
    0 ≤ Real.log
      (8 * (volume (P.normalizedHitAndRunBody b eta) /
        volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal /
        (hitAndRunTolerance P b eta) ^ 2) := by
  let M := (volume (P.normalizedHitAndRunBody b eta) /
    volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal
  let nu := hitAndRunTolerance P b eta
  have hM : 1 ≤ M := P.normalizedHitAndRun_warmness_ge_one b eta
  have hnu0 : 0 ≤ nu := by
    dsimp [nu, hitAndRunTolerance]
    apply le_min (by norm_num)
    exact div_nonneg (by positivity) ENNReal.toReal_nonneg
  have hnu1 : nu ≤ 1 := by
    dsimp [nu, hitAndRunTolerance]
    exact min_le_left _ _
  by_cases hz : nu = 0
  · simp [nu, hz]
  · have hnu : 0 < nu := lt_of_le_of_ne hnu0 (Ne.symm hz)
    have hsq : 0 < nu ^ 2 := sq_pos_of_pos hnu
    have hsq1 : nu ^ 2 ≤ 1 := by nlinarith
    apply Real.log_nonneg
    exact (le_div_iff₀ hsq).2 (by nlinarith)

theorem PolytopeData.hitAndRunTolerance_pos {n : Nat}
    (P : PolytopeData n) (b : Nat) {eta : Real} (heta0 : 0 < eta) :
    0 < hitAndRunTolerance P b eta := by
  have hG : 0 < P.scaledInradius b :=
    mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (P.scaledIncenter b) (P.scaledInradius b) ⊆
      P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  have hfin : volume (P.scaledBody b) ≠ ⊤ :=
    (P.scaledBody_bounded b).measure_lt_top.ne
  have hV : 0 < (volume (hitAndRunBody P b eta)).toReal := by
    simpa [hitAndRunBody, PolytopeData.scaledIncenter, PolytopeData.scaledInradius]
      using (Arlib.KV97.toReal_volume_inflated_pos hG Arlib.KV97.cOf_nonneg
        hbaseball hfin)
  unfold hitAndRunTolerance
  exact lt_min one_pos (div_pos (by positivity) hV)

theorem PolytopeData.hitAndRunTolerance_log_inv_le_volume
    {n : Nat} (P : PolytopeData n) (b : Nat)
    {eta : Real} (heta0 : 0 < eta) :
    Real.log (1 / hitAndRunTolerance P b eta) ≤
      Real.log (1 + 8 * (volume (hitAndRunBody P b eta)).toReal / eta) := by
  let V := (volume (hitAndRunBody P b eta)).toReal
  let nu := hitAndRunTolerance P b eta
  have hnu : 0 < nu := P.hitAndRunTolerance_pos b heta0
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hright : 0 < 1 + 8 * V / eta := by positivity
  have hinv : 1 / nu ≤ 1 + 8 * V / eta := by
    by_cases hraw : 1 ≤ (eta / 8) / V
    · have heq : nu = 1 := by
        dsimp [nu, hitAndRunTolerance]
        exact min_eq_left hraw
      rw [heq]
      have hquot : 0 ≤ 8 * V / eta := div_nonneg (by positivity) heta0.le
      norm_num
      linarith
    · have hrawle : (eta / 8) / V ≤ 1 := le_of_not_ge hraw
      have heq : nu = (eta / 8) / V := by
        dsimp [nu, hitAndRunTolerance]
        exact min_eq_right hrawle
      have hV : 0 < V := by
        by_contra hnot
        have hz : V = 0 := le_antisymm (le_of_not_gt hnot) hV0
        simp [heq, hz] at hnu
      rw [heq]
      have hident : 1 / ((eta / 8) / V) = 8 * V / eta := by
        field_simp
      rw [hident]
      linarith
  exact Real.log_le_log (div_pos one_pos hnu) hinv

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

theorem PolytopeData.kv97_kappa_le_samplerRadiusRequirement {n : Nat}
    (P : PolytopeData n) (hn : 0 < n) {eta : Real}
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
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
  have hfour : 4 / eta ≤ 32 * r / eta := by
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
  have hc : Arlib.KV97.cOf eta ≤ Real.sqrt (2 * L) := by
    unfold Arlib.KV97.cOf
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
  unfold Arlib.KV97.kappaOf samplerRadiusRequirement
  change Arlib.KV97.cOf eta + Real.sqrt (2 * Real.log r) ≤
    (512 * (n : Real) / eta) * Real.sqrt L
  have hκ : Arlib.KV97.cOf eta + Real.sqrt (2 * Real.log r) ≤
      4 * Real.sqrt L := by linarith
  exact hκ.trans (mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg L))

theorem PolytopeData.normalizedHitAndRun_diameter_le_four_ratio
    {n : Nat} (P : PolytopeData n) (hn : 0 < n) (b : Nat)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hprecision : samplerRadiusRequirement P eta ≤
      decimalScale b * P.inradius) :
    Metric.diam (P.normalizedHitAndRunBody b eta) ≤
      4 * P.outerRadius / P.inradius := by
  have hκ : Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
      (P.presentation.facetCount : Real) ≤ P.scaledInradius b := by
    exact (P.kv97_kappa_le_samplerRadiusRequirement hn heta0 heta1).trans
      (by simpa only [PolytopeData.scaledInradius] using hprecision)
  have hγ : 0 < P.scaledInradius b :=
    mul_pos (decimalScale_pos b) P.inradius_pos
  have hκratio : Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
      (P.presentation.facetCount : Real) / P.scaledInradius b ≤ 1 :=
    (div_le_iff₀ hγ).2 (by simpa using hκ)
  have hR : 0 ≤ P.outerRadius / P.inradius :=
    div_nonneg P.outerRadius_nonneg P.inradius_pos.le
  calc
    Metric.diam (P.normalizedHitAndRunBody b eta) ≤
        (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
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
  have hκ : Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
      (P.presentation.facetCount : Real) ≤ P.scaledInradius b :=
    (P.kv97_kappa_le_samplerRadiusRequirement hn heta0 heta1).trans
      (by simpa only [PolytopeData.scaledInradius] using hprecision)
  have hγ : 0 < P.scaledInradius b :=
    mul_pos (decimalScale_pos b) P.inradius_pos
  have hκratio : Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
      (P.presentation.facetCount : Real) / P.scaledInradius b ≤ 1 :=
    (div_le_iff₀ hγ).2 (by simpa using hκ)
  have hbaseball : Metric.ball (P.scaledIncenter b) (P.scaledInradius b) ⊆
      P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  have hcenterBody : P.scaledIncenter b ∈ P.scaledBody b :=
    P.scaledBody_inball b (by
      simp [PolytopeData.scaledIncenter, PolytopeData.scaledInradius,
        Metric.mem_closedBall, mul_nonneg (decimalScale_pos b).le P.inradius_pos.le])
  have hcenterInflated : P.scaledIncenter b ∈ hitAndRunBody P b eta := by
    exact Arlib.KV97.body_subset_inflated P.arlibNormal (P.scaledOffset b)
      (P.presentation.facetCount : Real) Arlib.KV97.cOf_nonneg hcenterBody
  have hcenterNorm : ‖P.scaledIncenter b‖ ≤
      decimalScale b * P.outerRadius := by
    have hmem : P.incenter ∈ P.carrier :=
      P.inball (by simp [Metric.mem_closedBall, P.inradius_pos.le])
    have hnorm : ‖toEuclidean P.incenter‖ ≤ P.outerRadius :=
      P.outer_bound P.incenter hmem
    dsimp [PolytopeData.scaledIncenter]
    simpa only [norm_smul, Real.norm_eq_abs,
      abs_of_pos (decimalScale_pos b)] using
      mul_le_mul_of_nonneg_left hnorm (decimalScale_pos b).le
  intro x hx
  have hdist := dist_le_of_mem_inflated hγ Arlib.KV97.cOf_nonneg
    hbaseball (P.scaledBody_dist_le_outerRadius b) x hx
    (P.scaledIncenter b) hcenterInflated
  have hbound : dist x (P.scaledIncenter b) ≤
      4 * decimalScale b * P.outerRadius := by
    have hR : 0 ≤ decimalScale b * P.outerRadius :=
      mul_nonneg (decimalScale_pos b).le P.outerRadius_nonneg
    calc
      _ ≤ (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
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

private theorem log_one_add_mul_le (n : Nat)
    {A C r V : Real} (hA : 0 ≤ A) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hV0 : 0 ≤ V) (hV : V ≤ r ^ n * C) :
    Real.log (1 + A * V) ≤
      (n : Real) * Real.log r + Real.log (1 + A) + Real.log (1 + C) := by
  have hrpow : 1 ≤ r ^ n := one_le_pow₀ hr
  have hstep1 : 1 + A * V ≤ 1 + A * (r ^ n * C) := by
    simpa only [add_comm] using
      (add_le_add_right (mul_le_mul_of_nonneg_left hV hA) 1)
  have hstep2 : 1 + A * (r ^ n * C) ≤ r ^ n * (1 + A * C) := by
    nlinarith [mul_nonneg hA hC]
  have hstep3 : 1 + A * C ≤ (1 + A) * (1 + C) := by nlinarith
  have hstep4 : r ^ n * (1 + A * C) ≤ r ^ n * ((1 + A) * (1 + C)) :=
    mul_le_mul_of_nonneg_left hstep3 (by positivity)
  have hleft : 0 < 1 + A * V := by
    positivity
  have hlog := Real.log_le_log hleft
    (hstep1.trans (hstep2.trans hstep4))
  have heq : Real.log (r ^ n * ((1 + A) * (1 + C))) =
      (n : Real) * Real.log r + Real.log (1 + A) + Real.log (1 + C) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  exact hlog.trans_eq heq

theorem Decomposition.normalizedHitAndRun_log_inv_tolerance_le
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    Real.log (1 / hitAndRunTolerance (D.component i) b p.epsilonPrime) ≤
      (n : Real) * ((b : Real) * Real.log 10 + Real.log 6 +
        max 0 (Real.log (TTCRuntime.theorem3OuterRadiusMax D))) +
        Real.log (1 + 8 / p.epsilonPrime) +
        Real.log (1 +
          (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal) := by
  let P := D.component i
  let eta := p.epsilonPrime
  let R := 5 * decimalScale b * P.outerRadius + 1
  let V := (volume (hitAndRunBody P b eta)).toReal
  let C := (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal
  have heta : 0 < eta := by
    dsimp [eta, ApproxParams.epsilonPrime]
    positivity [p.epsilon_pos]
  have heta1 : eta ≤ 1 := by
    dsimp [eta, ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  have hprec : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius := by
    simpa only [P, eta, decimalScale] using
      (le_max_right _ _).trans (hprecision.split i)
  have hV : V ≤ R ^ n * C :=
    P.hitAndRunBody_volume_toReal_le_scaled_outer_pow
      (by omega) b heta heta1 hprec
  have hr : 1 ≤ R := by
    dsimp [R]
    have := mul_nonneg (decimalScale_pos b).le P.outerRadius_nonneg
    linarith
  have hbase := P.hitAndRunTolerance_log_inv_le_volume b heta
  have hgeneric := log_one_add_mul_le n
    (A := 8 / eta) (C := C) (r := R) (V := V)
    (div_nonneg (by norm_num) heta.le) ENNReal.toReal_nonneg hr
    ENNReal.toReal_nonneg hV
  have hform : 1 + 8 * V / eta = 1 + (8 / eta) * V := by ring
  rw [hform] at hbase
  have hlogR := D.log_scaled_outer_ball_radius_le_precisionScale i b
  have hmul := mul_le_mul_of_nonneg_left hlogR
    (by exact_mod_cast (Nat.zero_le n) : 0 ≤ (n : Real))
  dsimp only [P, eta, R, V, C] at *
  linarith

theorem Decomposition.normalizedHitAndRun_diameter_le_four_rho
    {n k : Nat} {F : LRAFormula n k} (hn : 0 < n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    Metric.diam ((D.component i).normalizedHitAndRunBody b p.epsilonPrime) ≤
      4 * TTCRuntime.theorem3Rho D := by
  let P := D.component i
  have heta0 : 0 < p.epsilonPrime := by
    dsimp [ApproxParams.epsilonPrime]
    positivity [p.epsilon_pos]
  have heta1 : p.epsilonPrime ≤ 1 := by
    dsimp [ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  have hprec : samplerRadiusRequirement P p.epsilonPrime ≤
      decimalScale b * P.inradius := by
    simpa only [P, decimalScale] using
      (le_max_right _ _).trans (hprecision.split i)
  have hD := P.normalizedHitAndRun_diameter_le_four_ratio hn b heta0 heta1 hprec
  have hratio : P.outerRadius / P.inradius ≤ TTCRuntime.theorem3Rho D := by
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
    _ ≤ 4 * TTCRuntime.theorem3Rho D := by gcongr

theorem Decomposition.normalizedHitAndRun_warmness_le_rho_pow
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    (volume ((D.component i).normalizedHitAndRunBody b p.epsilonPrime) /
      volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal ≤
        (4 * TTCRuntime.theorem3Rho D + 1) ^ n := by
  apply (D.component i).normalizedHitAndRun_warmness_le_diameter_pow
    (by omega) b p.epsilonPrime (4 * TTCRuntime.theorem3Rho D)
  · unfold TTCRuntime.theorem3Rho
    positivity
  · exact D.normalizedHitAndRun_diameter_le_four_rho
      (by omega) b p hprecision i

theorem Decomposition.normalizedHitAndRun_log_warmness_le
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    Real.log ((volume ((D.component i).normalizedHitAndRunBody b p.epsilonPrime) /
      volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal) ≤
      (n : Real) * Real.log (4 * TTCRuntime.theorem3Rho D + 1) := by
  have hM0 := (D.component i).normalizedHitAndRun_warmness_ge_one b p.epsilonPrime
  have hM := D.normalizedHitAndRun_warmness_le_rho_pow hn b p hprecision i
  have hlog := Real.log_le_log (by linarith : 0 <
    (volume ((D.component i).normalizedHitAndRunBody b p.epsilonPrime) /
      volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal) hM
  simpa only [Real.log_pow] using hlog

/-- Specialization of the imported `2^64 n²D² log(8M/ν²)` deadline
to TTC's common radius ratio. -/
theorem Decomposition.normalizedHitAndRunSteps_le_rho_deadline
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    normalizedHitAndRunSteps (D.component i) b p.epsilonPrime ≤
      Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
        (TTCRuntime.theorem3Rho D) ^ 2 *
        Real.log (8 *
          (volume ((D.component i).normalizedHitAndRunBody b p.epsilonPrime) /
            volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal /
          (hitAndRunTolerance (D.component i) b p.epsilonPrime) ^ 2)) := by
  let d := Metric.diam ((D.component i).normalizedHitAndRunBody b p.epsilonPrime)
  let rho := TTCRuntime.theorem3Rho D
  let M := (volume ((D.component i).normalizedHitAndRunBody b p.epsilonPrime) /
    volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal
  let nu := hitAndRunTolerance (D.component i) b p.epsilonPrime
  have hlog : 0 ≤ Real.log (8 * M / nu ^ 2) := by
    apply (D.component i).normalizedHitAndRun_deadline_log_nonneg b
    dsimp [ApproxParams.epsilonPrime]
    positivity [p.epsilon_pos]
  have hd : d ≤ 4 * rho := D.normalizedHitAndRun_diameter_le_four_rho
    (by omega) b p hprecision i
  have hd0 : 0 ≤ d := by exact Metric.diam_nonneg
  have hrho : 0 ≤ rho := by
    dsimp [rho, TTCRuntime.theorem3Rho]
    exact le_trans (by norm_num : (0 : Real) ≤ 1) (le_max_left _ _)
  have hsq : d ^ 2 ≤ (4 * rho) ^ 2 :=
    (sq_le_sq₀ hd0 (by positivity)).2 hd
  unfold normalizedHitAndRunSteps
  apply Nat.ceil_mono
  unfold ArlibCommunity.Algorithms.HitAndRun.deadline
  change (2 : Real) ^ 64 * (n : Real) ^ 2 * d ^ 2 * Real.log (8 * M / nu ^ 2) ≤
    2 ^ 68 * (n : Real) ^ 2 * rho ^ 2 * Real.log (8 * M / nu ^ 2)
  calc
    _ ≤ (2 : Real) ^ 64 * (n : Real) ^ 2 * (4 * rho) ^ 2 *
        Real.log (8 * M / nu ^ 2) := by
      gcongr
    _ = _ := by
      rw [show (2 : Real) ^ 68 = 2 ^ 64 * 16 by norm_num]
      ring

theorem Decomposition.normalizedHitAndRun_deadline_log_le
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    Real.log (8 *
      (volume ((D.component i).normalizedHitAndRunBody b p.epsilonPrime) /
        volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal /
      (hitAndRunTolerance (D.component i) b p.epsilonPrime) ^ 2) ≤
      Real.log 8 + (n : Real) * Real.log (4 * TTCRuntime.theorem3Rho D + 1) +
        2 * Real.log (1 / hitAndRunTolerance (D.component i) b p.epsilonPrime) := by
  let M := (volume ((D.component i).normalizedHitAndRunBody b p.epsilonPrime) /
    volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal
  let nu := hitAndRunTolerance (D.component i) b p.epsilonPrime
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one
    ((D.component i).normalizedHitAndRun_warmness_ge_one b p.epsilonPrime)
  have heta : 0 < p.epsilonPrime := by
    dsimp [ApproxParams.epsilonPrime]
    positivity [p.epsilon_pos]
  have hnu : 0 < nu := (D.component i).hitAndRunTolerance_pos b heta
  have hlogM := D.normalizedHitAndRun_log_warmness_le hn b p hprecision i
  have hidentity : Real.log (8 * M / nu ^ 2) =
      Real.log 8 + Real.log M + 2 * Real.log (1 / nu) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) hM.ne', Real.log_pow,
      Real.log_div (by norm_num) hnu.ne']
    simp
    ring
  rw [hidentity]
  linarith

theorem Decomposition.normalizedHitAndRunSteps_le_explicitEnvelope
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    normalizedHitAndRunSteps (D.component i) b p.epsilonPrime ≤
      Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
        (TTCRuntime.theorem3Rho D) ^ 2 *
        TTCRuntime.theorem3SamplerLogEnvelope n b
          (TTCRuntime.theorem3Rho D)
          (TTCRuntime.theorem3OuterRadiusMax D) p.epsilonPrime) := by
  have hstep := D.normalizedHitAndRunSteps_le_rho_deadline hn b p hprecision i
  have hlog := D.normalizedHitAndRun_deadline_log_le hn b p hprecision i
  have hnu := D.normalizedHitAndRun_log_inv_tolerance_le hn b p hprecision i
  have henvelope :
      Real.log (8 *
        (volume ((D.component i).normalizedHitAndRunBody b p.epsilonPrime) /
          volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal /
        (hitAndRunTolerance (D.component i) b p.epsilonPrime) ^ 2) ≤
      TTCRuntime.theorem3SamplerLogEnvelope n b (TTCRuntime.theorem3Rho D)
        (TTCRuntime.theorem3OuterRadiusMax D) p.epsilonPrime := by
    unfold TTCRuntime.theorem3SamplerLogEnvelope
    linarith
  exact hstep.trans (Nat.ceil_mono (by
    have hfactor : 0 ≤ (2 : Real) ^ 68 * (n : Real) ^ 2 *
        (TTCRuntime.theorem3Rho D) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left henvelope hfactor))

theorem TTCRuntime.manuscriptExpectedComponentBudgetLinearPrecision_le_geometric
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    TTCRuntime.manuscriptExpectedComponentBudgetLinearPrecision hn p
      D.componentCount b cv18NonQueryFactor (D.component i) ≤
      TTCRuntime.manuscriptExpectedComponentBudgetGeometric hn D p b
        cv18NonQueryFactor i := by
  have hsteps := D.normalizedHitAndRunSteps_le_explicitEnvelope
    hn b p hprecision i
  unfold TTCRuntime.manuscriptExpectedComponentBudgetLinearPrecision
    TTCRuntime.manuscriptExpectedComponentBudgetGeometric
  dsimp only
  gcongr
  unfold TTCRuntime.samplingAttemptOperations
  gcongr

theorem theorem3_samplerLogEnvelope_le_factor
    (n b : Nat) (hn : 1 ≤ n) (rho R eta : Real)
    (hrho : 1 ≤ rho) (heta : 0 < eta) :
    TTCRuntime.theorem3SamplerLogEnvelope n b rho R eta ≤
      (n : Real) * TTCRuntime.theorem3PrecisionScale b R *
        TTCRuntime.theorem3SamplerLogFactor n rho eta := by
  let H := TTCRuntime.theorem3PrecisionScale b R
  let T := (n : Real) * H
  let A := Real.log 8
  let B := Real.log (4 * rho + 1)
  let C := Real.log 10
  let D := Real.log 6
  let E := Real.log (1 + 8 / eta)
  let G := Real.log (1 +
    (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal)
  have hH : 1 ≤ H := by
    dsimp [H, TTCRuntime.theorem3PrecisionScale]
    have hb : 0 ≤ (b : Real) := by positivity
    have hR : 0 ≤ max 0 (Real.log R) := le_max_left _ _
    linarith
  have hbH : (b : Real) ≤ H := by
    dsimp [H, TTCRuntime.theorem3PrecisionScale]
    have hR : 0 ≤ max 0 (Real.log R) := le_max_left _ _
    linarith
  have hRH : max 0 (Real.log R) ≤ H := by
    dsimp [H, TTCRuntime.theorem3PrecisionScale]
    have hb : 0 ≤ (b : Real) := by positivity
    linarith
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hT1 : 1 ≤ T := by
    dsimp [T]
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (sub_nonneg.mpr hH)]
  have hnT : (n : Real) ≤ T := by
    dsimp [T]
    nlinarith
  have hbnT : (n : Real) * b ≤ T := by
    dsimp [T]
    exact mul_le_mul_of_nonneg_left hbH (by linarith)
  have hRnT : (n : Real) * max 0 (Real.log R) ≤ T := by
    dsimp [T]
    exact mul_le_mul_of_nonneg_left hRH (by linarith)
  have hA : 0 ≤ A := by dsimp [A]; exact Real.log_nonneg (by norm_num)
  have hB : 0 ≤ B := by
    dsimp [B]
    apply Real.log_nonneg
    linarith
  have hC : 0 ≤ C := by dsimp [C]; exact Real.log_nonneg (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; exact Real.log_nonneg (by norm_num)
  have hE : 0 ≤ E := by
    dsimp [E]
    apply Real.log_nonneg
    have : 0 ≤ 8 / eta := div_nonneg (by norm_num) heta.le
    linarith
  have hG : 0 ≤ G := by
    dsimp [G]
    apply Real.log_nonneg
    have : 0 ≤ (volume
      (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal :=
      ENNReal.toReal_nonneg
    linarith
  have hA' := mul_le_mul_of_nonneg_right hT1 hA
  have hB' := mul_le_mul_of_nonneg_right hnT hB
  have hC' := mul_le_mul_of_nonneg_right hbnT hC
  have hD' := mul_le_mul_of_nonneg_right hnT hD
  have hR' := mul_le_mul_of_nonneg_right hRnT (by norm_num : (0 : Real) ≤ 1)
  have hE' := mul_le_mul_of_nonneg_right hT1 hE
  have hG' := mul_le_mul_of_nonneg_right hT1 hG
  unfold TTCRuntime.theorem3SamplerLogEnvelope
    TTCRuntime.theorem3SamplerLogFactor
  dsimp only [T, H, A, B, C, D, E, G] at *
  nlinarith

theorem theorem3_samplerLogFactor_le_dimension_polylog
    (n : Nat) (hn : 1 ≤ n) (rho eta : Real)
    (hrho : 1 ≤ rho) (heta : 0 < eta) :
    TTCRuntime.theorem3SamplerLogFactor n rho eta ≤
      (n : Real) * (Real.log 8 + Real.log (4 * rho + 1) +
        2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / eta) + 2)) := by
  have hG := euclidean_unitBall_log_volume_le_two_dim n hn
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hA : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ Real.log (4 * rho + 1) :=
    Real.log_nonneg (by linarith)
  have hC : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  have hD : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hE : 0 ≤ Real.log (1 + 8 / eta) := by
    apply Real.log_nonneg
    have : 0 ≤ 8 / eta := div_nonneg (by norm_num) heta.le
    linarith
  unfold TTCRuntime.theorem3SamplerLogFactor
  nlinarith [mul_nonneg (sub_nonneg.mpr hnR)
    (add_nonneg (add_nonneg hA hB) (by positivity :
      0 ≤ 2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / eta) + 2)))]

theorem theorem3_samplerLogEnvelope_le_dimension_precision_polylog
    (n b : Nat) (hn : 1 ≤ n) (rho R eta : Real)
    (hrho : 1 ≤ rho) (heta : 0 < eta) :
    TTCRuntime.theorem3SamplerLogEnvelope n b rho R eta ≤
      (n : Real) ^ 2 * TTCRuntime.theorem3PrecisionScale b R *
        (Real.log 8 + Real.log (4 * rho + 1) +
          2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / eta) + 2)) := by
  have hH : 0 ≤ TTCRuntime.theorem3PrecisionScale b R := by
    unfold TTCRuntime.theorem3PrecisionScale
    have hb : 0 ≤ (b : Real) := by positivity
    have hR : 0 ≤ max 0 (Real.log R) := le_max_left _ _
    linarith
  calc
    _ ≤ (n : Real) * TTCRuntime.theorem3PrecisionScale b R *
        TTCRuntime.theorem3SamplerLogFactor n rho eta :=
      theorem3_samplerLogEnvelope_le_factor n b hn rho R eta hrho heta
    _ ≤ (n : Real) ^ 2 * TTCRuntime.theorem3PrecisionScale b R *
        (Real.log 8 + Real.log (4 * rho + 1) +
          2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / eta) + 2)) := by
      have h := theorem3_samplerLogFactor_le_dimension_polylog n hn rho eta hrho heta
      have hn0 : (0 : Real) ≤ n := by positivity
      have hmul := mul_le_mul_of_nonneg_left h
        (mul_nonneg hn0 hH)
      nlinarith

theorem Decomposition.normalizedHitAndRunSteps_le_theorem3_polylog
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (b : Nat) (p : ApproxParams)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    normalizedHitAndRunSteps (D.component i) b p.epsilonPrime ≤
      Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 4 *
        (TTCRuntime.theorem3Rho D) ^ 2 *
        TTCRuntime.theorem3PrecisionScale b
          (TTCRuntime.theorem3OuterRadiusMax D) *
        (Real.log 8 + Real.log (4 * TTCRuntime.theorem3Rho D + 1) +
          2 * (Real.log 10 + Real.log 6 + 1 +
            Real.log (1 + 8 / p.epsilonPrime) + 2))) := by
  have hstep := D.normalizedHitAndRunSteps_le_explicitEnvelope hn b p hprecision i
  have henv := theorem3_samplerLogEnvelope_le_dimension_precision_polylog
    n b (by omega : 1 ≤ n) (TTCRuntime.theorem3Rho D)
    (TTCRuntime.theorem3OuterRadiusMax D) p.epsilonPrime
    (by unfold TTCRuntime.theorem3Rho; exact le_max_left _ _)
    (by dsimp [ApproxParams.epsilonPrime]; positivity [p.epsilon_pos])
  apply hstep.trans
  apply Nat.ceil_mono
  have hfactor : 0 ≤ (2 : Real) ^ 68 * (n : Real) ^ 2 *
      (TTCRuntime.theorem3Rho D) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left henv hfactor
  nlinarith [sq_nonneg (n : Real)]

end Kr25Ssmxt

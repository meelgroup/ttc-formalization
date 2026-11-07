import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.NormalizedDiameterRuntime
import Kr25Ssmxt.Analysis.RateLogBound

/-! Bounding the manuscript volume clip used by the first thinning loop. -/

namespace Kr25Ssmxt

theorem Decomposition.theorem3RMax_pos {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (hm : 0 < D.componentCount) :
    0 < TTCRuntime.theorem3RMax D := by
  let i : Fin D.componentCount := ⟨0, hm⟩
  have hfacets := (D.component i).facets_pos
  have hle : (D.component i).presentation.facetCount ≤
      TTCRuntime.theorem3RMax D := by
    unfold TTCRuntime.theorem3RMax
    exact Finset.le_sup (f := fun j : Fin D.componentCount =>
      (D.component j).presentation.facetCount) (Finset.mem_univ i)
  omega

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
    simp [x, Metric.mem_closedBall, dist_eq_norm, norm_smul, he,
      Real.norm_eq_abs, abs_of_pos P.inradius_pos]
  have hy : y ∈ P.carrier := by
    apply P.inball
    simp [y, Metric.mem_closedBall, norm_smul, he,
      Real.norm_eq_abs, abs_of_pos P.inradius_pos]
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

theorem PolytopeData.manuscriptVolumeClip_le_outer_pow {n : Nat}
    (P : PolytopeData n) (hn : 21 ≤ n) {eta : Real}
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    max (P.manuscriptVolumeLower eta) (P.manuscriptVolumeUpper eta) ≤
      Real.toNNReal (2 * (4 * P.outerRadius) ^ n) := by
  have hγR : P.inradius ≤ P.outerRadius :=
    P.inradius_le_outerRadius (by omega)
  have hR : 0 ≤ P.outerRadius := P.outerRadius_nonneg
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsqrt : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact hn1
  have hbase : 2 * P.inradius / Real.sqrt n ≤ 4 * P.outerRadius := by
    have hspos : 0 < Real.sqrt n := by linarith
    apply (div_le_iff₀ hspos).2
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hsqrt)]
  have hbase0 : 0 ≤ 2 * P.inradius / Real.sqrt n :=
    div_nonneg (mul_nonneg (by norm_num) P.inradius_pos.le)
      (by linarith)
  have hpow : (2 * P.inradius / Real.sqrt n) ^ n ≤
      (4 * P.outerRadius) ^ n := by gcongr
  have hpow2 : (2 * P.outerRadius) ^ n ≤ (4 * P.outerRadius) ^ n := by
    gcongr
    nlinarith
  apply max_le
  · unfold PolytopeData.manuscriptVolumeLower
    apply Real.toNNReal_mono
    have hcoeff : 0 ≤ 1 - eta := by linarith
    have hcoeff2 : 1 - eta ≤ 2 := by linarith
    calc
      (1 - eta) * (2 * P.inradius / Real.sqrt n) ^ n ≤
          2 * (2 * P.inradius / Real.sqrt n) ^ n := by
        gcongr
      _ ≤ 2 * (4 * P.outerRadius) ^ n := by gcongr
  · unfold PolytopeData.manuscriptVolumeUpper
    apply Real.toNNReal_mono
    have hcoeff : 1 + eta ≤ 2 := by linarith
    calc
      (1 + eta) * (2 * P.outerRadius) ^ n ≤
          2 * (2 * P.outerRadius) ^ n := by gcongr
      _ ≤ 2 * (4 * P.outerRadius) ^ n := by gcongr

theorem Decomposition.clippedVolume_clog_le_outerRadiusMax
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) :
    let v := max ((D.component i).manuscriptVolumeLower p.epsilonPrime)
      ((D.component i).manuscriptVolumeUpper p.epsilonPrime)
    Nat.clog 2 (Nat.ceil (v : Real) + 1) ≤
      2 + n * Nat.clog 2
        (Nat.ceil (4 * TTCRuntime.theorem3OuterRadiusMax D) + 1) := by
  let P := D.component i
  let v := max (P.manuscriptVolumeLower p.epsilonPrime)
    (P.manuscriptVolumeUpper p.epsilonPrime)
  have heta0 : 0 < p.epsilonPrime := by
    dsimp [ApproxParams.epsilonPrime]
    positivity [p.epsilon_pos]
  have heta1 : p.epsilonPrime ≤ 1 := by
    dsimp [ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  have hv := P.manuscriptVolumeClip_le_outer_pow hn heta0 heta1
  have hR := D.component_outerRadius_le_theorem3OuterRadiusMax i
  have hR0 : 0 ≤ TTCRuntime.theorem3OuterRadiusMax D := by
    unfold TTCRuntime.theorem3OuterRadiusMax
    positivity
  have hP0 : 0 ≤ P.outerRadius := P.outerRadius_nonneg
  have hreal : (v : Real) ≤
      2 * (4 * TTCRuntime.theorem3OuterRadiusMax D) ^ n := by
    have hfirst : (v : Real) ≤ 2 * (4 * P.outerRadius) ^ n := by
      have hnonneg : 0 ≤ 2 * (4 * P.outerRadius) ^ n := by
        positivity
      simpa only [Real.coe_toNNReal _ hnonneg] using
        (show (v : Real) ≤
          (Real.toNNReal (2 * (4 * P.outerRadius) ^ n) : Real) by
            exact_mod_cast hv)
    have hpow : (4 * P.outerRadius) ^ n ≤
        (4 * TTCRuntime.theorem3OuterRadiusMax D) ^ n := by
      gcongr
    nlinarith
  have hceil := Nat.ceil_mono hreal
  have hclog := Nat.clog_mono_right 2 (Nat.add_le_add_right hceil 1)
  exact hclog.trans (clog_two_ceil_two_pow_le
    (4 * TTCRuntime.theorem3OuterRadiusMax D) n (by positivity))

theorem Decomposition.manuscriptRate_clog_le_precision_outerRadius
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (i : Fin D.componentCount) :
    let v := max ((D.component i).manuscriptVolumeLower p.epsilonPrime)
      ((D.component i).manuscriptVolumeUpper p.epsilonPrime)
    Nat.clog 2
      (Nat.ceil (((manuscriptIntensity b n (p.threshold D.componentCount) v : NNReal) :
        Real) / p.threshold D.componentCount) + 1) ≤
      4 * (b * n) + 2 + n * Nat.clog 2
        (Nat.ceil (4 * TTCRuntime.theorem3OuterRadiusMax D) + 1) := by
  let v := max ((D.component i).manuscriptVolumeLower p.epsilonPrime)
    ((D.component i).manuscriptVolumeUpper p.epsilonPrime)
  have hfirst := manuscript_rate_clog_le_linear_precision b n
    (p.threshold_pos D.componentCount) v
  have hsecond := D.clippedVolume_clog_le_outerRadiusMax hn p i
  dsimp only [v] at hfirst hsecond ⊢
  omega

theorem TTCRuntime.manuscriptExpectedComponentBudgetGeometric_le_clip
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) :
    TTCRuntime.manuscriptExpectedComponentBudgetGeometric hn D p b
      cv18NonQueryFactor i ≤
      TTCRuntime.manuscriptExpectedComponentBudgetGeometricClip hn D p b
        cv18NonQueryFactor i := by
  have hrate := D.clippedVolume_clog_le_outerRadiusMax hn p i
  dsimp only at hrate
  unfold TTCRuntime.manuscriptExpectedComponentBudgetGeometric
    TTCRuntime.manuscriptExpectedComponentBudgetGeometricClip
  dsimp only
  gcongr

theorem log_plus_outer_le_clog (R : Real) (hR : 0 ≤ R) :
    max 0 (Real.log R) ≤
      (Nat.clog 2 (Nat.ceil (4 * R) + 1) : Real) := by
  let x := Nat.ceil (4 * R) + 1
  have hx : 0 < x := by dsimp [x]; omega
  have hRx : R ≤ (x : Real) := by
    calc
      R ≤ 4 * R := by linarith
      _ ≤ (Nat.ceil (4 * R) : Real) := Nat.le_ceil _
      _ ≤ x := by
        dsimp [x]
        exact_mod_cast Nat.le_succ _
  have hpow : (x : Real) ≤
      (2 : Real) ^ Nat.clog 2 x := by
    exact_mod_cast Nat.le_pow_clog (by omega) x
  have hlogx : Real.log (x : Real) ≤
      (Nat.clog 2 x : Real) * Real.log 2 := by
    have h := Real.log_le_log (by exact_mod_cast hx) hpow
    simpa only [Real.log_pow] using h
  have hlog2 : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
  have hlogbound : Real.log (x : Real) ≤ (Nat.clog 2 x : Real) := by
    have hc : 0 ≤ (Nat.clog 2 x : Real) := by positivity
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hlog2)]
  by_cases hR1 : R ≤ 1
  · have hlog : Real.log R ≤ 0 := by
      by_cases hz : R = 0
      · simp [hz]
      · have hpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
        simpa using Real.log_le_log hpos hR1
    simp [hlog]
  · have hpos : 0 < R := by linarith
    have hlogR : Real.log R ≤ Real.log (x : Real) :=
      Real.log_le_log hpos hRx
    have hlog0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    simpa [hlog0, x] using hlogR.trans hlogbound

theorem clog_outer_le_log_plus (R : Real) :
    (Nat.clog 2 (Nat.ceil (4 * R) + 1) : Real) ≤
      8 * (1 + max 0 (Real.log R)) := by
  by_cases hR1 : R ≤ 1
  · have hceil : Nat.ceil (4 * R) ≤ 4 := by
      have hreal : 4 * R ≤ (4 : Real) := by linarith
      have hc := Nat.ceil_mono hreal
      simpa using hc
    have hclog : Nat.clog 2 (Nat.ceil (4 * R) + 1) ≤ 3 := by
      have hx : Nat.ceil (4 * R) + 1 ≤ 5 := by omega
      exact (Nat.clog_mono_right 2 hx).trans (by decide)
    have hmax : 0 ≤ max 0 (Real.log R) := le_max_left _ _
    have hclogR : (Nat.clog 2 (Nat.ceil (4 * R) + 1) : Real) ≤ 3 := by
      exact_mod_cast hclog
    linarith
  · have hRpos : 0 < R := by linarith
    have hlog0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    let j := Nat.ceil (Real.log R)
    have hj : Real.log R ≤ (j : Real) := Nat.le_ceil _
    have hjupper : (j : Real) < Real.log R + 1 := Nat.ceil_lt_add_one hlog0
    have hRexp : R ≤ Real.exp (j : Real) := by
      rw [← Real.exp_log hRpos]
      exact Real.exp_le_exp.mpr hj
    have hexp10 : Real.exp (j : Real) ≤ (10 : Real) ^ j := by
      calc
        Real.exp (j : Real) = (Real.exp 1) ^ j := by
          simpa using (Real.exp_nat_mul 1 j)
        _ ≤ (10 : Real) ^ j := by
          gcongr
          linarith [Real.exp_one_lt_three]
    have hRpow : R ≤ (10 : Real) ^ j := hRexp.trans hexp10
    have hceil : Nat.ceil (4 * R) ≤ 4 * 10 ^ j := by
      have hreal : 4 * R ≤ ((4 * 10 ^ j : Nat) : Real) := by
        calc
          4 * R ≤ 4 * (10 : Real) ^ j := by gcongr
          _ = ((4 * 10 ^ j : Nat) : Real) := by push_cast; ring
      have hc : Nat.ceil (4 * R) ≤
          Nat.ceil (((4 * 10 ^ j : Nat) : Real)) := Nat.ceil_mono hreal
      simpa only [Nat.ceil_natCast] using hc
    have hpow : 1 ≤ (10 : Nat) ^ j := by
      have : 0 < (10 : Nat) ^ j := by positivity
      omega
    have hx : Nat.ceil (4 * R) + 1 ≤ 10 ^ (j + 1) := by
      rw [pow_succ]
      omega
    have hclog := (Nat.clog_mono_right 2 hx).trans
      (clog_two_ten_pow_le (j + 1))
    have hcast : (Nat.clog 2 (Nat.ceil (4 * R) + 1) : Real) ≤
        4 * ((j : Real) + 1) := by exact_mod_cast hclog
    rw [max_eq_right hlog0]
    linarith

theorem theorem3_first_loop_rounds_le_precisionScale
    (n b : Nat) (hn : 1 ≤ n) (R : Real) :
    ((4 * (b * n) + (2 + n * Nat.clog 2 (Nat.ceil (4 * R) + 1)) : Nat) : Real) ≤
      14 * (n : Real) * TTCRuntime.theorem3PrecisionScale b R := by
  have hclog := clog_outer_le_log_plus R
  have hL : 0 ≤ max 0 (Real.log R) := le_max_left _ _
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hbR : 0 ≤ (b : Real) := by positivity
  unfold TTCRuntime.theorem3PrecisionScale
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (n : Real) by positivity)
    (sub_nonneg.mpr hclog),
    mul_nonneg (by positivity : 0 ≤ (n : Real)) hbR,
    mul_nonneg (by positivity : 0 ≤ (n : Real)) hL]

end Kr25Ssmxt

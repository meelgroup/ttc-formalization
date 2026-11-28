import ttc.Analysis.ScaledBody
import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.PoissonMean
import ttc.Analysis.KV97HitAndRunSampling
import ttc.Analysis.NormalizedHitAndRunGeometry

/-! The finite-mass step in bounding sampler rejection attempts. -/

namespace ttc

open MeasureTheory ProbabilityTheory Metric Set
open ArlibCommunity.Algorithms.KV97
open scoped ENNReal

theorem finite_acceptance_mass_lower {n : Nat}
    (μ : Measure (Fin n → Int)) [IsProbabilityMeasure μ]
    (T : Finset (Fin n → Int)) (lower : Real)
    (hpoint : ∀ z ∈ T, lower ≤ μ.real {z}) :
    (T.card : Real) * lower ≤ μ.real (T : Set (Fin n → Int)) := by
  rw [← MeasureTheory.sum_measureReal_singleton T]
  calc
    (T.card : Real) * lower = ∑ _z ∈ T, lower := by simp
    _ ≤ ∑ z ∈ T, μ.real {z} := by
      apply Finset.sum_le_sum
      intro z hz
      exact hpoint z hz

theorem roundedAcceptanceProbability_ge_half_of_raw_mass {n : Nat}
    (μ : Measure (EuclideanSpace Real (Fin n)))
    (P : PolytopeData n) (b : Nat)
    (hraw : (1 / 2 : Real) ≤
      (kv97RoundedMeasureLaw μ).real (acceptedIntegers P b)) :
    (1 / 2 : Real) ≤ (roundedAcceptanceProbability μ P b : Real) := by
  unfold roundedAcceptanceProbability
  change (1 / 2 : Real) ≤
    min 1 (max 0 ((kv97RoundedMeasureLaw μ).real (acceptedIntegers P b)))
  exact le_min (by norm_num) (le_max_of_le_right hraw)

theorem roundedAcceptanceProbability_ge_half_of_pointwise {n : Nat}
    (μ : Measure (EuclideanSpace Real (Fin n))) [IsProbabilityMeasure μ]
    (P : PolytopeData n) (b : Nat) (lower : Real)
    (hfinite : (acceptedIntegers P b).Finite)
    (hpoint : ∀ z ∈ acceptedIntegers P b,
      lower ≤ (kv97RoundedMeasureLaw μ).real {z})
    (htotal : (1 / 2 : Real) ≤
      ((acceptedIntegers P b).ncard : Real) * lower) :
    (1 / 2 : Real) ≤ (roundedAcceptanceProbability μ P b : Real) := by
  letI : IsProbabilityMeasure (kv97RoundedMeasureLaw μ) :=
    Arlib.KV97.isProbabilityMeasure_roundedMeasureLaw μ
  let T : Finset (Fin n → Int) := hfinite.toFinset
  have hmass := finite_acceptance_mass_lower (kv97RoundedMeasureLaw μ)
    T lower (by
      intro z hz
      exact hpoint z (by simpa [T] using hz))
  have hT : ((T.card : Nat) : Real) = ((acceptedIntegers P b).ncard : Real) := by
    exact_mod_cast (Set.ncard_eq_toFinset_card (acceptedIntegers P b) hfinite).symm
  rw [hT] at hmass
  have hraw : (1 / 2 : Real) ≤
      (kv97RoundedMeasureLaw μ).real (acceptedIntegers P b) := by
    exact htotal.trans (by simpa [T] using hmass)
  exact roundedAcceptanceProbability_ge_half_of_raw_mass μ P b hraw

/-- The inverse-volume TV deadline gives an absolute lower bound for each
accepted rounded integer, before conditioning on acceptance. -/
theorem kv97_raw_point_lower_of_tvLe {n : Nat} (P : PolytopeData n)
    (b : Nat) {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (μ : Measure (EuclideanSpace Real (Fin n))) [IsProbabilityMeasure μ]
    (htv : ArlibCommunity.Foundations.Convex.TVLe μ
      (ArlibCommunity.Foundations.Convex.uniformOn volume (hitAndRunBody P b eta))
      (ENNReal.ofReal ((eta / 8) /
        (volume (hitAndRunBody P b eta)).toReal)))
    (z : Fin n → Int) (hz : z ∈ acceptedIntegers P b) :
    (1 - 3 * eta / 8) / (volume (hitAndRunBody P b eta)).toReal ≤
      (kv97RoundedMeasureLaw μ).real {z} := by
  let S := hitAndRunBody P b eta
  let V := (volume S).toReal
  let gamma : Real := decimalScale b * P.inradius
  have hgamma : 0 < gamma := mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (decimalScale b • toEuclidean P.incenter) gamma ⊆
      P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  have hfin : volume (P.scaledBody b) ≠ ⊤ :=
    (P.scaledBody_bounded b).measure_lt_top.ne
  have hS0 : volume S ≠ 0 :=
    ArlibCommunity.Algorithms.KV97.volume_inflated_ne_zero hgamma ArlibCommunity.Algorithms.KV97.cOf_nonneg hbaseball
  have hStop : volume S ≠ ⊤ :=
    ArlibCommunity.Algorithms.KV97.volume_inflated_ne_top hgamma ArlibCommunity.Algorithms.KV97.cOf_nonneg hbaseball hfin
  have hV : 0 < V := ENNReal.toReal_pos hS0 hStop
  letI : IsProbabilityMeasure (ArlibCommunity.Foundations.Convex.uniformOn volume S) :=
    ArlibCommunity.Foundations.Convex.isProbabilityMeasure_uniformOn volume hS0 hStop
  have hfacet1 : (1 : Real) ≤ P.presentation.facetCount := by
    exact_mod_cast P.facets_pos
  have hesc : ∫ p in Sᶜ, prodTent (kv97LatEmb n z) p ≤ eta / 4 := by
    have he := setIntegral_prodTent_compl_inflate_le_exp
      (c := samplerC eta) (r := (P.presentation.facetCount : Real))
      P.arlibNormal (P.scaledOffset b)
      (show kv97LatEmb n z ∈ P.scaledBody b by rwa [acceptedIntegers_eq] at hz) ArlibCommunity.Algorithms.KV97.cOf_nonneg hfacet1 (by simp)
    have hexp := ArlibCommunity.Algorithms.KV97.exp_cOf (ε := eta / 4) (by positivity)
      (by linarith)
    have h16 : ∫ p in Sᶜ, prodTent (kv97LatEmb n z) p ≤ eta / 4 / 4 := by
      simpa [S, hitAndRunBody, ArlibCommunity.Algorithms.KV97.inflated, samplerC, hexp] using he
    linarith
  have href : (1 - eta / 4) / V ≤
      ∫ p, prodTent (kv97LatEmb n z) p ∂(ArlibCommunity.Foundations.Convex.uniformOn volume S) :=
    (ArlibCommunity.Algorithms.KV97.uniformOn_window
      (S := S) (V := V) (E := eta / 4) (x := kv97LatEmb n z)
      (ArlibCommunity.Algorithms.KV97.measurableSet_inflated _ _ _ _) rfl hV hesc).1
  have hhi : ∫ p, prodTent (kv97LatEmb n z) p ∂(ArlibCommunity.Foundations.Convex.uniformOn volume S) ≤
      (1 + 0) / V :=
    (ArlibCommunity.Algorithms.KV97.uniformOn_window
      (S := S) (V := V) (E := eta / 4) (x := kv97LatEmb n z)
      (ArlibCommunity.Algorithms.KV97.measurableSet_inflated _ _ _ _) rfl hV hesc).2
  have hepsV :
      (ENNReal.ofReal ((eta / 8) / V)).toReal * V ≤ eta / 8 := by
    rw [ENNReal.toReal_ofReal (by positivity), div_mul_cancel₀ _ hV.ne']
  have hraw := (ArlibCommunity.Foundations.MarkovChainTheory.PointwiseRoute.window_of_tvLe
    (by simpa [S, V] using htv) ENNReal.ofReal_ne_top
    (measurable_prodTent (kv97LatEmb n z))
    (prodTent_nonneg (kv97LatEmb n z))
    (ArlibCommunity.Algorithms.KV97.prodTent_le_one (kv97LatEmb n z))
    hV hepsV href hhi).1
  rw [Arlib.KV97.roundedMeasureLaw_singleton_real]
  convert hraw using 1 <;> ring

theorem normalizedHitAndRun_acceptance_ge_half_of_count_volume {n : Nat}
    (hn : 2 ≤ n) (P : PolytopeData n) (b : Nat)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hprec : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius)
    (hfinite : (codedLatticePoints P b).Finite)
    (hcount : (1 / 2 : Real) ≤
      ((acceptedIntegers P b).ncard : Real) *
        ((1 - 3 * eta / 8) / (volume (hitAndRunBody P b eta)).toReal)) :
    (1 / 2 : Real) ≤
      (roundedAcceptanceProbability (normalizedHitAndRunContinuousLaw P b eta) P b : Real) := by
  let μ := normalizedHitAndRunContinuousLaw P b eta
  letI : IsProbabilityMeasure μ :=
    normalizedHitAndRunContinuousLaw_isProbabilityMeasure (by omega) P b eta
  apply roundedAcceptanceProbability_ge_half_of_pointwise μ P b
    ((1 - 3 * eta / 8) / (volume (hitAndRunBody P b eta)).toReal)
    (by
      apply Set.Finite.of_finite_image
      · rw [image_encodeInteger_acceptedIntegers]
        exact hfinite
      · exact (encodeInteger_injective b).injOn)
    ?_ hcount
  intro z hz
  exact kv97_raw_point_lower_of_tvLe P b heta0 heta1 μ
    (P.normalizedHitAndRun_tvLe hn b heta0 heta1 hprec) z hz

/-- Algebraic bridge from lattice count and inflation-volume estimates to
the raw acceptance-mass budget. -/
theorem count_volume_budget_of_comparison
    (N base inflated η latticeEta inflation : Real)
    (hInflated : 0 < inflated) (hN : 0 ≤ N)
    (hbase : base ≤ (1 + latticeEta) * N)
    (hinflate : inflated ≤ inflation * base)
    (hinflation : 0 ≤ inflation)
    (hbudget : inflation * (1 + latticeEta) ≤ 2 * (1 - 3 * η / 8)) :
    (1 / 2 : Real) ≤ N * ((1 - 3 * η / 8) / inflated) := by
  have hvolume : inflated ≤
      2 * (1 - 3 * η / 8) * N := by
    calc
      inflated ≤ inflation * base := hinflate
      _ ≤ inflation * ((1 + latticeEta) * N) :=
        mul_le_mul_of_nonneg_left hbase hinflation
      _ = (inflation * (1 + latticeEta)) * N := by ring
      _ ≤ (2 * (1 - 3 * η / 8)) * N :=
        mul_le_mul_of_nonneg_right hbudget hN
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hInflated).2
  nlinarith [hvolume]

/-- The paper's sampler precision makes facet inflation small compared
with the scaled inball. -/
theorem sampler_kappa_over_radius_le {n : Nat} (hn : 0 < n)
    (P : PolytopeData n) {η γ : Real} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hγ : 0 < γ) (hprecision : samplerRadiusRequirement P η ≤ γ) :
    ArlibCommunity.Algorithms.KV97.kappaOf (samplerC η)
      (P.presentation.facetCount : Real) / γ ≤ η / (128 * n) := by
  let r : Real := P.presentation.facetCount
  let L : Real := Real.log (32 * r / η)
  have hr : 1 ≤ r := by
    have hrNat : 1 ≤ P.presentation.facetCount := Nat.succ_le_iff.mpr P.facets_pos
    change (1 : Real) ≤ (P.presentation.facetCount : Real)
    exact_mod_cast hrNat
  have harg : 1 < 32 * r / η := by
    apply (lt_div_iff₀ hη0).2
    nlinarith
  have hL : 0 < L := Real.log_pos harg
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hlog1 : Real.log (4 / (η / 4)) ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [show 4 / (η / 4) = 16 / η by field_simp; ring]
    apply (div_le_div_of_nonneg_right ?_ hη0.le)
    nlinarith
  have hlog2 : Real.log r ≤ L := by
    apply Real.log_le_log (by linarith)
    apply (le_div_iff₀ hη0).2
    nlinarith
  have hc : samplerC η ≤ 2 * Real.sqrt L := by
    have hsquare := ArlibCommunity.Algorithms.KV97.cOf_sq (ε := η / 4) (by positivity)
      (by linarith)
    have hrootSquare : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL.le
    have hc0 := ArlibCommunity.Algorithms.KV97.cOf_nonneg (ε := η / 4)
    show ArlibCommunity.Algorithms.KV97.cOf (η / 4) ≤ _
    nlinarith
  have hfacet : Real.sqrt (2 * Real.log r) ≤ 2 * Real.sqrt L := by
    have hrootSquare : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL.le
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
    have hsquare : (Real.sqrt (2 * Real.log r)) ^ 2 =
        2 * Real.log r := Real.sq_sqrt (by positivity)
    have hnonneg := Real.sqrt_nonneg (2 * Real.log r)
    nlinarith
  have hkappa : ArlibCommunity.Algorithms.KV97.kappaOf (samplerC η) r ≤
      4 * Real.sqrt L := by
    unfold ArlibCommunity.Algorithms.KV97.kappaOf
    linarith
  have hreq : (512 * n / η) * Real.sqrt L ≤ γ := by
    simpa [samplerRadiusRequirement, r, L] using hprecision
  have hmain : ArlibCommunity.Algorithms.KV97.kappaOf (samplerC η) r ≤
      (η / (128 * n)) * γ := by
    have hnreal : (0 : Real) < n := by exact_mod_cast hn
    have hcoef : 0 < η / (128 * n) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hreq hcoef.le
    have hcancel : (η / (128 * n)) * ((512 * n / η) * Real.sqrt L) =
        4 * Real.sqrt L := by
      field_simp
      norm_num
    nlinarith
  exact (div_le_iff₀ hγ).2 hmain

theorem inflation_budget_of_small_radius {n : Nat} (hn : 0 < n)
    {η latticeEta x : Real} (hη0 : 0 < η) (hη1 : η ≤ 1 / 8)
    (hLattice0 : 0 ≤ latticeEta) (hLattice : latticeEta ≤ 1 / 8)
    (hx0 : 0 ≤ x) (hx : x ≤ η / (128 * n)) :
    (1 + x) ^ n * (1 + latticeEta) ≤ 2 * (1 - 3 * η / 8) := by
  have hnreal : (0 : Real) < n := by exact_mod_cast hn
  have hnx : (n : Real) * x ≤ 1 / 128 := by
    have hmul := mul_le_mul_of_nonneg_left hx hnreal.le
    have hcancel : (n : Real) * (η / (128 * n)) = η / 128 := by
      field_simp
    rw [hcancel] at hmul
    nlinarith
  have hpow : (1 + x) ^ n ≤ Real.exp (1 / 128) := by
    have hbase : 1 + x ≤ Real.exp x := by
      simpa [add_comm] using Real.add_one_le_exp x
    have hpow' : (1 + x) ^ n ≤ (Real.exp x) ^ n := by
      exact pow_le_pow_left₀ (by linarith) hbase _
    calc
      (1 + x) ^ n ≤ (Real.exp x) ^ n := hpow'
      _ = Real.exp ((n : Real) * x) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp (1 / 128) := Real.exp_le_exp.mpr hnx
  have hexp : Real.exp (1 / 128) ≤ 9 / 8 := by
    have h := Real.exp_le_two_add_div_two_sub
      (show (0 : Real) ≤ 1 / 128 by norm_num)
      (show (1 / 128 : Real) < 2 by norm_num)
    nlinarith
  have hηnonneg : 0 ≤ 1 + latticeEta := by linarith
  have hprod : (1 + x) ^ n * (1 + latticeEta) ≤ (9 / 8) * (1 + latticeEta) :=
    mul_le_mul_of_nonneg_right (hpow.trans hexp) hηnonneg
  nlinarith

theorem normalizedHitAndRun_acceptance_ge_half_of_base_comparison {n : Nat}
    (hn : 2 ≤ n) (P : PolytopeData n) (b : Nat)
    {eta : Real} (heta0 : 0 < eta) (heta8 : eta ≤ 1 / 8)
    (latticeEta : Real) (hlattice0 : 0 ≤ latticeEta)
    (hlattice8 : latticeEta ≤ 1 / 8)
    (hfinite : (codedLatticePoints P b).Finite)
    (hprecision : samplerRadiusRequirement P eta ≤
      decimalScale b * P.inradius)
    (hbase : (volume (P.scaledBody b)).toReal ≤
      (1 + latticeEta) * ((acceptedIntegers P b).ncard : Real)) :
    (1 / 2 : Real) ≤
      (roundedAcceptanceProbability (normalizedHitAndRunContinuousLaw P b eta) P b : Real) := by
  let gamma : Real := decimalScale b * P.inradius
  let inflation : Real := (1 + ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta)
    (P.presentation.facetCount : Real) / gamma) ^ n
  have hgamma : 0 < gamma := mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (decimalScale b • toEuclidean P.incenter) gamma ⊆
      P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  have hfin : volume (P.scaledBody b) ≠ ⊤ :=
    (P.scaledBody_bounded b).measure_lt_top.ne
  have hV : 0 < (volume (hitAndRunBody P b eta)).toReal := by
    simpa [hitAndRunBody, gamma] using
      (ArlibCommunity.Algorithms.KV97.toReal_volume_inflated_pos hgamma ArlibCommunity.Algorithms.KV97.cOf_nonneg
        hbaseball hfin)
  have hinflate : (volume (hitAndRunBody P b eta)).toReal ≤
      inflation * (volume (P.scaledBody b)).toReal := by
    simpa [hitAndRunBody, inflation, gamma, PolytopeData.scaledBody] using
      (ArlibCommunity.Algorithms.KV97.toReal_volume_inflated_le hgamma ArlibCommunity.Algorithms.KV97.cOf_nonneg
        hbaseball hfin)
  have hkappa0 : 0 ≤ ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta)
      (P.presentation.facetCount : Real) :=
    ArlibCommunity.Algorithms.KV97.kappaOf_nonneg ArlibCommunity.Algorithms.KV97.cOf_nonneg
  have hinflation : 0 ≤ inflation := by
    unfold inflation
    positivity
  have hkappa := sampler_kappa_over_radius_le (by omega) P heta0
    (by linarith) hgamma hprecision
  have hbudget : inflation * (1 + latticeEta) ≤ 2 * (1 - 3 * eta / 8) := by
    exact inflation_budget_of_small_radius (by omega) heta0 heta8
      hlattice0 hlattice8
      (div_nonneg hkappa0 hgamma.le) hkappa
  have hcount := count_volume_budget_of_comparison
    ((acceptedIntegers P b).ncard : Real)
    (volume (P.scaledBody b)).toReal
    (volume (hitAndRunBody P b eta)).toReal eta latticeEta inflation
    hV (by positivity) hbase hinflate hinflation hbudget
  exact normalizedHitAndRun_acceptance_ge_half_of_count_volume hn P b
    heta0 (by linarith) hprecision hfinite hcount

end ttc

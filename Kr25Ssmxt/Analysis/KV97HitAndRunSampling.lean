import Kr25Ssmxt.Analysis.HitAndRunScaledPolytope
import Kr25Ssmxt.Analysis.IntegerRoundingBridge

/-!
# KV97 randomized rounding driven by finite-step Hit-and-Run

This file connects the inverse-volume total-variation guarantee to the actual randomized
rounding and rejection law, with the final result stated in TTC's
`AlmostUniformPointwise` interface.
-/

noncomputable section

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory Metric Set
open Arlib.Lattice.Rounding
open scoped ENNReal

private lemma kv97_ratio_window_mem_relErr {eta N p : Real}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hN : 0 < N)
    (hlo : (1 - 3 * eta / 8) / ((1 + eta / 8) * N) ≤ p)
    (hhi : p ≤ (1 + eta / 8) / ((1 - 3 * eta / 8) * N)) :
    p ∈ Arlib.relErr eta (1 / N) := by
  rw [Arlib.mem_relErr]
  have hplus : 0 < 1 + eta / 8 := by linarith
  have hminus : 0 < 1 - 3 * eta / 8 := by linarith
  have hlscalar : 1 - eta ≤ (1 - 3 * eta / 8) / (1 + eta / 8) := by
    rw [le_div_iff₀ hplus]
    nlinarith [mul_nonneg heta0 (sub_nonneg.mpr heta1)]
  have huscalar : (1 + eta / 8) / (1 - 3 * eta / 8) ≤ 1 + eta := by
    rw [div_le_iff₀ hminus]
    nlinarith [mul_nonneg heta0 (sub_nonneg.mpr heta1)]
  constructor
  · calc
      (1 - eta) * (1 / N) = (1 - eta) / N := by ring
      _ ≤ ((1 - 3 * eta / 8) / (1 + eta / 8)) / N := by
        exact div_le_div_of_nonneg_right hlscalar hN.le
      _ = (1 - 3 * eta / 8) / ((1 + eta / 8) * N) := by field_simp
      _ ≤ p := hlo
  · calc
      p ≤ (1 + eta / 8) / ((1 - 3 * eta / 8) * N) := hhi
      _ = ((1 + eta / 8) / (1 - 3 * eta / 8)) / N := by field_simp
      _ ≤ (1 + eta) / N := div_le_div_of_nonneg_right huscalar hN.le
      _ = (1 + eta) * (1 / N) := by ring

private lemma acceptedIntegers_finite {n : Nat} (P : PolytopeData n) (b : Nat)
    (hfinite : (codedLatticePoints P b).Finite) : (acceptedIntegers P b).Finite := by
  apply Set.Finite.of_finite_image
  · rw [image_encodeInteger_acceptedIntegers]
    exact hfinite
  · exact (encodeInteger_injective b).injOn

private lemma acceptedIntegers_nonempty {n : Nat} (P : PolytopeData n) (b : Nat)
    (hnonempty : (codedLatticePoints P b).Nonempty) : (acceptedIntegers P b).Nonempty := by
  rw [← image_encodeInteger_acceptedIntegers] at hnonempty
  rcases hnonempty with ⟨_, z, hz, rfl⟩
  exact ⟨z, hz⟩

private lemma ncard_acceptedIntegers {n : Nat} (P : PolytopeData n) (b : Nat) :
    (acceptedIntegers P b).ncard = (codedLatticePoints P b).ncard := by
  rw [← image_encodeInteger_acceptedIntegers,
    Set.ncard_image_of_injective _ (encodeInteger_injective b)]

/-- A continuous law at TV distance `(eta/8)/Vol(P')` from uniform on the KV97 inflated
body becomes an `eta`-pointwise-almost-uniform TTC lattice-point law after randomized
rounding and rejection. -/
theorem almostUniform_acceptedRoundedLatticeLaw_of_tvLe {n : Nat}
    (P : PolytopeData n) (b : Nat) {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty)
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsProbabilityMeasure mu]
    (htv : Arlib.TVLe mu
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
          (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)))
      (ENNReal.ofReal ((eta / 8) /
        (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
          (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))).toReal))) :
    AlmostUniformPointwise (acceptedRoundedLatticeLaw mu P b)
      (codedLatticePoints P b) eta := by
  let S := Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
    (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)
  let V := (volume S).toReal
  let T := acceptedIntegers P b
  have hTfin : T.Finite := acceptedIntegers_finite P b hfinite
  have hTne : T.Nonempty := acceptedIntegers_nonempty P b hnonempty
  have hTcard : T.ncard = (codedLatticePoints P b).ncard := ncard_acceptedIntegers P b
  letI : Fintype T := hTfin.fintype
  letI : Nonempty T := hTne.to_subtype
  let gamma : Real := decimalScale b * P.inradius
  have hgamma : 0 < gamma := mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (decimalScale b • toEuclidean P.incenter) gamma ⊆
      P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  have hfin : volume (P.scaledBody b) ≠ ⊤ :=
    (P.scaledBody_bounded b).measure_lt_top.ne
  have hS0 : volume S ≠ 0 :=
    Arlib.KV97.volume_inflated_ne_zero hgamma Arlib.KV97.cOf_nonneg hbaseball
  have hStop : volume S ≠ ⊤ :=
    Arlib.KV97.volume_inflated_ne_top hgamma Arlib.KV97.cOf_nonneg hbaseball hfin
  have hV : 0 < V := ENNReal.toReal_pos hS0 hStop
  letI : IsProbabilityMeasure (Arlib.uniformOn volume S) :=
    Arlib.isProbabilityMeasure_uniformOn volume hS0 hStop
  have hfacet1 : (1 : Real) ≤ P.presentation.facetCount := by
    exact_mod_cast P.facets_pos
  have href : ∀ z ∈ T,
      (1 - eta / 4) / V ≤
          ∫ p, prodTent (kv97LatEmb n z) p ∂(Arlib.uniformOn volume S) ∧
        ∫ p, prodTent (kv97LatEmb n z) p ∂(Arlib.uniformOn volume S) ≤
          (1 + 0) / V := by
    intro z hz
    have hesc : ∫ p in Sᶜ, prodTent (kv97LatEmb n z) p ≤ eta / 4 := by
      have he := setIntegral_prodTent_compl_inflate_le_exp
        (c := Arlib.KV97.cOf eta) (r := (P.presentation.facetCount : Real))
        P.arlibNormal (P.scaledOffset b) hz Arlib.KV97.cOf_nonneg hfacet1 (by simp)
      simpa [S, Arlib.KV97.inflated, Arlib.KV97.exp_cOf heta0 heta1] using he
    exact Arlib.PointwiseRoute.uniformOn_window
      (S := S) (V := V) (E := eta / 4) (x := kv97LatEmb n z)
      (Arlib.KV97.measurableSet_inflated _ _ _ _) rfl hV hesc
  have hepsV :
      (ENNReal.ofReal ((eta / 8) / V)).toReal * V ≤ eta / 8 := by
    rw [ENNReal.toReal_ofReal (by positivity), div_mul_cancel₀ _ hV.ne']
  have hTncard : T.ncard = Fintype.card T := by
    rw [← Nat.card_coe_set_eq T, Nat.card_eq_fintype_card]
  have hraw : ∀ z ∈ T,
      (1 - 3 * eta / 8) / ((1 + eta / 8) * (T.ncard : Real)) ≤
          (kv97RoundedMeasureLaw mu).real {z} /
            (kv97RoundedMeasureLaw mu).real T ∧
        (kv97RoundedMeasureLaw mu).real {z} /
            (kv97RoundedMeasureLaw mu).real T ≤
          (1 + eta / 8) / ((1 - 3 * eta / 8) * (T.ncard : Real)) := by
    intro z hz
    have h := Arlib.PointwiseRoute.ratio_bounds_of_tvLe
      (i := (⟨z, hz⟩ : T)) (V := V) (a := eta / 4) (b := 0) (θ := eta / 8)
      (g := fun w : T => fun p => prodTent (kv97LatEmb n w.1) p)
      (by simpa [S, V] using htv) ENNReal.ofReal_ne_top
      (fun w => measurable_prodTent (kv97LatEmb n w.1))
      (fun w p => prodTent_nonneg (kv97LatEmb n w.1) p)
      (fun w p => Arlib.PointwiseRoute.prodTent_le_one (kv97LatEmb n w.1) p)
      hV hepsV (fun w => (href w.1 w.2).1) (fun w => (href w.1 w.2).2)
      (by linarith)
    rw [Arlib.KV97.roundedMeasureLaw_singleton_real,
      Arlib.KV97.roundedMeasureLaw_real_finite mu T hTfin]
    rw [hTncard]
    convert h using 1 <;> ring
  have hN : 0 < (T.ncard : Real) := by
    exact_mod_cast hTne.ncard_pos hTfin
  obtain ⟨z, hz⟩ := hTne
  have hratioPos : 0 <
      (kv97RoundedMeasureLaw mu).real {z} /
        (kv97RoundedMeasureLaw mu).real T := by
    exact (div_pos (by linarith) (mul_pos (by linarith) hN)).trans_le (hraw z hz).1
  have hacceptReal : (kv97RoundedMeasureLaw mu).real T ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at hratioPos
    exact (lt_irrefl 0) hratioPos
  have haccept : kv97RoundedMeasureLaw mu T ≠ 0 := by
    intro hzero
    apply hacceptReal
    simp [Measure.real, hzero]
  apply acceptedRoundedLatticeLaw_almostUniform_of_ratio mu P b hfinite hnonempty haccept
  intro w hw
  rw [← hTcard]
  exact kv97_ratio_window_mem_relErr heta0.le heta1 hN (hraw w hw).1 (hraw w hw).2

/-- End-to-end single-point sampler in the dimension range of Arlib's unconditional
Hit-and-Run theorem: finite walk, KV97 randomized rounding, rejection, and TTC coding. -/
theorem PolytopeData.exists_hitAndRun_latticePointLaw {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat)
    (hunit : 1 ≤ decimalScale b * P.inradius)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty) :
    ∃ (D : Real) (m : Nat),
      (∀ x ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
          (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real),
        ∀ y ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
          (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real), dist x y ≤ D) ∧
      Arlib.MarkovChains.hrDeadlineUncond n D
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
              (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)) /
            volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal
          (min 1 ((eta / 8) /
            (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
              (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))).toReal)) ≤
        (m : Real) ∧
      m = Nat.ceil (Arlib.MarkovChains.hrDeadlineUncond n D
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
              (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)) /
            volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal
          (min 1 ((eta / 8) /
            (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
              (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))).toReal))) ∧
      AlmostUniformPointwise
        (acceptedRoundedLatticeLaw
          (Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun
              (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
                (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))))
            (Arlib.uniformOn volume
              (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)) m)
          P b)
        (codedLatticePoints P b) eta := by
  obtain ⟨D, m, hD, hdeadline, hmceil, htv⟩ := P.exists_hitAndRun_inflated_tvLe_inv_volume hn b hunit
    (cp := Arlib.KV97.cOf eta) (r := (P.presentation.facetCount : Real))
    Arlib.KV97.cOf_nonneg (by positivity : 0 < eta / 8)
  let mu0 : Measure (EuclideanSpace Real (Fin n)) :=
    Arlib.uniformOn volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)
  have hball0 : volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hballtop : volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  letI : IsProbabilityMeasure mu0 :=
    Arlib.isProbabilityMeasure_uniformOn volume hball0 hballtop
  let mu : Measure (EuclideanSpace Real (Fin n)) :=
    Arlib.MarkovChains.iterate
      (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun
        (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
          (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)))) mu0 m
  letI : IsProbabilityMeasure mu := by
    dsimp only [mu]
    infer_instance
  refine ⟨D, m, hD, hdeadline, hmceil, ?_⟩
  apply almostUniform_acceptedRoundedLatticeLaw_of_tvLe P b heta0 heta1 hfinite hnonempty mu
  simpa [mu, mu0] using htv

end Kr25Ssmxt

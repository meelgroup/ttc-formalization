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
      (Arlib.uniformOn volume ((fun z : EuclideanSpace Real (Fin n) => γ • z + cen) ⁻¹' A)) =
        Arlib.uniformOn volume A := by
  have hS : Measurable (fun z : EuclideanSpace Real (Fin n) => γ • z + cen) := by fun_prop
  ext t ht
  rw [Measure.map_apply hS ht, Arlib.uniformOn_apply volume (hA.preimage hS)
    (ht.preimage hS), Arlib.uniformOn_apply volume hA ht, ← Set.preimage_inter,
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
  exact Arlib.KV97.body_subset_inflated P.arlibNormal (P.scaledOffset b)
    (P.presentation.facetCount : Real) Arlib.KV97.cOf_nonneg hscaled

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
      (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
        (P.presentation.facetCount : Real) / P.scaledInradius b) *
        (2 * P.outerRadius / P.inradius) := by
  have hG : 0 < P.scaledInradius b :=
    mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (P.scaledIncenter b) (P.scaledInradius b) ⊆
      P.scaledBody b := Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  let κ := Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
    (P.presentation.facetCount : Real)
  let C := (1 + κ / P.scaledInradius b) * (2 * P.outerRadius / P.inradius)
  have hκ : 0 ≤ κ := Arlib.KV97.kappaOf_nonneg Arlib.KV97.cOf_nonneg
  have hdist : ∀ x ∈ P.normalizedHitAndRunBody b eta,
      ∀ y ∈ P.normalizedHitAndRunBody b eta, dist x y ≤ C := by
    intro x hx y hy
    have hx' : P.samplerChart b x ∈ hitAndRunBody P b eta := by
      rwa [P.normalizedHitAndRunBody_eq_preimage b eta] at hx
    have hy' : P.samplerChart b y ∈ hitAndRunBody P b eta := by
      rwa [P.normalizedHitAndRunBody_eq_preimage b eta] at hy
    have hbound := dist_le_of_mem_inflated hG Arlib.KV97.cOf_nonneg hbaseball
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

/-- The finite-facet walk in unit-inball coordinates has the inverse-volume
total-variation accuracy required by KV97 after mapping back to the scaled body. -/
theorem PolytopeData.normalizedHitAndRun_tvLe {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat) {eta : Real} (heta0 : 0 < eta) :
    Arlib.TVLe (normalizedHitAndRunContinuousLaw P b eta)
      (Arlib.uniformOn volume (hitAndRunBody P b eta))
      (ENNReal.ofReal ((eta / 8) /
        (volume (hitAndRunBody P b eta)).toReal)) := by
  letI : NeZero n := ⟨by omega⟩
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
      using (Arlib.KV97.toReal_volume_inflated_pos hG Arlib.KV97.cOf_nonneg
        hbaseball hfin)
  let eps : Real := min 1 ((eta / 8) / (volume (hitAndRunBody P b eta)).toReal)
  have heps0 : 0 < eps := (lt_min_iff).2 ⟨one_pos, div_pos (by positivity) hV⟩
  have heps1 : eps ≤ 1 := min_le_left _ _
  have hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun K))
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1))
        (normalizedHitAndRunSteps P b eta))
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
    apply tvLe_iterate_lazy_hitAndRun_from_unit_inball hn
      (Arlib.Polytope.convex_body P.arlibNormal (P.normalizedHitAndRunOffset b eta))
      (Arlib.Polytope.isClosed_body P.arlibNormal (P.normalizedHitAndRunOffset b eta))
      (Arlib.Polytope.measurableSet_body P.arlibNormal
        (P.normalizedHitAndRunOffset b eta))
      hbounded (P.normalizedHitAndRun_unitBall b eta)
      (fun _ hx _ hy => Metric.dist_le_diam_of_mem hbounded hx hy)
      heps0 heps1
    change ArlibCommunity.Algorithms.HitAndRun.deadline n (Metric.diam K)
      (volume K / volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal
      eps ≤ (normalizedHitAndRunSteps P b eta : Real)
    simpa only [normalizedHitAndRunSteps, hitAndRunTolerance, K, eps]
      using (Nat.le_ceil (ArlibCommunity.Algorithms.HitAndRun.deadline n
        (Metric.diam K)
        (volume K / volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal
        eps))
  have hfiniteStep := ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep_eq_step
    P.arlibNormal (P.normalizedHitAndRunOffset b eta) hbounded
  have hmapped := hmix.map (show Measurable (P.samplerChart b) by
    unfold PolytopeData.samplerChart
    fun_prop)
  have htarget : (Arlib.uniformOn volume K).map (P.samplerChart b) =
      Arlib.uniformOn volume (hitAndRunBody P b eta) := by
    change (Arlib.uniformOn volume (P.normalizedHitAndRunBody b eta)).map
      (P.samplerChart b) = Arlib.uniformOn volume (hitAndRunBody P b eta)
    rw [P.normalizedHitAndRunBody_eq_preimage b eta]
    exact map_uniformOn_samplerChart hG (P.scaledIncenter b)
      (Arlib.KV97.measurableSet_inflated P.arlibNormal (P.scaledOffset b)
        (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))
  have hmix' := hmapped.mono (ENNReal.ofReal_mono (min_le_right _ _))
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
    Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)
  have hball0 : volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hballtop : volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  letI : IsProbabilityMeasure mu0 :=
    Arlib.isProbabilityMeasure_uniformOn volume hball0 hballtop
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
    (hunit : 1 ≤ decimalScale b * P.inradius)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty) :
    AlmostUniformPointwise
      (normalizedHitAndRunPointLaw hn P b hunit eta heta0 heta1 hfinite hnonempty)
      (codedLatticePoints P b) eta := by
  letI : NeZero n := ⟨by omega⟩
  let mu := normalizedHitAndRunContinuousLaw P b eta
  let mu0 : Measure (EuclideanSpace Real (Fin n)) :=
    Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)
  have hball0 : volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hballtop : volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  letI : IsProbabilityMeasure mu0 :=
    Arlib.isProbabilityMeasure_uniformOn volume hball0 hballtop
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
  simpa [mu, hitAndRunBody] using P.normalizedHitAndRun_tvLe hn b heta0

/-- Forgetting the number of rejection attempts recovers the conditional
rounded point law used by the manuscript sampler. -/
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

/-- Summing retry costs across independent requests preserves the manuscript
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
      (fun draws => (true, fun i => (draws i).1)) =
    (Measure.pi (fun _ : Fin count => ν)).map (fun draws => (true, draws))
  rw [← hpi, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end Kr25Ssmxt

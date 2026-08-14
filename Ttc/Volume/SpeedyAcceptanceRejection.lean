/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Volume.AmbientGaussianRejection
import Ttc.Volume.CVSampler

/-!
# An operational rejection loop for the speedy-to-Gaussian acceptance filter

`CVSampler.phaseLaw` expresses its final rejection step as a normalized `withDensity`.
This file realizes that expression by i.i.d. pairs consisting of a proposal point and an
independent uniform coin on `[0,1]`.  The first accepted point has exactly the normalized
`withDensity` law.  For the ideal inflated-Gaussian proposal, the acceptance ratio bound in
`MapSpeedyToTarget` gives at most two expected rounds.
-/

namespace Ttc.SpeedyRejection

open MeasureTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.Probability
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- The point/coin pair is accepted when the coin is below `speedyAcceptReal`. -/
def acceptRegion (c s : ℝ) : Set (Space n × ℝ) :=
  {q | q.2 ≤ speedyAcceptReal c s q.1}

theorem measurableSet_acceptRegion (c s : ℝ) :
    MeasurableSet (acceptRegion (n := n) c s) :=
  measurableSet_le measurable_snd
    ((measurable_speedyAcceptReal c s).comp measurable_fst)

/-- The independent uniform coin used in each rejection round. -/
noncomputable def unitCoin : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance instIsProbabilityMeasureUnitCoin : IsProbabilityMeasure unitCoin := by
  rw [unitCoin, ← Arlib.uniformOn_unitInterval_eq_restrict]
  exact Arlib.isProbabilityMeasure_uniformOn_unitInterval

/-- One operational rejection proposal: a point from `Q` and an independent uniform coin. -/
noncomputable def proposal (Q : Measure (Space n)) : Measure (Space n × ℝ) :=
  Q.prod unitCoin

instance instIsProbabilityMeasureProposal (Q : Measure (Space n)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (proposal Q) := by
  unfold proposal
  infer_instance

theorem slice_acceptRegion_of_mem (c s : ℝ) {S : Set (Space n)} {x : Space n} (hx : x ∈ S) :
    Prod.mk x ⁻¹' (Prod.fst ⁻¹' S ∩ acceptRegion c s) = Iic (speedyAcceptReal c s x) := by
  ext u
  simp [acceptRegion, hx]

theorem slice_acceptRegion_of_notMem (c s : ℝ) {S : Set (Space n)} {x : Space n}
    (hx : x ∉ S) :
    Prod.mk x ⁻¹' (Prod.fst ⁻¹' S ∩ acceptRegion c s) = (∅ : Set ℝ) := by
  ext u
  simp [acceptRegion, hx]

/-- A uniform `[0,1]` coin falls below the speedy acceptance probability with exactly that
probability. -/
theorem unitCoin_Iic_speedyAccept {c s : ℝ} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1) (x : Space n) :
    unitCoin (Iic (speedyAcceptReal c s x)) = ENNReal.ofReal (speedyAcceptReal c s x) := by
  have h0 := (speedyAcceptReal_pos c s x).le
  have h1 := speedyAcceptReal_le_one hs hc2 x
  rw [unitCoin, Measure.restrict_apply measurableSet_Iic,
    show Iic (speedyAcceptReal c s x) ∩ Icc (0 : ℝ) 1 =
        Icc 0 (speedyAcceptReal c s x) by
      ext u
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hu, hu0, _⟩
        exact ⟨hu0, hu⟩
      · rintro ⟨hu0, hu⟩
        exact ⟨hu, hu0, hu.trans h1⟩,
    Real.volume_Icc, sub_zero]

/-- The uniform-coin event is exactly the `withDensity` numerator on every measurable
cylinder. -/
theorem proposal_apply_acceptRegion (Q : Measure (Space n)) [SFinite Q]
    {c s : ℝ} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1) {S : Set (Space n)} (hS : MeasurableSet S) :
    proposal Q (Prod.fst ⁻¹' S ∩ acceptRegion c s)
      = ∫⁻ x in S, ENNReal.ofReal (speedyAcceptReal c s x) ∂Q := by
  rw [proposal, Measure.prod_apply
    ((measurable_fst hS).inter (measurableSet_acceptRegion c s)),
    ← lintegral_indicator hS]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, slice_acceptRegion_of_mem c s hx,
      unitCoin_Iic_speedyAccept hs hc2]
  · rw [Set.indicator_of_notMem hx, slice_acceptRegion_of_notMem c s hx, measure_empty]

/-- The one-round acceptance probability is the total mass of the acceptance-weighted
proposal. -/
theorem proposal_acceptRegion (Q : Measure (Space n)) [SFinite Q]
    {c s : ℝ} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1) :
    proposal Q (acceptRegion c s)
      = (Q.withDensity fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ := by
  have h := proposal_apply_acceptRegion Q hs hc2 (S := Set.univ) MeasurableSet.univ
  rw [Set.preimage_univ, Set.univ_inter] at h
  rw [h, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- Reading the point from a pair conditioned on coin acceptance gives exactly the normalized
`withDensity` law used by `CVSampler.phaseLaw`. -/
theorem map_fst_condOn_proposal (Q : Measure (Space n)) [IsProbabilityMeasure Q]
    {c s : ℝ} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1) :
    Measure.map Prod.fst (Arlib.condOn (proposal Q) (acceptRegion c s))
      = Arlib.condOn
          (Q.withDensity fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_fst hS,
    Arlib.condOn_apply _ (measurableSet_acceptRegion c s) (measurable_fst hS),
    proposal_apply_acceptRegion Q hs hc2 hS, proposal_acceptRegion Q hs hc2,
    Arlib.condOn_apply _ MeasurableSet.univ hS, Set.inter_univ,
    withDensity_apply _ hS]

/-- The point returned by the explicit i.i.d. first-acceptance loop. -/
noncomputable def firstAcceptedPoint (c s : ℝ) (omega : RoundSpace (Space n × ℝ)) : Space n :=
  (Ttc.CV.firstAcceptedDraw (acceptRegion c s) omega).1

theorem measurable_firstAcceptedPoint (c s : ℝ) :
    Measurable (firstAcceptedPoint (n := n) c s) :=
  measurable_fst.comp (Ttc.CV.measurable_firstAcceptedDraw (measurableSet_acceptRegion c s))

/-- **Operational output law.** The first point whose independent coin accepts has exactly
the normalized `withDensity` law, not merely a TV approximation to it. -/
theorem map_firstAcceptedPoint_eq_condOn_withDensity (Q : Measure (Space n))
    [IsProbabilityMeasure Q] {c s : ℝ} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hmass : (Q.withDensity fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ ≠ 0) :
    Measure.map (firstAcceptedPoint c s) (roundsMeasure (proposal Q))
      = Arlib.condOn
          (Q.withDensity fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ := by
  calc
    Measure.map (firstAcceptedPoint c s) (roundsMeasure (proposal Q))
        = Measure.map Prod.fst
            (Measure.map (Ttc.CV.firstAcceptedDraw (acceptRegion c s))
              (roundsMeasure (proposal Q))) := by
            rw [Measure.map_map measurable_fst
              (Ttc.CV.measurable_firstAcceptedDraw (measurableSet_acceptRegion c s))]
            rfl
    _ = Measure.map Prod.fst (Arlib.condOn (proposal Q) (acceptRegion c s)) := by
          rw [Ttc.CV.map_firstAcceptedDraw_eq_condOn (proposal Q)
            (measurableSet_acceptRegion c s)]
          rw [proposal_acceptRegion Q hs hc2]
          exact pos_iff_ne_zero.2 hmass
    _ = Arlib.condOn
          (Q.withDensity fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ :=
        map_fst_condOn_proposal Q hs hc2

/-- Positive acceptance makes the explicit loop terminate almost surely. -/
theorem rejection_terminates_ae (Q : Measure (Space n)) [IsProbabilityMeasure Q]
    {c s : ℝ} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hmass : (Q.withDensity fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ ≠ 0) :
    roundsMeasure (proposal Q) (neverAccepts (acceptRegion c s)) = 0 := by
  apply measure_neverAccepts (proposal Q) (measurableSet_acceptRegion c s)
  rw [proposal_acceptRegion Q hs hc2]
  exact pos_iff_ne_zero.2 hmass

/-- A half-mass lower bound gives at most two expected rejection rounds. -/
theorem expected_rejection_rounds_le_two_of_half (Q : Measure (Space n))
    [IsProbabilityMeasure Q] {c s : ℝ} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hhalf : ENNReal.ofReal (1 / 2) ≤
      (Q.withDensity fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ) :
    (∫ omega, (roundCountNat (acceptRegion c s) omega : ℝ)
      ∂(roundsMeasure (proposal Q))) ≤ 2 := by
  have hacc : ENNReal.ofReal (1 / 2) ≤ proposal Q (acceptRegion c s) := by
    rw [proposal_acceptRegion Q hs hc2]
    exact hhalf
  have h := integral_roundCountNat_le (proposal Q) (measurableSet_acceptRegion c s)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hacc
  norm_num at h ⊢
  exact h

/-- A quarter-mass lower bound, as obtained for the approximate proposal inside
`tvLe_speedyRejection_target_of`, gives at most four rounds. -/
theorem expected_rejection_rounds_le_four_of_quarter (Q : Measure (Space n))
    [IsProbabilityMeasure Q] {c s : ℝ} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hquarter : ENNReal.ofReal (1 / 4) ≤
      (Q.withDensity fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ) :
    (∫ omega, (roundCountNat (acceptRegion c s) omega : ℝ)
      ∂(roundsMeasure (proposal Q))) ≤ 4 := by
  have hacc : ENNReal.ofReal (1 / 4) ≤ proposal Q (acceptRegion c s) := by
    rw [proposal_acceptRegion Q hs hc2]
    exact hquarter
  have h := integral_roundCountNat_le (proposal Q) (measurableSet_acceptRegion c s)
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) hacc
  norm_num at h ⊢
  exact h

/-! ## The ideal inflated-Gaussian proposal -/

/-- The exact proposal obtained after conditioning on the shrunken body and rescaling in the
ideal speedy-to-target argument. -/
noncomputable def inflatedGaussianProposal (K : Set (Space n)) (c s : ℝ) : Measure (Space n) :=
  Arlib.condOn
    ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ

theorem isProbabilityMeasure_inflatedGaussianProposal {K : Set (Space n)}
    (hball : ball (0 : Space n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    IsProbabilityMeasure (inflatedGaussianProposal K c s) := by
  have hs' : 0 < s / c ^ 2 := by positivity
  have h0 : ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ ≠ 0 := by
    rw [gaussianRestrict_univ]
    exact (lintegral_gaussianWeight_pos hs' one_pos hball).ne'
  have htop : ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ ≠ ⊤ := by
    rw [gaussianRestrict_univ]
    exact lintegral_gaussianWeight_ne_top hs' hKvol
  exact Arlib.isProbabilityMeasure_condOn _ h0 htop

/-- The acceptance mass of the ideal inflated-Gaussian proposal is at least `c^n`.  This is
the operational form of `pow_le_acceptance_ratio`. -/
theorem pow_le_inflatedGaussian_acceptanceMass {K : Set (Space n)}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (hball : ball (0 : Space n) 1 ⊆ K)
    (hKvol : volume K ≠ ⊤) {c s : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hs : 0 < s) :
    ENNReal.ofReal (c ^ n) ≤
      ((inflatedGaussianProposal K c s).withDensity
        fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ := by
  have hs' : 0 < s / c ^ 2 := by positivity
  have hM0 : ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ ≠ 0 := by
    rw [gaussianRestrict_univ]
    exact (lintegral_gaussianWeight_pos hs' one_pos hball).ne'
  have hMtop : ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ ≠ ⊤ := by
    rw [gaussianRestrict_univ]
    exact lintegral_gaussianWeight_ne_top hs' hKvol
  have h0K : (0 : Space n) ∈ K := hball (mem_ball_self one_pos)
  rw [inflatedGaussianProposal, Arlib.condOn_def, Measure.restrict_univ,
    Arlib.withDensity_smul_measure, withDensity_gaussian_mul_speedyAccept hc0.ne' hs.ne',
    Measure.smul_apply, smul_eq_mul, gaussianRestrict_univ, gaussianRestrict_univ]
  exact pow_le_acceptance_ratio hK hKc h0K hc0 hc1 hs hKvol hball

/-- At the source shrink factor `c = 1 - 1/(2n)`, the ideal operational rejection loop uses
at most two rounds in expectation. -/
theorem expected_inflatedGaussian_rejection_rounds_le_two (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {s : ℝ} (hs : 0 < s) :
    let c : ℝ := 1 - 1 / (2 * (n : ℝ))
    ∫ omega, (roundCountNat (acceptRegion c s) omega : ℝ)
        ∂(roundsMeasure (proposal (inflatedGaussianProposal K c s))) ≤ 2 := by
  dsimp only
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hc0 : (0 : ℝ) < 1 - 1 / (2 * (n : ℝ)) := by
    have : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : 1 - 1 / (2 * (n : ℝ)) ≤ 1 := by
    have : 0 ≤ 1 / (2 * (n : ℝ)) := by positivity
    linarith
  have hc2 : (1 - 1 / (2 * (n : ℝ))) ^ 2 ≤ 1 := sq_shrink_le_one hn
  letI : IsProbabilityMeasure
      (inflatedGaussianProposal K (1 - 1 / (2 * (n : ℝ))) s) :=
    isProbabilityMeasure_inflatedGaussianProposal hball hKvol hc0 hs
  have hpow := pow_le_inflatedGaussian_acceptanceMass hK hKc hball hKvol hc0 hc1 hs
  have hhalf : ENNReal.ofReal (1 / 2) ≤
      ((inflatedGaussianProposal K (1 - 1 / (2 * (n : ℝ))) s).withDensity
        fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) s x)) Set.univ :=
    le_trans (ENNReal.ofReal_le_ofReal (half_le_one_sub_inv_two_mul_pow hn)) hpow
  exact expected_rejection_rounds_le_two_of_half
    (inflatedGaussianProposal K (1 - 1 / (2 * (n : ℝ))) s) hs hc2 hhalf

/-! ## Direct identification with `CVSampler.phaseLaw` -/

/-- The point proposal appearing immediately before the final `withDensity` in
`CVSampler.phaseLaw`. -/
noncomputable def phasePointProposal (K : Set (Space n)) (δ s : ℝ)
    (mu0 : Measure (Space n)) (t : ℕ) : Measure (Space n) :=
  Measure.map (fun x : Space n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
    (Arlib.condOn
      (iterate (lazy (speedyMetropolisGaussian K δ s)) mu0 t)
      ((1 - 1 / (2 * (n : ℝ))) • K))

/-- The explicit first-accepted-point loop returns exactly `CVSampler.phaseLaw`. -/
theorem map_firstAcceptedPoint_eq_phaseLaw (K : Set (Space n)) (δ : ℝ) {s : ℝ}
    (mu0 : Measure (Space n)) (t : ℕ)
    [IsProbabilityMeasure (phasePointProposal K δ s mu0 t)] (hs : 0 < s)
    (hc2 : (1 - 1 / (2 * (n : ℝ))) ^ 2 ≤ 1)
    (hmass : ((phasePointProposal K δ s mu0 t).withDensity fun x =>
      ENNReal.ofReal (speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) s x)) Set.univ ≠ 0) :
    Measure.map (firstAcceptedPoint (1 - 1 / (2 * (n : ℝ))) s)
        (roundsMeasure (proposal (phasePointProposal K δ s mu0 t)))
      = Ttc.CVSampler.phaseLaw K δ s mu0 t := by
  rw [map_firstAcceptedPoint_eq_condOn_withDensity
    (phasePointProposal K δ s mu0 t) hs hc2 hmass]
  rw [phasePointProposal, Ttc.CVSampler.phaseLaw]

end Ttc.SpeedyRejection

#print axioms Ttc.SpeedyRejection.map_firstAcceptedPoint_eq_condOn_withDensity
#print axioms Ttc.SpeedyRejection.rejection_terminates_ae
#print axioms Ttc.SpeedyRejection.expected_rejection_rounds_le_two_of_half
#print axioms Ttc.SpeedyRejection.expected_rejection_rounds_le_four_of_quarter
#print axioms Ttc.SpeedyRejection.pow_le_inflatedGaussian_acceptanceMass
#print axioms Ttc.SpeedyRejection.expected_inflatedGaussian_rejection_rounds_le_two
#print axioms Ttc.SpeedyRejection.map_firstAcceptedPoint_eq_phaseLaw

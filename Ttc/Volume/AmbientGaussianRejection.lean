/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptiveChunkEndpoints
import Arlib.Probability.RejectionRounds
import Arlib.MarkovChains.Continuous.PointwiseRoute
import Arlib.Convexity.GaussianCooling.PhaseMeanRoute

/-!
# Direct ambient-Gaussian rejection for Gaussian cooling phases

An elementary proposal is a draw from the normalized spherical Gaussian on the ambient
Euclidean space.  It is accepted exactly when the membership query `x in K` succeeds.
Conditioning this proposal law on acceptance is the exact phase-zero cooling law.

The Chernoff cold-end certificate bounds the acceptance probability below by `1 - epsilon`.
The explicit i.i.d. trajectory and round-count construction in `RejectionRounds` then gives
almost-sure termination and expected membership-query count at most `(1 - epsilon)⁻¹`.

The final section supplies the generic output-law lemma missing from `RejectionRounds`:
the first accepted draw pushes the i.i.d. trajectory law forward to `condOn`.
-/

namespace Ttc.CV

open MeasureTheory Metric Set
open Arlib Arlib.GaussianCooling Arlib.MarkovChains
open scoped ENNReal

variable {n : Nat}

/-- The unnormalized spherical ambient Gaussian with variance `s`. -/
noncomputable def ambientGaussianMeasure (s : Real) : Measure (Space n) :=
  (volume : Measure (Space n)).withDensity (gaussianWeight s)

/-- The ambient Gaussian probability law.  Normalization is implemented as conditioning
the finite positive Gaussian measure on `univ`; it contains no reference to `K`. -/
noncomputable def ambientGaussianProb (s : Real) : Measure (Space n) :=
  uniformOn (ambientGaussianMeasure (n := n) s) Set.univ

/-- The unnormalized ambient Gaussian has the standard explicit total mass. -/
theorem ambientGaussianMeasure_univ {s : Real} (hs : 0 < s) :
    ambientGaussianMeasure (n := n) s Set.univ =
      ENNReal.ofReal ((2 * Real.pi * s) ^ ((n : Real) / 2)) := by
  simp only [ambientGaussianMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact lintegral_gaussianWeight_univ hs

theorem ambientGaussianMeasure_univ_ne_zero {s : Real} (hs : 0 < s) :
    ambientGaussianMeasure (n := n) s Set.univ ≠ 0 := by
  rw [ambientGaussianMeasure_univ hs]
  exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)

theorem ambientGaussianMeasure_univ_ne_top {s : Real} (hs : 0 < s) :
    ambientGaussianMeasure (n := n) s Set.univ ≠ ⊤ := by
  rw [ambientGaussianMeasure_univ hs]
  exact ENNReal.ofReal_ne_top

/-- The proposal is genuinely a probability measure. -/
theorem isProbabilityMeasure_ambientGaussianProb {s : Real} (hs : 0 < s) :
    IsProbabilityMeasure (ambientGaussianProb (n := n) s) := by
  unfold ambientGaussianProb
  exact isProbabilityMeasure_uniformOn _
    (ambientGaussianMeasure_univ_ne_zero hs) (ambientGaussianMeasure_univ_ne_top hs)

/-- **Exact phase-zero law.** Rejecting ambient Gaussian proposals until `x in K` produces
the same conditional measure as `coolLaw m sigmaSq K 0`.

The proposal itself is independent of `K`; the only acceptance test is set membership. -/
theorem condOn_ambientGaussianProb_eq_coolLaw_zero
    {m : Nat} {sigmaSq : Nat -> Real} (hm : 0 < m)
    (hsigma : forall j, 0 < sigmaSq j) {K : Set (Space n)}
    (hKm : MeasurableSet K) (hball : ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) :
    condOn (ambientGaussianProb (n := n) (sigmaSq 0)) K = coolLaw m sigmaSq K 0 := by
  rw [ambientGaussianProb,
    Arlib.PointwiseRoute.condOn_uniformOn_eq_uniformOn
      (ambientGaussianMeasure (n := n) (sigmaSq 0)) hKm (subset_univ K)
      (ambientGaussianMeasure_univ_ne_zero (hsigma 0))
      (ambientGaussianMeasure_univ_ne_top (hsigma 0))]
  change uniformOn
      ((volume : Measure (Space n)).withDensity (gaussianWeight (sigmaSq 0))) K =
    coolLaw m sigmaSq K 0
  exact (coolLaw_eq_uniformOn_gaussianWeight hsigma hKm hball hfin hm).symm

/-- **Exact law at an arbitrary Gaussian phase.**  Conditioning an ambient spherical
Gaussian of variance `sigmaSq i` on the membership event `K` is the phase-`i` cooling law. -/
theorem condOn_ambientGaussianProb_eq_coolLaw
    {m : Nat} {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (Space n)} (hKm : MeasurableSet K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m) :
    condOn (ambientGaussianProb (n := n) (sigmaSq i)) K = coolLaw m sigmaSq K i := by
  rw [ambientGaussianProb,
    Arlib.PointwiseRoute.condOn_uniformOn_eq_uniformOn
      (ambientGaussianMeasure (n := n) (sigmaSq i)) hKm (subset_univ K)
      (ambientGaussianMeasure_univ_ne_zero (hsigma i))
      (ambientGaussianMeasure_univ_ne_top (hsigma i))]
  change uniformOn
      ((volume : Measure (Space n)).withDensity (gaussianWeight (sigmaSq i))) K =
    coolLaw m sigmaSq K i
  exact (coolLaw_eq_uniformOn_gaussianWeight hsigma hKm hball hfin hi).symm

/-- The ambient Gaussian mass of `K` is the Gaussian-cooling integral `G`. -/
theorem ambientGaussianMeasure_apply_eq_G {K : Set (Space n)}
    (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤) {s : Real} (hs : 0 < s) :
    ambientGaussianMeasure (n := n) s K =
      ENNReal.ofReal (G (indicator K (1 : Space n -> Real)) s) := by
  have h := withDensity_gaussianWeight_eq_ofReal_setIntegral
    (n := n) hs hKm hfin (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Space n)))
  rw [Set.univ_inter, setIntegral_univ] at h
  rw [G_indicator_eq K hKm]
  simpa [ambientGaussianMeasure, gaussianWeightReal, integral_indicator hKm] using h

/-- **Chernoff acceptance bound.** Under the cold-end certificate, one ambient Gaussian
proposal passes the membership query with probability at least `1 - epsilon`. -/
theorem ambientGaussianProb_acceptance_ge_of_chernoff
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    {s rho t epsilon : Real} (hs : 0 < s) (hrho : 0 <= rho)
    (ht0 : 0 < t) (ht1 : t < 1) (hepsilon0 : 0 <= epsilon)
    (hepsilon1 : epsilon < 1)
    (hballrho : closedBall (0 : Space n) rho ⊆ K)
    (hcert : Real.exp (-(t * rho ^ 2) / (2 * s)) *
        (2 * Real.pi * (s / (1 - t))) ^ ((n : Real) / 2) <=
      epsilon * (2 * Real.pi * s) ^ ((n : Real) / 2)) :
    ENNReal.ofReal (1 - epsilon) <= ambientGaussianProb (n := n) s K := by
  have hrel := G_indicator_mem_relErr_ambient_of_chernoff hKm hs hrho ht0 ht1
    hepsilon0 hballrho hcert
  have hZpos : 0 < (2 * Real.pi * s) ^ ((n : Real) / 2) := by positivity
  have hZ0 : ENNReal.ofReal ((2 * Real.pi * s) ^ ((n : Real) / 2)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hZpos
  have hZtop : ENNReal.ofReal ((2 * Real.pi * s) ^ ((n : Real) / 2)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  rw [ambientGaussianProb, uniformOn_apply _ MeasurableSet.univ hKm,
    Set.inter_univ, ambientGaussianMeasure_apply_eq_G hKm hfin hs,
    ambientGaussianMeasure_univ hs,
    ENNReal.le_div_iff_mul_le (Or.inl hZ0) (Or.inl hZtop)]
  rw [← ENNReal.ofReal_mul (by linarith : 0 <= 1 - epsilon)]
  exact ENNReal.ofReal_le_ofReal hrel.1

/-- **Constant cold-regime acceptance.**  If `K` contains the unit ball and
`4 * n * s <= 1`, at least half of the ambient Gaussian proposals are accepted. -/
theorem ambientGaussianProb_acceptance_ge_half
    {K : Set (Space n)} (hKm : MeasurableSet K) (hn : 1 ≤ n)
    {s : Real} (hs : 0 < s) (hcold : 4 * (n : Real) * s ≤ 1)
    (hball : closedBall (0 : Space n) 1 ⊆ K) :
    ENNReal.ofReal (1 / 2 : Real) ≤ ambientGaussianProb (n := n) s K := by
  have hhalf := Arlib.GaussianCooling.half_lintegral_gaussianWeight_univ_le_closedBall
    (n := n) hn hs (by norm_num : (0 : Real) < 1)
    (by simpa using hcold)
  have hmass : ENNReal.ofReal (1 / 2 : Real) * ambientGaussianMeasure (n := n) s Set.univ ≤
      ambientGaussianMeasure (n := n) s K := by
    calc
      ENNReal.ofReal (1 / 2 : Real) * ambientGaussianMeasure (n := n) s Set.univ ≤
          ambientGaussianMeasure (n := n) s (closedBall (0 : Space n) 1) := by
        simpa [ambientGaussianMeasure, withDensity_apply _ MeasurableSet.univ,
          withDensity_apply _ measurableSet_closedBall] using hhalf
      _ ≤ ambientGaussianMeasure (n := n) s K := measure_mono hball
  rw [ambientGaussianProb, uniformOn_apply _ MeasurableSet.univ hKm,
    Set.inter_univ,
    ENNReal.le_div_iff_mul_le
      (Or.inl (ambientGaussianMeasure_univ_ne_zero hs))
      (Or.inl (ambientGaussianMeasure_univ_ne_top hs))]
  exact hmass

/-- The operational rejection loop terminates almost surely.  Each round makes one draw and
accepts precisely on the membership event `K`. -/
theorem ambientGaussian_rejection_terminates_ae
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    {s rho t epsilon : Real} (hs : 0 < s) (hrho : 0 <= rho)
    (ht0 : 0 < t) (ht1 : t < 1) (hepsilon0 : 0 <= epsilon)
    (hepsilon1 : epsilon < 1)
    (hballrho : closedBall (0 : Space n) rho ⊆ K)
    (hcert : Real.exp (-(t * rho ^ 2) / (2 * s)) *
        (2 * Real.pi * (s / (1 - t))) ^ ((n : Real) / 2) <=
      epsilon * (2 * Real.pi * s) ^ ((n : Real) / 2)) :
    Arlib.Probability.roundsMeasure (ambientGaussianProb (n := n) s)
      (Arlib.Probability.neverAccepts K) = 0 := by
  let proposal := ambientGaussianProb (n := n) s
  letI : IsProbabilityMeasure proposal := isProbabilityMeasure_ambientGaussianProb hs
  have hacc := ambientGaussianProb_acceptance_ge_of_chernoff hKm hfin hs hrho ht0 ht1
    hepsilon0 hepsilon1 hballrho hcert
  have hpos : 0 < proposal K :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by linarith : 0 < 1 - epsilon)) hacc
  exact Arlib.Probability.measure_neverAccepts proposal hKm hpos

/-- **Expected membership-query cost.** The number of ambient proposals (equivalently,
membership tests) before acceptance has expectation at most `(1 - epsilon)^{-1}`. -/
theorem expected_ambientGaussian_rejection_rounds_le
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    {s rho t epsilon : Real} (hs : 0 < s) (hrho : 0 <= rho)
    (ht0 : 0 < t) (ht1 : t < 1) (hepsilon0 : 0 <= epsilon)
    (hepsilon1 : epsilon < 1)
    (hballrho : closedBall (0 : Space n) rho ⊆ K)
    (hcert : Real.exp (-(t * rho ^ 2) / (2 * s)) *
        (2 * Real.pi * (s / (1 - t))) ^ ((n : Real) / 2) <=
      epsilon * (2 * Real.pi * s) ^ ((n : Real) / 2)) :
    (∫ omega, (Arlib.Probability.roundCountNat K omega : Real)
      ∂(Arlib.Probability.roundsMeasure (ambientGaussianProb (n := n) s))) <=
        (1 - epsilon) ^ (-1 : Int) := by
  let proposal := ambientGaussianProb (n := n) s
  letI : IsProbabilityMeasure proposal := isProbabilityMeasure_ambientGaussianProb hs
  have hacc := ambientGaussianProb_acceptance_ge_of_chernoff hKm hfin hs hrho ht0 ht1
    hepsilon0 hepsilon1 hballrho hcert
  have hround := Arlib.Probability.integral_roundCountNat_le proposal hKm
    (by linarith : 0 < 1 - epsilon) (by linarith : 1 - epsilon <= 1) hacc
  simpa [proposal, zpow_neg_one] using hround

open Arlib.Probability

/-- In the cold regime, direct ambient-Gaussian rejection terminates almost surely. -/
theorem ambientGaussian_rejection_terminates_ae_of_cold
    {K : Set (Space n)} (hKm : MeasurableSet K) (hn : 1 ≤ n)
    {s : Real} (hs : 0 < s) (hcold : 4 * (n : Real) * s ≤ 1)
    (hball : closedBall (0 : Space n) 1 ⊆ K) :
    roundsMeasure (ambientGaussianProb (n := n) s) (neverAccepts K) = 0 := by
  let proposal := ambientGaussianProb (n := n) s
  letI : IsProbabilityMeasure proposal := isProbabilityMeasure_ambientGaussianProb hs
  have hacc := ambientGaussianProb_acceptance_ge_half hKm hn hs hcold hball
  have hpos : 0 < proposal K :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num : (0 : Real) < 1 / 2)) hacc
  exact measure_neverAccepts proposal hKm hpos

/-- **Constant expected query cost in the cold regime.**  With acceptance at least `1/2`,
the expected number of draws, and hence membership tests, is at most `2`. -/
theorem expected_ambientGaussian_rejection_rounds_le_two
    {K : Set (Space n)} (hKm : MeasurableSet K) (hn : 1 ≤ n)
    {s : Real} (hs : 0 < s) (hcold : 4 * (n : Real) * s ≤ 1)
    (hball : closedBall (0 : Space n) 1 ⊆ K) :
    (∫ omega, (roundCountNat K omega : Real)
      ∂(roundsMeasure (ambientGaussianProb (n := n) s))) ≤ 2 := by
  let proposal := ambientGaussianProb (n := n) s
  letI : IsProbabilityMeasure proposal := isProbabilityMeasure_ambientGaussianProb hs
  have hacc := ambientGaussianProb_acceptance_ge_half hKm hn hs hcold hball
  have hround := integral_roundCountNat_le proposal hKm
    (by norm_num : (0 : Real) < 1 / 2) (by norm_num : (1 / 2 : Real) ≤ 1) hacc
  norm_num at hround ⊢
  simpa [proposal] using hround

/-! ## The output law of generic rejection sampling -/

variable {E : Type*} [MeasurableSpace E]

/-- The candidate at the first accepted index.  On the null event that no candidate is ever
accepted, `Nat.sInf empty = 0`, so this returns the zeroth candidate as an irrelevant default. -/
noncomputable def firstAcceptedDraw (A : Set E) (omega : RoundSpace E) : E :=
  omega (roundCountNat A omega - 1)

omit [MeasurableSpace E] in
theorem firstAcceptedDraw_preimage (A B : Set E) :
    firstAcceptedDraw A ⁻¹' B =
      ⋃ k : Nat, {omega | roundCountNat A omega - 1 = k} ∩ draw k ⁻¹' B := by
  ext omega
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq,
    draw_apply, firstAcceptedDraw]
  exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨k, hk, hB⟩ => hk ▸ hB⟩

/-- Selecting a coordinate using the measurable first-acceptance index remains measurable. -/
theorem measurable_firstAcceptedDraw {A : Set E} (hA : MeasurableSet A) :
    Measurable (firstAcceptedDraw A) := by
  intro B hB
  rw [firstAcceptedDraw_preimage]
  refine MeasurableSet.iUnion fun k => ?_
  have hsub : Measurable (fun l : Nat => l - 1) := Measurable.of_discrete
  exact ((hsub.comp (measurable_roundCountNat hA)) (measurableSet_singleton k)).inter
    ((measurable_draw k) hB)

/-- Exactly `k` rejected proposals followed by an accepted proposal lying in `B`. -/
def firstAcceptsIn (A B : Set E) (k : Nat) : Set (RoundSpace E) :=
  survives A k ∩ draw k ⁻¹' (A ∩ B)

theorem measurableSet_firstAcceptsIn {A B : Set E} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (k : Nat) : MeasurableSet (firstAcceptsIn A B k) :=
  (measurableSet_survives hA k).inter ((measurable_draw k) (hA.inter hB))

omit [MeasurableSpace E] in
theorem firstAcceptsIn_eq_pi (A B : Set E) (k : Nat) :
    firstAcceptsIn A B k = Set.pi (↑(Finset.range (k + 1)))
      (fun i => if i < k then Aᶜ else A ∩ B) := by
  ext omega
  simp only [firstAcceptsIn, Set.mem_inter_iff, survives, Set.mem_setOf_eq,
    Set.mem_preimage, draw_apply, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · rintro ⟨hbefore, hat⟩ i hi
    split_ifs with hik
    · exact hbefore i hik
    · have : i = k := by omega
      simpa [this] using hat
  · intro h
    constructor
    · intro i hi
      simpa [hi] using h i (by omega)
    · simpa using h k (by omega)

/-- The exact geometric-cylinder mass of `k` rejections followed by acceptance in `B`. -/
theorem roundsMeasure_firstAcceptsIn (nu : Measure E) [IsProbabilityMeasure nu]
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) (k : Nat) :
    roundsMeasure nu (firstAcceptsIn A B k) = nu Aᶜ ^ k * nu (A ∩ B) := by
  rw [firstAcceptsIn_eq_pi, roundsMeasure,
    Measure.infinitePi_pi _ (fun i _ => by
      split_ifs
      · exact hA.compl
      · exact hA.inter hB)]
  rw [Finset.prod_range_succ]
  congr 1
  · calc
      ∏ i ∈ Finset.range k, nu (if i < k then Aᶜ else A ∩ B) =
          ∏ _i ∈ Finset.range k, nu Aᶜ := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [Finset.mem_range.mp hi]
      _ = nu Aᶜ ^ k := by simp
  · simp

omit [MeasurableSpace E] in
theorem pairwise_disjoint_firstAcceptsIn (A B : Set E) :
    Pairwise (Function.onFun Disjoint (firstAcceptsIn A B)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro omega hi hj
  rcases hi with ⟨hiBefore, hiAt⟩
  rcases hj with ⟨hjBefore, hjAt⟩
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hjBefore i hijlt hiAt.1
  · exact hiBefore j hjilt hjAt.1

omit [MeasurableSpace E] in
/-- The first-hit cylinders exhaust exactly the terminating trajectories whose selected
candidate lies in `B`. -/
theorem iUnion_firstAcceptsIn (A B : Set E) :
    (⋃ k : Nat, firstAcceptsIn A B k) =
      (neverAccepts A)ᶜ ∩ firstAcceptedDraw A ⁻¹' B := by
  ext omega
  constructor
  · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage]
    rintro ⟨k, hbefore, hat⟩
    have hne : {j | omega j ∈ A}.Nonempty := ⟨k, hat.1⟩
    have hsInf : sInf {j | omega j ∈ A} = k := by
      apply le_antisymm (Nat.sInf_le hat.1)
      by_contra hlt
      exact hbefore _ (not_le.mp hlt) (Nat.sInf_mem hne)
    constructor
    · intro hnever
      exact hnever k hat.1
    · simpa [firstAcceptedDraw, roundCountNat, hsInf] using hat.2
  · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage]
    rintro ⟨hterminates, hout⟩
    have hne : {j | omega j ∈ A}.Nonempty := by
      by_contra hempty
      apply hterminates
      intro j hj
      apply hempty
      exact ⟨j, hj⟩
    let k := sInf {j | omega j ∈ A}
    have hmem : omega k ∈ A := Nat.sInf_mem hne
    refine ⟨k, ?_, hmem, ?_⟩
    · intro j hj
      exact Nat.notMem_of_lt_sInf hj
    · simpa [firstAcceptedDraw, roundCountNat, k] using hout

/-- The terminating first-hit event has the conditional numerator divided by the
acceptance probability. -/
theorem roundsMeasure_iUnion_firstAcceptsIn (nu : Measure E) [IsProbabilityMeasure nu]
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    roundsMeasure nu (⋃ k : Nat, firstAcceptsIn A B k) = nu (A ∩ B) / nu A := by
  rw [measure_iUnion (pairwise_disjoint_firstAcceptsIn A B)
      (measurableSet_firstAcceptsIn hA hB)]
  simp_rw [roundsMeasure_firstAcceptsIn nu hA hB]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    prob_compl_eq_one_sub hA,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one,
    ENNReal.div_eq_inv_mul]

/-- **Generic rejection-sampling law.**  Under positive acceptance probability, selecting
the first accepted candidate pushes the explicit i.i.d. trajectory law to `condOn nu A`. -/
theorem map_firstAcceptedDraw_eq_condOn (nu : Measure E) [IsProbabilityMeasure nu]
    {A : Set E} (hA : MeasurableSet A) (hpos : 0 < nu A) :
    Measure.map (firstAcceptedDraw A) (roundsMeasure nu) = condOn nu A := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_firstAcceptedDraw hA) hB,
    ← measure_sdiff_null (s := firstAcceptedDraw A ⁻¹' B)
      (measure_neverAccepts nu hA hpos)]
  have hset : firstAcceptedDraw A ⁻¹' B \ neverAccepts A =
      ⋃ k : Nat, firstAcceptsIn A B k := by
    rw [iUnion_firstAcceptsIn]
    ext omega
    simp [and_comm]
  rw [hset, roundsMeasure_iUnion_firstAcceptsIn nu hA hB,
    condOn_apply nu hA hB, Set.inter_comm]

/-- Operational ambient-Gaussian rejection at an arbitrary phase has the exact cooling
law, provided the membership event has positive proposal probability. -/
theorem map_firstAcceptedDraw_ambientGaussian_eq_coolLaw
    {m : Nat} {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (Space n)} (hKm : MeasurableSet K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m)
    (hpos : 0 < ambientGaussianProb (n := n) (sigmaSq i) K) :
    Measure.map (firstAcceptedDraw K)
        (roundsMeasure (ambientGaussianProb (n := n) (sigmaSq i))) =
      coolLaw m sigmaSq K i := by
  let proposal := ambientGaussianProb (n := n) (sigmaSq i)
  letI : IsProbabilityMeasure proposal := isProbabilityMeasure_ambientGaussianProb (hsigma i)
  rw [map_firstAcceptedDraw_eq_condOn proposal hKm hpos,
    condOn_ambientGaussianProb_eq_coolLaw hsigma hKm hball hfin hi]

/-- **Cold phase capstone.**  At every phase satisfying `4 * n * sigmaSq i <= 1`,
ambient Gaussian proposals plus membership rejection terminate almost surely and their
first accepted output has exactly `coolLaw m sigmaSq K i`. -/
theorem map_firstAcceptedDraw_ambientGaussian_eq_coolLaw_of_cold
    {m : Nat} {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 ≤ n) (hball : closedBall (0 : Space n) 1 ⊆ K)
    {i : Nat} (hi : i < m) (hcold : 4 * (n : Real) * sigmaSq i ≤ 1) :
    Measure.map (firstAcceptedDraw K)
        (roundsMeasure (ambientGaussianProb (n := n) (sigmaSq i))) =
      coolLaw m sigmaSq K i := by
  have hacc := ambientGaussianProb_acceptance_ge_half hKm hn (hsigma i) hcold hball
  have hpos : 0 < ambientGaussianProb (n := n) (sigmaSq i) K :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num : (0 : Real) < 1 / 2)) hacc
  exact map_firstAcceptedDraw_ambientGaussian_eq_coolLaw hsigma hKm
    ((ball_subset_closedBall.trans hball)) hfin hi hpos

/-- The cold phase's exact sampler uses at most two expected membership queries. -/
theorem expected_ambientGaussian_phase_rejection_rounds_le_two
    {m : Nat} {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hn : 1 ≤ n)
    (hball : closedBall (0 : Space n) 1 ⊆ K)
    {i : Nat} (_hi : i < m) (hcold : 4 * (n : Real) * sigmaSq i ≤ 1) :
    (∫ omega, (roundCountNat K omega : Real)
      ∂(roundsMeasure (ambientGaussianProb (n := n) (sigmaSq i)))) ≤ 2 :=
  expected_ambientGaussian_rejection_rounds_le_two hKm hn (hsigma i) hcold hball

/-! ### Axiom audit -/

#print axioms ambientGaussianMeasure_univ
#print axioms isProbabilityMeasure_ambientGaussianProb
#print axioms condOn_ambientGaussianProb_eq_coolLaw_zero
#print axioms condOn_ambientGaussianProb_eq_coolLaw
#print axioms ambientGaussianProb_acceptance_ge_of_chernoff
#print axioms ambientGaussianProb_acceptance_ge_half
#print axioms ambientGaussian_rejection_terminates_ae
#print axioms expected_ambientGaussian_rejection_rounds_le
#print axioms ambientGaussian_rejection_terminates_ae_of_cold
#print axioms expected_ambientGaussian_rejection_rounds_le_two
#print axioms map_firstAcceptedDraw_eq_condOn
#print axioms map_firstAcceptedDraw_ambientGaussian_eq_coolLaw_of_cold
#print axioms expected_ambientGaussian_phase_rejection_rounds_le_two

end Ttc.CV

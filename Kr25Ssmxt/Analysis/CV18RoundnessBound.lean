import Kr25Ssmxt.Analysis.CV18NormalizedPolytope
import Kr25Ssmxt.Model.Run

/-! A geometric bound on the concrete CV18 roundness parameter. -/

namespace Kr25Ssmxt

open MeasureTheory

/-- The exact cap of the amplified CV18 implementation is bounded by its
published scheduled complexity rate and confidence multiplier. -/
theorem CommunityCV18.queryBudget_cast_le_scheduled_rate
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams) :
    (CommunityCV18.queryBudget q : Real) ≤
      (8 * ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p) + 1) *
        (64 * ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant *
          ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate q + 1) := by
  let A := 8 * ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p)
  let B := 64 * ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant *
    ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate q
  have hA : 0 ≤ A := by
    have hlog : (1 : Real) ≤
        ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p) := by
      unfold ArlibCommunity.Algorithms.CV18.protectedLog
      exact le_max_left _ _
    dsimp [A]
    linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity [ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant_pos,
      ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate_pos q]
  have hceilA :
      (ArlibCommunity.Algorithms.CV18.confidenceRepetitions q : Real) ≤ A + 1 := by
    exact (Nat.ceil_lt_add_one hA).le
  have hceilB :
      (ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledQueryBudget q : Real) ≤
        B + 1 := by
    exact (Nat.ceil_lt_add_one hB).le
  change (ArlibCommunity.Algorithms.CV18.confidenceRepetitions q *
      ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledQueryBudget q : Nat) ≤
    (A + 1) * (B + 1)
  push_cast
  exact mul_le_mul hceilA hceilB (Nat.cast_nonneg _) (by positivity)

/-- Remove CV18's only nonsuppressed geometric parameter from its base rate. -/
theorem CommunityCV18.base_rate_le_rho_log_product
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams)
    (rho : Real) (hrho : 1 ≤ rho)
    (hround : q.roundness ≤ 4 * rho ^ 2 + 1) :
    ArlibCommunity.Algorithms.CV18.volumeBaseComplexityRate q ≤
      (5 * rho ^ 2 * (q.n : Real) ^ 3 / q.eps ^ 2) *
        ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.eps) ^ 2 *
        ArlibCommunity.Algorithms.CV18.protectedLog ((q.n : Real) / q.eps) ^ 2 *
        ArlibCommunity.Algorithms.CV18.protectedLog
          (ArlibCommunity.Algorithms.CV18.volumeTerminalScale q) ^ 2 := by
  have hmax : max 1 q.roundness ≤ 5 * rho ^ 2 := by
    apply max_le
    · nlinarith [sq_nonneg rho]
    · nlinarith [sq_nonneg rho]
  unfold ArlibCommunity.Algorithms.CV18.volumeBaseComplexityRate
  gcongr

theorem CommunityCV18.queryBudget_cast_le_scheduled_rate_no_ceiling
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams) :
    (CommunityCV18.queryBudget q : Real) ≤
      9 * (64 * ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
        + 1) *
      ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p) *
      ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate q := by
  let L := ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p)
  let S := ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate q
  let C := ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
  have hL : 1 ≤ L := by
    unfold L ArlibCommunity.Algorithms.CV18.protectedLog
    exact le_max_left _ _
  have hS : 1 ≤ S := ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate_one_le q
  have hC : 0 ≤ C :=
    (ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant_pos).le
  have hA : 8 * L + 1 ≤ 9 * L := by linarith
  have hB : 64 * C * S + 1 ≤ (64 * C + 1) * S := by
    nlinarith [mul_nonneg (show 0 ≤ 64 * C by positivity)
      (sub_nonneg.mpr hS)]
  have hbound := CommunityCV18.queryBudget_cast_le_scheduled_rate q
  change (CommunityCV18.queryBudget q : Real) ≤
    (8 * L + 1) * (64 * C * S + 1) at hbound
  calc
    _ ≤ (8 * L + 1) * (64 * C * S + 1) := hbound
    _ ≤ (9 * L) * ((64 * C + 1) * S) := by
      apply mul_le_mul hA hB
      · positivity
      · positivity
    _ = _ := by ring

theorem TTCRuntime.theorem3CV18LogEnvelope_nonneg
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams) :
    0 ≤ TTCRuntime.theorem3CV18LogEnvelope q := by
  have hlog (x : Real) :
      0 ≤ ArlibCommunity.Algorithms.CV18.protectedLog x := by
    unfold ArlibCommunity.Algorithms.CV18.protectedLog
    exact le_trans (by norm_num : (0 : Real) ≤ 1) (le_max_left _ _)
  have hacc : 0 ≤ ArlibCommunity.Algorithms.CV18.figureOneScheduledAccuracyLog q :=
    (zero_le_one.trans
      (ArlibCommunity.Algorithms.CV18.figureOneScheduledAccuracyLog_one_le q))
  have h1 := hlog (1 / q.p)
  have h2 := hlog (1 / q.eps)
  have h3 := hlog ((q.n : Real) / q.eps)
  have h4 := hlog (ArlibCommunity.Algorithms.CV18.volumeTerminalScale q)
  have h5 := hlog
    (1 / ArlibCommunity.Algorithms.CV18.figureOneCorrectedBlockMixingError q
      (ArlibCommunity.Algorithms.CV18.figureOneSafeRetryCount q - 1))
  unfold TTCRuntime.theorem3CV18LogEnvelope
  positivity

theorem CommunityCV18.queryBudget_cast_le_rho_polylog
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams)
    (rho : Real) (hrho : 1 ≤ rho)
    (hround : q.roundness ≤ 4 * rho ^ 2 + 1) :
    (CommunityCV18.queryBudget q : Real) ≤
      45 * (64 *
        ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
        + 1) *
        (q.n : Real) ^ 3 * rho ^ 2 / q.eps ^ 2 *
        TTCRuntime.theorem3CV18LogEnvelope q := by
  let C := ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
  let L := ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p)
  let S := ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate q
  let B := ArlibCommunity.Algorithms.CV18.volumeBaseComplexityRate q
  have hbase := CommunityCV18.base_rate_le_rho_log_product q rho hrho hround
  have hacc0 : 0 ≤ ArlibCommunity.Algorithms.CV18.figureOneScheduledAccuracyLog q :=
    (zero_le_one.trans
      (ArlibCommunity.Algorithms.CV18.figureOneScheduledAccuracyLog_one_le q))
  have hS : S ≤
      (5 * rho ^ 2 * (q.n : Real) ^ 3 / q.eps ^ 2) *
      ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.eps) ^ 2 *
      ArlibCommunity.Algorithms.CV18.protectedLog ((q.n : Real) / q.eps) ^ 2 *
      ArlibCommunity.Algorithms.CV18.protectedLog
        (ArlibCommunity.Algorithms.CV18.volumeTerminalScale q) ^ 2 *
      ArlibCommunity.Algorithms.CV18.figureOneScheduledAccuracyLog q *
      ArlibCommunity.Algorithms.CV18.protectedLog
        (1 / ArlibCommunity.Algorithms.CV18.figureOneCorrectedBlockMixingError q
          (ArlibCommunity.Algorithms.CV18.figureOneSafeRetryCount q - 1)) ^ 2 := by
    dsimp [S, ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate]
    gcongr
  have hL0 : 0 ≤ L := by
    dsimp [L, ArlibCommunity.Algorithms.CV18.protectedLog]
    exact le_trans (by norm_num : (0 : Real) ≤ 1) (le_max_left _ _)
  have hC0 : 0 ≤ C :=
    (ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant_pos).le
  have hprefix : 0 ≤ 9 * (64 * C + 1) * L := by positivity
  have hquery := CommunityCV18.queryBudget_cast_le_scheduled_rate_no_ceiling q
  calc
    _ ≤ 9 * (64 * C + 1) * L * S := hquery
    _ ≤ 9 * (64 * C + 1) * L *
      ((5 * rho ^ 2 * (q.n : Real) ^ 3 / q.eps ^ 2) *
      ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.eps) ^ 2 *
      ArlibCommunity.Algorithms.CV18.protectedLog ((q.n : Real) / q.eps) ^ 2 *
      ArlibCommunity.Algorithms.CV18.protectedLog
        (ArlibCommunity.Algorithms.CV18.volumeTerminalScale q) ^ 2 *
      ArlibCommunity.Algorithms.CV18.figureOneScheduledAccuracyLog q *
      ArlibCommunity.Algorithms.CV18.protectedLog
        (1 / ArlibCommunity.Algorithms.CV18.figureOneCorrectedBlockMixingError q
          (ArlibCommunity.Algorithms.CV18.figureOneSafeRetryCount q - 1)) ^ 2) := by
        gcongr
    _ = _ := by
      unfold TTCRuntime.theorem3CV18LogEnvelope
      dsimp [C, L]
      ring

theorem PolytopeData.communityCV18_roundness_le_outer_sq {n : Nat}
    (P : PolytopeData n) :
    CommunityCV18.roundness P ≤ P.cv18OuterRadius ^ 2 + 1 := by
  have hR : 0 ≤ P.cv18OuterRadius := P.cv18OuterRadius_nonneg
  have hbound :
      ‖∫ x in P.cv18Body, ‖x‖ ^ 2‖ ≤
        P.cv18OuterRadius ^ 2 * (volume P.cv18Body).toReal := by
    apply norm_setIntegral_le_of_norm_le_const
      (P.volume_cv18Body_ne_top.lt_top)
    intro x hx
    have hxR : ‖x‖ ≤ P.cv18OuterRadius := by
      have := P.cv18Body_subset_outerBall hx
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hsq : ‖x‖ ^ 2 ≤ P.cv18OuterRadius ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR).2 hxR
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg x)] using hsq
  unfold CommunityCV18.roundness
  have hvol : 0 ≤ (volume P.cv18Body).toReal := ENNReal.toReal_nonneg
  by_cases hz : (volume P.cv18Body).toReal = 0
  · have hint : (∫ x in P.cv18Body, ‖x‖ ^ 2) = 0 := by
      have hzero : ‖∫ x in P.cv18Body, ‖x‖ ^ 2‖ = 0 := by
        have h := hbound
        rw [hz, mul_zero] at h
        exact le_antisymm h (norm_nonneg _)
      exact norm_eq_zero.mp hzero
    simp [hz, hint]
    positivity
  · have hvolpos : 0 < (volume P.cv18Body).toReal := lt_of_le_of_ne hvol (Ne.symm hz)
    have hdiv :
        |(∫ x in P.cv18Body, ‖x‖ ^ 2) / (volume P.cv18Body).toReal| ≤
          P.cv18OuterRadius ^ 2 := by
      rw [abs_div, abs_of_pos hvolpos]
      exact (div_le_iff₀ hvolpos).2 (by
        simpa [Real.norm_eq_abs] using hbound)
    linarith

theorem PolytopeData.cv18OuterRadius_le_two_ratio {n : Nat}
    (P : PolytopeData n) :
    P.cv18OuterRadius ≤ 2 * max 1 (P.outerRadius / P.inradius) := by
  have hcenter : ‖toEuclidean P.incenter‖ ≤ P.outerRadius := by
    have hmem : P.incenter ∈ P.carrier :=
      P.inball (by simp [Metric.mem_closedBall, P.inradius_pos.le])
    simpa only [toEuclidean] using P.outer_bound P.incenter hmem
  have hratio : (P.outerRadius + ‖toEuclidean P.incenter‖) /
      P.inradius ≤ 2 * (P.outerRadius / P.inradius) := by
    calc
      (P.outerRadius + ‖toEuclidean P.incenter‖) / P.inradius ≤
          (2 * P.outerRadius) / P.inradius :=
        (div_le_div_iff_of_pos_right P.inradius_pos).2 (by linarith)
      _ = 2 * (P.outerRadius / P.inradius) := by ring
  unfold PolytopeData.cv18OuterRadius
  apply max_le
  · have h : (1 : Real) ≤ max 1 (P.outerRadius / P.inradius) :=
      le_max_left _ _
    linarith
  · exact hratio.trans (by
      gcongr
      exact le_max_right _ _)

theorem PolytopeData.communityCV18_roundness_le_ratio {n : Nat}
    (P : PolytopeData n) :
    CommunityCV18.roundness P ≤
      4 * (max 1 (P.outerRadius / P.inradius)) ^ 2 + 1 := by
  have hR := P.communityCV18_roundness_le_outer_sq
  have houter := P.cv18OuterRadius_le_two_ratio
  have hnonneg : 0 ≤ P.cv18OuterRadius := P.cv18OuterRadius_nonneg
  have hmax : 0 ≤ max 1 (P.outerRadius / P.inradius) :=
    le_trans (by norm_num : (0 : Real) ≤ 1) (le_max_left _ _)
  nlinarith [sq_le_sq₀ hnonneg (by positivity : 0 ≤ 2 * max 1
    (P.outerRadius / P.inradius)) |>.2 houter]

theorem Decomposition.communityCV18_roundness_le_rho {n k : Nat}
    {F : LRAFormula n k} (D : Decomposition F)
    (i : Fin D.componentCount) :
    CommunityCV18.roundness (D.component i) ≤
      4 * (TTCRuntime.theorem3Rho D) ^ 2 + 1 := by
  let P := D.component i
  have hratio0 : 0 ≤ P.outerRadius / P.inradius :=
    div_nonneg P.outerRadius_nonneg P.inradius_pos.le
  have hsup : P.outerRadius / P.inradius ≤
      TTCRuntime.theorem3Rho D := by
    have hle : Real.toNNReal (P.outerRadius / P.inradius) ≤
        (Finset.univ.sup fun j : Fin D.componentCount =>
          Real.toNNReal ((D.component j).outerRadius / (D.component j).inradius) :
            NNReal) := Finset.le_sup (f := fun j : Fin D.componentCount =>
              Real.toNNReal ((D.component j).outerRadius / (D.component j).inradius))
              (Finset.mem_univ i)
    have hleR : (P.outerRadius / P.inradius : Real) ≤
        ((Finset.univ.sup fun j : Fin D.componentCount =>
          Real.toNNReal ((D.component j).outerRadius / (D.component j).inradius) :
            NNReal) : Real) := by
      calc
        P.outerRadius / P.inradius =
            (Real.toNNReal (P.outerRadius / P.inradius) : Real) :=
          (Real.coe_toNNReal _ hratio0).symm
        _ ≤ _ := by exact_mod_cast hle
    exact hleR.trans (le_max_right _ _)
  have hmax : max 1 (P.outerRadius / P.inradius) ≤
      TTCRuntime.theorem3Rho D :=
    max_le (le_max_left _ _) hsup
  have hbase := P.communityCV18_roundness_le_ratio
  have hnonneg : 0 ≤ max 1 (P.outerRadius / P.inradius) := by
    exact le_trans (by norm_num) (le_max_left _ _)
  nlinarith [sq_le_sq₀ hnonneg (by
    unfold TTCRuntime.theorem3Rho
    exact le_trans (by norm_num : (0 : Real) ≤ 1) (le_max_left _ _)) |>.2 hmax]

theorem Decomposition.communityCV18_queryBudget_le_rho_polylog
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (i : Fin D.componentCount)
    (eta delta : Real) (h : CommunityCV18.AdmissibleCV18Request eta delta) :
    (CommunityCV18.queryBudgetFor (by omega) (D.component i) eta delta : Real) ≤
      45 * (64 *
        ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
        + 1) *
        (n : Real) ^ 3 * (TTCRuntime.theorem3Rho D) ^ 2 / (eta / 2) ^ 2 *
        TTCRuntime.theorem3CV18LogEnvelope
          (CommunityCV18.params (by omega) (D.component i) eta delta h) := by
  let q := CommunityCV18.params (by omega) (D.component i) eta delta h
  have hrho : 1 ≤ TTCRuntime.theorem3Rho D := by
    unfold TTCRuntime.theorem3Rho
    exact le_max_left _ _
  have hround : q.roundness ≤ 4 * (TTCRuntime.theorem3Rho D) ^ 2 + 1 :=
    D.communityCV18_roundness_le_rho i
  have hbound := CommunityCV18.queryBudget_cast_le_rho_polylog q
    (TTCRuntime.theorem3Rho D) hrho hround
  simpa only [q, CommunityCV18.queryBudgetFor, dif_pos h,
    CommunityCV18.params] using hbound

theorem Decomposition.communityCV18_queryBudget_le_envelope
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) :
    CommunityCV18.queryBudgetFor (by omega) (D.component i) p.epsilonPrime
      (p.deltaPrime D.componentCount) ≤
      TTCRuntime.theorem3CV18QueryEnvelope hn D p i := by
  have h := D.communityCV18_queryBudget_le_rho_polylog hn i
    p.epsilonPrime (p.deltaPrime D.componentCount)
    (CommunityCV18.admissibleTTCRequest D p i)
  have hc := Nat.ceil_mono h
  rw [Nat.ceil_natCast] at hc
  simpa only [TTCRuntime.theorem3CV18QueryEnvelope] using hc

theorem Decomposition.communityCV18_queryEnvelope_le_max
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) :
    TTCRuntime.theorem3CV18QueryEnvelope hn D p i ≤
      TTCRuntime.theorem3CV18QueryMax hn D p := by
  let q := CommunityCV18.params (by omega) (D.component i) p.epsilonPrime
    (p.deltaPrime D.componentCount) (CommunityCV18.admissibleTTCRequest D p i)
  have hlog0 : 0 ≤ TTCRuntime.theorem3CV18LogEnvelope q :=
    TTCRuntime.theorem3CV18LogEnvelope_nonneg q
  have hsup : Real.toNNReal (TTCRuntime.theorem3CV18LogEnvelope q) ≤
      (Finset.univ.sup fun j : Fin D.componentCount =>
        let qj := CommunityCV18.params (by omega) (D.component j) p.epsilonPrime
          (p.deltaPrime D.componentCount) (CommunityCV18.admissibleTTCRequest D p j)
        Real.toNNReal (TTCRuntime.theorem3CV18LogEnvelope qj) : NNReal) :=
    Finset.le_sup (f := fun j : Fin D.componentCount =>
      let qj := CommunityCV18.params (by omega) (D.component j) p.epsilonPrime
        (p.deltaPrime D.componentCount) (CommunityCV18.admissibleTTCRequest D p j)
      Real.toNNReal (TTCRuntime.theorem3CV18LogEnvelope qj)) (Finset.mem_univ i)
  have hlog : TTCRuntime.theorem3CV18LogEnvelope q ≤
      TTCRuntime.theorem3CV18LogMax hn D p := by
    calc
      TTCRuntime.theorem3CV18LogEnvelope q =
          (Real.toNNReal (TTCRuntime.theorem3CV18LogEnvelope q) : Real) :=
        (Real.coe_toNNReal _ hlog0).symm
      _ ≤ _ := by
        unfold TTCRuntime.theorem3CV18LogMax
        exact_mod_cast hsup
  unfold TTCRuntime.theorem3CV18QueryEnvelope TTCRuntime.theorem3CV18QueryMax
  apply Nat.ceil_mono
  have hcoeff : 0 ≤ 45 * (64 *
      ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
      + 1) *
      (n : Real) ^ 3 * (TTCRuntime.theorem3Rho D) ^ 2 /
      (p.epsilonPrime / 2) ^ 2 := by
    positivity [ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant_pos]
  exact mul_le_mul_of_nonneg_left hlog hcoeff

theorem TTCRuntime.manuscriptExpectedComponentBudgetGeometricClip_le_theorem3
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) :
    TTCRuntime.manuscriptExpectedComponentBudgetGeometricClip hn D p b
      cv18NonQueryFactor i ≤
      TTCRuntime.manuscriptExpectedComponentBudgetTheorem3 hn D p b
        cv18NonQueryFactor i := by
  have hqueries := D.communityCV18_queryBudget_le_envelope hn p i
  unfold TTCRuntime.manuscriptExpectedComponentBudgetGeometricClip
    TTCRuntime.manuscriptExpectedComponentBudgetTheorem3
  dsimp only
  unfold TTCRuntime.membershipQueryOperations
  gcongr

theorem TTCRuntime.manuscriptExpectedComponentBudgetTheorem3_le_uniform
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) :
    TTCRuntime.manuscriptExpectedComponentBudgetTheorem3 hn D p b
      cv18NonQueryFactor i ≤
      TTCRuntime.theorem3UniformComponentBudget hn D p b cv18NonQueryFactor := by
  have hqueries := D.communityCV18_queryEnvelope_le_max hn p i
  have hfacets : (D.component i).presentation.facetCount ≤
      TTCRuntime.theorem3RMax D := by
    unfold TTCRuntime.theorem3RMax
    exact Finset.le_sup (f := fun j : Fin D.componentCount =>
      (D.component j).presentation.facetCount) (Finset.mem_univ i)
  unfold TTCRuntime.manuscriptExpectedComponentBudgetTheorem3
    TTCRuntime.theorem3UniformComponentBudget
  dsimp only
  unfold TTCRuntime.membershipQueryOperations TTCRuntime.facetScanOperations
    TTCRuntime.samplingAttemptOperations TTCRuntime.rejectionTestOperations
  gcongr <;> simp only [TTCRuntime.facetScanOperations,
    TTCRuntime.rejectionTestOperations] <;> gcongr

end Kr25Ssmxt

import ttc.Analysis.MembershipCost
import ttc.Analysis.BoundingRadius
import ttc.Analysis.CV18Admissible
import ttc.Analysis.RuntimeBudgets
import ttc.Analysis.CV18NormalizedPolytope
import ttc.Analysis.ReferenceProgram
import ttc.Analysis.EuclideanInball

/-! A geometric bound on the concrete CV18 roundness parameter. -/

namespace ttc

open MeasureTheory

/-- The exact cap of the amplified CV18 implementation is bounded by its
published scheduled complexity rate and confidence multiplier. -/
theorem CommunityCV18.queryBudget_cast_le_scheduled_rate
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams) :
    (CommunityCV18.queryBudget q : Real) ≤
      (8 * ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p) + 1) *
        (64 * ArlibCommunity.Algorithms.CV18.runCostConstant *
          ArlibCommunity.Algorithms.CV18.runRate q + 1) := by
  let A := 8 * ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p)
  let B := 64 * ArlibCommunity.Algorithms.CV18.runCostConstant *
    ArlibCommunity.Algorithms.CV18.runRate q
  have hA : 0 ≤ A := by
    have hlog : (1 : Real) ≤
        ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p) := by
      unfold ArlibCommunity.Algorithms.CV18.protectedLog
      exact le_max_left _ _
    dsimp [A]
    linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity [ArlibCommunity.Algorithms.CV18.runCostConstant_pos,
      ArlibCommunity.Algorithms.CV18.runRate_pos q]
  have hceilA :
      (ArlibCommunity.Algorithms.CV18.confidenceRepetitions q : Real) ≤ A + 1 := by
    exact (Nat.ceil_lt_add_one hA).le
  have hceilB :
      (ArlibCommunity.Algorithms.CV18.queryBudget q : Real) ≤
        B + 1 := by
    exact (Nat.ceil_lt_add_one hB).le
  change (ArlibCommunity.Algorithms.CV18.confidenceRepetitions q *
      ArlibCommunity.Algorithms.CV18.queryBudget q : Nat) ≤
    (A + 1) * (B + 1)
  push_cast
  exact mul_le_mul hceilA hceilB (Nat.cast_nonneg _) (by positivity)

/-- Remove CV18's only nonsuppressed geometric parameter from its base rate. -/
theorem CommunityCV18.base_rate_le_rho_log_product
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams)
    (rho : Real) (hrho : 1 ≤ rho)
    (hround : q.roundness ≤ 4 * rho ^ 2 + 1) :
    ArlibCommunity.Algorithms.CV18.baseRate q ≤
      (5 * rho ^ 2 * (q.n : Real) ^ 3 / q.eps ^ 2) *
        ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.eps) ^ 2 *
        ArlibCommunity.Algorithms.CV18.protectedLog ((q.n : Real) / q.eps) ^ 2 *
        ArlibCommunity.Algorithms.CV18.protectedLog
          (ArlibCommunity.Algorithms.CV18.terminalScale q) ^ 2 := by
  have hmax : max 1 q.roundness ≤ 5 * rho ^ 2 := by
    apply max_le
    · nlinarith [sq_nonneg rho]
    · nlinarith [sq_nonneg rho]
  unfold ArlibCommunity.Algorithms.CV18.baseRate
  gcongr

theorem CommunityCV18.queryBudget_cast_le_scheduled_rate_no_ceiling
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams) :
    (CommunityCV18.queryBudget q : Real) ≤
      9 * (64 * ArlibCommunity.Algorithms.CV18.runCostConstant
        + 1) *
      ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p) *
      ArlibCommunity.Algorithms.CV18.runRate q := by
  let L := ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p)
  let S := ArlibCommunity.Algorithms.CV18.runRate q
  let C := ArlibCommunity.Algorithms.CV18.runCostConstant
  have hL : 1 ≤ L := by
    unfold L ArlibCommunity.Algorithms.CV18.protectedLog
    exact le_max_left _ _
  have hS : 1 ≤ S := ArlibCommunity.Algorithms.CV18.runRate_one_le q
  have hC : 0 ≤ C :=
    (ArlibCommunity.Algorithms.CV18.runCostConstant_pos).le
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
  have hacc : 0 ≤ ArlibCommunity.Algorithms.CV18.accuracyLog q :=
    (zero_le_one.trans
      (ArlibCommunity.Algorithms.CV18.accuracyLog_one_le q))
  have h1 := hlog (1 / q.p)
  have h2 := hlog (1 / q.eps)
  have h3 := hlog ((q.n : Real) / q.eps)
  have h4 := hlog (ArlibCommunity.Algorithms.CV18.terminalScale q)
  have h5 := hlog
    (1 / ArlibCommunity.Algorithms.CV18.blockMixingError q
      (ArlibCommunity.Algorithms.CV18.maxRetries q - 1))
  unfold TTCRuntime.theorem3CV18LogEnvelope
  positivity

theorem CommunityCV18.queryBudget_cast_le_rho_polylog
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams)
    (rho : Real) (hrho : 1 ≤ rho)
    (hround : q.roundness ≤ 4 * rho ^ 2 + 1) :
    (CommunityCV18.queryBudget q : Real) ≤
      45 * (64 *
        ArlibCommunity.Algorithms.CV18.runCostConstant
        + 1) *
        (q.n : Real) ^ 3 * rho ^ 2 / q.eps ^ 2 *
        TTCRuntime.theorem3CV18LogEnvelope q := by
  let C := ArlibCommunity.Algorithms.CV18.runCostConstant
  let L := ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p)
  let S := ArlibCommunity.Algorithms.CV18.runRate q
  let B := ArlibCommunity.Algorithms.CV18.baseRate q
  have hbase := CommunityCV18.base_rate_le_rho_log_product q rho hrho hround
  have hacc0 : 0 ≤ ArlibCommunity.Algorithms.CV18.accuracyLog q :=
    (zero_le_one.trans
      (ArlibCommunity.Algorithms.CV18.accuracyLog_one_le q))
  have hS : S ≤
      (5 * rho ^ 2 * (q.n : Real) ^ 3 / q.eps ^ 2) *
      ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.eps) ^ 2 *
      ArlibCommunity.Algorithms.CV18.protectedLog ((q.n : Real) / q.eps) ^ 2 *
      ArlibCommunity.Algorithms.CV18.protectedLog
        (ArlibCommunity.Algorithms.CV18.terminalScale q) ^ 2 *
      ArlibCommunity.Algorithms.CV18.accuracyLog q *
      ArlibCommunity.Algorithms.CV18.protectedLog
        (1 / ArlibCommunity.Algorithms.CV18.blockMixingError q
          (ArlibCommunity.Algorithms.CV18.maxRetries q - 1)) ^ 2 := by
    dsimp [S, ArlibCommunity.Algorithms.CV18.runRate]
    gcongr
  have hL0 : 0 ≤ L := by
    dsimp [L, ArlibCommunity.Algorithms.CV18.protectedLog]
    exact le_trans (by norm_num : (0 : Real) ≤ 1) (le_max_left _ _)
  have hC0 : 0 ≤ C :=
    (ArlibCommunity.Algorithms.CV18.runCostConstant_pos).le
  have hprefix : 0 ≤ 9 * (64 * C + 1) * L := by positivity
  have hquery := CommunityCV18.queryBudget_cast_le_scheduled_rate_no_ceiling q
  calc
    _ ≤ 9 * (64 * C + 1) * L * S := hquery
    _ ≤ 9 * (64 * C + 1) * L *
      ((5 * rho ^ 2 * (q.n : Real) ^ 3 / q.eps ^ 2) *
      ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.eps) ^ 2 *
      ArlibCommunity.Algorithms.CV18.protectedLog ((q.n : Real) / q.eps) ^ 2 *
      ArlibCommunity.Algorithms.CV18.protectedLog
        (ArlibCommunity.Algorithms.CV18.terminalScale q) ^ 2 *
      ArlibCommunity.Algorithms.CV18.accuracyLog q *
      ArlibCommunity.Algorithms.CV18.protectedLog
        (1 / ArlibCommunity.Algorithms.CV18.blockMixingError q
          (ArlibCommunity.Algorithms.CV18.maxRetries q - 1)) ^ 2) := by
        gcongr
    _ = _ := by
      unfold TTCRuntime.theorem3CV18LogEnvelope
      dsimp [C, L]
      ring

theorem Decomposition.communityCV18_roundness_le_rho {n k : Nat}
    {F : LRAFormula n k} (D : Decomposition F)
    (i : Fin D.componentCount) :
    CommunityCV18.roundness (D.component i) ≤
      4 * (TTCRuntime.Rho D) ^ 2 + 1 := by
  let P := D.component i
  have hratio0 : 0 ≤ P.outerRadius / P.inradius :=
    div_nonneg P.outerRadius_nonneg P.inradius_pos.le
  have hsup : P.outerRadius / P.inradius ≤
      TTCRuntime.Rho D := by
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
  -- `roundness = (R₀/γ)²/n` and `R₀ ≤ 2√n R`, so `roundness ≤ 4 (R/γ)² ≤ 4ρ²`.
  have hγ := P.inradius_pos
  have hB := P.boundingRadius_le
  have hB0 := P.boundingRadius_nonneg
  have hρ0 : 0 ≤ P.outerRadius / P.inradius := hratio0
  have hρ := le_trans zero_le_one (le_max_left 1 _ : (1 : Real) ≤ TTCRuntime.Rho D)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [CommunityCV18.roundness, P, Nat.cast_zero, div_zero]
    positivity
  have hn0 : (0 : Real) < n := by exact_mod_cast hn
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  have hratio : P.BoundingRadius / P.inradius ≤
      2 * Real.sqrt n * (P.outerRadius / P.inradius) := by
    rw [div_le_iff₀ hγ]
    calc P.BoundingRadius ≤ 2 * Real.sqrt n * P.outerRadius := hB
      _ = _ := by field_simp
  have hsq2 : (P.BoundingRadius / P.inradius) ^ 2 ≤
      4 * n * (P.outerRadius / P.inradius) ^ 2 := by
    have h := pow_le_pow_left₀ (div_nonneg hB0 hγ.le) hratio 2
    calc _ ≤ (2 * Real.sqrt n * (P.outerRadius / P.inradius)) ^ 2 := h
      _ = 4 * (Real.sqrt n ^ 2) * (P.outerRadius / P.inradius) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have hmax : max 1 (P.BoundingRadius / P.inradius) = P.BoundingRadius / P.inradius :=
    max_eq_right ((one_le_div hγ).2 (P.inradius_le_boundingRadius hn))
  have hround : CommunityCV18.roundness P ≤ 4 * (P.outerRadius / P.inradius) ^ 2 := by
    unfold CommunityCV18.roundness
    rw [hmax, div_le_iff₀ hn0]
    linarith
  have hsup2 : (P.outerRadius / P.inradius) ^ 2 ≤ (TTCRuntime.Rho D) ^ 2 :=
    pow_le_pow_left₀ hρ0 hsup 2
  change CommunityCV18.roundness P ≤ _
  linarith

theorem Decomposition.communityCV18_queryBudget_le_rho_polylog
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (i : Fin D.componentCount)
    (eta delta : Real) (h : CommunityCV18.AdmissibleCV18Request eta delta) :
    (CommunityCV18.queryBudgetFor (by omega) (D.component i) eta delta : Real) ≤
      45 * (64 *
        ArlibCommunity.Algorithms.CV18.runCostConstant
        + 1) *
        (n : Real) ^ 3 * (TTCRuntime.Rho D) ^ 2 / (eta / 2) ^ 2 *
        TTCRuntime.theorem3CV18LogEnvelope
          (CommunityCV18.params (by omega) (D.component i) eta delta h) := by
  let q := CommunityCV18.params (by omega) (D.component i) eta delta h
  have hrho : 1 ≤ TTCRuntime.Rho D := by
    unfold TTCRuntime.Rho
    exact le_max_left _ _
  have hround : q.roundness ≤ 4 * (TTCRuntime.Rho D) ^ 2 + 1 :=
    D.communityCV18_roundness_le_rho i
  have hbound := CommunityCV18.queryBudget_cast_le_rho_polylog q
    (TTCRuntime.Rho D) hrho hround
  simpa only [q, CommunityCV18.queryBudgetFor, dif_pos h,
    CommunityCV18.params] using hbound

theorem Decomposition.communityCV18_queryBudget_le_envelope
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) :
    CommunityCV18.queryBudgetFor (by omega) (D.component i) p.ε'
      (p.δ' D.componentCount) ≤
      TTCRuntime.theorem3CV18QueryEnvelope hn D p i := by
  have h := D.communityCV18_queryBudget_le_rho_polylog hn i
    p.ε' (p.δ' D.componentCount)
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
  let q := CommunityCV18.params (by omega) (D.component i) p.ε'
    (p.δ' D.componentCount) (CommunityCV18.admissibleTTCRequest D p i)
  have hlog0 : 0 ≤ TTCRuntime.theorem3CV18LogEnvelope q :=
    TTCRuntime.theorem3CV18LogEnvelope_nonneg q
  have hsup : Real.toNNReal (TTCRuntime.theorem3CV18LogEnvelope q) ≤
      (Finset.univ.sup fun j : Fin D.componentCount =>
        let qj := CommunityCV18.params (by omega) (D.component j) p.ε'
          (p.δ' D.componentCount) (CommunityCV18.admissibleTTCRequest D p j)
        Real.toNNReal (TTCRuntime.theorem3CV18LogEnvelope qj) : NNReal) :=
    Finset.le_sup (f := fun j : Fin D.componentCount =>
      let qj := CommunityCV18.params (by omega) (D.component j) p.ε'
        (p.δ' D.componentCount) (CommunityCV18.admissibleTTCRequest D p j)
      Real.toNNReal (TTCRuntime.theorem3CV18LogEnvelope qj)) (Finset.mem_univ i)
  have hlog : TTCRuntime.theorem3CV18LogEnvelope q ≤
      TTCRuntime.theorem3CV18LogMax hn D p := by
    calc
      TTCRuntime.theorem3CV18LogEnvelope q =
          (Real.toNNReal (TTCRuntime.theorem3CV18LogEnvelope q) : Real) :=
        (Real.coe_toNNReal _ hlog0).symm
      _ ≤ _ := by
        unfold TTCRuntime.theorem3CV18LogMax
        simp only [dif_pos (CommunityCV18.admissibleTTCRequest D p i)]
        exact_mod_cast hsup
  unfold TTCRuntime.theorem3CV18QueryEnvelope TTCRuntime.theorem3CV18QueryMax
  apply Nat.ceil_mono
  have hcoeff : 0 ≤ 45 * (64 *
      ArlibCommunity.Algorithms.CV18.runCostConstant
      + 1) *
      (n : Real) ^ 3 * (TTCRuntime.Rho D) ^ 2 /
      (p.ε' / 2) ^ 2 := by
    positivity [ArlibCommunity.Algorithms.CV18.runCostConstant_pos]
  exact mul_le_mul_of_nonneg_left hlog hcoeff

theorem TTCRuntime.expectedComponentBudgetGeometric_le_theorem3
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) :
    TTCRuntime.expectedComponentBudgetGeometric hn D p b
      cv18NonQueryFactor i ≤
      TTCRuntime.expectedComponentBudgetTheorem3 hn D p b
        cv18NonQueryFactor i := by
  have hqueries := D.communityCV18_queryBudget_le_envelope hn p i
  unfold TTCRuntime.expectedComponentBudgetGeometric
    TTCRuntime.expectedComponentBudgetTheorem3
  dsimp only
  unfold TTCRuntime.membershipQueryOperations
  gcongr

theorem TTCRuntime.expectedComponentBudgetTheorem3_le_uniform
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) :
    TTCRuntime.expectedComponentBudgetTheorem3 hn D p b
      cv18NonQueryFactor i ≤
      TTCRuntime.theorem3UniformComponentBudget hn D p b cv18NonQueryFactor := by
  have hqueries := D.communityCV18_queryEnvelope_le_max hn p i
  have hfacets : (D.component i).presentation.facetCount ≤
      TTCRuntime.RMax D := by
    unfold TTCRuntime.RMax
    exact Finset.le_sup (f := fun j : Fin D.componentCount =>
      (D.component j).presentation.facetCount) (Finset.mem_univ i)
  unfold TTCRuntime.expectedComponentBudgetTheorem3
    TTCRuntime.theorem3UniformComponentBudget
  dsimp only
  unfold TTCRuntime.membershipQueryOperations TTCRuntime.facetScanOperations
    TTCRuntime.samplingAttemptOperations TTCRuntime.rejectionTestOperations
    TTCRuntime.hitAndRunStepOperations
  gcongr <;> (try simp only [TTCRuntime.facetScanOperations]) <;> gcongr

end ttc

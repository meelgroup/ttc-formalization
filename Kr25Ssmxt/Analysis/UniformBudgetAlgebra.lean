import Kr25Ssmxt.Analysis.CV18Admissible
import Kr25Ssmxt.Analysis.RuntimeBudgets
import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.ThresholdCapBound

/-! Elementary arithmetic behind the uniform per-component cost envelope. -/

namespace Kr25Ssmxt

namespace TTCRuntime

def uniformBudgetNat (n r cap queries steps rounds : Nat) : Nat :=
  membershipQueryOperations n r queries +
    membershipQueryOperations n r (queries + 1) +
    cap * (facetScanOperations n r + 1) +
    rounds * rateThinningRoundOperations cap +
    poissonDrawOperations +
    4 * countThinningRoundOperations cap +
    cap * (2 * samplingAttemptOperations n r steps + appendCopyOperations)

theorem uniformBudgetNat_le_coarse_product
    (n r cap queries steps rounds : Nat) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    uniformBudgetNat n r cap queries steps rounds ≤
      30 * n * r * (cap + 1) * (queries + steps + rounds + 1) := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hr
  subst n
  subst r
  unfold uniformBudgetNat membershipQueryOperations facetScanOperations
    rateThinningRoundOperations countThinningRoundOperations
    poissonDrawOperations fairCoinOperations binomialDrawOperations
    scalarOperationCost samplingAttemptOperations ballStartOperations roundPointOperations
    rejectionTestOperations appendCopyOperations
  dsimp [facetScanOperations]
  ring_nf
  omega

theorem theorem3UniformComponentBudget_eq_uniformBudgetNat
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b : Nat) :
    theorem3UniformComponentBudget hn D p b 1 =
      (uniformBudgetNat n (theorem3RMax D) (sampleCap p D.componentCount)
        (theorem3CV18QueryMax hn D p)
        (Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
          (theorem3Rho D) ^ 2 *
          theorem3SamplerLogEnvelope n b
            (theorem3Rho D) (theorem3OuterRadiusMax D) p.ε'))
        (4 * (b * n) + (2 + n * Nat.clog 2
          (Nat.ceil (4 * theorem3OuterRadiusMax D) + 1))) : ENNReal) := by
  unfold theorem3UniformComponentBudget uniformBudgetNat
  simp [Nat.cast_add, Nat.cast_mul]

theorem theorem3UniformComponentBudget_le_coarse_product
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hm : 0 < D.componentCount) :
    theorem3UniformComponentBudget hn D p b 1 ≤
      ((30 * n * theorem3RMax D * (sampleCap p D.componentCount + 1) *
        (theorem3CV18QueryMax hn D p +
          Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
            (theorem3Rho D) ^ 2 *
            theorem3SamplerLogEnvelope n b
              (theorem3Rho D) (theorem3OuterRadiusMax D) p.ε') +
          (4 * (b * n) + (2 + n * Nat.clog 2
            (Nat.ceil (4 * theorem3OuterRadiusMax D) + 1))) + 1) : Nat) : ENNReal) := by
  rw [theorem3UniformComponentBudget_eq_uniformBudgetNat hn D p b]
  exact_mod_cast uniformBudgetNat_le_coarse_product _ _ _ _ _ _
    (by omega : 1 ≤ n) (D.theorem3RMax_pos hm)

theorem theorem3UniformIndexSum_le_parameterFactor
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b : Nat) :
    let rho := theorem3Rho D
    let R := theorem3OuterRadiusMax D
    let H := theorem3PrecisionScale b R
    let M := (n : Real) ^ 4 * rho ^ 2 * H
    theorem3CV18QueryMax hn D p +
        Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 *
          theorem3SamplerLogEnvelope n b rho R p.ε') +
        (4 * (b * n) + (2 + n * Nat.clog 2 (Nat.ceil (4 * R) + 1))) + 1 ≤
      Nat.ceil (M * theorem3ParameterFactorCV18 hn D p) := by
  dsimp only
  let rho := theorem3Rho D
  let R := theorem3OuterRadiusMax D
  let H := theorem3PrecisionScale b R
  let Lcv := theorem3CV18LogMax hn D p
  let Lhr := Real.log 8 + Real.log (4 * rho + 1) +
    2 * (Real.log 10 + Real.log 6 + 1 +
      Real.log (1 + 8 / p.ε') + 2)
  let A := 45 * (64 *
    ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant + 1)
  let M := (n : Real) ^ 4 * rho ^ 2 * H
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hrho : 1 ≤ rho := by
    dsimp [rho, theorem3Rho]
    exact le_max_left _ _
  have hH : 1 ≤ H := by
    dsimp [H, theorem3PrecisionScale]
    have hb : 0 ≤ (b : Real) := by positivity
    have hR : 0 ≤ max 0 (Real.log R) := le_max_left _ _
    linarith
  have hM : 1 ≤ M := by
    dsimp [M]
    have hn4 : (1 : Real) ≤ (n : Real) ^ 4 := one_le_pow₀ hn1
    have hrho2 : (1 : Real) ≤ rho ^ 2 := one_le_pow₀ hrho
    nlinarith [mul_nonneg (sub_nonneg.mpr hn4) (sub_nonneg.mpr hrho2),
      mul_nonneg (sub_nonneg.mpr hH) (sub_nonneg.mpr hrho2)]
  have hLcv : 0 ≤ Lcv := by
    dsimp [Lcv, theorem3CV18LogMax]
    exact NNReal.coe_nonneg _
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity [ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant_pos]
  have heps : 0 < p.ε' := by
    dsimp [ApproxParams.ε']
    positivity [p.epsilon_pos]
  have hLhr : 0 ≤ Lhr := by
    dsimp [Lhr]
    have hlogrho : 0 ≤ Real.log (4 * rho + 1) :=
      Real.log_nonneg (by linarith)
    have hlogeta : 0 ≤ Real.log (1 + 8 / p.ε') := by
      apply Real.log_nonneg
      have : 0 ≤ 8 / p.ε' := div_nonneg (by norm_num) heps.le
      linarith
    positivity
  have hQ0 : 0 ≤ A * (n : Real) ^ 3 * rho ^ 2 /
      (p.ε' / 2) ^ 2 * Lcv := by positivity
  have hQ : (theorem3CV18QueryMax hn D p : Real) ≤
      A * (n : Real) ^ 3 * rho ^ 2 /
        (p.ε' / 2) ^ 2 * Lcv + 1 := by
    simpa [theorem3CV18QueryMax, A, rho, Lcv] using
      (Nat.ceil_lt_add_one hQ0).le
  have hS0 : 0 ≤ (2 : Real) ^ 68 * (n : Real) ^ 4 * rho ^ 2 * H * Lhr := by
    positivity
  have henv := theorem3_samplerLogEnvelope_le_dimension_precision_polylog
    n b (by omega : 1 ≤ n) rho R p.ε' hrho heps
  have hS :
      (Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 *
        theorem3SamplerLogEnvelope n b rho R p.ε') : Real) ≤
        (2 : Real) ^ 68 * (n : Real) ^ 4 * rho ^ 2 * H * Lhr + 1 := by
    have hcoeff : 0 ≤ (2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 := by
      positivity
    have hceil := Nat.ceil_mono (mul_le_mul_of_nonneg_left henv hcoeff)
    have hidentity :
        (2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 *
          ((n : Real) ^ 2 * H * Lhr) =
        (2 : Real) ^ 68 * (n : Real) ^ 4 * rho ^ 2 * H * Lhr := by ring
    change Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 *
      theorem3SamplerLogEnvelope n b rho R p.ε') ≤
      Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 *
        ((n : Real) ^ 2 * H * Lhr)) at hceil
    rw [hidentity] at hceil
    have hceilR :
        (Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 *
          theorem3SamplerLogEnvelope n b rho R p.ε') : Real) ≤
        (Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 4 * rho ^ 2 * H * Lhr) : Real) := by
      exact_mod_cast hceil
    have hupper := (Nat.ceil_lt_add_one hS0).le
    nlinarith [hceilR]
  have hK := theorem3_first_loop_rounds_le_precisionScale n b
    (by omega : 1 ≤ n) R
  change ((4 * (b * n) + (2 + n * Nat.clog 2 (Nat.ceil (4 * R) + 1)) : Nat) : Real) ≤
    14 * (n : Real) * H at hK
  push_cast at hK
  have hQscale : A * (n : Real) ^ 3 * rho ^ 2 /
      (p.ε' / 2) ^ 2 * Lcv ≤
      M * (A * Lcv / (p.ε' / 2) ^ 2) := by
    dsimp [M]
    have : (n : Real) ^ 3 ≤ (n : Real) ^ 4 * H := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hH),
        pow_nonneg (by positivity : (0 : Real) ≤ n) 3]
    have hcoeff : 0 ≤ A * rho ^ 2 * Lcv / (p.ε' / 2) ^ 2 := by
      positivity
    calc
      _ = ((n : Real) ^ 3) *
          (A * rho ^ 2 * Lcv / (p.ε' / 2) ^ 2) := by ring
      _ ≤ ((n : Real) ^ 4 * H) *
          (A * rho ^ 2 * Lcv / (p.ε' / 2) ^ 2) :=
        mul_le_mul_of_nonneg_right this hcoeff
      _ = _ := by ring
  have hKscale : 14 * (n : Real) * H ≤ 14 * M := by
    dsimp [M]
    have hpow : (n : Real) ≤ (n : Real) ^ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1)
        (by positivity : 0 ≤ (n : Real) ^ 3),
        mul_nonneg (sub_nonneg.mpr hn1)
        (by positivity : 0 ≤ (n : Real) ^ 2),
        mul_nonneg (sub_nonneg.mpr hn1)
        (by positivity : 0 ≤ (n : Real))]
    have hrho2 : (1 : Real) ≤ rho ^ 2 := one_le_pow₀ hrho
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) (show 0 ≤ H by linarith),
      mul_nonneg (sub_nonneg.mpr hrho2) (show 0 ≤ H by linarith)]
  have hsum :
      ((theorem3CV18QueryMax hn D p +
        Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 *
          theorem3SamplerLogEnvelope n b rho R p.ε') +
        (4 * (b * n) + (2 + n * Nat.clog 2 (Nat.ceil (4 * R) + 1))) + 1 : Nat) : Real) ≤
        M * theorem3ParameterFactorCV18 hn D p := by
    change ((theorem3CV18QueryMax hn D p +
        Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 *
          theorem3SamplerLogEnvelope n b rho R p.ε') +
        (4 * (b * n) + (2 + n * Nat.clog 2 (Nat.ceil (4 * R) + 1))) + 1 : Nat) : Real) ≤
      M * (A * Lcv / (p.ε' / 2) ^ 2 +
        (2 : Real) ^ 68 * Lhr + 20)
    push_cast
    have hSscale : (2 : Real) ^ 68 * (n : Real) ^ 4 * rho ^ 2 * H * Lhr =
        M * ((2 : Real) ^ 68 * Lhr) := by dsimp [M]; ring
    rw [hSscale] at hS
    have hQ' : (theorem3CV18QueryMax hn D p : Real) ≤
        M * (A * Lcv / (p.ε' / 2) ^ 2) + 1 := by linarith
    have hK' : 4 * ((b : Real) * n) +
        (2 + (n : Real) * Nat.clog 2 (Nat.ceil (4 * R) + 1)) ≤
        14 * M := by linarith
    have hsum1 := add_le_add (add_le_add (add_le_add hQ' hS) hK')
      (le_refl (1 : Real))
    nlinarith [hM]
  have hfinal := hsum.trans (Nat.le_ceil (M * theorem3ParameterFactorCV18 hn D p))
  dsimp [rho, R, H, M] at hfinal ⊢
  exact_mod_cast hfinal

theorem theorem3UniformComponentBudget_le_headline_scale
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hm : 0 < D.componentCount) :
    theorem3UniformComponentBudget hn D p b 1 ≤
      ENNReal.ofReal (30 * (n : Real) ^ 5 *
        (theorem3RMax D : Real) * (theorem3Rho D) ^ 2 *
        theorem3PrecisionScale b (theorem3OuterRadiusMax D) *
        ((sampleCap p D.componentCount : Real) + 1) *
        (theorem3ParameterFactorCV18 hn D p + 1)) := by
  let r := theorem3RMax D
  let cap := sampleCap p D.componentCount
  let Q := theorem3CV18QueryMax hn D p
  let rho := theorem3Rho D
  let R := theorem3OuterRadiusMax D
  let H := theorem3PrecisionScale b R
  let L := theorem3ParameterFactorCV18 hn D p
  let M := (n : Real) ^ 4 * rho ^ 2 * H
  let S := Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 * rho ^ 2 *
    theorem3SamplerLogEnvelope n b rho R p.ε')
  let K := 4 * (b * n) + (2 + n * Nat.clog 2 (Nat.ceil (4 * R) + 1))
  have hindex : Q + S + K + 1 ≤ Nat.ceil (M * L) := by
    simpa only [Q, S, K, M, L, rho, R, H] using
      theorem3UniformIndexSum_le_parameterFactor hn D p b
  have hbudget : theorem3UniformComponentBudget hn D p b 1 ≤
      ((30 * n * r * (cap + 1) * (Q + S + K + 1) : Nat) : ENNReal) := by
    simpa only [Q, S, K, r, cap, rho, R] using
      theorem3UniformComponentBudget_le_coarse_product hn D p b hm
  have hnat : 30 * n * r * (cap + 1) * (Q + S + K + 1) ≤
      30 * n * r * (cap + 1) * Nat.ceil (M * L) := by
    gcongr
  have hfirst : theorem3UniformComponentBudget hn D p b 1 ≤
      ((30 * n * r * (cap + 1) * Nat.ceil (M * L) : Nat) : ENNReal) :=
    hbudget.trans (by exact_mod_cast hnat)
  have hrho : 1 ≤ rho := by
    dsimp [rho, theorem3Rho]
    exact le_max_left _ _
  have hH : 1 ≤ H := by
    dsimp [H, theorem3PrecisionScale]
    have hb : 0 ≤ (b : Real) := by positivity
    have hR : 0 ≤ max 0 (Real.log R) := le_max_left _ _
    linarith
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hM : 1 ≤ M := by
    dsimp [M]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn1) (one_le_pow₀ hrho)) hH
  have hLcv : 0 ≤ theorem3CV18LogMax hn D p := by
    unfold theorem3CV18LogMax
    positivity
  have hL : 0 ≤ L := by
    dsimp [L, theorem3ParameterFactorCV18]
    have hlogrho : 0 ≤ Real.log (4 * rho + 1) :=
      Real.log_nonneg (by linarith)
    have heps : 0 < p.ε' := by
      dsimp [ApproxParams.ε']
      positivity [p.epsilon_pos]
    have hlogeta : 0 ≤ Real.log (1 + 8 / p.ε') := by
      apply Real.log_nonneg
      have : 0 ≤ 8 / p.ε' := div_nonneg (by norm_num) heps.le
      linarith
    positivity [ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant_pos]
  have hML : 0 ≤ M * L := mul_nonneg (by linarith) hL
  have hceil : (Nat.ceil (M * L) : Real) ≤ M * L + 1 :=
    (Nat.ceil_lt_add_one hML).le
  have hreal :
      ((30 * n * r * (cap + 1) * Nat.ceil (M * L) : Nat) : Real) ≤
        30 * (n : Real) ^ 5 * r * rho ^ 2 * H *
          ((cap : Real) + 1) * (L + 1) := by
    push_cast
    have hcoeff : 0 ≤ 30 * (n : Real) * r * ((cap : Real) + 1) := by positivity
    have hupper := mul_le_mul_of_nonneg_left hceil hcoeff
    have hMplus : M * L + 1 ≤ M * (L + 1) := by nlinarith [hM]
    have hupper2 := mul_le_mul_of_nonneg_left hMplus hcoeff
    have hidentity : 30 * (n : Real) * r * ((cap : Real) + 1) *
        (M * (L + 1)) =
        30 * (n : Real) ^ 5 * r * rho ^ 2 * H *
          ((cap : Real) + 1) * (L + 1) := by dsimp [M]; ring
    nlinarith [hupper, hupper2]
  have hcast :
      ((30 * n * r * (cap + 1) * Nat.ceil (M * L) : Nat) : ENNReal) ≤
        ENNReal.ofReal (30 * (n : Real) ^ 5 * r * rho ^ 2 * H *
          ((cap : Real) + 1) * (L + 1)) := by
    calc
      ((30 * n * r * (cap + 1) * Nat.ceil (M * L) : Nat) : ENNReal) =
          ENNReal.ofReal
            ((30 * n * r * (cap + 1) * Nat.ceil (M * L) : Nat) : Real) := by
        norm_cast
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  have hresult := hfirst.trans hcast
  simpa only [r, cap, rho, R, H, L] using hresult

end TTCRuntime
end Kr25Ssmxt

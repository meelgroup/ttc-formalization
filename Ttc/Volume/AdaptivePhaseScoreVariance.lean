/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.ChunkedVarianceUnconditional
import Arlib.Convexity.GaussianCooling.PhaseVar

/-!
# The adaptive localization bound on the actual Cousins--Vempala phase score

`ChunkedVarianceUnconditional` proves the accelerated estimate in the paper's `gW/G`
notation.  This file transports it to the actual `phaseScore` under `coolLaw`, keeping the
terminal uniform phase separate.  Thus every index before the adaptive offset is an honest
Gaussian-to-Gaussian phase of a schedule whose total length is `offset + 1`.
-/

namespace Ttc.CV

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked

variable {n : ℕ}

/-- The localization-free product inequality, read as a second-moment bound for an actual
interior `phaseScore`. -/
theorem compactConvex_phaseScore_sq_moment_le {m : ℕ} {σsq : ℕ → ℝ}
    (hn : 2 ≤ n) (hσ : ∀ j, 0 < σsq j) {K : Set (EuclSpace n)} (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : ℕ} (hi : i + 1 < m) {α R : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 1 / 2)
    (hrate : σsq (i + 1) = σsq i * (1 + α))
    (hKR : K ⊆ closedBall 0 R) :
    ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i) ≤
      Real.exp (2 * R ^ 2 * α ^ 2 / σsq (i + 1)) *
        (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2 := by
  have ha0 := hσ i
  have hb0 := hσ (i + 1)
  have hαp : 0 < 1 + α := by linarith
  have hαm : 0 < 1 - α := by linarith
  have hab : 2 * σsq i - σsq (i + 1) ≠ 0 := by rw [hrate]; nlinarith
  set a := σsq i with ha
  set b := σsq (i + 1) with hb
  set c := a * b / (2 * a - b) with hc
  set F : EuclSpace n → ℝ := indicator K 1 with hF
  have hchain := chain_pos (m := m) hσ hball hfin i
  have hGa : G F a = chain m σsq K i :=
    (chain_eq_G (Nat.lt_of_succ_lt hi) hKcl.measurableSet).symm
  have hGb : G F b = chain m σsq K (i + 1) :=
    (chain_eq_G hi hKcl.measurableSet).symm
  have hsqrt : 0 < √b := Real.sqrt_pos.2 hb0
  have hsqrtSq : (√b) ^ 2 = b := Real.sq_sqrt hb0.le
  have hcore := compactConvex_G_product_le (n := n) hn
    hKc hKcl hKb hvol hsqrt hα0 hα2 hKR
  rw [hsqrtSq] at hcore
  have hba : b / (1 + α) = a := by
    rw [hrate, mul_div_assoc, div_self hαp.ne', mul_one]
  have h2ab : 2 * a - b = a * (1 - α) := by
    rw [hrate]
    ring
  have hbc : b / (1 - α) = c := by
    rw [hc, h2ab, div_eq_div_iff hαm.ne' (mul_pos ha0 hαm).ne']
    ring
  rw [hba, hbc, ← show F = indicator K (1 : EuclSpace n → ℝ) by rfl] at hcore
  have hGApos : 0 < G F a := by rw [hGa]; exact hchain
  rw [integral_phaseScore_sq_coolLaw hKcl.measurableSet hchain hi ha0.ne' hb0.ne' hab,
    integral_phaseScore_coolLaw hKcl.measurableSet hchain, ← hc, ← hF, ← hGa, ← hGb]
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_div_iff₀ hGApos (pow_pos hGApos 2)).2
  calc
    G F c * G F a ^ 2 = (G F a * G F c) * G F a := by ring
    _ ≤ (Real.exp (2 * R ^ 2 * α ^ 2 / b) * G F b ^ 2) * G F a :=
      mul_le_mul_of_nonneg_right hcore hGApos.le
    _ = (Real.exp (2 * R ^ 2 * α ^ 2 / b) * G F b ^ 2) * G F a := rfl

/-- Every flattened adaptive Gaussian phase has exactly the raw relative-second-moment
factor used in the chunk product.  The extra terminal phase is why the score length is
`adaptiveChunkOffset ... J + 1`. -/
theorem adaptivePhaseScore_sq_moment_le {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclSpace n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s₀ : ℝ} {J : ℕ} (hC : 0 < C) (hs₀ : 0 < s₀)
    (hbelow : ∀ j < J, adaptiveChunkStart (C ^ 2 * n) s₀ j ≤ C ^ 2 * n)
    (hKR : K ⊆ closedBall 0 (C * √n))
    (i : Fin (adaptiveChunkOffset (C ^ 2 * n) s₀ J)) :
    ∫ x, phaseScore (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
          (adaptiveSigmaSq (C ^ 2 * n) s₀) K i x ^ 2
          ∂(coolLaw (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
            (adaptiveSigmaSq (C ^ 2 * n) s₀) K i) ≤
      adaptiveGlobalPhaseVarFactor 1 (C ^ 2 * n) s₀ i *
        (∫ x, phaseScore (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
            (adaptiveSigmaSq (C ^ 2 * n) s₀) K i x
            ∂(coolLaw (adaptiveChunkOffset (C ^ 2 * n) s₀ J + 1)
              (adaptiveSigmaSq (C ^ 2 * n) s₀) K i)) ^ 2 := by
  let N : ℝ := C ^ 2 * n
  let u : ℝ := adaptiveSigmaSq N s₀ i
  let α : ℝ := adaptivePhaseRate N s₀ i
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  have hu : 0 < u := adaptiveSigmaSq_pos hN hs₀ i
  have hchunk : adaptivePhaseChunk N s₀ i < J :=
    adaptivePhaseChunk_lt_of_lt_offset hN hs₀ i.isLt
  have hstart : 0 < adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i) :=
    adaptiveChunkStart_pos hN hs₀ _
  have hstartu : adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i) ≤ u :=
    adaptiveChunkStart_le_geom hN hs₀ _ (adaptiveLocalPhase N s₀ i)
  have hα : α = adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i) / (2 * N) := rfl
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hα2 : α ≤ 1 / 2 := by
    rw [hα, div_le_iff₀ (by positivity : 0 < 2 * N)]
    have hb := hbelow _ hchunk
    change adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ ↑i) ≤ N at hb
    nlinarith
  have hi0 := i.isLt
  change (i : ℕ) < adaptiveChunkOffset N s₀ J at hi0
  have hi : (i : ℕ) + 1 < adaptiveChunkOffset N s₀ J + 1 := by omega
  have hraw := compactConvex_phaseScore_sq_moment_le
    (m := adaptiveChunkOffset N s₀ J + 1)
    (σsq := adaptiveSigmaSq N s₀) hn (fun q => adaptiveSigmaSq_pos hN hs₀ q)
    hKc hKcl hKb hvol hball hfin hi hα0 hα2
    (adaptiveSigmaSq_succ_eq_phaseRate hN hs₀ i) hKR
  have hexp : Real.exp (2 * N * α ^ 2 / (u * (1 + α))) ≤ 1 + u / N :=
    chunkConstantRate_exp_le hN hstart
      (by simpa [N] using hbelow _ hchunk) hstartu hα
  have hR : (C * √(n : ℝ)) ^ 2 = N := by
    dsimp [N]
    rw [mul_pow, Real.sq_sqrt hnpos.le]
  have hsucc : adaptiveSigmaSq N s₀ ((i : ℕ) + 1) = u * (1 + α) :=
    adaptiveSigmaSq_succ_eq_phaseRate hN hs₀ i
  rw [hR, hsucc] at hraw
  have hfac : adaptiveGlobalPhaseVarFactor 1 N s₀ i = 1 + u / N := by
    simp [adaptiveGlobalPhaseVarFactor, u]
  rw [hfac]
  exact hraw.trans (mul_le_mul_of_nonneg_right hexp (sq_nonneg _))

#print axioms compactConvex_phaseScore_sq_moment_le
#print axioms adaptivePhaseScore_sq_moment_le

end Ttc.CV

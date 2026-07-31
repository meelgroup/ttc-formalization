/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.BallFacet
import Ttc.Analysis.Parameters
import Ttc.Analysis.Recentred
import Ttc.Analysis.ProdLaw

/-!
# `lem:nonconv`, assembled over an actual facet system

`Analysis/Recentred` proves the shell geometry, `Analysis/ClB` and
`Analysis/ProdLaw` prove `claim:cl` for the actual rounding, and
`Analysis/Nonconv` proves the two summation steps. All of them are stated over
free reals or over an abstract kernel. This file puts them together over one
`Ttc.FacetSystem` presented by coefficient vectors, and concludes `lem:nonconv`
for its body against its **integer-point count** — no free reals left.

The parameters are the algorithm's: `η = ε/8`, the internal `θ = η/2` of the
repair (finding 1), `κ = Ttc.Params.kappa`, `γ = Ttc.Params.gamma`.

## Two departures from `Ttc.nonconv_recentred`

* The two shell losses are **not equal**. The inflated side loses `η/16`
  (`Ttc.Params.shell_factor_bound`) and the deflated side `η/8`
  (`Ttc.Params.shell_factor_bound_deflated`), because `κ/(γ−κ) ≤ 2κ/γ` costs a
  factor `2`. `Ttc.nonconv_recentred_general` takes the two separately; both
  values still fit, with room.
* The lattice-point set is not assumed finite. It is finite *because* of
  `claim:cl`(a): that step bounds `|T|` for every finite `T ⊆ Q ∩ ℤⁿ`
  (`Ttc.FacetSystem.card_le_of_claim_a`), which is exactly the hypothesis of
  `Ttc.finite_of_forall_finset_card_le`.
-/

namespace Ttc

open MeasureTheory Set

variable {n : ℕ} {ι F : Type*}

/-! ## The arithmetic, with the two shell losses kept apart -/

/-- **`lem:nonconv` with two shell factors.** `Ttc.nonconv_recentred` is the case
`s₁ = s₂ = η/16`; the assembly needs `s₁ = η/16`, `s₂ = η/8`.

The lower bound uses only the inflated loss `s₁` and the upper bound only the
deflated loss `s₂`, so the two never have to be equalised. -/
theorem nonconv_recentred_general {η θ N volQ volQ' volQ'' s₁ s₂ : ℝ}
    (hN : 0 ≤ N) (_hvolQ : 0 ≤ volQ)
    (_hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hlow : (1 - η) * (1 + s₁) ≤ 1 - θ / 2)
    (hupp : 1 + s₂ ≤ (1 + η) * (1 - θ / 2))
    (hA : (1 - θ / 2) * N ≤ volQ')
    (hBC : (1 - θ / 2) * volQ'' ≤ N)
    (hup : volQ' ≤ (1 + s₁) * volQ)
    (hdn : volQ ≤ (1 + s₂) * volQ'') :
    (1 - η) * N ≤ volQ ∧ volQ ≤ (1 + η) * N := by
  have hd : (0:ℝ) < 1 - θ / 2 := by linarith
  have hs : (0:ℝ) < 1 + s₁ := by linarith
  constructor
  · -- `(1−η)(1+s₁)N ≤ (1−θ/2)N ≤ volQ' ≤ (1+s₁)volQ`, then cancel `1+s₁`
    have h1 : (1 - η) * (1 + s₁) * N ≤ (1 - θ / 2) * N :=
      mul_le_mul_of_nonneg_right hlow hN
    have h2 : (1 - η) * (1 + s₁) * N ≤ (1 + s₁) * volQ := le_trans h1 (le_trans hA hup)
    nlinarith
  · -- `(1−θ/2)volQ ≤ (1+s₂)(1−θ/2)volQ'' ≤ (1+s₂)N ≤ (1+η)(1−θ/2)N`, then cancel
    have hs2 : (0:ℝ) ≤ 1 + s₂ := by linarith
    have h1 : (1 - θ / 2) * volQ ≤ (1 - θ / 2) * ((1 + s₂) * volQ'') :=
      mul_le_mul_of_nonneg_left hdn hd.le
    have h2 : (1 - θ / 2) * ((1 + s₂) * volQ'') ≤ (1 + s₂) * N := by
      have := mul_le_mul_of_nonneg_left hBC hs2
      nlinarith
    have h3 : (1 + s₂) * N ≤ (1 + η) * (1 - θ / 2) * N :=
      mul_le_mul_of_nonneg_right hupp hN
    nlinarith

/-! ## Measurability and finiteness of the bodies -/

namespace FacetSystem

variable (S : FacetSystem n ι F)

theorem measurableSet_body [Countable ι] (t : ℝ) : MeasurableSet (S.body t) :=
  MeasurableSet.iUnion fun i => S.measurableSet_piece t i

theorem volume_body_ne_top [Fintype ι] {t : ℝ} (hfin : ∀ i, volume (S.piece t i) ≠ ⊤) :
    volume (S.body t) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_iUnion_fintype_le volume (fun i => S.piece t i))
  exact (ENNReal.sum_lt_top.2 fun i _ => (hfin i).lt_top).ne

/-- An inflated piece still has finite volume: it sits inside a homothety of the
original one. -/
theorem volume_piece_inflated_ne_top (cen : ι → Space n) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (i : ι) (hball : ∀ j, S.part j = i → γ * S.w j ≤ S.b j - S.f j (cen i))
    (hfin : volume (S.piece 0 i) ≠ ⊤) :
    volume (S.piece κ i) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
    (S.volume_piece_inflated_le_zero cen hγ hκ i hball)

/-- A piece with an inscribed ball has positive volume — which is what makes the
`claim:cl` divisions legitimate. -/
theorem volume_piece_pos (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    {γ t : ℝ} (hγ : 0 < γ) {cen : Space n} {i : ι}
    (hball : ∀ j, S.part j = i → γ * S.w j ≤ S.b j + t * S.w j - S.f j cen) :
    0 < volume (S.piece t i) :=
  lt_of_lt_of_le (Metric.measure_ball_pos volume cen hγ)
    (measure_mono (S.ball_subset_piece Aof hf hw hball))

/-- The paper's `A_j·p − A_j·x`, in coefficient form. -/
theorem form_sub_eq_sum (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k) (j : F) (p x : Space n) :
    S.f j p - S.f j x = ∑ k, Aof j k * (p k - x k) := by
  rw [hf, hf, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## The two summed forms of `claim:cl`, over the actual sets -/

/-- **`claim:cl`(a), summed.** Every finite set of lattice points of the body has
`(1 − θ/2)·|T| ≤ vol Q'`. Applied to *all* of them it is `hA` of
`Ttc.nonconv_recentred_general`; applied to an arbitrary finite subset it is what
makes `Q ∩ ℤⁿ` finite in the first place. -/
theorem card_le_of_claim_a [Fintype F] (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    (hAnz : ∀ j, 0 < ∑ k, Aof j k ^ 2)
    {θ r κ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 1 ≤ r) (hcard : (Fintype.card F : ℝ) ≤ r)
    (hκ : κ = Real.sqrt (2 * Real.log (4 / θ)) + Real.sqrt (2 * Real.log r))
    (hmeas : MeasurableSet (S.body κ)) (hpos : 0 < (volume (S.body κ)).toReal)
    (hfin : volume (S.body κ) ≠ ⊤)
    (T : Finset (Fin n → ℤ)) (hT : ∀ z ∈ T, latPt z ∈ S.body 0) :
    (1 - θ / 2) * (T.card : ℝ) ≤ (volume (S.body κ)).toReal := by
  classical
  refine sum_lower_of_claim_a hpos T (fun z => roundProb (prodKernel n) (S.body κ) (latPt z))
    ?_ (sum_roundProb_le_one hmeas T hpos hfin)
  intro z hz
  have hx : latPt z ∈ S.body 0 := hT z hz
  have hcover : (prodKernel n).supp (latPt z) \ S.body κ
      ⊆ ⋃ j ∈ (Finset.univ : Finset F),
        {p : Space n | (Real.sqrt (2 * Real.log (4 / θ)) + Real.sqrt (2 * Real.log r))
              * coeffNorm (Aof j) ≤ ∑ k, Aof j k * (p k - (latPt z) k)} := by
    intro p hp
    obtain ⟨j, hj⟩ := cover_of_notMem_body S hx hp.2
    refine Set.mem_biUnion (Finset.mem_univ j) ?_
    simp only [Set.mem_setOf_eq]
    rw [← hκ, ← hw j, ← S.form_sub_eq_sum Aof hf j p (latPt z)]
    exact hj
  have hcl := prodKernel_claim_cl_a (latPt z) hmeas (Finset.univ : Finset F) Aof
    hθ hθ1 hr (by simpa using hcard) ENNReal.toReal_nonneg (fun j _ => hAnz j) hcover
  refine le_trans ?_ hcl
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hpos.le)

/-- **`claim:cl`(b)+(c), summed.** `(1 − θ/2)·vol Q'' ≤ |T|` whenever `T` contains
every lattice point of the body. This is `hBC` of
`Ttc.nonconv_recentred_general`. -/
theorem deflated_le_card [Fintype F] (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    (hAnz : ∀ j, 0 < ∑ k, Aof j k ^ 2)
    {θ r κ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 1 ≤ r) (hcard : (Fintype.card F : ℝ) ≤ r)
    (hκ : κ = Real.sqrt (2 * Real.log (4 / θ)) + Real.sqrt (2 * Real.log r))
    (hmeas : MeasurableSet (S.body (-κ))) (hpos : 0 < (volume (S.body (-κ))).toReal)
    (hfin : volume (S.body (-κ)) ≠ ⊤)
    (T : Finset (Fin n → ℤ)) (hT : ∀ z, latPt z ∈ S.body 0 → z ∈ T) :
    (1 - θ / 2) * (volume (S.body (-κ))).toReal ≤ (T.card : ℝ) := by
  classical
  refine sum_upper_of_claim_bc hpos T (fun z => roundProb (prodKernel n) (S.body (-κ)) (latPt z))
    ?_ (fun z _ => claim_cl_c (prodKernel n) _ _ hpos.le)
  have hb := prodKernel_claim_cl_b S Aof hf hw hAnz hθ hθ1 hr hcard hκ T hT hmeas hpos hfin
  linarith

end FacetSystem

/-- The upper-bound arithmetic at the deflated shell loss `η/8`. -/
theorem recentred_upper_arith_deflated {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    1 + η / 8 ≤ (1 + η) * (1 - η / 4) := by nlinarith

/-! ## `lem:nonconv`, assembled -/

set_option maxHeartbeats 1000000 in
/-- **`lem:nonconv` for an actual facet system, with nothing assumed.**

Hypotheses: the facets are genuine linear constraints with nonzero normals, each
polytope contains an `ℓ₂`-ball of radius `γ` about its own centre (the paper's
hypothesis, `Ttc.FacetSystem.facet_of_ball_subset` turning it into the facet form
the proof uses), each polytope has finite volume, and the counts `m`, `r` bound
the family. Conclusion: the paper's `lem:nonconv`, at `η = ε/8`, about the body's
own integer-point count. -/
theorem FacetSystem.nonconv_of_ball [Fintype ι] [Fintype F] (S : FacetSystem n ι F)
    (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    (hAnz : ∀ j, 0 < ∑ k, Aof j k ^ 2)
    (P : Params) (hn : P.n = n)
    (hm : (Fintype.card ι : ℝ) ≤ P.m) (hr : (Fintype.card F : ℝ) ≤ P.r)
    (cen : ι → Space n)
    (hball : ∀ i, Metric.ball (cen i) P.gamma ⊆ S.piece 0 i)
    (hfin : ∀ i, volume (S.piece 0 i) ≠ ⊤) :
    (1 - P.eta) * ((S.body 0 ∩ intLattice n).ncard : ℝ) ≤ (volume (S.body 0)).toReal ∧
      (volume (S.body 0)).toReal ≤ (1 + P.eta) * ((S.body 0 ∩ intLattice n).ncard : ℝ) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hbody : S.body 0 = (∅ : Set (Space n)) := by
      rw [FacetSystem.body]; exact Set.iUnion_of_empty _
    rw [hbody]
    simp
  obtain ⟨i₀⟩ := hι
  -- the parameters
  have hη0 : 0 < P.eta := P.eta_pos
  have hη1 : P.eta ≤ 1 := P.eta_le_one
  have hγ : 0 < P.gamma := P.gamma_pos
  have hκ0 : 0 ≤ P.kappa := P.kappa_nonneg
  have hκγ : P.kappa < P.gamma := lt_of_le_of_lt P.kappa_le_gamma_half (by linarith)
  have hmpos : (0:ℝ) < P.m := by
    have : (1:ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.hm
    linarith
  have hθ0 : (0:ℝ) < P.eta / 2 := by linarith
  have hθ1 : P.eta / 2 ≤ 1 := by linarith
  have hκeq : P.kappa
      = Real.sqrt (2 * Real.log (4 / (P.eta / 2))) + Real.sqrt (2 * Real.log P.r) := by
    have h8 : (8:ℝ) / P.eta = 4 / (P.eta / 2) := by field_simp; norm_num
    rw [Params.kappa, h8]
  -- the facet form of the inscribed ball
  have hbf : ∀ i, ∀ j, S.part j = i → P.gamma * S.w j ≤ S.b j - S.f j (cen i) :=
    fun i j hj => S.facet_of_ball_subset Aof hf hw hγ (hball i) j hj
  -- finiteness
  have hfinκ : ∀ i, volume (S.piece P.kappa i) ≠ ⊤ :=
    fun i => S.volume_piece_inflated_ne_top cen hγ hκ0 i (hbf i) (hfin i)
  have hfinnκ : ∀ i, volume (S.piece (-P.kappa) i) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top (hfin i) (measure_mono (S.piece_mono (by linarith) i))
  have htopκ : volume (S.body P.kappa) ≠ ⊤ := S.volume_body_ne_top hfinκ
  have htop0 : volume (S.body 0) ≠ ⊤ := S.volume_body_ne_top hfin
  have htopnκ : volume (S.body (-P.kappa)) ≠ ⊤ := S.volume_body_ne_top hfinnκ
  -- positivity: the deflated body contains a ball of radius `γ − κ`
  have hposnκ : 0 < volume (S.body (-P.kappa)) := by
    refine lt_of_lt_of_le ?_ (measure_mono (S.piece_subset_body (-P.kappa) i₀))
    refine S.volume_piece_pos Aof hf hw (γ := P.gamma - P.kappa) (by linarith)
      (cen := cen i₀) ?_
    intro j hj
    have h := hbf i₀ j hj
    nlinarith [S.w_nonneg j]
  have hposκ : 0 < volume (S.body P.kappa) :=
    lt_of_lt_of_le hposnκ (measure_mono (S.body_mono (by linarith)))
  have hposκr : 0 < (volume (S.body P.kappa)).toReal := ENNReal.toReal_pos hposκ.ne' htopκ
  have hposnκr : 0 < (volume (S.body (-P.kappa))).toReal :=
    ENNReal.toReal_pos hposnκ.ne' htopnκ
  -- the lattice points, as a `Finset`
  have hcardle : ∀ T : Finset (Fin n → ℤ), (↑T : Set (Fin n → ℤ)) ⊆ {z | latPt z ∈ S.body 0} →
      (T.card : ℝ) ≤ (volume (S.body P.kappa)).toReal / (1 - P.eta / 2 / 2) := by
    intro T hT
    have h := S.card_le_of_claim_a Aof hf hw hAnz hθ0 hθ1 P.hr hr hκeq
      (S.measurableSet_body P.kappa) hposκr htopκ T (fun z hz => hT hz)
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - P.eta / 2 / 2)]
    linarith
  have hEfin : {z : Fin n → ℤ | latPt z ∈ S.body 0}.Finite :=
    finite_of_forall_finset_card_le hcardle
  have hTmem : ∀ z, z ∈ hEfin.toFinset ↔ latPt z ∈ S.body 0 := by
    intro z; rw [Set.Finite.mem_toFinset]; rfl
  have hEcard : {z : Fin n → ℤ | latPt z ∈ S.body 0}.ncard = hEfin.toFinset.card :=
    Set.ncard_eq_toFinset_card _ hEfin
  have hNcard : ((S.body 0 ∩ intLattice n).ncard : ℝ) = (hEfin.toFinset.card : ℝ) := by
    rw [ncard_inter_intLattice, hEcard]
  -- the two summed forms of `claim:cl`
  have hA := S.card_le_of_claim_a Aof hf hw hAnz hθ0 hθ1 P.hr hr hκeq
    (S.measurableSet_body P.kappa) hposκr htopκ hEfin.toFinset (fun z hz => (hTmem z).1 hz)
  have hBC := S.deflated_le_card Aof hf hw hAnz hθ0 hθ1 P.hr hr hκeq
    (S.measurableSet_body (-P.kappa)) hposnκr htopnκ hEfin.toFinset (fun z hz => (hTmem z).2 hz)
  -- the two shell bounds
  have hKpos : (0:ℝ) ≤ P.kappa / P.gamma := div_nonneg hκ0 hγ.le
  have hup : (volume (S.body P.kappa)).toReal
      ≤ (1 + P.eta / 16) * (volume (S.body 0)).toReal := by
    have h1 := S.volume_body_inflated_le cen hγ hκ0 hbf hfinκ
    have h2 : (1 + P.kappa / P.gamma) ^ n ≤ 1 + (P.eta / 8) / (2 * P.m) := by
      have h := P.shell_factor_bound
      rw [hn] at h
      refine le_trans h (le_of_eq ?_)
      field_simp
      ring
    have hK1 : (1:ℝ) ≤ (1 + P.kappa / P.gamma) ^ n := one_le_pow₀ (by linarith)
    have h3 := shell_factor_le (m := P.m) (K := (1 + P.kappa / P.gamma) ^ n)
      (η := P.eta / 8) hmpos h2
    have h4 : 1 + (Fintype.card ι : ℝ) * ((1 + P.kappa / P.gamma) ^ n - 1)
        ≤ 1 + P.eta / 16 := by nlinarith
    calc (volume (S.body P.kappa)).toReal
        ≤ (1 + (Fintype.card ι : ℝ) * ((1 + P.kappa / P.gamma) ^ n - 1))
            * (volume (S.body 0)).toReal := h1
      _ ≤ (1 + P.eta / 16) * (volume (S.body 0)).toReal :=
          mul_le_mul_of_nonneg_right h4 ENNReal.toReal_nonneg
  have hdn : (volume (S.body 0)).toReal
      ≤ (1 + P.eta / 8) * (volume (S.body (-P.kappa))).toReal := by
    have h1 := S.volume_body_deflated_le cen hκ0 hκγ hbf hfin
    have hKpos' : (0:ℝ) ≤ P.kappa / (P.gamma - P.kappa) :=
      div_nonneg hκ0 (by linarith)
    have h2 : (1 + P.kappa / (P.gamma - P.kappa)) ^ n ≤ 1 + (P.eta / 4) / (2 * P.m) := by
      have h := P.shell_factor_bound_deflated
      rw [hn] at h
      refine le_trans h (le_of_eq ?_)
      field_simp
      ring
    have hK1 : (1:ℝ) ≤ (1 + P.kappa / (P.gamma - P.kappa)) ^ n := one_le_pow₀ (by linarith)
    have h3 := shell_factor_le (m := P.m) (K := (1 + P.kappa / (P.gamma - P.kappa)) ^ n)
      (η := P.eta / 4) hmpos h2
    have h4 : 1 + (Fintype.card ι : ℝ) * ((1 + P.kappa / (P.gamma - P.kappa)) ^ n - 1)
        ≤ 1 + P.eta / 8 := by nlinarith
    calc (volume (S.body 0)).toReal
        ≤ (1 + (Fintype.card ι : ℝ) * ((1 + P.kappa / (P.gamma - P.kappa)) ^ n - 1))
            * (volume (S.body (-P.kappa))).toReal := h1
      _ ≤ (1 + P.eta / 8) * (volume (S.body (-P.kappa))).toReal :=
          mul_le_mul_of_nonneg_right h4 ENNReal.toReal_nonneg
  -- assemble
  rw [hNcard]
  refine nonconv_recentred_general (Nat.cast_nonneg _) ENNReal.toReal_nonneg hθ0 hθ1
    (by linarith) (by linarith) ?_ ?_ hA hBC hup hdn
  · have := recentred_lower_arith hη0 hη1
    linarith
  · have := recentred_upper_arith_deflated hη0 hη1
    linarith

end Ttc

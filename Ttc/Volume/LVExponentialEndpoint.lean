/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.LVExponentialTail
import Mathlib.Analysis.Complex.Exponential

namespace Ttc.CVAdaptive

open MeasureTheory Set

/-- The endpoint expression in LV07, equation (8).  Up to the positive factor `gamma`,
this is an antiderivative of `(x^2-1) * exp (gamma*x)`. -/
noncomputable def lvExpEndpoint (gamma x : Real) : Real :=
  Real.exp (gamma * x) * (x ^ 2 - 2 * x / gamma + 2 / gamma ^ 2 - 1)

theorem hasDerivAt_lvExpEndpoint {gamma : Real} (hgamma : gamma ≠ 0) (x : Real) :
    HasDerivAt (lvExpEndpoint gamma)
      (gamma * Real.exp (gamma * x) * (x ^ 2 - 1)) x := by
  have hlin : HasDerivAt (fun y : Real ↦ gamma * y) gamma x := hasDerivAt_const_mul gamma
  have hexp : HasDerivAt (fun y : Real ↦ Real.exp (gamma * y))
      (gamma * Real.exp (gamma * x)) x := by
    have h := (Real.hasDerivAt_exp (gamma * x)).comp x hlin
    exact (by simpa only [Function.comp_def] using h.congr_deriv (mul_comm _ _))
  have hpoly : HasDerivAt
      (fun y : Real ↦ y ^ 2 - 2 * y / gamma + 2 / gamma ^ 2 - 1)
      (2 * x - 2 / gamma) x := by
    have hterm : HasDerivAt (fun y : Real ↦ 2 * y / gamma) (2 / gamma) x := by
      exact (hasDerivAt_const_mul (x := x) (2 : Real)).div_const gamma
    have h := ((((hasDerivAt_id x).pow 2).sub hterm).add_const
      (2 / gamma ^ 2)).sub_const 1
    simpa only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one] using h
  unfold lvExpEndpoint
  exact (hexp.mul hpoly).congr_deriv (by field_simp [hgamma]; ring)

theorem lvExpEndpoint_deriv {gamma : Real} (hgamma : gamma ≠ 0) (x : Real) :
    deriv (lvExpEndpoint gamma) x = gamma * Real.exp (gamma * x) * (x ^ 2 - 1) := by
  exact (hasDerivAt_lvExpEndpoint hgamma x).deriv

theorem intervalIntegral_sq_sub_one_mul_exp {gamma a b : Real} (hgamma : gamma ≠ 0) :
    (∫ x in a..b, (x ^ 2 - 1) * Real.exp (gamma * x)) =
      (lvExpEndpoint gamma b - lvExpEndpoint gamma a) / gamma := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y ↦ lvExpEndpoint gamma y / gamma)
        ((x ^ 2 - 1) * Real.exp (gamma * x)) x := by
    intro x _
    have h := (hasDerivAt_lvExpEndpoint hgamma x).div_const gamma
    exact h.congr_deriv (by field_simp [hgamma])
  simpa only [div_sub_div_same] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) a b)

private theorem criticalPolynomial_lt_exp {u : Real} (hu : 2 <= u) :
    (u + 1) ^ 2 + u ^ 2 * (u * (u + 2) / (u + 1)) / 2 <
      Real.exp (u * (u + 2) / (u + 1)) := by
  let y := u * (u + 2) / (u + 1)
  have hu1 : 0 < u + 1 := by linarith
  have hy : 0 <= y := by dsimp [y]; positivity
  have hsum := Real.sum_le_exp_of_nonneg hy 9
  norm_num [Finset.sum_range_succ] at hsum
  have hpoly :
      (u + 1) ^ 2 + u ^ 2 * y / 2 <
        1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 +
          y ^ 6 / 720 + y ^ 7 / 5040 + y ^ 8 / 40320 := by
    let v := u - 2
    have hv : 0 <= v := by dsimp [v]; linarith
    have hpos : 0 <
        8790016 + 641622016 * v + 2654740992 * v ^ 2 + 5134400768 * v ^ 3 +
        6054853504 * v ^ 4 + 4849360320 * v ^ 5 + 2789805760 * v ^ 6 +
        1190725504 * v ^ 7 + 384431376 * v ^ 8 + 94974368 * v ^ 9 +
        18065488 * v ^ 10 + 2648688 * v ^ 11 + 297304 * v ^ 12 +
        24976 * v ^ 13 + 1488 * v ^ 14 + 56 * v ^ 15 + v ^ 16 := by positivity
    dsimp [y, v] at *
    field_simp [hu1.ne'] at hpos ⊢
    nlinarith
  exact hpoly.trans_le (by simpa only [y] using hsum)

/-- The bespoke transcendental comparison used by LV07 after equation (9). -/
theorem lvExpEndpoint_critical_lt_one {gamma : Real} (hgamma0 : 0 < gamma)
    (hgamma1 : gamma < 1) (hcritical : -1 / (1 - gamma) <= -3) :
    lvExpEndpoint gamma (-1 / (1 - gamma)) < lvExpEndpoint gamma 1 := by
  let u := gamma / (1 - gamma)
  have hd : 0 < 1 - gamma := sub_pos.mpr hgamma1
  have hu : 0 < u := div_pos hgamma0 hd
  have hu1 : 0 < u + 1 := by positivity
  have huid : u + 1 = 1 / (1 - gamma) := by
    dsimp [u]
    field_simp [hd.ne']
    ring
  have hxid : -1 / (1 - gamma) = -(u + 1) := by
    calc
      -1 / (1 - gamma) = -(1 / (1 - gamma)) := by ring
      _ = -(u + 1) := congrArg Neg.neg huid.symm
  have hgammaid : gamma = u / (u + 1) := by
    dsimp [u]
    field_simp [hd.ne', hgamma0.ne']
    ring
  have hu2 : 2 <= u := by
    rw [hxid] at hcritical
    linarith
  let y := u * (u + 2) / (u + 1)
  let A := (u + 1) ^ 2 + u ^ 2 * y / 2
  let B₁ := 2 * (u + 1) / u ^ 2
  let Bc := (u + 1) ^ 2 + 2 * (u + 1) / (u / (u + 1)) +
    2 / (u / (u + 1)) ^ 2 - 1
  have hyid : y = u + gamma := by
    dsimp [y]
    rw [hgammaid]
    field_simp [hu1.ne']
    ring
  have hA := criticalPolynomial_lt_exp hu2
  change A < Real.exp y at hA
  rw [hyid, Real.exp_add] at hA
  have hB₁0 : 0 < B₁ := by dsimp [B₁]; positivity
  have hBc : Bc = B₁ * A := by
    dsimp [Bc, B₁, A, y]
    field_simp [hu.ne', hu1.ne']
    ring
  have hscaled := mul_lt_mul_of_pos_left hA (mul_pos (Real.exp_pos (-u)) hB₁0)
  rw [hgammaid] at hscaled
  have hexpcancel : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hxid, hgammaid]
  dsimp [lvExpEndpoint]
  rw [show u / (u + 1) * -(u + 1) = -u by field_simp [hu1.ne'],
    show u / (u + 1) * 1 = u / (u + 1) by ring]
  have hleft : (-(u + 1)) ^ 2 - 2 * -(u + 1) / (u / (u + 1)) +
      2 / (u / (u + 1)) ^ 2 - 1 = Bc := by
    dsimp [Bc]
    ring
  have hright : (1 : Real) ^ 2 - 2 * 1 / (u / (u + 1)) +
      2 / (u / (u + 1)) ^ 2 - 1 = B₁ := by
    dsimp [B₁]
    field_simp [hu.ne', hu1.ne']
    ring
  rw [hleft, hright]
  rw [hBc]
  calc
    Real.exp (-u) * (B₁ * A) = (Real.exp (-u) * B₁) * A := by ring
    _ < (Real.exp (-u) * B₁) *
        (Real.exp u * Real.exp (u / (u + 1))) := hscaled
    _ = Real.exp (u / (u + 1)) * B₁ := by
      calc
        _ = (Real.exp (-u) * Real.exp u) * B₁ * Real.exp (u / (u + 1)) := by ring
        _ = _ := by rw [hexpcancel, one_mul]; ring

/-- The first source comparison after equation (9): `g(gamma,2)>g(gamma,-1)`. -/
theorem lvExpEndpoint_neg_one_lt_two {gamma : Real} (hgamma : 0 < gamma) :
    lvExpEndpoint gamma (-1) < lvExpEndpoint gamma 2 := by
  have hsum := Real.sum_le_exp_of_nonneg (show 0 <= 3 * gamma by positivity) 5
  norm_num [Finset.sum_range_succ] at hsum
  have hpoly : 2 * gamma + 2 <
      (1 + 3 * gamma + (3 * gamma) ^ 2 / 2 + (3 * gamma) ^ 3 / 6 +
        (3 * gamma) ^ 4 / 24) * (3 * gamma ^ 2 - 4 * gamma + 2) := by
    have hsq : 0 < gamma ^ 4 := pow_pos hgamma 4
    have h6 : 0 <= gamma ^ 6 := by positivity
    nlinarith
  have hfactor : 0 < 3 * gamma ^ 2 - 4 * gamma + 2 := by nlinarith [sq_nonneg (gamma - 2 / 3)]
  have hmain : 2 * gamma + 2 < Real.exp (3 * gamma) *
      (3 * gamma ^ 2 - 4 * gamma + 2) :=
    hpoly.trans_le (mul_le_mul_of_nonneg_right hsum hfactor.le)
  have hscale := mul_lt_mul_of_pos_left hmain (mul_pos (Real.exp_pos (-gamma))
    (sq_pos_of_pos hgamma))
  have hexp : Real.exp (-gamma) * Real.exp (3 * gamma) = Real.exp (2 * gamma) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscaled : Real.exp (-gamma) * (2 * gamma + 2) <
      Real.exp (2 * gamma) * (3 * gamma ^ 2 - 4 * gamma + 2) := by
    calc
      _ < Real.exp (-gamma) *
          (Real.exp (3 * gamma) * (3 * gamma ^ 2 - 4 * gamma + 2)) :=
        mul_lt_mul_of_pos_left hmain (Real.exp_pos _)
      _ = _ := by rw [← mul_assoc, hexp]
  unfold lvExpEndpoint
  norm_num
  field_simp [hgamma.ne']
  convert hscaled using 1 <;> ring

private theorem lvExpEndpoint_strictMonoOn_Iic {gamma : Real} (hgamma : 0 < gamma) :
    StrictMonoOn (lvExpEndpoint gamma) (Set.Iic (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic (-1)) (by unfold lvExpEndpoint; fun_prop)
  intro x hx
  rw [interior_Iic] at hx
  rw [lvExpEndpoint_deriv hgamma.ne']
  have hx' : x < -1 := hx
  have hs : 0 < x ^ 2 - 1 := by
    nlinarith [mul_pos (by linarith : 0 < -1 - x) (by linarith : 0 < 1 - x)]
  positivity

private theorem lvExpEndpoint_strictAntiOn_Icc {gamma : Real} (hgamma : 0 < gamma) :
    StrictAntiOn (lvExpEndpoint gamma) (Set.Icc (-1) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (-1) 1) (by unfold lvExpEndpoint; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rcases hx with ⟨hxL, hxR⟩
  rw [lvExpEndpoint_deriv hgamma.ne']
  have hs : x ^ 2 - 1 < 0 := by
    nlinarith [mul_pos (by linarith : 0 < x + 1) (by linarith : 0 < 1 - x)]
  exact mul_neg_of_pos_of_neg (mul_pos hgamma (Real.exp_pos _)) hs

private theorem lvExpEndpoint_strictMonoOn_Ici {gamma : Real} (hgamma : 0 < gamma) :
    StrictMonoOn (lvExpEndpoint gamma) (Set.Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) (by unfold lvExpEndpoint; fun_prop)
  intro x hx
  rw [interior_Ici] at hx
  have hx1 : 1 < x := hx
  rw [lvExpEndpoint_deriv hgamma.ne']
  have hs : 0 < x ^ 2 - 1 := by
    nlinarith [mul_pos (by linarith : 0 < x - 1) (by linarith : 0 < x + 1)]
  positivity

private theorem lvExpEndpoint_one_le_of_nonneg {gamma b : Real} (hgamma : 0 < gamma)
    (hb : 0 <= b) : lvExpEndpoint gamma 1 <= lvExpEndpoint gamma b := by
  by_cases hb1 : b <= 1
  · exact (lvExpEndpoint_strictAntiOn_Icc hgamma).antitoneOn
      (by exact ⟨by linarith, hb1⟩) (by constructor <;> norm_num) hb1
  · exact (lvExpEndpoint_strictMonoOn_Ici hgamma).monotoneOn
      (by norm_num) (by exact le_of_not_ge hb1) (le_of_not_ge hb1)

private theorem lvExpEndpoint_neg_three_lt_one {gamma : Real} (hgamma : 0 < gamma)
    (hgamma23 : gamma <= 2 / 3) :
    lvExpEndpoint gamma (-3) < lvExpEndpoint gamma 1 := by
  have hsum := Real.sum_le_exp_of_nonneg (show 0 <= 4 * gamma by positivity) 10
  norm_num [Finset.sum_range_succ] at hsum
  have hp (k : Nat) : gamma ^ k <= (2 / 3 : Real) ^ k :=
    pow_le_pow_left₀ hgamma.le hgamma23 k
  have hpoly : 4 * gamma ^ 2 + 3 * gamma + 1 <
      (1 + 4 * gamma + (4 * gamma) ^ 2 / 2 + (4 * gamma) ^ 3 / 6 +
        (4 * gamma) ^ 4 / 24 + (4 * gamma) ^ 5 / 120 + (4 * gamma) ^ 6 / 720 +
        (4 * gamma) ^ 7 / 5040 + (4 * gamma) ^ 8 / 40320 +
        (4 * gamma) ^ 9 / 362880) * (1 - gamma) := by
    have h3 : 0 < gamma ^ 3 := pow_pos hgamma 3
    have hQ : 0 < 967680 - 774144 * gamma ^ 2 - 1032192 * gamma ^ 3 -
        884736 * gamma ^ 4 - 589824 * gamma ^ 5 - 327680 * gamma ^ 6 -
        262144 * gamma ^ 7 := by
      nlinarith [hp 2, hp 3, hp 4, hp 5, hp 6, hp 7]
    nlinarith
  have hmain : 4 * gamma ^ 2 + 3 * gamma + 1 < Real.exp (4 * gamma) * (1 - gamma) :=
    hpoly.trans_le (mul_le_mul_of_nonneg_right hsum (by linarith))
  have hscaled := mul_lt_mul_of_pos_left hmain
    (mul_pos (Real.exp_pos (-3 * gamma)) (by norm_num : (0 : Real) < 2))
  have hexp : Real.exp (-3 * gamma) * Real.exp (4 * gamma) = Real.exp gamma := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : Real.exp (-3 * gamma) * (2 * (4 * gamma ^ 2 + 3 * gamma + 1)) <
      Real.exp gamma * (2 * (1 - gamma)) := by
    calc
      _ < Real.exp (-3 * gamma) * (2 * (Real.exp (4 * gamma) * (1 - gamma))) :=
        mul_lt_mul_of_pos_left (by nlinarith [hmain]) (Real.exp_pos _)
      _ = 2 * (Real.exp (-3 * gamma) * Real.exp (4 * gamma)) * (1 - gamma) := by ring
      _ = _ := by rw [hexp]; ring
  unfold lvExpEndpoint
  norm_num
  field_simp [hgamma.ne']
  convert hs using 1 <;> ring

/-- The complete endpoint implication following the exponential-extremizer reduction in LV07
Lemma 5.7.  This is equations (6)--(9) and the two transcendental comparisons in the source. -/
theorem lv_exponential_endpoint_rate {gamma a b : Real} (hgamma : 0 < gamma)
    (ha : a <= -3) (hb : 0 <= b)
    (hmoment : (∫ x in a..b, x ^ 2 * Real.exp (gamma * x)) <=
      ∫ x in a..b, Real.exp (gamma * x)) :
    (a + 1) / a <= gamma := by
  have hab : a <= b := by linarith
  have hint : IntervalIntegrable (fun x : Real ↦ Real.exp (gamma * x)) volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b
  have hdiff : (∫ x in a..b, (x ^ 2 - 1) * Real.exp (gamma * x)) <= 0 := by
    rw [show (fun x : Real ↦ (x ^ 2 - 1) * Real.exp (gamma * x)) =
      fun x ↦ x ^ 2 * Real.exp (gamma * x) - Real.exp (gamma * x) by funext x; ring,
      intervalIntegral.integral_sub (hint.continuousOn_mul (by fun_prop)) hint]
    linarith
  rw [intervalIntegral_sq_sub_one_mul_exp hgamma.ne'] at hdiff
  have hba : lvExpEndpoint gamma b <= lvExpEndpoint gamma a := by
    rcases (div_nonpos_iff.mp hdiff) with h | h
    · linarith
    · linarith
  have hb2 : b < 2 := by
    by_contra hnot
    have h2b : 2 <= b := le_of_not_gt hnot
    have hga : lvExpEndpoint gamma a <= lvExpEndpoint gamma (-1) := by
      exact (lvExpEndpoint_strictMonoOn_Iic hgamma).monotoneOn (by simp; linarith)
        (by simp) (by linarith)
    have h2 : lvExpEndpoint gamma 2 <= lvExpEndpoint gamma b := by
      exact (lvExpEndpoint_strictMonoOn_Ici hgamma).monotoneOn (by norm_num)
        (by simp; linarith) h2b
    linarith [lvExpEndpoint_neg_one_lt_two hgamma]
  have ha0 : a < 0 := by linarith
  by_cases hgamma1 : 1 <= gamma
  · have : (a + 1) / a <= 1 := by
      rw [div_le_one_of_neg ha0]
      linarith
    exact this.trans hgamma1
  · have hgammaLt : gamma < 1 := lt_of_not_ge hgamma1
    have hgamma_gt23 : 2 / 3 < gamma := by
      by_contra hnot
      have hgamma23 : gamma <= 2 / 3 := le_of_not_gt hnot
      have hga3 : lvExpEndpoint gamma a <= lvExpEndpoint gamma (-3) := by
        exact (lvExpEndpoint_strictMonoOn_Iic hgamma).monotoneOn (by simp; linarith)
          (by norm_num) ha
      have h31 := lvExpEndpoint_neg_three_lt_one hgamma hgamma23
      have h1b := lvExpEndpoint_one_le_of_nonneg hgamma hb
      exact (not_lt_of_ge (h1b.trans hba)) (hga3.trans_lt h31)
    let c := -1 / (1 - gamma)
    have hc3 : c <= -3 := by
      dsimp [c]
      rw [div_le_iff₀ (sub_pos.mpr hgammaLt)]
      nlinarith
    have hca : c <= a := by
      by_contra hnot
      have hac : a < c := lt_of_not_ge hnot
      have hca1 : c <= -1 := hc3.trans (by norm_num)
      have hlt : lvExpEndpoint gamma a < lvExpEndpoint gamma c := by
        exact lvExpEndpoint_strictMonoOn_Iic hgamma
          (show a ∈ Set.Iic (-1) by exact ha.trans (by norm_num)) hca1 hac
      have hc1 := lvExpEndpoint_critical_lt_one hgamma hgammaLt hc3
      have h1b := lvExpEndpoint_one_le_of_nonneg hgamma hb
      exact (not_lt_of_ge (h1b.trans hba)) (hlt.trans hc1)
    dsimp [c] at hca
    rw [div_le_iff_of_neg ha0]
    have hpos : 0 < 1 - gamma := sub_pos.mpr hgammaLt
    rw [div_le_iff₀ hpos] at hca
    nlinarith

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.lvExpEndpoint_critical_lt_one
#print axioms Ttc.CVAdaptive.lvExpEndpoint_neg_one_lt_two
#print axioms Ttc.CVAdaptive.lv_exponential_endpoint_rate

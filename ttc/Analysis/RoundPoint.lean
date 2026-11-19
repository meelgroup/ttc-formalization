import ttc.Analysis.MembershipCost
import ArlibCommunity.Algorithms.KV97.Analysis.RoundLaw

/-! # The rounding program is KV97's randomized rounding

`roundPoint` (`Model/Prelude.lean`) rounds coordinate `pᵢ` to `⌊pᵢ⌋ + [vᵢ < pᵢ − ⌊pᵢ⌋]` for a
uniform `vᵢ ∈ [0, 1]`. This file proves that it costs exactly `5n` and that its law
(`roundPointLaw`) is arlib's KV97 rounding law `roundLaw`. -/

open MeasureTheory Set
open scoped ENNReal

namespace ttc

namespace RoundPoint

open ArlibCommunity.Algorithms.KV97

theorem roundPoint_value {n : Nat} (p : Fin n → Real) (v : Fin n → Real) :
    (roundPoint n p v).value = fun i => ⌊p i⌋ + if v i < p i - ⌊p i⌋ then 1 else 0 := by
  funext i
  simp only [roundPoint, Counted.forEach, Counted.bind_eq, Counted.andThen_value, Counted.draw,
    Counted.floor, Counted.sub, Counted.lt, Counted.addInt, decide_eq_true_eq]

/-- **Rounding costs exactly `5n` operations**: per coordinate, one random number, `⌊·⌋`, a
subtraction, a comparison and an addition. -/
theorem roundCost_eq (n : Nat) : roundCost n = 5 * n := by
  have hcost : ∀ (p v : Fin n → Real), (roundPoint n p v).cost = 5 * n := by
    intro p v
    simp only [roundPoint, Counted.forEach, Counted.bind_eq, Counted.andThen_cost, Counted.draw,
      Counted.floor, Counted.sub, Counted.lt, Counted.addInt, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  simp only [roundCost, hcost, ciSup_const]

/-- One coordinate: `⌊a⌋ + [v < a − ⌊a⌋]` with `v` uniform on `[0, 1]` has KV97's
one-dimensional rounding law. -/
theorem map_unit_eq_tentInt (a : Real) :
    (volume.restrict (Icc (0 : Real) 1)).map
        (fun v : Real => ⌊a⌋ + if v < a - ⌊a⌋ then (1 : Int) else 0) = tentInt a := by
  have hf : Measurable (fun v : Real => ⌊a⌋ + if v < a - ⌊a⌋ then (1 : Int) else 0) :=
    measurable_const.add (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  have h0 : (0 : Real) ≤ a - ⌊a⌋ := by linarith [Int.floor_le a]
  have h1 : a - ⌊a⌋ < 1 := by linarith [Int.lt_floor_add_one a]
  refine Measure.ext_of_singleton fun m => ?_
  rw [Measure.map_apply hf (measurableSet_singleton m), tentInt_singleton,
    Measure.restrict_apply (hf (measurableSet_singleton m))]
  by_cases hup : m = ⌊a⌋ + 1
  · subst hup
    have hset : (fun v : Real => ⌊a⌋ + if v < a - ⌊a⌋ then (1 : Int) else 0) ⁻¹' {⌊a⌋ + 1} ∩
        Icc 0 1 = Ico 0 (a - ⌊a⌋) := by
      ext v
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨hv, hv0, hv1⟩
        refine ⟨hv0, ?_⟩
        by_contra hlt
        rw [if_neg hlt] at hv
        omega
      · rintro ⟨hv0, hvlt⟩
        exact ⟨by rw [if_pos hvlt], hv0, by linarith⟩
    rw [hset, Real.volume_Ico, sub_zero, tent_sub_floor_succ]
  · by_cases hdown : m = ⌊a⌋
    · subst hdown
      have hset : (fun v : Real => ⌊a⌋ + if v < a - ⌊a⌋ then (1 : Int) else 0) ⁻¹' {⌊a⌋} ∩
          Icc 0 1 = Icc (a - ⌊a⌋) 1 := by
        ext v
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Icc]
        constructor
        · rintro ⟨hv, hv0, hv1⟩
          refine ⟨?_, hv1⟩
          by_contra hlt
          push Not at hlt
          rw [if_pos hlt] at hv
          omega
        · rintro ⟨hvge, hv1⟩
          exact ⟨by rw [if_neg (not_lt.mpr hvge)]; simp, by linarith, hv1⟩
      rw [hset, Real.volume_Icc, tent_sub_floor]
    · have hset : (fun v : Real => ⌊a⌋ + if v < a - ⌊a⌋ then (1 : Int) else 0) ⁻¹' {m} ∩
          Icc 0 1 = ∅ := by
        ext v
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        intro hv
        split_ifs at hv <;> omega
      rw [hset, measure_empty, tent_eq_zero_of_ne_floor a m hdown hup, ENNReal.ofReal_zero]

/-- **The rounding program has KV97's rounding law.** -/
theorem roundPointLaw_eq {n : Nat} (p : EuclideanSpace Real (Fin n)) :
    roundPointLaw p = roundLaw (WithLp.ofLp p) := by
  have hval : (fun v : Fin n → Real => (roundPoint n (WithLp.ofLp p) v).value) =
      fun v i => (fun (i : Fin n) (w : Real) =>
        ⌊p i⌋ + if w < p i - ⌊p i⌋ then (1 : Int) else 0) i (v i) := by
    funext v
    rw [roundPoint_value]
  rw [roundPointLaw, hval, Measure.pi_map_pi
    (f := fun (i : Fin n) (w : Real) => ⌊p i⌋ + if w < p i - ⌊p i⌋ then (1 : Int) else 0)
    (fun i => (measurable_const.add
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)).aemeasurable)]
  simp only [map_unit_eq_tentInt]
  rfl

end RoundPoint

end ttc

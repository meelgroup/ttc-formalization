import Ttc.Exec.CVGaussianHybridAcceptedWarm

/-!
# Logarithmic envelope for the hybrid actual-path warmness recurrence

The actual seed warmness may compound across finite-retry phases.  This is harmless for
the operational mixing deadline: only its logarithm is used.  The independently drawn
fallback is charged by its survival-weighted contribution, chosen to be at most one.

This file records the resulting minimal recurrence and an explicit geometric envelope.
Reference expected cost is deliberately not part of this statement; it is evaluated on
the separate exact retained reference and therefore does not carry this warmness factor.
-/

namespace Ttc.CVHybridOperationalWarmLog

open Ttc.CVGaussianHybridAcceptedWarm
open Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVHybridSchedule
open scoped ENNReal

/-- Minimal declared actual-path warmness when the survival-weighted fallback contribution
is bounded by one. -/
noncomputable def hybridOperationalWarm
    (n : Nat) (N s0 : Real) (retries : Nat → Nat) (M0 : ENNReal) : Nat → ENNReal
  | 0 => M0
  | i + 1 =>
      (retries i : ENNReal) *
        ((16 * acceleratedSeedWarmFactor n (1 + phaseRate n N s0 i)) *
          hybridOperationalWarm n N s0 retries M0 i) + 1

/-- Real base of the geometric warmness envelope under a uniform retry cap. -/
noncomputable def hybridOperationalWarmBase (n L : Nat) : ENNReal :=
  (L : ENNReal) * (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1

theorem one_le_hybridOperationalWarm
    {n : Nat} {N s0 : Real} {retries : Nat → Nat} {M0 : ENNReal}
    (hM0 : 1 ≤ M0) : ∀ i, 1 ≤ hybridOperationalWarm n N s0 retries M0 i := by
  intro i
  cases i with
  | zero => exact hM0
  | succ i =>
      rw [hybridOperationalWarm]
      exact le_add_left le_rfl

/-- A bounded phase rate and retry count give a geometric envelope.  In the source hybrid
schedule the rate hypotheses are discharged by `1/n ≤ 1/2` in the cold block and
`adaptiveChunkRate_le_half` in the hot block. -/
theorem hybridOperationalWarm_le_pow_envelope
    {n L : Nat} {N s0 : Real} {retries : Nat → Nat} {M0 : ENNReal}
    (hM0 : 1 ≤ M0)
    (hretries : ∀ i, retries i ≤ L)
    (hrate0 : ∀ i, 0 ≤ phaseRate n N s0 i)
    (hrateHalf : ∀ i, phaseRate n N s0 i ≤ 1 / 2) :
    ∀ i, hybridOperationalWarm n N s0 retries M0 i ≤
      hybridOperationalWarmBase n L ^ i * M0 := by
  intro i
  induction i with
  | zero => simp [hybridOperationalWarm]
  | succ i ih =>
      rw [hybridOperationalWarm, pow_succ]
      have hfactor :
          acceleratedSeedWarmFactor n (1 + phaseRate n N s0 i) ≤
            ENNReal.ofReal ((2 : Real) ^ (n + 1)) := by
        apply acceleratedSeedWarmFactor_le_pow_two
        · linarith [hrate0 i]
        · linarith [hrateHalf i]
      have hretry : (retries i : ENNReal) ≤ L := by
        exact_mod_cast hretries i
      have hwarmOne := one_le_hybridOperationalWarm
        (n := n) (N := N) (s0 := s0) (retries := retries) hM0 i
      calc
        (retries i : ENNReal) *
              ((16 * acceleratedSeedWarmFactor n (1 + phaseRate n N s0 i)) *
                hybridOperationalWarm n N s0 retries M0 i) + 1 ≤
            hybridOperationalWarmBase n L *
              hybridOperationalWarm n N s0 retries M0 i := by
          unfold hybridOperationalWarmBase
          calc
            (retries i : ENNReal) *
                  ((16 * acceleratedSeedWarmFactor n
                    (1 + phaseRate n N s0 i)) *
                    hybridOperationalWarm n N s0 retries M0 i) + 1 ≤
                (L : ENNReal) *
                  ((16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) *
                    hybridOperationalWarm n N s0 retries M0 i) +
                  hybridOperationalWarm n N s0 retries M0 i := by
              gcongr
            _ = ((L : ENNReal) *
                  (16 * ENNReal.ofReal ((2 : Real) ^ (n + 1))) + 1) *
                hybridOperationalWarm n N s0 retries M0 i := by ring
        _ ≤ hybridOperationalWarmBase n L *
              (hybridOperationalWarmBase n L ^ i * M0) := by gcongr
        _ = hybridOperationalWarmBase n L ^ i * M0 *
              hybridOperationalWarmBase n L := by ac_rfl
        _ = hybridOperationalWarmBase n L ^ i *
              hybridOperationalWarmBase n L * M0 := by
          rw [mul_assoc, mul_comm M0 (hybridOperationalWarmBase n L), ← mul_assoc]

/-- `toReal` version of the geometric recurrence envelope. -/
theorem hybridOperationalWarm_toReal_le_pow
    {n L : Nat} {N s0 : Real} {retries : Nat → Nat} {M0 : ENNReal}
    (hM0 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (hretries : ∀ i, retries i ≤ L)
    (hrate0 : ∀ i, 0 ≤ phaseRate n N s0 i)
    (hrateHalf : ∀ i, phaseRate n N s0 i ≤ 1 / 2) (i : Nat) :
    (hybridOperationalWarm n N s0 retries M0 i).toReal ≤
      (hybridOperationalWarmBase n L).toReal ^ i * M0.toReal := by
  have hraw := hybridOperationalWarm_le_pow_envelope
    hM0 hretries hrate0 hrateHalf i
  have hbaseTop : hybridOperationalWarmBase n L ≠ ⊤ := by
    unfold hybridOperationalWarmBase
    exact (ENNReal.add_ne_top).2 ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top), by norm_num⟩
  have htop : hybridOperationalWarmBase n L ^ i * M0 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hbaseTop) hM0top
  have := ENNReal.toReal_mono htop hraw
  rwa [ENNReal.toReal_mul, ENNReal.toReal_pow] at this

/-- The compounding actual-path warmness contributes only an affine logarithmic term. -/
theorem log_hybridOperationalWarm_toReal_le
    {n L : Nat} {N s0 : Real} {retries : Nat → Nat} {M0 : ENNReal}
    (hM0 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (hretries : ∀ i, retries i ≤ L)
    (hrate0 : ∀ i, 0 ≤ phaseRate n N s0 i)
    (hrateHalf : ∀ i, phaseRate n N s0 i ≤ 1 / 2) (i : Nat) :
    Real.log (hybridOperationalWarm n N s0 retries M0 i).toReal ≤
      (i : Real) * Real.log (hybridOperationalWarmBase n L).toReal +
        Real.log M0.toReal := by
  have hwarmPos : 0 < (hybridOperationalWarm n N s0 retries M0 i).toReal := by
    have htop : hybridOperationalWarm n N s0 retries M0 i ≠ ⊤ := by
      apply ne_top_of_le_ne_top _
        (hybridOperationalWarm_le_pow_envelope hM0 hretries hrate0 hrateHalf i)
      exact ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (by
          unfold hybridOperationalWarmBase
          exact (ENNReal.add_ne_top).2
            ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
              (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top), by norm_num⟩)) hM0top
    exact ENNReal.toReal_pos (ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1)
        (one_le_hybridOperationalWarm hM0 i))) htop
  have hbound := hybridOperationalWarm_toReal_le_pow
    hM0 hM0top hretries hrate0 hrateHalf i
  have hlog := Real.log_le_log hwarmPos hbound
  have hbasePos : 0 < (hybridOperationalWarmBase n L).toReal := by
    apply ENNReal.toReal_pos
    · unfold hybridOperationalWarmBase
      exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1)
        (le_add_left le_rfl))
    · unfold hybridOperationalWarmBase
      exact (ENNReal.add_ne_top).2
        ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
          (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top), by norm_num⟩
  have hM0pos : 0 < M0.toReal := ENNReal.toReal_pos (ne_of_gt
    ((by norm_num : (0 : ENNReal) < 1).trans_le hM0)) hM0top
  rw [Real.log_mul (pow_ne_zero i hbasePos.ne') hM0pos.ne', Real.log_pow] at hlog
  simpa [mul_comm] using hlog

#print axioms hybridOperationalWarm_le_pow_envelope
#print axioms log_hybridOperationalWarm_toReal_le

end Ttc.CVHybridOperationalWarmLog

import Ttc.Exec.CVSwitchedSmallRateUniversalWarm
import Ttc.Volume.CVHybridSchedule

/-! A globally `1/n`-slow variance schedule reaching an arbitrary terminal scale. -/

set_option autoImplicit false

namespace Ttc.CVSlowGeometricSchedule

open Arlib.GaussianCooling
open Ttc.CVHybridSchedule

/-- Number of `1/n` geometric transitions required to grow `s0` to `N`. -/
noncomputable def slowGeometricPhases (n : Nat) (N s0 : Real) : Nat :=
  coldPhases n (s0 / N)

/-- The corresponding globally slow variance schedule. -/
noncomputable def slowGeometricSigmaSq (n : Nat) (s0 : Real) (i : Nat) : Real :=
  geomSchedule s0 (1 / (n : Real)) i

theorem slowGeometricSigmaSq_pos
    {n : Nat} (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    0 < slowGeometricSigmaSq n s0 i := by
  unfold slowGeometricSigmaSq
  exact geomSchedule_pos hs0 (by positivity) i

@[simp] theorem slowGeometricSigmaSq_succ
    (n : Nat) (s0 : Real) (i : Nat) :
    slowGeometricSigmaSq n s0 (i + 1) =
      (1 + 1 / (n : Real)) * slowGeometricSigmaSq n s0 i := by
  unfold slowGeometricSigmaSq
  rw [geomSchedule_succ]
  ring

/-- Explicit phase count: the conservative schedule pays only the expected extra
factor `n` times the logarithmic terminal variance ratio. -/
theorem slowGeometricPhases_cast_lt
    {n : Nat} (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0) :
    (slowGeometricPhases n N s0 : Real) <
      2 * (n : Real) * max 0 (Real.log (N / s0)) + 1 := by
  have h := coldPhases_cast_lt_add_one hn (s0 / N)
  unfold slowGeometricPhases
  convert h using 1
  field_simp

/-- The declared final index reaches the requested variance `N`. -/
theorem terminal_le_slowGeometricSigmaSq
    {n : Nat} (hn : 1 ≤ n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hs0N : s0 ≤ N) :
    N ≤ slowGeometricSigmaSq n s0 (slowGeometricPhases n N s0) := by
  have hratio0 : 0 < s0 / N := div_pos hs0 hN
  have hratio1 : s0 / N ≤ 1 := (div_le_one hN).2 hs0N
  have hend := one_le_coldEnd hn hratio0 hratio1
  unfold coldEnd at hend
  unfold slowGeometricPhases slowGeometricSigmaSq
  have hscale := mul_le_mul_of_nonneg_left hend hN.le
  have hs0eq : N * (s0 / N) = s0 := by field_simp
  rw [geomSchedule] at hscale ⊢
  calc
    N = N * 1 := by ring
    _ ≤ N * (s0 / N * (1 + 1 / (n : Real)) ^ coldPhases n (s0 / N)) := hscale
    _ = s0 * (1 + 1 / (n : Real)) ^ coldPhases n (s0 / N) := by
      rw [← mul_assoc, hs0eq]

#print axioms slowGeometricPhases_cast_lt
#print axioms terminal_le_slowGeometricSigmaSq

end Ttc.CVSlowGeometricSchedule

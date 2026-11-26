/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.Program

/-! Regression tests for uncharged scalar arithmetic at the numeric input boundary. -/

namespace ttcTest.Breach.NatArithmetic

noncomputable def test (x : ℕ) := ttc.Program.A.lit (x + x)

end ttcTest.Breach.NatArithmetic

/--
error: Free scalar arithmetic in ttcTest.Breach.NatArithmetic:
  ttcTest.Breach.NatArithmetic.test: HAdd.hAdd at Nat
  A program computes with numeric data only through a charged operation.
-/
#guard_msgs (whitespace := lax) in
#ttcProgramSealFixture ttcTest.Breach.NatArithmetic

namespace ttcTest.Breach.IntArithmetic

noncomputable def test (x : ℤ) := ttc.Program.A.lit (Int.mul x x)

end ttcTest.Breach.IntArithmetic

/--
error: Free scalar arithmetic in ttcTest.Breach.IntArithmetic:
  ttcTest.Breach.IntArithmetic.test: Int.mul
  A program computes with numeric data only through a charged operation.
-/
#guard_msgs (whitespace := lax) in
#ttcProgramSealFixture ttcTest.Breach.IntArithmetic

namespace ttcTest.Breach.RealArithmetic

noncomputable def test (x : ℝ) := ttc.Program.A.lit (x + x)

end ttcTest.Breach.RealArithmetic

/--
error: Free scalar arithmetic in ttcTest.Breach.RealArithmetic:
  ttcTest.Breach.RealArithmetic.test: HAdd.hAdd at Real
  A program computes with numeric data only through a charged operation.
-/
#guard_msgs (whitespace := lax) in
#ttcProgramSealFixture ttcTest.Breach.RealArithmetic

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.Program

/-!
# The sealed planar component estimator

This is the planar replacement for a single CV18 volume call. It is kept
separate from the main model until the dimension-two accuracy and cost of the
whole estimator are assembled.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Program

open Arlib.Computation (Num)
open ttc.Model.Operations

/-! ### Direct planar volume estimation -/

/-- The half-side and side of the enclosing square, its area, and the number of trials. -/
structure PlanarConstants where
  radius : Num ℝ
  width : Num ℝ
  boxArea : Num ℝ
  trials : Num ℕ

/-- For the normalized planar input, `roundness = R²/2`. The enclosing square has
area `4R²` and the body contains a unit-area square. The relative Chernoff bound
therefore needs `⌈3 · 4R² · log(2/p) / eps²⌉` trials. -/
noncomputable def planarConstantsProg (eps roundness p : Num ℝ) : Prog PlanarConstants := do
  let r2 ← A.mulLit 2 roundness
  let R ← A.sqrt r2
  let width ← A.mulLit 2 R
  let area ← A.mulLit 4 r2
  let logArg ← A.litDiv 2 p
  let l ← A.log logArg
  let scale ← A.mulLit 3 area
  let numerator ← A.mul scale l
  let eps2 ← A.mul eps eps
  let quot ← A.div numerator eps2
  let trials ← A.ceil quot
  pure ⟨R, width, area, trials⟩

/-- Map a held unit-uniform coordinate onto the side of the square. -/
def planarCoordinateProg (K : PlanarConstants) (u : Num ℝ) : Prog (Num ℝ) := do
  let x ← A.mul K.width u
  A.sub x K.radius

/-- Draw a point uniformly from the square using two charged unit draws. -/
def planarSquarePoint (K : PlanarConstants) : M 2 (NumPoint 2) := do
  let u ← unit
  let v ← unit
  let x ← run (planarCoordinateProg K u)
  let y ← run (planarCoordinateProg K v)
  pure (Fin.cons x (fun _ => y))

/-- Count one hit, charging the membership routine and any increment. -/
def planarTrial (K : PlanarConstants) (member : NumPoint 2 → Prog Bool)
    (count : Num ℕ) : M 2 (Num ℕ ⊕ Empty) := do
  let x ← planarSquarePoint K
  let inside ← run (member x)
  if inside then
    let one ← run (A.lit (1 : ℕ))
    let count' ← run (A.add count one)
    pure (.inl count')
  else pure (.inl count)

/-- Multiply the observed fraction of hits by the square's area. -/
noncomputable def planarEstimateProg (K : PlanarConstants) (count : Num ℕ) : Prog (Num ℝ) := do
  let hit ← A.cast count
  let trials ← A.cast K.trials
  let ratio ← A.div hit trials
  A.mul K.boxArea ratio

/-- Direct area estimation for one normalized planar component. -/
noncomputable def planarArea (member : NumPoint 2 → Prog Bool)
    (eps roundness p : Num ℝ) : M 2 (Num ℝ) := do
  let K ← run (planarConstantsProg eps roundness p)
  let zero ← run (A.lit (0 : ℕ))
  let count ← loopUntil K.trials (planarTrial K member) zero
  run (planarEstimateProg K (count.elim id Empty.elim))

end ttc.Program

#ttcProgramSeal ttc.Program
#ttcExecutableModule ttc.Planar.Program

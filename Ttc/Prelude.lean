/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Prelude: the ambient space

`Ttc.Space n` is `ℝⁿ` with the Euclidean (`ℓ₂`) norm and Lebesgue measure. Every
geometric statement in this development lives here.

Two facts about it are used pervasively and are recorded by Mathlib rather than
proved here: `finrank ℝ (Space n) = n` (`finrank_euclideanSpace_fin`), and that
`volume` is an additive Haar measure, so it scales by `|c|ⁿ` under dilation
(`MeasureTheory.Measure.addHaar_smul`).

The `ℓ₂` norm matters: the paper's inscribed-ball hypotheses are about
`ℓ₂`-balls, and `Ttc.Internal.Rounding` bounds `‖A_ij‖₂`.
-/

namespace Ttc

/-- The ambient space: `ℝⁿ` with the Euclidean norm and Lebesgue measure. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

end Ttc

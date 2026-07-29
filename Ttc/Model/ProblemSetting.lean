/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Decomposition

/-!
# `Model/ProblemSetting`: what the algorithm enumerates is what the theorem bounds

The quantity `TTC` estimates is `Vol(F)` — the Lebesgue volume of the solution
set of the input SMT(LRA) formula. That is `Ttc.volSol` (`Model/Prelude`), and it
is what the headline theorem in `Model/Theorem` bounds.

This file records the other half: that the set whose volume is bounded is exactly
the set the algorithm enumerates. `Ttc.sol_eq_iUnion_region` is the paper's
`thm:decomposition`,

> Let `F_dnf = ⋁_{i=1}^m c_i` be the DNF abstraction of the SMT formula `F`. Then
> `⋃_{i=1}^m P(c_i) = Sol(F)`.

It is what makes the target of the algorithm (a union of convex regions, one per
DNF cube) and the target of the theorem (the solution set) the **same set**. Its
two inclusions — soundness `P(c_i) ⊆ Sol(F)` and completeness
`Sol(F) ⊆ ⋃ P(c_i)` — are proved in `Analysis/Decomposition`; this file only
combines them, so there is no proof here to work through.

## What the formalisation exposes

The paper's proof of soundness argues "by construction `ℓ_ij ⊨ F_dnf`, therefore by
the property of Boolean abstraction, if `⋀ M(ℓ_ij)` can be satisfied then `F` is
satisfied". That phrasing is a slip: an individual literal does not entail the
DNF, and the direction actually needed is that the *cube* entails the formula. The
correct and sufficient hypothesis is exactly `Ttc.IsDNFOf D φ`, i.e. that `D` and
`φ` agree on every Boolean assignment — which is what a correct AllSAT/`ToDNF`
procedure delivers. Under that hypothesis both inclusions are immediate. See the
README, finding 6.
-/

namespace Ttc

open MeasureTheory Set

variable {A X : Type*} {n : ℕ} {M : A → Set X} {φ : BForm A} {D : DNF A}

/-! ## `thm:decomposition`: the algorithm's target is the theorem's target -/

/-- **`thm:decomposition`.** The union of the regions of the cubes of a
DNF abstraction of `F` is exactly `Sol(F)`.

Both inclusions are proved in `Analysis/Decomposition`
(`Ttc.region_subset_sol`, `Ttc.sol_subset_iUnion_region`). -/
theorem sol_eq_iUnion_region (h : IsDNFOf D φ) :
    ⋃ c ∈ D, region M c = sol M φ :=
  Subset.antisymm
    (iUnion₂_subset fun _ hc => region_subset_sol h hc)
    (sol_subset_iUnion_region h)

/-- The decomposition specialised to linear atoms: the solution set of an SMT(LRA)
formula is a finite union of convex regions. This is the form the volume
computation consumes. -/
theorem sol_eq_iUnion_convex (atoms : A → LinAtom n) (h : IsDNFOf D φ) :
    ∃ R : Cube A → Set (Space n),
      (∀ c, Convex ℝ (R c)) ∧ ⋃ c ∈ D, R c = sol (fun a => (atoms a).halfspace) φ :=
  ⟨region (fun a => (atoms a).halfspace), convex_region atoms, sol_eq_iUnion_region h⟩

end Ttc

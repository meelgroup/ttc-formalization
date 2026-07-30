/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Pseudocode

/-!
# `Model/ProblemSetting`: the problem, and everything assumed about it

`Ttc.TtcProb` is the whole hypothesis surface of the development: the input
formula, the run, the probability space its randomness lives in, and the two
lemmas the paper proves but this development assumes. `Model/Theorem` quantifies
over it and adds nothing.
-/

namespace Ttc

/-- The problem instance, the run, and the assumptions.

| Field | Paper | Status |
| --- | --- | --- |
| `isDNF` | `ToDNF`/AllSAT is correct | assumed of the external tool; `thm:decomposition` is *proved* from it |
| `lattice_lo`, `lattice_hi` | `lem:lattice` at `η = ε/8` | **assumed**; derivation from `lem:nonconv` proved in `Analysis/{Lattice,Nonconv,Recentred,Repair}` |
| `numlattice` | `lem:numlattice` | **assumed**; epoch skeleton proved in `Analysis/{Sketch,Poisson}` |

`L` is a bare real, intended as `|Q ∩ 𝕃ⁿ| / 10^(ρ·n)` but not tied to any lattice
(`AUDIT.md` §4). The output, by contrast, *is* the algorithm's: `numlattice` is
stated over `Ttc.ttcOutput`, so there is no faithfulness bridge to assume.
Inhabited by `Ttc.trivialProb` (`Analysis/Capstone`). Running time is out of
scope. -/
structure TtcProb (A : Type*) (n : ℕ) where
  /-- The multiplicative accuracy parameter. -/
  ε : ℝ
  /-- The failure probability. -/
  δ : ℝ
  /-- `ε` is positive. -/
  hε0 : 0 < ε
  /-- `ε` is at most one. -/
  hε1 : ε ≤ 1
  /-- The interpretation of atoms as sets of points. -/
  M : A → Set (Space n)
  /-- The Boolean abstraction of the input formula. -/
  φ : BForm A
  /-- The DNF produced by circuit AllSAT. -/
  D : DNF A
  /-- `D` really is a DNF representation of `φ`. -/
  isDNF : IsDNFOf D φ
  /-- The normalised lattice count `|Q ∩ 𝕃ⁿ| / 10^(ρ·n)`. -/
  L : ℝ
  /-- A count is nonnegative. -/
  hL : 0 ≤ L
  /-- `lem:lattice`, lower half, at `η = ε/8`. -/
  lattice_lo : (1 - ε / 8) * L ≤ volSol M φ
  /-- `lem:lattice`, upper half, at `η = ε/8`. -/
  lattice_hi : volSol M φ ≤ (1 + ε / 8) * L
  /-- The sample space of the algorithm's randomness. -/
  Ω : Type
  /-- Its σ-algebra. -/
  mΩ : MeasurableSpace Ω
  /-- The law of the algorithm's randomness. -/
  μ : @MeasureTheory.Measure Ω mΩ
  /-- It is a probability measure. -/
  isProb : @MeasureTheory.IsProbabilityMeasure Ω mΩ μ
  /-- The parameter block the run uses. -/
  P : Params
  /-- The oracle bundle **drawn at `ω`** — where all the randomness sits. -/
  O : Ω → Oracles n (Cube A)
  /-- The iteration budget both `while` loops run on. -/
  fuel : ℕ
  /-- `γ̂`, the smallest inscribed-ball radius over the polytopes — what the LP of
  `alg:prec` returns. The LP is not modelled, so this is an input. -/
  gammaHat : ℝ
  /-- `ρ`, the precision `GetPrecision` returns (`alg:ttc` line 17). It fixes the
  lattice `𝕃ⁿ = 10^(-ρ)·ℤⁿ` that `GenerateSamples` draws from. -/
  ρ : ℤ
  /-- `ρ` really is `GetPrecision`'s output for this `γ̂` (`alg:prec` line 91). -/
  rho_eq : ρ = P.precision gammaHat
  /-- **`lem:numlattice`**: with probability `≥ 1 − δ`, the output is within
  `(1 ± ε/3)` of the normalised lattice count. Assumed. -/
  numlattice : 1 - δ ≤
    (μ {ω | (1 - ε / 3) * L ≤ ttcOutput P O fuel ρ D ω ∧
            ttcOutput P O fuel ρ D ω ≤ (1 + ε / 3) * L}).toReal

end Ttc

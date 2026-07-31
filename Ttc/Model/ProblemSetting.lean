/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Pseudocode

/-!
# `Model/ProblemSetting`: the problem, and everything assumed about it

`Ttc.TtcProb` is the whole hypothesis surface of the development: the input
formula, the run, the probability space its randomness lives in, and the one
lemma the paper proves but this development assumes. `Model/Theorem` quantifies
over it and adds nothing.

`lem:lattice` is **not** among the assumptions: it is *proved* from the geometric
fields below (`Ttc.TtcProb.lattice_lo`, `Ttc.TtcProb.lattice_hi`, in
`Analysis/LatticeAssembled`). What those fields assume is what the paper assumes —
that the atoms are linear, that each polytope contains an inscribed ball of radius
`γ̂` and has finite volume, and that the DNF has no negated literal.
-/

namespace Ttc

open MeasureTheory

/-- The problem instance, the run, and the assumptions.

| Field | Paper | Status |
| --- | --- | --- |
| `isDNF` | `ToDNF`/AllSAT is correct | assumed of the external tool; `thm:decomposition` is *proved* from it |
| `ball_subset`, `volume_ne_top`, `isPositive`, `normal_ne_zero` | `lem:nonconv`'s hypotheses | assumed of the *input*; `lem:lattice` is **proved** from them (`Analysis/LatticeAssembled`) |
| `numlattice` | `lem:numlattice` | **assumed**; epoch skeleton proved in `Analysis/{Sketch,Poisson}` |

`L` is the actual normalised lattice count `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)` (`L_eq`).
The output is the algorithm's: `numlattice` is stated over `Ttc.ttcOutput`, so
there is no faithfulness bridge to assume. Inhabited by `Ttc.trivialProb`
(`Analysis/Capstone`). Running time is out of scope. -/
structure TtcProb (A : Type*) (n : ℕ) where
  /-- The multiplicative accuracy parameter. -/
  ε : ℝ
  /-- The failure probability. -/
  δ : ℝ
  /-- `ε` is positive. -/
  hε0 : 0 < ε
  /-- `ε` is at most one. -/
  hε1 : ε ≤ 1
  /-- The atoms of the SMT(LRA) formula: each is a linear constraint `A x ≤ b`. -/
  atoms : A → LinAtom n
  /-- The interpretation of atoms as sets of points. -/
  M : A → Set (Space n)
  /-- The interpretation is the one the linear atoms denote — the formula really is
  in the LRA fragment. -/
  M_eq : M = fun a => (atoms a).halfspace
  /-- The Boolean abstraction of the input formula. -/
  φ : BForm A
  /-- The DNF produced by circuit AllSAT. -/
  D : DNF A
  /-- `D` really is a DNF representation of `φ`. -/
  isDNF : IsDNFOf D φ
  /-- No literal of `D` is negated, so each `P(cᵢ)` is an intersection of *closed*
  half-spaces — see the README, finding 5, for why the count side needs this. -/
  isPositive : DNF.IsPositive D
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
  /-- The run's accuracy parameter is the one the theorem bounds against. -/
  eps_eq : P.ε = ε
  /-- The run's dimension is the ambient one. -/
  dim_eq : P.n = n
  /-- `m` bounds the number of polytopes in the decomposition. -/
  cubes_le : (Nat.card {c : Cube A // c ∈ D} : ℝ) ≤ P.m
  /-- `r` bounds the total number of facets. -/
  facets_le : (Nat.card (FacetIndex D) : ℝ) ≤ P.r
  /-- Every facet is a genuine constraint: its normal vector is nonzero. -/
  normal_ne_zero : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2
  /-- The oracle bundle **drawn at `ω`** — where all the randomness sits. -/
  O : Ω → Oracles n (Cube A)
  /-- The iteration budget both `while` loops run on. -/
  fuel : ℕ
  /-- The centre of the ball inscribed in each polytope. -/
  cen : {c : Cube A // c ∈ D} → Space n
  /-- `γ̂`, the inscribed-ball radius — what the LP of `alg:prec` returns. The LP is
  not modelled, so this is an input. -/
  gammaHat : ℝ
  /-- `γ̂` is positive. -/
  hgammaHat : 0 < gammaHat
  /-- **`lem:nonconv`'s hypothesis**: each `P(cᵢ)` contains an `ℓ₂`-ball of radius
  `γ̂`, about its own centre `cen i`. -/
  ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val
  /-- Each polytope has finite volume. -/
  volume_ne_top : ∀ i : {c : Cube A // c ∈ D}, volume (region M i.val) ≠ ⊤
  /-- `ρ`, the precision `GetPrecision` returns (`alg:ttc` line 17). It fixes the
  lattice `𝕃ⁿ = 10^(-ρ)·ℤⁿ` that `GenerateSamples` draws from. -/
  ρ : ℤ
  /-- `ρ` really is `GetPrecision`'s output for this `γ̂` (`alg:prec` line 91). -/
  rho_eq : ρ = P.precision gammaHat
  /-- The normalised lattice count `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)`. -/
  L : ℝ
  /-- `L` really is that count — it is not a free real. -/
  L_eq : L = normalisedCount M φ ρ
  /-- **`lem:numlattice`**: with probability `≥ 1 − δ`, the output is within
  `(1 ± ε/3)` of the normalised lattice count. Assumed. -/
  numlattice : 1 - δ ≤
    (μ {ω | (1 - ε / 3) * L ≤ ttcOutput P O fuel ρ D ω ∧
            ttcOutput P O fuel ρ D ω ≤ (1 + ε / 3) * L}).toReal

end Ttc

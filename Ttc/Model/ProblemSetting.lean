/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Coupling
import Ttc.Analysis.SketchProcess

/-!
# `Model/ProblemSetting`: the problem, and everything assumed about it

`Ttc.TtcProb` is the whole hypothesis surface of the development: the input
formula, the run, the probability space its randomness lives in, and a
description of the sampler. `Model/Theorem` quantifies over it and adds nothing.

**No lemma of the paper is assumed here.** `lem:lattice` is *proved* from the
geometric fields (`Ttc.TtcProb.lattice_lo`, `Ttc.TtcProb.lattice_hi`, in
`Analysis/LatticeAssembled`); `lem:numlattice` is *proved* from the sampler
fields (`Ttc.TtcProb.numlattice_union`, hence `Ttc.TtcProb.numlattice`, in
`Analysis/NumLatticeModel` and `Analysis/NumLattice`).

What the fields assume is what the paper assumes of its *input* — that the atoms
are linear, that each polytope contains an inscribed ball of radius `γ̂` and has
finite volume, that the DNF has no negated literal — plus, of its *sampler*, that
the randomness is the Poisson/thinning family of `Analysis/Coupling`.
-/

namespace Ttc

open MeasureTheory

/-- The problem instance, the run, and the assumptions.

| Field | Paper | Status |
| --- | --- | --- |
| `isDNF` | `ToDNF`/AllSAT is correct | assumed of the external tool; `thm:decomposition` is *proved* from it |
| `ball_subset`, `volume_ne_top`, `isPositive`, `normal_ne_zero` | `lem:nonconv`'s hypotheses | assumed of the *input*; `lem:lattice` is **proved** from them (`Analysis/LatticeAssembled`) |
| `law_eq`, `oracle_eq`, `rate_eq_L`, … | the sampler is the Poisson/thinning family | assumed of the *sampler*; `lem:numlattice` is **proved** from them (`Ttc.TtcProb.numlattice`) |

`L` is the actual normalised lattice count `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)` (`L_eq`).
The output is the algorithm's: `numlattice` is stated over `Ttc.ttcOutput`, so
there is no faithfulness bridge to assume. Inhabited **non-degenerately** by
`Ttc.Box.boxProb` (`Analysis/BoxProb`). Running time is out of scope. -/
structure TtcProb (A : Type*) (n : ℕ) where
  /-- The multiplicative accuracy parameter. -/
  ε : ℝ
  /-- The failure probability. -/
  δ : ℝ
  /-- `ε` is positive. -/
  hε0 : 0 < ε
  /-- `ε` is at most one. -/
  hε1 : ε ≤ 1
  /-- `δ` is positive. -/
  hδ0 : 0 < δ
  /-- `δ` is at most one. -/
  hδ1 : δ ≤ 1
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
  /-- The run's failure probability is the one the theorem bounds against. -/
  delta_eq : P.δ = δ
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
  /-- **`GenerateSamples`' contract** (`alg:ttc` line 43): the points it returns for
  cube `cᵢ` really are lattice points of `P(cᵢ)`. `Ttc.Oracles` only fixes *how
  many* it returns; that they lie where they should is a property of the external
  sampler, so it is assumed of it here. -/
  gen_mem : ∀ (ω : Ω) (c : ℕ) (i : Cube A) (j N : ℕ), i ∈ D →
    ∀ s ∈ (O ω).gen c i j N ρ, s ∈ region M i ∩ fineLattice n (latticeScale ρ)
  /-- The normalised lattice count `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)`. -/
  L : ℝ
  /-- `L` really is that count — it is not a free real. -/
  L_eq : L = normalisedCount M φ ρ
  /-- The number of lattice points the coupled family is indexed by.

  **From here on the fields describe the sampler.** `lem:numlattice` is no longer
  assumed: these say *what the randomness is* — the Poisson/thinning family of
  `Analysis/Coupling` — and the bound is **proved** from them
  (`Ttc.TtcProb.numlattice_union`, hence `Ttc.TtcProb.numlattice`). An assumed
  conclusion about probabilities has been replaced by an assumed description of
  the algorithm's own randomness. -/
  Lidx : ℕ
  /-- An injective enumeration of them. -/
  ptE : Fin Lidx → Space n
  /-- The enumeration really is injective. -/
  ptE_inj : Function.Injective ptE
  /-- Each point's rate at level `0`. -/
  θ : Fin Lidx → ℝ
  /-- Rates are nonnegative. -/
  θ_nonneg : ∀ s, 0 ≤ θ s
  /-- The total rate is positive — the instance is not empty. -/
  θ_pos : 0 < ∑ s, θ s
  /-- The volume estimate the run uses for each cube. -/
  vol : Cube A → ℝ
  /-- The coverage test the run uses. -/
  cover : Space n → Cube A → Bool
  /-- Cube membership, on the enumerated points. -/
  memPt : Cube A → Fin Lidx → Bool
  /-- Reading a sample point `ω` as a trajectory of the family. -/
  toTraj : Ω → (ℕ → Fin Lidx → ℕ)
  /-- That reading is measurable. -/
  toTraj_meas : @AEMeasurable Ω (ℕ → Fin Lidx → ℕ) _ mΩ toTraj μ
  /-- **The randomness IS the coupled family** — its law is `Ttc.trajLaw`. -/
  law_eq : @MeasureTheory.Measure.map Ω (ℕ → Fin Lidx → ℕ) mΩ _ toTraj μ = trajLaw θ
  /-- **The oracles read that family** (`Ttc.trajOracles`). -/
  oracle_eq : ∀ ω, O ω = trajOracles ptE_inj vol cover memPt (toTraj ω)
  /-- The coverage test agrees with cube membership on the lattice. -/
  cover_eq : ∀ s i, cover (ptE s) i = memPt i s
  /-- The cubes cover every enumerated point. -/
  cover_all : ∀ s, (D.any fun i => memPt i s) = true
  /-- The epoch index the union bound runs to. -/
  jstar : ℕ
  /-- There is at least one epoch. -/
  hjstar : 1 ≤ jstar
  /-- By epoch `j*−1` no cube's rate can still trigger a `halveDown`. -/
  rate_small : ∀ i ∈ D, ¬ (P.thresh / vol i ≤ (1 / 2 : ℝ) ^ (jstar - 1))
  /-- The level-`j*−1` rate is at most `Thresh/2`. -/
  rate_le : 2 * totalRate θ (jstar - 1) ≤ P.thresh
  /-- …and at least `(1−ε')·Thresh/8`, so the epoch series converges. -/
  lamStar_ge : (1 - P.epsPrime) * P.thresh / 8 ≤ totalRate θ (jstar - 1)
  /-- **The rates reproduce the lattice count.** This is what `lem:lattice`
  supplies; it is the only place the geometry meets the probability. -/
  rate_eq_L : ∑ s, θ s = L

end Ttc

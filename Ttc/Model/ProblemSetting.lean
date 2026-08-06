/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Dnf
import Ttc.Runtime
import Ttc.Coupling.Family
import Ttc.Process.SketchProcess

/-!
# `Model/ProblemSetting`: the problem, and everything assumed about it

`Ttc.TtcProb` is the whole hypothesis surface of the development: the input
formula, the run, the probability space its randomness lives in, and a
description of the sampler. `Model/Theorem` quantifies over it and adds nothing.

**No lemma of the paper is assumed here.** `lem:lattice` is *proved* from the
geometric fields (`Ttc.TtcProb.lattice_lo`, `Ttc.TtcProb.lattice_hi`, in
`Lattice/Assembled`); `lem:numlattice` is *proved* from the sampler
fields (`Ttc.TtcProb.numlattice_union`, hence `Ttc.TtcProb.numlattice`, in
`Coupling/Transfer` and `Coupling/NumLattice`).

What the fields assume is what the paper assumes of its *input* — that the atoms
are linear, that each polytope contains an inscribed ball of radius `γ̂` and has
finite volume, that the DNF has no negated literal — plus, of its *sampler*, that
the randomness is the Poisson/thinning family of `Coupling/Family`.
-/

namespace Ttc

open MeasureTheory

/-- The problem instance, the run, and the assumptions.

| Field | Paper | Status |
| --- | --- | --- |
| `isDNF` | `ToDNF`/AllSAT is correct | assumed of the external tool; `thm:decomposition` is *proved* from it |
| `ball_subset`, `volume_ne_top`, `isPositive`, `normal_ne_zero` | `lem:nonconv`'s hypotheses | assumed of the *input*; `lem:lattice` is **proved** from them (`Lattice/Assembled`) |
| `law_eq`, `oracle_eq`, `theta_lo`/`theta_hi`, … | the sampler is the Poisson/thinning family | assumed of the *sampler*; `lem:numlattice` is **proved** from them (`Ttc.TtcProb.numlattice`) |

`L` is the actual normalised lattice count `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)` (`L_eq`).
The output is the algorithm's: `numlattice` is stated over `Ttc.ttcOutput`, so
there is no faithfulness bridge to assume. Inhabited **non-degenerately** by
`Ttc.Box.boxProb` (`Witness/BoxProb`). Running time is out of scope. -/
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
  /-- The Boolean abstraction of the input formula (`alg:ttc` line 15). -/
  φ : BForm A
  /-- **`alg:ttc` line 16**: `F_dnf ← ToDNF(F_bool)`, the circuit-AllSAT call, as a
  function of the formula. A parameter rather than the fixed `Ttc.toDNF`, because
  `thm:runtime`'s `m` is *this* procedure's cube count — see `Ttc.ttcOutput`. -/
  toDNF : BForm A → DNF A
  /-- **The AllSAT call is correct.** Assumed of the external tool; `Ttc.toDNF`
  together with `Ttc.toDNF_isDNFOf` shows the assumption is satisfiable by an
  actual converter, and the witness discharges it that way. -/
  isDNF : IsDNFOf (toDNF φ) φ
  /-- No literal of the DNF is negated, so each `P(cᵢ)` is an intersection of
  *closed* half-spaces. `Ttc.toDNF_isPositive` derives this from a negation-free
  input formula, which is how the witness discharges it — see the README,
  finding 5. -/
  isPositive : DNF.IsPositive (toDNF φ)
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
  cubes_le : (Nat.card {c : Cube A // c ∈ toDNF φ} : ℝ) ≤ P.m
  /-- `r` bounds the total number of facets. -/
  facets_le : (Nat.card (FacetIndex (toDNF φ)) : ℝ) ≤ P.r
  /-- Every facet is a genuine constraint: its normal vector is nonzero. -/
  normal_ne_zero : ∀ j : FacetIndex (toDNF φ),
    0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2
  /-- The oracle bundle **drawn at `ω`** — where all the randomness sits. -/
  O : Ω → Oracles n (Cube A)
  /-- The centre of the ball inscribed in each polytope. -/
  cen : {c : Cube A // c ∈ toDNF φ} → Space n
  /-- `γ̂`, the inscribed-ball radius — what the LP of `alg:prec` returns. The LP is
  not modelled, so this is an input. -/
  gammaHat : ℝ
  /-- `γ̂` is positive. -/
  hgammaHat : 0 < gammaHat
  /-- **`lem:nonconv`'s hypothesis**: each `P(cᵢ)` contains an `ℓ₂`-ball of radius
  `γ̂`, about its own centre `cen i`. -/
  ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val
  /-- Each polytope has finite volume. -/
  volume_ne_top : ∀ i : {c : Cube A // c ∈ toDNF φ}, volume (region M i.val) ≠ ⊤
  /-- `ρ`, the precision `GetPrecision` returns (`alg:ttc` line 17). It fixes the
  lattice `𝕃ⁿ = 10^(-ρ)·ℤⁿ` that `GenerateSamples` draws from. -/
  ρ : ℤ
  /-- `ρ` really is `GetPrecision`'s output for this `γ̂` (`alg:prec` line 91). -/
  rho_eq : ρ = P.precision gammaHat
  /-- **`GenerateSamples`' contract** (`alg:ttc` line 43): the points it returns for
  cube `cᵢ` really are lattice points of `P(cᵢ)`. `Ttc.Oracles` only fixes *how
  many* it returns; that they lie where they should is a property of the external
  sampler, so it is assumed of it here. -/
  gen_mem : ∀ (ω : Ω) (i : Cube A) (j N : ℕ), i ∈ toDNF φ →
    ∀ s ∈ (O ω).gen i j N ρ, s ∈ region M i ∩ fineLattice n (latticeScale ρ)
  /-- The normalised lattice count `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)`. -/
  L : ℝ
  /-- `L` really is that count — it is not a free real. -/
  L_eq : L = normalisedCount M φ ρ
  /-- The number of lattice points the coupled family is indexed by.

  **From here on the fields describe the sampler.** `lem:numlattice` is no longer
  assumed: these say *what the randomness is* — the Poisson/thinning family of
  `Coupling/Family` — and the bound is **proved** from them
  (`Ttc.TtcProb.numlattice_union`, hence `Ttc.TtcProb.numlattice`). An assumed
  conclusion about probabilities has been replaced by an assumed description of
  the algorithm's own randomness. -/
  Lidx : ℕ
  /-- An injective enumeration of them. -/
  ptE : Fin Lidx → Space n
  /-- The enumeration really is injective. -/
  ptE_inj : Function.Injective ptE
  /-- **The enumeration lands in `Sol(F) ∩ 𝕃ⁿ`** … -/
  ptE_mem : ∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)
  /-- … **and hits all of it.** With `ptE_inj` this makes `ptE` a bijection onto
  `Sol(F) ∩ 𝕃ⁿ`, so `Lidx` is the paper's `|Sol(F) ∩ 𝕃ⁿ|` rather than a free
  choice, and the family is indexed by the points the algorithm actually counts. -/
  ptE_onto : ∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x
  /-- Each point's rate at level `0`. -/
  θ : Fin Lidx → ℝ
  /-- **The paper's Invariant** (`analysis.tex:265`), lower half: each lattice
  point's level-`0` rate is at least `(1−ε')(1−ε/8)/10^(ρ·n)`. The two error
  sources are `Vol_ED`'s `ε'` and `lem:lattice`'s `η = ε/8`. -/
  theta_lo : ∀ s, (1 - P.epsPrime) * (1 - P.eta) / (latticeScale ρ) ^ n ≤ θ s
  /-- **The paper's Invariant**, upper half. -/
  theta_hi : ∀ s, θ s ≤ (1 + P.epsPrime) * (1 + P.eta) / (latticeScale ρ) ^ n
  /-- The volume estimate the run uses for each cube. -/
  vol : Cube A → ℝ
  /-- The coverage test the run uses. -/
  cover : Space n → Cube A → Bool
  /-- Cube membership, on the enumerated points. -/
  memPt : Cube A → Fin Lidx → Bool
  /-- **Cube membership is the geometric one** — `memPt` is not a free predicate.
  Only cubes of `D` are constrained, which is all the run ever reads. -/
  memPt_eq : ∀ i ∈ toDNF φ, ∀ s, memPt i s = true ↔ ptE s ∈ region M i
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
  /-- **`Vol_ED`'s accuracy contract** (`analysis.tex:269`): the volume oracle
  overestimates by at most `(1+ε')`. `Vol_ED` is an external algorithm neither the
  paper nor this development implements, so its guarantee is assumed of it — the
  same status as `isDNF`. Only the upper half is needed here; the lower half feeds
  the Invariant, which is assumed directly as `theta_lo`/`theta_hi`. -/
  volED_hi : ∀ i ∈ toDNF φ, vol i ≤ (1 + P.epsPrime) * (volume (region M i)).toReal
  /-- Every cube of the decomposition carries a positive rate. -/
  vol_pos : ∀ i ∈ toDNF φ, 0 < vol i
  /-- **The instance is big enough for the sketch to be worth running** — the
  paper's own regime. The epoch index `j*` and its window are *not* assumed: they
  follow from this by `Ttc.exists_epoch`, and the first loop's cut-off follows by
  `Ttc.rate_small_of_epoch`. -/
  big : (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ s


namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- **The DNF the algorithm works with** — line 16's output on the input formula. A
`def`, not a field: the structure carries the *procedure* and the formula, so the
cube list is determined by the input rather than supplied beside it. -/
@[reducible] def D : DNF A := T.toDNF T.φ

/-- **`m`, the number of decomposed polytopes** — the length of the cube list the
main loop folds over. This is `thm:runtime`'s `m`, and `Ttc.TtcProb.cubes_le`
bounds it by the parameter block's `P.m`. -/
def numCubes : ℕ := T.D.length

end TtcProb

end Ttc

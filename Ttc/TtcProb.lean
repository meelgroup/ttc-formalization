/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Dnf
import Ttc.Runtime
import Ttc.Coupling.Family
import Ttc.Process.SketchProcess
import Ttc.Lattice.Decomposition
import Ttc.Volume.Oracle
import Ttc.Sampler.Interface
import Arlib.Lattice.KV97.Theorem2
import Arlib.Probability.TV
import Arlib.Probability.UniformOn

/-!
# `TtcProb`: the abstract interface — everything the result assumes

`Ttc.TtcProb` is the whole hypothesis surface of the development: the input
formula, the run, the probability space its randomness lives in, and a
description of the sampler. `Model/Theorem` quantifies over it and adds nothing.

This is `CLAUDE.md` §1's **layer 1**, an assumption bundle, so it is *not* part of
the audit surface `Model/`: `Model/ProblemSetting` states the paper's problem —
what `Vol(F)` is and what "within `(1 ± ε)`" means — and stops there. The
hypotheses a reader must weigh are here.

**No lemma of the paper is assumed here.** `lem:lattice` is *proved* from the
geometric fields (`Ttc.TtcProb.lattice_lo`, `Ttc.TtcProb.lattice_hi`, in
`Lattice/Assembled`); `lem:numlattice` is *proved* from the sampler
fields (`Ttc.TtcProb.numlattice_union`, hence `Ttc.TtcProb.numlattice`, in
`Coupling/Transfer` and `Coupling/NumLattice`).

What the fields assume is what the paper assumes of its *input* — that the atoms
are linear, that each polytope contains an inscribed ball of radius `γ̂` and has
finite volume, that the DNF has no negated literal — plus, of its *sampler*, that
the randomness is the Poisson/thinning family of `Coupling/Family`.

The two field types that are *other papers'* assumption bundles are declared
separately: `Ttc.VolumeAlgorithm` (`Volume/Oracle`) and `Ttc.KV97Sampler`
(`Sampler/Interface`). The `def`s that merely read a `Ttc.TtcProb` are in
`Ttc/Access.lean`.
-/

namespace Ttc

open MeasureTheory Pointwise

/-- **`TTC(F, ε, δ)`'s output, as a random variable over an abstract sample space.**

`Ttc.run` (`Model/Pseudocode`) — the transcription of `alg:ttc` lines 22–46 — with
its oracle bundle drawn at the sample point `ω`, and with the cube list supplied by
a line-16 converter applied to `φ`, `F`'s Boolean abstraction (line 15).  `P` is the
parameter block of lines 17–20 and `ρ` is `GetPrecision`'s output (line 17).

`toDNF` is a *parameter* rather than the fixed `Ttc.toDNF` of `Model/Prelude`
because `TTC` runs an optimised circuit AllSAT, and `thm:runtime` is stated in
terms of `m`, **that** procedure's cube count — pinning the converter would prove
the guarantee for a different, generally exponentially larger `m`.  Correctness
holds for any converter meeting `Ttc.IsDNFOf`, and `Ttc.toDNF_isDNFOf` shows at
least one does, so the parameter is not an empty hypothesis.

**Not part of the audit surface, and not the algorithm's own output.**  Its binders
`Ω`, `O` and `toDNF` are exactly the `Ttc.TtcProb` fields of the same names, so it
belongs with the hypothesis bundle it is measured against rather than with the
pseudocode: `Ttc.ttcAlgOutput` and `Ttc.ttcRun` (`Model/Pseudocode`) are the
algorithm at its *own* inputs and neither unfolds to this.  `Ttc.numlattice` is
stated over it, and `Ttc.runCost` is what `thm:runtime` bounds over the same run. -/
noncomputable def ttcOutput {A : Type*} {n : ℕ} {Ω : Type} (P : Params)
    (O : Ω → Oracles n (Cube A)) (toDNF : BForm A → DNF A) (ρ : ℤ)
    (φ : BForm A) (ω : Ω) : ℝ :=
  run P (O ω) ρ (toDNF φ)

/-- The problem instance, the run, and the assumptions.

| Field | Paper | Status |
| --- | --- | --- |
| `isDNF` | `ToDNF`/AllSAT is correct | assumed of the external tool; `thm:decomposition` is *proved* from it |
| `ball_subset`, `volume_ne_top`, `isPositive`, `normal_ne_zero` | `lem:nonconv`'s hypotheses | assumed of the *input*; `lem:lattice` is **proved** from them (`Lattice/Assembled`) |
| `law_eq`, `oracle_eq`, `sampler`, `theta_eq`, … | the sampler is the Poisson/thinning family, drawing by Kannan–Vempala rounding | assumed of the *sampler*; `lem:numlattice` is **proved** from them (`Ttc.TtcProb.numlattice`), and so are `eq:almostuniform` (`Ttc.TtcProb.samp_unif`) and the paper's Invariant (`Ttc.TtcProb.theta_lo`/`theta_hi`) |

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
  sampler, so it is assumed of it here.

  Its **distributional** contract (`eq:sampler`/`eq:almostuniform`: the law is
  within a `(1±ε')` factor of uniform on `P(cᵢ) ∩ 𝕃ⁿ`, pointwise) is no longer
  assumed at all: the field `sampler` below describes the Kannan–Vempala
  construction, and `Ttc.TtcProb.samp_unif` derives the contract from it. -/
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
  /-- The volume estimate the run uses for each cube. -/
  vol : Cube A → ℝ
  /-- `GenerateSamples`' output law on each cube: `sampD i x` is the mass the
  sampler, run on `P(cᵢ)`, puts on the lattice point `x`. -/
  sampD : Cube A → Space n → ℝ
  /-- **`GenerateSamples` is Kannan–Vempala's sampler** — the *construction*, not
  its guarantee. See `Ttc.KV97Sampler` above: the discrete law `sampD` is the
  rejection-normalised randomized rounding of a nearly-uniform continuous draw
  from the inflated dilate `10^ρ · P(cᵢ)`.

  **This field replaces the former `samp_unif`**

  ```
  samp_unif : ∀ i ∈ toDNF φ, ∀ x ∈ region M i ∩ fineLattice n (latticeScale ρ),
    (1 - P.epsPrime) / ((region M i ∩ fineLattice n (latticeScale ρ)).ncard : ℝ)
        ≤ sampD i x ∧
      sampD i x
        ≤ (1 + P.epsPrime) / ((region M i ∩ fineLattice n (latticeScale ρ)).ncard : ℝ)
  ```

  which was `eq:almostuniform` (`sections/related.tex:21`) **assumed** of the
  external sampler. It is now the *theorem* `Ttc.TtcProb.samp_unif`
  (`Ttc/Sampler/Bridge.lean`), with a byte-identical statement, proved from this
  field by `Ttc.almostUniform_of_kv97_density` — i.e. by `Arlib.KV97.theorem2`
  and the `ℤⁿ → 𝕃ⁿ` transport. So the entire Kannan–Vempala development is now
  load-bearing for the headline rather than a parallel justification of it.

  Together with `theta_eq` this also yields the paper's Invariant
  (`analysis.tex:265`), formerly the two fields

  ```
  theta_lo : ∀ s, (1 - P.epsPrime) ^ 2 * (1 - P.eta) / (latticeScale ρ) ^ n ≤ θ s
  theta_hi : ∀ s, θ s ≤ (1 + P.epsPrime) ^ 2 * (1 + P.eta) / (latticeScale ρ) ^ n
  ```

  now `Ttc.TtcProb.theta_lo`/`Ttc.TtcProb.theta_hi`, also with byte-identical
  statements, so nothing downstream changed. -/
  sampler : KV97Sampler A n M (toDNF φ) ρ P.epsPrime sampD
  /-- **How the run accumulates `𝒳`** (`alg:ttc` lines 43–46): each lattice point's
  level-`0` rate is the sampler's mass at that point, times the volume estimate of
  the cube it was drawn from. The cube is existentially quantified because the
  point is drawn from whichever cube of the decomposition contains it.

  This is a description of the algorithm, not a bound on it — the sole
  quantitative input is `Ttc.TtcProb.samp_unif`, itself a theorem. Together they
  yield the paper's Invariant:
  `theta_eq` names the cube, `samp_unif` gives `eq:almostuniform` there,
  `Ttc.TtcProb.volCoins_good` gives `Vol_ED`'s accuracy and
  `Ttc.TtcProb.lattice_cube_lo`/`lattice_cube_hi` give `lem:lattice`, and
  `Ttc.TtcProb.theta_window_cube` telescopes the three. -/
  theta_eq : ∀ s, ∃ i, i ∈ toDNF φ ∧ ptE s ∈ region M i ∧
    θ s = sampD i (ptE s) * vol i
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
  /-- **`Vol_ED` is Cousins–Vempala Theorem 1.1** (`vol3_journal.tex:144`), bundled
  as `Ttc.VolumeAlgorithm` (declared at the top of this file; everything *proved*
  about it is in `Ttc/Volume/Bridge.lean`).

  This field and the three below replace the former single field

  ```
  volED_hi : ∀ i ∈ toDNF φ, vol i ≤ (1 + P.epsPrime) * (volume (region M i)).toReal
  ```

  which asserted the bound at *every* sample point — i.e. that `Vol_ED` never
  fails — and so was strictly stronger than what any randomized volume algorithm
  delivers. `Ttc.TtcProb.volED_hi` is now a **theorem** with that exact statement,
  so nothing downstream changed. -/
  volAlg : VolumeAlgorithm n
  /-- The coins the `m` `Vol_ED` calls of `alg:ttc` line 24 consumed.

  A single sample point, not a random variable: `oracle_eq` binds `vol` outside
  the run's `ω`, so the volume estimates are fixed reals throughout the coupling.
  Randomizing them would change `trajOracles` and every lemma below it; the
  probabilistic content is instead carried by `Ttc.TtcProb.volGood_prob`, which
  bounds the measure of the set of coins for which `volCoins_good` holds. -/
  volCoins : volAlg.Ω
  /-- **`vol` is what `Vol_ED` returned.** Each estimate is Theorem 1.1's output
  on the *normalised* polytope — the one that contains the unit ball, as Theorem
  1.1 requires — rescaled by `γ̂ⁿ` (`Ttc.VolumeAlgorithm.of_ball`), at the
  accuracy `ε'` and confidence `δ'` of `alg:ttc` line 18.

  This is the field that stops `vol` being a free function of the right shape: it
  pins it to a named published algorithm. -/
  volED_eq : ∀ (i : Cube A) (hi : i ∈ toDNF φ), vol i =
      gammaHat ^ n * volAlg.est (roundBody (cen ⟨i, hi⟩) gammaHat (region M i))
        P.epsPrime P.deltaPrime volCoins
  /-- **The `m` calls all landed in their good event.** This is the residual
  assumption, and unlike the `volED_hi` it replaces it is an *event*, not a
  posited inequality: `Ttc.TtcProb.volGood_prob` proves it holds with probability
  at least `1 − m·δ' = 1 − δ/4` (`Ttc.Params.vol_failure_eq`), which is exactly
  the share of the failure budget `Ttc.numlattice_failure_le` reserves for the
  volume oracle.

  Two-sided, because that is what Theorem 1.1 gives. The upper half is what
  `Ttc.TtcProb.vol_lt_two_total` consumes; the lower half feeds the Invariant. -/
  volCoins_good : ∀ i ∈ toDNF φ,
      vol i ∈ relErr P.epsPrime (volume (region M i)).toReal
  /-- Every cube of the decomposition carries a positive rate. -/
  vol_pos : ∀ i ∈ toDNF φ, 0 < vol i
  /-- **The instance is big enough for the sketch to be worth running** — the
  paper's own regime. The epoch index `j*` and its window are *not* assumed: they
  follow from this by `Ttc.exists_epoch`, and the first loop's cut-off follows by
  `Ttc.rate_small_of_epoch`. -/
  big : (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ s

end Ttc

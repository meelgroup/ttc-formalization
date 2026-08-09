/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Final
import Ttc.Exec.CubeBounds
import Ttc.Exec.Dedup
import Ttc.Exec.RegimeMain

/-!
# `Exec/Inputs`: `ttc_volume_final` with seven binders removed

`Ttc.ttc_volume_inputs` is `Ttc.ttc_volume_final` (`Exec/Final.lean`) with **17
explicit binders** instead of 26.  Seven come off in four independent ways, and
the point of this file is that each of them is *discharged*, not weakened away.

## What went, and why it could

| Gone | Why |
| --- | --- |
| `M`, `M_eq` | `M_eq : M = fun a => (atoms a).halfspace` **defines** `M`.  Substituting it is a substitution, not a strengthening: `M := Ttc.atomSet atoms` and `M_eq := rfl`. |
| `toDNF`, `isDNF`, `isPositive` | the converter is pinned to `Ttc.toDNFd` (`Exec/Dedup`), `isDNF` is `Ttc.toDNFd_isDNFOf`, and `isPositive` is `Ttc.toDNFd_isPositive` applied to `hφ : φ.IsPositive` — a syntactic condition on the **input formula**. |
| `hm` | `Ttc.one_le_card_cubes_of_ne_nil` at `Ttc.toDNFd_ne_nil hφ`.  A positive formula's DNF is never empty, because `Ttc.BForm` has **no `false` constructor** and `IsPositive (.neg _)` is `False`. |
| `hr` | `Ttc.one_le_card_facets_of_isBounded`, from `hbdd` and `hn`.  A literal-free cube has `region = Set.univ ⊆ sol`, and `Set.univ` is unbounded in `Ttc.Space n` for `n ≥ 1`. |
| `P`, `hP` | `hP : P = ttcParams …` **defines** `P`.  Substituting it gives `P := Ttc.inputParams …` and `hP := rfl`. |
| `hlen` | `Ttc.length_toDNFd_le_card`, with **equality**: `Ttc.toDNFd` is duplicate-free, so its length *is* `Nat.card` of its cube set. |

## What `hφ` and `hbdd` are now doing, which is more than before

They were input conditions already; they are now also what discharges `hm` and
`hr`.  Neither was strengthened, and no hypothesis was added.

## The one honest cost: `hlen` was bought, not proved away

`Ttc.toDNF` **provably** fails `hlen` (`Ttc.toDNF_length_gt_card_cubes`: `a ∨ a`
has DNF `[[a],[a]]`).  Pinning the converter to the deduplicated
`Ttc.toDNFd` is therefore a change to what the algorithm runs on, not a proof
about what it already ran on.  Deduplication preserves the semantics exactly
(`Ttc.mem_toDNFd` — same cubes, hence the same `IsDNFOf`, the same regions and the
same union) but it changes the **cost profile**: `m` shrinks, so
`P.deltaPrime = δ₀/(4m)` grows and every surviving cube is estimated at a looser
confidence.  A shorter run at a weaker per-cube guarantee is a different run.
Read that as a repricing, exactly like the `δ₀ = 4δ/5` one of `Exec/Final`.

## What is left, and why (17 binders)

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hbdd hcoeff cen gammaHat hgammaHat ball_subset big
```

* `atoms φ ε δ` and `hε0 hε1 hδ0 hδ1 hn` — the algorithm's inputs and the FPRAS
  parameter range.  `ApproxNFA.approxNFA_countNFA` (the nfalean template) has
  exactly these nine and nothing else.
* `hφ` — README finding 5.  A negated atom denotes an *open* half-space, which the
  counting side cannot use.  A genuine restriction, checkable by inspecting `φ`.
* `hbdd` — **necessary, not incidental.**  An unbounded `Sol(F)` has infinite
  volume, and `Ttc.volSol` would report `ENNReal.toReal ⊤ = 0`.
* `hcoeff` — no atom is degenerate (`0 ≤ b` is not a half-space).  Removing it
  needs degenerate atoms handled in the facet system; not attempted.
* `cen gammaHat hgammaHat ball_subset` — the inscribed ball, which `alg:ttc`
  computes by an LP.  **Deliberately still binders**: replacing them with an
  existence hypothesis would force the conclusion to name a `Classical.choose`,
  and `big` would then be unprovable for any concrete instance, destroying the
  non-vacuity witnesses.  They are instance *data*.
* `big` — the regime condition.  See `Exec/Regime.lean` for what is known about it.

## Costs

Unchanged from `Ttc.ttc_volume_final`: exponential in `n` on both routes
(`Θ(Rⁿ/(ε²p))` Monte-Carlo samples, `2^Θ(n)·log(M·Vol(P′)/ε′)` certified ball-walk
steps), the `δ₀ = 4δ/5` repricing, and `thm:runtime` out of scope.
-/

namespace Ttc

open MeasureTheory Set Pointwise

section Inputs

variable {A : Type*} {n : ℕ}

/-! ## The two substitutions, as definitions -/

/-- **The interpretation `M` the theorem used to take as a binder.**  `M_eq` said
`M = fun a => (atoms a).halfspace`; this is that right-hand side, named. -/
def atomSet (atoms : A → LinAtom n) : A → Set (Space n) := fun a => (atoms a).halfspace

/-- **The parameter block `TTC` computes** (`alg:ttc` lines 17–20), with `hm` and
`hr` supplied by `Ttc.one_le_card_cubes_of_ne_nil` and
`Ttc.one_le_card_facets_of_isBounded` rather than assumed.  `hP` said
`P = ttcParams …`; this is that right-hand side, named.

The internal failure parameter is `δ₀ = 4δ/5`, so that the conclusion is a clean
`1 − δ` — see `Exec/Final.lean` for what that reprices. -/
noncomputable def inputParams (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)) : Params :=
  ttcParams (toDNFd φ) n ε (4 * δ / 5) hε0 hε1 hn
    (one_le_card_cubes_of_ne_nil (toDNFd_ne_nil hφ))
    (one_le_card_facets_of_isBounded hn (toDNFd_isDNFOf φ) hbdd (toDNFd_ne_nil hφ))

/-! ## The statement -/

/-- **`thm:volumettc` + `thm:runtime` at 17 binders.**

`Ttc.ttc_volume_final` with `M`/`M_eq`, the converter and its two properties, `hm`,
`hr`, `P`/`hP` and `hlen` all discharged — see this module's docstring for which
lemma discharges which, and for the one repricing this buys.

* **Accuracy.**  `Pr[ output ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, over the joint law of the
  volume coins and the sample coins.
* **Running time.**  `alg:ttc`'s charged cost `m·(C_vol + C_sample·Thresh)`, under
  `Ttc.Terminates`.

Correctness, not efficiency: both oracle routes are exponential in `n`. -/
theorem ttc_volume_inputs
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))
    (hcoeff : ∀ j : FacetIndex (toDNFd φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNFd φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region (atomSet atoms) i.val)
    (big : ∀ c ∈ mcGood (atomSet atoms) (toDNFd φ) cen gammaHat
        (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime
        (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).deltaPrime,
      (1 - (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime)
          * (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).thresh / 8
        ≤ ∑ s, rates (atomSet atoms) φ (toDNFd φ)
            ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)
            (e2eSampD (atomSet atoms) (toDNFd φ)
              ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime (canonRfac (toDNFd φ))
              (Jt := Fin (Nat.card (FacetIndex (toDNFd φ)))) (canonAm atoms (toDNFd φ))
              (canonBv atoms (toDNFd φ)
                (latticeScale ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)))
              cen gammaHat (canonDm (atomSet atoms) (toDNFd φ)
                ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)))
            (mcVol (atomSet atoms) (toDNFd φ) cen gammaHat
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).deltaPrime c) s) :
    (1 - δ ≤
      (∫⁻ c, trajLaw (rates (atomSet atoms) φ (toDNFd φ)
            ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)
            (e2eSampD (atomSet atoms) (toDNFd φ)
              ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime (canonRfac (toDNFd φ))
              (Jt := Fin (Nat.card (FacetIndex (toDNFd φ)))) (canonAm atoms (toDNFd φ))
              (canonBv atoms (toDNFd φ)
                (latticeScale ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)))
              cen gammaHat (canonDm (atomSet atoms) (toDNFd φ)
                ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)))
            (mcVol (atomSet atoms) (toDNFd φ) cen gammaHat
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).deltaPrime c))
          {t : ℕ → Fin (latticeCount (atomSet atoms) φ
              ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)) → ℕ |
            ttcOutput (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd)
                (coveredOracles (atomSet atoms) φ
                  ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)
                  (mcVol (atomSet atoms) (toDNFd φ) cen gammaHat
                    (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime
                    (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).deltaPrime c))
                toDNFd ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat) φ t
              ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount (atomSet atoms) φ
          ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).thresh →
      Terminates (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd)
          (coveredOracles (atomSet atoms) φ
            ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)
            (mcVol (atomSet atoms) (toDNFd φ) cen gammaHat
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).deltaPrime c) t) (toDNFd φ) →
      runCost (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd)
          (coveredOracles (atomSet atoms) φ
            ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)
            (mcVol (atomSet atoms) (toDNFd φ) cen gammaHat
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime
              (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).deltaPrime c) t)
          cVol cSample ((inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat)
          (toDNFd φ)
        ≤ (toDNFd φ).length * (cVol + cSample * thr)) :=
  ttc_volume_final atoms φ ε δ hε0 hε1 hδ0 hδ1 hn (atomSet atoms) rfl toDNFd
    (toDNFd_isDNFOf φ) (toDNFd_isPositive hφ)
    (one_le_card_cubes_of_ne_nil (toDNFd_ne_nil hφ))
    (one_le_card_facets_of_isBounded hn (toDNFd_isDNFOf φ) hbdd (toDNFd_ne_nil hφ))
    (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd) rfl
    (length_toDNFd_le_card φ) hbdd hcoeff cen gammaHat hgammaHat ball_subset big

/-! ## The quantities the statement layer measures

`Model/Theorem` states the guarantee about these four names and nothing else.  They
are definitional wrappers over the terms above — not abstraction barriers — so
`Ttc.ttc_volume_estimate` stays one application of `Ttc.ttc_volume_inputs`.  They
live here rather than in `Model/` so that `Model/Theorem.lean` contains the paper's
theorem and nothing else. -/

section Measured

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
  (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
  (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))

/-- **`GetPrecision`'s output** (`alg:ttc` line 17): `ρ ← ⌈log₁₀(γ/γ̂)⌉`, computed
from the parameter block and the inscribed radius. -/
noncomputable def runPrec (gammaHat : ℝ) : ℤ :=
  (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).precision gammaHat

/-- **`|Sol(F) ∩ 𝕃ⁿ|`** at that precision — the index the run's sample coins range
over. -/
noncomputable def runCount (gammaHat : ℝ) : ℕ :=
  latticeCount (atomSet atoms) φ (runPrec atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat)

/-- **The oracle bundle `alg:ttc` reads**, as a closed term: `Vol_ED` is `Ttc.mcVol`
at the volume coins `c`, the rest is `Ttc.coveredOracles` at the sample coins `t`.
Nothing here is a hypothesis. -/
noncomputable def runOracles (cen : {c : Cube A // c ∈ toDNFd φ} → Space n)
    (gammaHat : ℝ) (c : ℕ → Space n)
    (t : ℕ → Fin (runCount atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) → ℕ) :
    Oracles n (Cube A) :=
  coveredOracles (atomSet atoms) φ (runPrec atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat)
    (mcVol (atomSet atoms) (toDNFd φ) cen gammaHat
      (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime
      (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).deltaPrime c) t

/-- **What `TTC(F, ε, δ)` returns on the run `(c, t)`** — `Ttc.ttcOutput`
(`Model/Pseudocode`) on the cube list `Ttc.toDNFd φ` at the computed precision. -/
noncomputable def ttcRunOutput (cen : {c : Cube A // c ∈ toDNFd φ} → Space n)
    (gammaHat : ℝ) (c : ℕ → Space n)
    (t : ℕ → Fin (runCount atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) → ℕ) : ℝ :=
  ttcOutput (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd)
    (runOracles atoms φ ε δ hε0 hε1 hn hφ hbdd cen gammaHat c) toDNFd
    (runPrec atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) φ t

/-- **The level-`0` rates `θ`** (`alg:ttc` line 20): the sampler's mass at each
enumerated lattice point times that point's cube's volume estimate.  `Ttc.trajLaw`
of this is the law the sample coins are drawn from. -/
noncomputable def runRates (cen : {c : Cube A // c ∈ toDNFd φ} → Space n)
    (gammaHat : ℝ) (c : ℕ → Space n) :
    Fin (runCount atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) → ℝ :=
  rates (atomSet atoms) φ (toDNFd φ)
    (runPrec atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat)
    (e2eSampD (atomSet atoms) (toDNFd φ)
      (runPrec atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat)
      (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime (canonRfac (toDNFd φ))
      (Jt := Fin (Nat.card (FacetIndex (toDNFd φ)))) (canonAm atoms (toDNFd φ))
      (canonBv atoms (toDNFd φ)
        (latticeScale (runPrec atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat)))
      cen gammaHat (canonDm (atomSet atoms) (toDNFd φ)
        (runPrec atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat)))
    (mcVol (atomSet atoms) (toDNFd φ) cen gammaHat
      (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).epsPrime
      (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).deltaPrime c)


/-! ## The regime condition, replaced by a condition on the input

`Ttc.ttc_volume_inputs`' last binder, `big`, is a `∀` over the volume coins
mentioning `Ttc.e2eSampD`, `Ttc.mcVol` and `Ttc.mcGood` — nothing a reader can check
of an instance.  `Ttc.big_of_volume` (`Exec/RegimeMain`) proves it from one scalar
inequality about the input, so the statement can carry that instead.

**This does not widen the theorem's reach.**  `Ttc.Box.big_not_derivable`
(`Exec/Regime`) shows the restriction is real: `big` fails for small bodies and no
choice of precision escapes it.  What changes is that the restriction becomes
legible — and it is exactly the paper's own unstated `j* ≥ 1`
(`sections/analysis.tex:284`; README finding 20). -/

/-- **`thm:volumettc` + `thm:runtime` with the regime condition made legible.**

`Ttc.ttc_volume_inputs` with `big` replaced by

```
hvol : P.thresh / 4 ≤ volSol (atomSet atoms) φ
```

— *the solution set is at least a quarter of the threshold*.  Same 17 binders, same
conclusion; the last one is now a scalar inequality about `Vol(F)` rather than a
quantified statement about the sampler's internals. -/
theorem ttc_volume_vol
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))
    (hcoeff : ∀ j : FacetIndex (toDNFd φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNFd φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region (atomSet atoms) i.val)
    (hvol : (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).thresh / 4
      ≤ volSol (atomSet atoms) φ) :
    (1 - δ ≤
      (∫⁻ c, trajLaw (runRates atoms φ ε δ hε0 hε1 hn hφ hbdd cen gammaHat c)
            {t | ttcRunOutput atoms φ ε δ hε0 hε1 hn hφ hbdd cen gammaHat c t
              ∈ relErr ε (volSol (atomSet atoms) φ)}
          ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (runCount atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).thresh →
      Terminates (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd)
          (runOracles atoms φ ε δ hε0 hε1 hn hφ hbdd cen gammaHat c t) (toDNFd φ) →
      runCost (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd)
          (runOracles atoms φ ε δ hε0 hε1 hn hφ hbdd cen gammaHat c t)
          cVol cSample (runPrec atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) (toDNFd φ)
        ≤ (toDNFd φ).length * (cVol + cSample * thr)) :=
  ttc_volume_inputs atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hbdd hcoeff
    cen gammaHat hgammaHat ball_subset
    (fun c hc => big_of_volume atoms (toDNFd_isDNFOf φ) (toDNFd_isPositive hφ)
      (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd) rfl le_rfl
      (one_le_card_facets_of_isBounded hn (toDNFd_isDNFOf φ) hbdd (toDNFd_ne_nil hφ))
      le_rfl (normal_ne_zero_of_coeff_ne_zero hcoeff) hbdd cen hgammaHat ball_subset
      rfl hvol hc)

end Measured

end Inputs

end Ttc

/-! ## Axiom profile -/

#check @Ttc.ttc_volume_inputs

#print axioms Ttc.ttc_volume_inputs
#print axioms Ttc.ttc_volume_vol

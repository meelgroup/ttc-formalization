/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Inputs
import Ttc.Witness.TwoCube

/-!
# `Witness/Inputs`: `Ttc.ttc_volume_inputs` is not vacuous

`Ttc.ttc_volume_inputs` (`Exec/Inputs.lean`) is a `∀` under **17 hypotheses**

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hbdd hcoeff cen gammaHat hgammaHat ball_subset big
```

and a `∀` whose hypotheses nothing satisfies is worth nothing (`CLAUDE.md` §11).
This file exhibits data that satisfies all of them, at **every** `n ≥ 1` and
**every** `(ε, δ) ∈ (0,1]²`, and then pins the conclusion at two parameter numerals
where the achieved bound is proved **strictly positive inside the statement** — so
the conclusion is not the vacuous `0 ≤ (…).toReal` that
`ENNReal.toReal ⊤ = 0` would otherwise permit.

The instance is the **two-cube** one of `Ttc/Witness/TwoCube.lean`: the pair of
disjoint boxes `[0,c]ⁿ` and `[lo, lo+c]ⁿ` with `c = max 1 Thresh(ε, 4δ/5)` and
`lo > c` a multiple of the lattice spacing.  Nothing new is assumed here: every
hypothesis is discharged by a lemma that file already proves, transported along one
list equality.

## What is landed

| result | content |
| --- | --- |
| `Ttc.TwoCube.toDNFd_twoForm` | the two-cube DNF is `Nodup`, so `Ttc.toDNFd` **is** `Ttc.toDNF` on it |
| `Ttc.TwoCube.inputParams_eq` | `Ttc.inputParams` at this instance **is** `Ttc.TwoCube.parT` at `δ₀ = 4δ/5` |
| `Ttc.TwoCube.coeff_ne_zero_two_d`, `ball_subset_two_d`, `big_two_d` | `hcoeff`, `ball_subset` and `big`, at the deduplicated cube list |
| `Ttc.TwoCube.ttc_volume_inputs_two_cube` | `Ttc.ttc_volume_inputs` itself, at every `(ε, δ) ∈ (0,1]²` |
| `Ttc.TwoCube.twoProbD_eq_twoProb` | the deduplicated run **is** the `Ttc.toDNF` run, here |
| `Ttc.TwoCube.ttc_volume_inputs_two_cube_at` | the same at `(1/3, 9/10)` and `(1/2, 1/4)`, bounds `1/10` and `3/4`, both proved positive |

No `Prop`, `structure` or `class` bundling a hypothesis is introduced.  The six
`def`s of this file (`Ttc.TwoCube.cenD`, `sampTd`, `volTd`, `ratesTd`, `twoProbD`,
`twoAccD`) are pure abbreviations for terms `Ttc.ttc_volume_inputs` puts in its own
slots; each carries a lemma identifying it (`Ttc.TwoCube.cenD_toDNF`,
`Ttc.TwoCube.twoProbD_def`, `Ttc.TwoCube.twoProbD_eq_twoProb`), and none of them
asserts anything.

## The one thing that had to be bridged: `Ttc.toDNFd` versus `Ttc.toDNF`

`Ttc.ttc_volume_inputs` pins the AllSAT call to the **duplicate-free**
`Ttc.toDNFd` — that is how it discharges `hlen`, which `Ttc.toDNF` provably fails
(`Ttc.toDNF_length_gt_card_cubes`).  The two-cube witness, on the other hand, is
built throughout over `Ttc.toDNF (twoForm n)`, and the cube index type
`{c // c ∈ toDNFd (twoForm n)}` is *not* the type `{c // c ∈ Ttc.toDNF (twoForm n)}`
that `cen`, `hcoeff`, `ball_subset` and `big` are indexed by.

The bridge is `Ttc.TwoCube.toDNFd_twoForm`: the two-cube DNF is `[cubeL, cubeR]`
with `cubeL ≠ cubeR` (`Ttc.TwoCube.toDNF_twoForm`, `Ttc.TwoCube.cubeL_ne_cubeR`),
hence `Nodup`, hence its own `List.dedup` (`List.Nodup.dedup`).  So on **this**
instance the two lists are equal and the transport is a rewrite.  The only care
needed is that the rewrite must not be blocked by a dependent motive, which is why
`Ttc.TwoCube.cenD` takes the cube list as a *parameter* instead of being fixed at one
of the two lists: with `cen` a function of `D`, every hypothesis is uniform in `D`
and `rw [toDNFd_twoForm]` is type-correct.

**This equality is special to this witness, not a general fact.**  In general
deduplication removes cubes, so it shrinks `m = Nat.card {c // c ∈ D}`, and
`Ttc.Params.deltaPrime = δ₀/(4m)` therefore *grows*: every surviving cube is
estimated at a looser confidence.  That is a genuinely different run, and
`Exec/Dedup.lean` says so.  Here it is a no-op — `m = 2` either way — which is
exactly why the transport is available at all.

## Cost caveat

Unchanged from `Ttc.TwoCube.ttc_volume_final_two_cube`, and stated with the result:
the construction is **exponential in `n` on both oracle routes** — the volume
estimator is hit-and-miss Monte Carlo at `Θ(Rⁿ/(ε'²δ'))` samples, the ball walk's
certified step count is `2^Θ(n)·log(M·Vol(P′)/ε′)`, and the lattice transcription
enumerates `Ttc.latticeCount ≈ Θ((c·10^ρ)ⁿ)` points — and with `m = 2` **each of
those costs is paid twice**, once per cube.  The charged bound
`m·(C_vol + C_sample·Thresh)` grows with `m`, and `Thresh` itself carries a `log m`.
What is established is unconditional *correctness*, not efficiency; `thm:runtime`
remains out of scope.
-/

namespace Ttc

namespace TwoCube

open MeasureTheory Set Pointwise

variable {n : ℕ}

/-- **The two-cube DNF is already duplicate-free**, so deduplication is the identity
on it. -/
theorem toDNFd_twoForm (n : ℕ) (hn : 1 ≤ n) :
    Ttc.toDNFd (twoForm n) = Ttc.toDNF (twoForm n) := by
  have hnd : (Ttc.toDNF (twoForm n)).Nodup := by
    rw [toDNF_twoForm]
    simp [cubeL_ne_cubeR hn]
  exact @List.Nodup.dedup _ (Classical.decEq (Cube (A2 n))) _ hnd

/-- `Ttc.atomSet` at the witness's atoms **is** the witness's interpretation. -/
theorem atomSet_atomsT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Ttc.atomSet (atomsT n hn ε δ hε0 hε1) = MTT n hn ε δ hε0 hε1 := rfl

/-- `Ttc.ttcParams` depends on the DNF only through the two counts, and its two
side conditions are `Prop`s, so equal DNFs give equal parameter blocks. -/
theorem ttcParams_congr {A : Type*} {D D' : DNF A} (h : D = D') (n : ℕ) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ D}) (hr : 1 ≤ Nat.card (FacetIndex D))
    (hm' : 1 ≤ Nat.card {c : Cube A // c ∈ D'}) (hr' : 1 ≤ Nat.card (FacetIndex D')) :
    ttcParams D n ε δ hε0 hε1 hn hm hr = ttcParams D' n ε δ hε0 hε1 hn hm' hr' := by
  subst h; rfl

/-- **The parameter block `Ttc.ttc_volume_inputs` computes is the witness's own.** -/
theorem inputParams_eq (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    inputParamsTotal (atomsT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n) ε δ
      = parT n hn ε (4 * δ / 5) hε0 hε1 :=
  (inputParamsTotal_eq_inputParams _ _ _ _ hε0 hε1 hn twoForm_isPositive
        (isBounded_sol_T n hn ε (4 * δ / 5) hε0 hε1)).trans
    (ttcParams_congr (toDNFd_twoForm n hn) n ε (4 * δ / 5) hε0 hε1 hn _ _ _ _)

open scoped Classical in
/-- **The two ball centres, as a function of the cube list.**  The body of
`Ttc.TwoCube.cenT` never looks at the membership proof, so it makes sense over *any*
DNF; keeping the list a parameter is what lets `Ttc.TwoCube.toDNFd_twoForm` be
rewritten under it. -/
noncomputable def cenD (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (D : DNF (A2 n)) : {c : Cube (A2 n) // c ∈ D} → Space n :=
  fun i => if i.val = cubeL n then sbCentre n 0 (sideT n hn ε δ hε0 hε1)
    else sbCentre n (loT n hn ε δ hε0 hε1) (sideT n hn ε δ hε0 hε1)

/-- At `Ttc.toDNF (twoForm n)` it is the witness's own centre map. -/
theorem cenD_toDNF (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    cenD n hn ε δ hε0 hε1 (Ttc.toDNF (twoForm n)) = cenT n hn ε δ hε0 hε1 := rfl

/-! ## The three data hypotheses, transported to `Ttc.toDNFd` -/

/-- **`hcoeff` at `Ttc.toDNFd`.** -/
theorem coeff_ne_zero_two_d (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ j : FacetIndex (Ttc.toDNFd (twoForm n)),
      (atomsT n hn ε δ hε0 hε1 j.2.val.atom).coeff ≠ 0 := by
  rw [toDNFd_twoForm n hn]
  exact coeff_ne_zero_two _ _

/-- **`ball_subset` at `Ttc.toDNFd`.** -/
theorem ball_subset_two_d (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ i : {c : Cube (A2 n) // c ∈ Ttc.toDNFd (twoForm n)},
      Metric.ball (cenD n hn ε δ hε0 hε1 (Ttc.toDNFd (twoForm n)) i) (gamT n hn ε δ hε0 hε1)
        ⊆ region (MTT n hn ε δ hε0 hε1) i.val := by
  rw [toDNFd_twoForm n hn, cenD_toDNF]
  exact ball_subset_two n hn ε δ hε0 hε1

/-- **`big` at `Ttc.toDNFd`**, in the parameter block `Ttc.TwoCube.parT`. -/
theorem big_two_d (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ c ∈ mcGood (MTT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n))
        (cenD n hn ε δ hε0 hε1 (Ttc.toDNFd (twoForm n))) (gamT n hn ε δ hε0 hε1)
        (parT n hn ε δ hε0 hε1).epsPrime (parT n hn ε δ hε0 hε1).deltaPrime,
      (1 - (parT n hn ε δ hε0 hε1).epsPrime) * (parT n hn ε δ hε0 hε1).thresh / 8
        ≤ ∑ s, rates (MTT n hn ε δ hε0 hε1) (twoForm n) (Ttc.toDNFd (twoForm n))
            (rhoT n hn ε δ hε0 hε1)
            (e2eSampD (MTT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n))
              (rhoT n hn ε δ hε0 hε1) (parT n hn ε δ hε0 hε1).epsPrime
              (canonRfac (Ttc.toDNFd (twoForm n)))
              (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNFd (twoForm n)))))
              (canonAm (atomsT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n)))
              (canonBv (atomsT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n))
                (latticeScale (rhoT n hn ε δ hε0 hε1)))
              (cenD n hn ε δ hε0 hε1 (Ttc.toDNFd (twoForm n))) (gamT n hn ε δ hε0 hε1)
              (canonDm (MTT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n))
                (rhoT n hn ε δ hε0 hε1)))
            (mcVol (MTT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n))
              (cenD n hn ε δ hε0 hε1 (Ttc.toDNFd (twoForm n))) (gamT n hn ε δ hε0 hε1)
              (parT n hn ε δ hε0 hε1).epsPrime (parT n hn ε δ hε0 hε1).deltaPrime c) s := by
  rw [toDNFd_twoForm n hn, cenD_toDNF]
  exact fun c hc => big_two n hn ε δ hε0 hε1 hδ0 hδ1 c hc

/-! ## The run, named

Pure abbreviations, mirroring `Ttc.TwoCube.sampT`, `volT`, `ratesT`, `twoProb` and
`twoAcc` one-for-one at the deduplicated cube list.  They assert nothing; each is the
term `Ttc.ttc_volume_inputs` puts in that slot.
-/

/-- The sampler's discrete law, at `Ttc.toDNFd` — `Ttc.TwoCube.sampT`'s definition
with the cube list deduplicated. -/
noncomputable def sampTd (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Cube (A2 n) → Space n → ℝ :=
  e2eSampD (MTT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n)) (rhoT n hn ε δ hε0 hε1)
    (parT n hn ε δ hε0 hε1).epsPrime (canonRfac (Ttc.toDNFd (twoForm n)))
    (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNFd (twoForm n)))))
    (canonAm (atomsT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n)))
    (canonBv (atomsT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n))
      (latticeScale (rhoT n hn ε δ hε0 hε1)))
    (cenD n hn ε δ hε0 hε1 (Ttc.toDNFd (twoForm n))) (gamT n hn ε δ hε0 hε1)
    (canonDm (MTT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n)) (rhoT n hn ε δ hε0 hε1))

/-- The Monte-Carlo volume oracle's output, at `Ttc.toDNFd`. -/
noncomputable def volTd (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (c : ℕ → Space n) : Cube (A2 n) → ℝ :=
  mcVol (MTT n hn ε δ hε0 hε1) (Ttc.toDNFd (twoForm n))
    (cenD n hn ε δ hε0 hε1 (Ttc.toDNFd (twoForm n))) (gamT n hn ε δ hε0 hε1)
    (parT n hn ε δ hε0 hε1).epsPrime (parT n hn ε δ hε0 hε1).deltaPrime c

/-- The constructed level-`0` rates, at `Ttc.toDNFd`. -/
noncomputable def ratesTd (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (c : ℕ → Space n) :
    Fin (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1)) → ℝ :=
  rates (MTT n hn ε δ hε0 hε1) (twoForm n) (Ttc.toDNFd (twoForm n))
    (rhoT n hn ε δ hε0 hε1) (sampTd n hn ε δ hε0 hε1) (volTd n hn ε δ hε0 hε1 c)

/-- The probability `Ttc.ttc_volume_inputs` bounds on this witness: an abbreviation
for the integral, asserting nothing (`Ttc.TwoCube.twoProbD_def`).  Its `δ` argument is
the **internal** failure parameter `δ₀ = 4δ/5`. -/
noncomputable def twoProbD (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ENNReal :=
  ∫⁻ c, trajLaw (ratesTd n hn ε δ hε0 hε1 c)
      {t : ℕ → Fin (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n)
          (rhoT n hn ε δ hε0 hε1)) → ℕ |
        ttcOutput (parT n hn ε δ hε0 hε1)
            (coveredOracles (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1)
              (volTd n hn ε δ hε0 hε1 c))
            Ttc.toDNFd (rhoT n hn ε δ hε0 hε1) (twoForm n) t
          ∈ relErr ε (volSol (MTT n hn ε δ hε0 hε1) (twoForm n))}
    ∂(MonteCarlo.coins n)

theorem twoProbD_def (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    twoProbD n hn ε δ hε0 hε1 =
      ∫⁻ c, trajLaw (ratesTd n hn ε δ hε0 hε1 c)
          {t : ℕ → Fin (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n)
              (rhoT n hn ε δ hε0 hε1)) → ℕ |
            ttcOutput (parT n hn ε δ hε0 hε1)
                (coveredOracles (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1)
                  (volTd n hn ε δ hε0 hε1 c))
                Ttc.toDNFd (rhoT n hn ε δ hε0 hε1) (twoForm n) t
              ∈ relErr ε (volSol (MTT n hn ε δ hε0 hε1) (twoForm n))}
        ∂(MonteCarlo.coins n) := rfl

/-- The same quantity as a real number. -/
noncomputable def twoAccD (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  (twoProbD n hn ε δ hε0 hε1).toReal

/-! ## The witness -/

/-- **`Ttc.ttc_volume_inputs` on a DNF with two cubes**, at every `(ε, δ) ∈ (0,1]²`
and every `n ≥ 1`.

All 17 hypotheses are met by the two-cube data of `Ttc/Witness/TwoCube.lean`:
`hφ` is `Ttc.TwoCube.twoForm_isPositive`, `hbdd` is `Ttc.TwoCube.isBounded_sol_T`,
`hcoeff`/`ball_subset`/`big` are that file's own lemmas transported along
`Ttc.TwoCube.toDNFd_twoForm`, and `cen`/`gammaHat` are the two distinct box centres
with the shared inscribed radius `c/2`.  The parameter block the theorem computes is
`Ttc.TwoCube.parT` at the internal `δ₀ = 4δ/5` (`Ttc.TwoCube.inputParams_eq`), so
`m = 2` and `Ttc.Params.deltaPrime = δ₀/8` really is the two-call union bound.

The accuracy conjunct is `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1 − δ` in the **user's** `δ`;
the runtime conjunct is `alg:ttc`'s charged cost `m·(C_vol + C_sample·Thresh)` under
`Ttc.Terminates`.

**Cost — exponential in `n`, and paid twice.**  See this module's docstring: both
oracle routes are exponential in the dimension and `m = 2` pays each of them once per
cube.  Unconditional correctness, not efficiency. -/
theorem ttc_volume_inputs_two_cube (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ ≤ twoAccD n hn ε (4 * δ / 5) hε0 hε1)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount (MTT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n)
          (rhoT n hn ε (4 * δ / 5) hε0 hε1)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (parT n hn ε (4 * δ / 5) hε0 hε1).thresh →
      Terminates (parT n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles (MTT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n)
            (rhoT n hn ε (4 * δ / 5) hε0 hε1) (volTd n hn ε (4 * δ / 5) hε0 hε1 c) t)
          (Ttc.toDNFd (twoForm n)) →
      runCost (parT n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles (MTT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n)
            (rhoT n hn ε (4 * δ / 5) hε0 hε1) (volTd n hn ε (4 * δ / 5) hε0 hε1 c) t)
          cVol cSample (rhoT n hn ε (4 * δ / 5) hε0 hε1) (Ttc.toDNFd (twoForm n))
        ≤ (Ttc.toDNFd (twoForm n)).length * (cVol + cSample * thr)) := by
  have h0 : (0 : ℝ) < 4 * δ / 5 := by linarith
  have h1 : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  have h := ttc_volume_inputs (atomsT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n) ε δ
    hε0 hε1 hδ0 hδ1 hn twoForm_isPositive (isBounded_sol_T n hn ε (4 * δ / 5) hε0 hε1)
    (coeff_ne_zero_two_d n hn ε (4 * δ / 5) hε0 hε1)
    (cenD n hn ε (4 * δ / 5) hε0 hε1 (Ttc.toDNFd (twoForm n)))
    (gamT n hn ε (4 * δ / 5) hε0 hε1) (gamT_pos n hn ε (4 * δ / 5) hε0 hε1)
    (ball_subset_two_d n hn ε (4 * δ / 5) hε0 hε1)
    (by rw [inputParams_eq n hn ε δ hε0 hε1]
        exact big_two_d n hn ε (4 * δ / 5) hε0 hε1 h0 h1)
  rw [inputParams_eq n hn ε δ hε0 hε1] at h
  exact h

/-- **On this witness the deduplicated run is the run.**  Both cube lists are equal
(`Ttc.TwoCube.toDNFd_twoForm`), so the whole integrand — sampler law, volume oracle,
rates, oracles and output — coincides with `Ttc.TwoCube.twoProb`'s.  This is special
to a witness whose DNF happens to be `Nodup`; in general `Ttc.toDNFd` shrinks `m` and
changes `Ttc.Params.deltaPrime`. -/
theorem twoProbD_eq_twoProb (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    twoProbD n hn ε δ hε0 hε1 = twoProb n hn ε δ hε0 hε1 := by
  unfold twoProbD twoProb ratesTd ratesT sampTd sampT volTd volT
  simp only [ttcOutput]
  rw [toDNFd_twoForm n hn, cenD_toDNF]

/-- The real-valued form of `Ttc.TwoCube.twoProbD_eq_twoProb`: the bound
`Ttc.ttc_volume_inputs` certifies here is the very number
`Ttc.TwoCube.ttc_volume_final_two_cube` certifies. -/
theorem twoAccD_eq_twoAcc (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    twoAccD n hn ε δ hε0 hε1 = twoAcc n hn ε δ hε0 hε1 := by
  rw [twoAccD, twoAcc, twoProbD_eq_twoProb]

/-- **The two-cube guarantee of `Ttc.ttc_volume_inputs`, on the named probability.** -/
theorem two_cube_inputs_acc_ge (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ twoAccD n hn ε (4 * δ / 5) hε0 hε1 :=
  (ttc_volume_inputs_two_cube n hn ε δ hε0 hε1 hδ0 hδ1).1

/-- **`Ttc.ttc_volume_inputs` on a two-cube DNF at two structurally different
parameter pairs, with the achieved bound a positive numeral.**

* `(ε, δ) = (1/3, 9/10)`: bound `1/10 > 0`, at a `δ ∈ (4/5, 1)` where
  `Ttc.ttc_volume_endToEnd`'s budget `1 − δ − δ/4 = −1/8` certifies nothing.
* `(ε, δ) = (1/2, 1/4)`: a different accuracy *and* confidence, so the two runs have
  different sides `Ttc.TwoCube.sideT`, different precisions `Ttc.TwoCube.rhoT`,
  different corners `Ttc.TwoCube.loT` and different parameter blocks
  `Ttc.TwoCube.parT` — two instances, not one instance twice.

Both numerals are proved strictly positive **in the statement**, so neither conclusion
is the vacuous `0 ≤ (…).toReal`.  Both runs carry the exponential cost of
`Ttc.TwoCube.ttc_volume_inputs_two_cube`, twice over. -/
theorem ttc_volume_inputs_two_cube_at (n : ℕ) (hn : 1 ≤ n)
    (hε₁ : (0 : ℝ) < 1/3) (hε₁' : (1/3 : ℝ) ≤ 1)
    (hε₂ : (0 : ℝ) < 1/2) (hε₂' : (1/2 : ℝ) ≤ 1) :
    ((0 : ℝ) < 1/10 ∧ (1/10 : ℝ) ≤ twoAccD n hn (1/3) (4 * (9/10) / 5) hε₁ hε₁'
      ∧ (4/5 : ℝ) < 9/10 ∧ (9/10 : ℝ) < 1)
    ∧ ((0 : ℝ) < 3/4 ∧ (3/4 : ℝ) ≤ twoAccD n hn (1/2) (4 * (1/4) / 5) hε₂ hε₂') := by
  refine ⟨⟨by norm_num, ?_, by norm_num, by norm_num⟩, ⟨by norm_num, ?_⟩⟩
  · have h := two_cube_inputs_acc_ge n hn (1/3) (9/10) hε₁ hε₁' (by norm_num) (by norm_num)
    linarith
  · have h := two_cube_inputs_acc_ge n hn (1/2) (1/4) hε₂ hε₂' (by norm_num) (by norm_num)
    linarith

/-- **The bound is a genuine number, not `ENNReal.toReal ⊤ = 0`.**  A strictly
positive lower bound on the `toReal` forces the measure itself to be nonzero and
finite. -/
theorem twoProbD_pos_ne_top (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1/3) (hε1 : (1/3 : ℝ) ≤ 1) :
    0 < twoProbD n hn (1/3) (4 * (9/10) / 5) hε0 hε1
      ∧ twoProbD n hn (1/3) (4 * (9/10) / 5) hε0 hε1 ≠ ⊤ := by
  have h := (ttc_volume_inputs_two_cube_at n hn hε0 hε1 (by norm_num) (by norm_num)).1.2.1
  have hpos : 0 < (twoProbD n hn (1/3) (4 * (9/10) / 5) hε0 hε1).toReal :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/10) h
  exact ⟨(ENNReal.toReal_pos_iff.1 hpos).1, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩

end TwoCube

end Ttc

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout — no `sorry`, no custom axiom,
no `native_decide`. -/

#check @Ttc.TwoCube.ttc_volume_inputs_two_cube

#print axioms Ttc.TwoCube.toDNFd_twoForm
#print axioms Ttc.TwoCube.atomSet_atomsT
#print axioms Ttc.TwoCube.ttcParams_congr
#print axioms Ttc.TwoCube.inputParams_eq
#print axioms Ttc.TwoCube.cenD
#print axioms Ttc.TwoCube.cenD_toDNF
#print axioms Ttc.TwoCube.coeff_ne_zero_two_d
#print axioms Ttc.TwoCube.ball_subset_two_d
#print axioms Ttc.TwoCube.big_two_d
#print axioms Ttc.TwoCube.sampTd
#print axioms Ttc.TwoCube.volTd
#print axioms Ttc.TwoCube.ratesTd
#print axioms Ttc.TwoCube.twoProbD
#print axioms Ttc.TwoCube.twoProbD_def
#print axioms Ttc.TwoCube.twoAccD
#print axioms Ttc.TwoCube.ttc_volume_inputs_two_cube
#print axioms Ttc.TwoCube.twoProbD_eq_twoProb
#print axioms Ttc.TwoCube.twoAccD_eq_twoAcc
#print axioms Ttc.TwoCube.two_cube_inputs_acc_ge
#print axioms Ttc.TwoCube.ttc_volume_inputs_two_cube_at
#print axioms Ttc.TwoCube.twoProbD_pos_ne_top

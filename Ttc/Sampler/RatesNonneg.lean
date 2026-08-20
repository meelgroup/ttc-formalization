/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Api
import Ttc.Exec.Inputs
import Ttc.Exec.Inscribed
import Ttc.Exec.ScaleFactor

/-!
# `Sampler/RatesNonneg`: `0 ≤ θ s`, for the constructed rates

`Ttc/Process/Truncation.lean` proves that the absorption loops terminate
`Ttc.trajLaw`-almost surely under the single hypothesis

```lean
hθ : ∀ s, 0 ≤ θ s
```

To apply it at the *constructed* rate vector one needs exactly that statement for
`Ttc.rates`, and — after the plumbing of `Exec/Inputs` — for `Ttc.runRates`.

`Ttc/Sampler/Rates.lean` already has `Ttc.rates_pos`, but it is a **strictly
stronger** statement bought with two side conditions that nonnegativity does not
need: `0 < vol i` (which, at the constructed volume oracle, is only available on
the Monte-Carlo good event `Ttc.mcGood`, see `Ttc.mcVol_pos`) and strict positivity
of the sampler's mass at the enumerated points (which comes from
`eq:almostuniform`, hence from `ε' < 1` and a nonempty finite lattice).  This file
shows that the *weak* inequality is genuinely cheaper:

* `Ttc.kv97SampD_nonneg` — **no hypothesis at all**.  The constructed discrete law
  is a quotient of an integral of `Arlib.Lattice.Rounding.prodTent ≥ 0` by a
  `finsum` of such integrals; both are nonnegative, and `x / 0 = 0` makes the
  degenerate denominator harmless.  Consequently `Ttc.e2eSampD_nonneg` is
  hypothesis-free too.
* `Ttc.MonteCarlo.est_nonneg` — **no hypothesis at all**: `Ttc.MonteCarlo.scale` is
  unconditionally positive (`Ttc.MonteCarlo.scale_pos`, since
  `Ttc.MonteCarlo.rad` is defined to be `1` when no enclosing radius exists) and the
  scores are indicators.
* `Ttc.mcVol_nonneg` — one hypothesis, `0 ≤ γ`, and only because the prefactor is
  `γ ^ n` with `n` possibly odd.  At the run this is `Ttc.autoGamma`-derived and is
  supplied by `hgammaHat : 0 < γ̂`, i.e. it costs nothing new.

So the answer to "is nonnegativity really weaker than `Ttc.rates_pos`?" is **yes**:
`0 < vol i` is *not* needed, and neither is `eq:almostuniform`.  The only residue is
the sign of the inscribed radius in `γ ^ n`, and that is free too
(`Ttc.runScale_mul_autoGamma_nonneg`, Part 5).

## `Ttc.ttcRates`

`Ttc.ttcRates` (`Ttc/Exec/Api.lean`) is `Ttc.runRates` applied to `Ttc.ttcAtoms`,
`Ttc.ttcInput`, `Ttc.ttcCen` and `Ttc.ttcScaledRadius`, and `Ttc.ttcScaledRadius` is
by definition `Ttc.runScale … * Ttc.autoGamma …`.  So

```lean
theorem ttcRates_nonneg … (c) (s) : 0 ≤ ttcRates atoms φ ε δ c s :=
  runRates_nonneg _ _ _ _ _ (runScale_mul_autoGamma_nonneg atoms _ ε δ) c s
```

is the whole specialisation, and it is **Part 6** of this file
(`Ttc.ttcRates_nonneg`).  It is **unconditional**: not one of `hε0`, `hε1`, `hn`,
`hφ`, `hpos` is needed, and neither is anything about the run.  (After the `Exec/Api`
proof-binder strip, `Ttc.ttcRates` is a `def` taking only `atoms φ ε δ c`, so those
binders are not even in scope to be dropped.)
-/

namespace Ttc

open MeasureTheory Set

/-! ## Part 1.  `0 ≤ θ s` for `Ttc.rates`, in two forms -/

variable {A : Type*} {n : ℕ}

/-- **`0 ≤ θ s`, in the totally hypothesis-free form.**  `Ttc.rates` is a product of
a sampler mass and a volume estimate, so nonnegativity of the two factors — at
*every* cube, which is how both constructed oracles come — is all it takes.  In
particular there is no `IsDNFOf`, no `HasLatticeEnum` and no positivity anywhere. -/
theorem rates_nonneg (M : A → Set (Space n)) (φ : BForm A) (D : DNF A) (ρ : ℤ)
    {sampD : Cube A → Space n → ℝ} {vol : Cube A → ℝ}
    (hsamp : ∀ i x, 0 ≤ sampD i x) (hvol : ∀ i, 0 ≤ vol i)
    (s : Fin (latticeCount M φ ρ)) : 0 ≤ rates M φ D ρ sampD vol s :=
  mul_nonneg (hsamp _ _) (hvol _)

/-- **`0 ≤ θ s`, with the two factors only assumed nonnegative on the
decomposition** — the exact analogue of `Ttc.rates_pos`'s hypothesis shape, with
`<` weakened to `≤`.  `Ttc.cubeAt_spec` puts the chosen cube in `D` and the
enumerated point in its region, which is what lets the localised hypotheses
apply. -/
theorem rates_nonneg_of_mem {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ)
    {sampD : Cube A → Space n → ℝ} {vol : Cube A → ℝ}
    (hvol : ∀ i ∈ D, 0 ≤ vol i)
    (hsamp : ∀ i ∈ D, ∀ x ∈ region M i ∩ fineLattice n (latticeScale ρ), 0 ≤ sampD i x)
    (s : Fin (latticeCount M φ ρ)) : 0 ≤ rates M φ D ρ sampD vol s := by
  obtain ⟨hmem, hreg⟩ := cubeAt_spec hDNF hle s
  exact mul_nonneg
    (hsamp _ hmem _ ⟨hreg, (latticeEnum_mem hle s).2⟩)
    (hvol _ hmem)

/-! ## Part 2.  The constructed sampler mass is nonnegative, unconditionally

`Ttc.kv97SampD` is
`(∫ p, prodTent (10^ρ • x) p ∂law) / (∑ᶠ k ∈ (10^ρ • P(c)) ∩ ℤⁿ, ∫ p, prodTent k p ∂law)`
on a cube of `D` and `0` off it.  `Arlib.Lattice.Rounding.prodTent` is a product of
tents `max (1 − |·|) 0`, hence nonnegative pointwise, so both the numerator and every
summand of the denominator are nonnegative integrals; `finsum_nonneg` handles the
possibly-infinite index type and `div_nonneg` finishes.  Nothing is assumed about
`law` — not even that it is a probability measure.
-/

/-- **The constructed discrete law is nonnegative, with no hypotheses.**  Note that
this holds even when the normalising `finsum` is `0` (or not summable, in which case
`finsum` is `0` by definition): `x / 0 = 0`. -/
theorem kv97SampD_nonneg (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (law : {c : Cube A // c ∈ D} → Measure (Space n)) (i : Cube A) (x : Space n) :
    0 ≤ kv97SampD M D ρ law i x := by
  classical
  rw [kv97SampD]
  split
  · exact div_nonneg
      (integral_nonneg fun p => Arlib.Lattice.Rounding.prodTent_nonneg _ p)
      (finsum_nonneg fun _ => integral_nonneg fun p =>
        Arlib.Lattice.Rounding.prodTent_nonneg _ p)
  · exact le_rfl

/-- **`Ttc.e2eSampD` is nonnegative, with no hypotheses.**  It is `Ttc.kv97SampD` at
a particular `law`, and `Ttc.kv97SampD_nonneg` does not look at `law`. -/
theorem e2eSampD_nonneg (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (epsPrime rfac : ℝ) {Jt : Type}
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ)
    (Dm : {c : Cube A // c ∈ D} → ℝ) (i : Cube A) (x : Space n) :
    0 ≤ e2eSampD M D ρ epsPrime rfac Am bv cen gammaHat Dm i x :=
  kv97SampD_nonneg M D ρ _ i x

/-! ## Part 3.  The constructed volume estimate is nonnegative -/

namespace MonteCarlo

/-- Each score is an indicator of the constant `1`, hence nonnegative. -/
theorem score_nonneg (K : Set (Space n)) (i : ℕ) (ω : ℕ → Space n) : 0 ≤ score K i ω :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- **`0 ≤ Vol_ED`'s raw estimate, with no hypotheses.**  `Ttc.MonteCarlo.scale` is
unconditionally positive (`Ttc.MonteCarlo.scale_pos` — `Ttc.MonteCarlo.rad` falls
back to `1` when no enclosing radius exists), the sample count is a successor, and
the scores are indicators. -/
theorem est_nonneg (K : Set (Space n)) (ε pf : ℝ) (ω : ℕ → Space n) :
    0 ≤ est K ε pf ω := by
  refine mul_nonneg (div_nonneg (scale_pos K).le (Nat.cast_nonneg _)) ?_
  exact Finset.sum_nonneg fun i _ => score_nonneg K i ω

end MonteCarlo

/-- **`0 ≤ Vol_ED` at the coins**, for every cube — on the DNF and off it.

The single hypothesis is `0 ≤ γ`: the estimate carries the prefactor `γ ^ n`, which
for odd `n` is negative when `γ < 0`.  Every caller has `0 < γ̂` already
(`Ttc.ttc_volume`'s `hgammaHat`), so this is not a new demand.  In particular **no**
`Ttc.mcGood` / good-event hypothesis is needed, unlike `Ttc.mcVol_pos`. -/
theorem mcVol_nonneg (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) {γ : ℝ} (hγ : 0 ≤ γ) (ε' δ' : ℝ)
    (c : ℕ → Space n) (i : Cube A) : 0 ≤ mcVol M D cen γ ε' δ' c i := by
  classical
  rw [mcVol]
  split
  · exact mul_nonneg (pow_nonneg hγ n) (MonteCarlo.est_nonneg _ _ _ c)
  · exact le_rfl

/-! ## Part 4.  The specialisation at the run's rate vector

`Ttc.runRates` (`Exec/Inputs`) is `Ttc.rates` at `Ttc.e2eSampD` and `Ttc.mcVol`, so
Parts 1–3 combine into a statement whose only hypothesis is the sign of the
inscribed radius.
-/

/-- **`0 ≤ θ s` for the run's constructed rate vector.**

Exactly the hypothesis `Ttc/Process/Truncation.lean` asks of `θ`, at
`Ttc.runRates` — the rate vector `Ttc.ttcRates` (`Exec/Api`) is a definitional
wrapper of.  The one hypothesis, `0 ≤ γ̂`, is weaker than the `hgammaHat : 0 < γ̂`
every consumer already carries; in particular neither `Ttc.mcGood`, nor `0 < vol i`,
nor `eq:almostuniform` appears. -/
theorem runRates_nonneg (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (cen : {c : Cube A // c ∈ toDNFd φ} → Space n) {gammaHat : ℝ} (hγ : 0 ≤ gammaHat)
    (c : ℕ → Space n) (s : Fin (runCount atoms φ ε δ gammaHat)) :
    0 ≤ runRates atoms φ ε δ cen gammaHat c s :=
  rates_nonneg _ _ _ _
    (fun i x => e2eSampD_nonneg _ _ _ _ _ _ _ _ _ _ i x)
    (fun i => mcVol_nonneg _ _ _ hγ _ _ c i) s

/-! ## Part 5.  The run's inscribed radius is nonnegative, for free

`Ttc.ttcRates` (`Exec/Api`) is `Ttc.runRates` at `γ̂ := Ttc.ttcScaledRadius`, which is
`Ttc.runScale … * Ttc.autoGamma …`.  Both factors are nonnegative with **no**
hypotheses: `Ttc.scaleFactor` is a `max 1 (…)` raised to `1/n`, and `Ttc.gammaOf` is an infimum of
`Ttc.ballData` radii, which `Ttc.gammaOf_nonneg` shows is `≥ 0` even when the
infimum is over an empty family.  So `Ttc.runRates_nonneg_autoGamma` below is
hypothesis-free, and `Ttc.ttcRates_nonneg` is a `rfl`-application of it — see this
module's docstring, section "`Ttc.ttcRates`", for why that last step is not here. -/

/-- `Ttc.runScale` is nonnegative, with no hypotheses.  (`Ttc.runScale_pos`
(`Exec/Rescaled`) is the same fact, but its statement carries five unused binders
from an `include`; the proof term there is also `Ttc.scaleFactor_pos`.) -/
theorem runScale_nonneg (atoms : A → LinAtom n) (φ : BForm A) (ε δ gammaHat : ℝ) :
    0 ≤ runScale atoms φ ε δ gammaHat :=
  (scaleFactor_pos _ _ _).le

/-- `Ttc.autoGamma`, the `GetPrecision` inscribed radius, is nonnegative with no
hypotheses — `Ttc.gammaOf_nonneg`. -/
theorem autoGamma_nonneg (atoms : A → LinAtom n) (φ : BForm A) :
    0 ≤ autoGamma atoms φ :=
  gammaOf_nonneg _ _

/-- **The dilated inscribed radius — the `γ̂` every run wrapper is applied to — is
nonnegative, with no hypotheses.**  This is `Ttc.ttcScaledRadius atoms φ …` once
`φ` is read as the preprocessed formula `cleanForm atoms (pruneForm atoms φ)`. -/
theorem runScale_mul_autoGamma_nonneg (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ) :
    0 ≤ runScale atoms φ ε δ (autoGamma atoms φ) * autoGamma atoms φ :=
  mul_nonneg (runScale_nonneg _ _ _ _ _) (autoGamma_nonneg _ _)

/-- **`0 ≤ θ s` at the run's *own* inscribed radius, with no hypotheses at all.**

`Ttc.runRates_nonneg` with its single hypothesis discharged by
`Ttc.runScale_mul_autoGamma_nonneg`.  This is the shape `Ttc.ttcRates` has: modulo
the `Exec/Api` abbreviations `Ttc.ttcAtoms`, `Ttc.ttcInput`, `Ttc.ttcCen` and
`Ttc.ttcScaledRadius`, it *is* `∀ s, 0 ≤ ttcRates atoms φ ε δ hε0 hε1 hn hφ hpos c s`. -/
theorem runRates_nonneg_autoGamma (atoms atoms' : A → LinAtom n) (φ ψ : BForm A) (ε δ : ℝ)
    (cen : {c : Cube A // c ∈ toDNFd φ} → Space n) (c : ℕ → Space n)
    (s : Fin (runCount atoms φ ε δ
      (runScale atoms' ψ ε δ (autoGamma atoms' ψ) * autoGamma atoms' ψ))) :
    0 ≤ runRates atoms φ ε δ cen
      (runScale atoms' ψ ε δ (autoGamma atoms' ψ) * autoGamma atoms' ψ) c s :=
  runRates_nonneg atoms φ ε δ cen (runScale_mul_autoGamma_nonneg atoms' ψ ε δ) c s

/-! ## Part 6.  The run's own rate vector, `Ttc.ttcRates`

`Ttc.ttcRates` (`Exec/Api`) is `Ttc.runRates` at `Ttc.ttcAtoms`, `Ttc.ttcInput`,
`Ttc.ttcCen` and `Ttc.ttcScaledRadius`, and `Ttc.ttcScaledRadius` is by definition
`Ttc.runScale atoms (ttcInput atoms φ) ε δ (ttcRadius atoms φ) * ttcRadius atoms φ`
with `Ttc.ttcRadius atoms φ = autoGamma atoms (ttcInput atoms φ)`.  So Part 5's
`Ttc.runScale_mul_autoGamma_nonneg` is *exactly* the missing hypothesis of
`Ttc.runRates_nonneg`, at `atoms' := atoms` and `ψ := Ttc.ttcInput atoms φ`. -/

/-- **`0 ≤ θ s` at the run's rate vector, with no hypotheses at all.**

This is the hypothesis `Ttc.trajLaw_ae_terminates` (`Process/Truncation`) asks of
`θ`, at the vector `Ttc.ttcTrajKernel` (`Monadic/Kernel`) is the trajectory law of:
`Ttc.ttcTrajKernel atoms φ ε δ c = trajLaw (ttcRates atoms φ ε δ c)` by `rfl`.

**Unconditional.**  None of the FPRAS parameter range (`0 < ε ≤ 1`), the dimension
(`1 ≤ n`), the input's shape (`φ.IsPositive`), the nondegeneracy
(`0 < volSol …`) or anything about the volume coins `c` is used — in particular no
`Ttc.mcGood` good event and no `eq:almostuniform`.  The two facts consumed are
Part 4 (a product of two nonnegative factors) and Part 5 (the dilated inscribed
radius is a product of a `max 1 _` with an infimum of radii). -/
theorem ttcRates_nonneg (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (c : ℕ → Space n) (s : Fin (ttcIndex atoms φ ε δ)) :
    0 ≤ ttcRates atoms φ ε δ c s :=
  runRates_nonneg _ _ _ _ _
    (runScale_mul_autoGamma_nonneg atoms (ttcInput atoms φ) ε δ) c s

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms rates_nonneg
#print axioms rates_nonneg_of_mem
#print axioms kv97SampD_nonneg
#print axioms e2eSampD_nonneg
#print axioms MonteCarlo.score_nonneg
#print axioms MonteCarlo.est_nonneg
#print axioms mcVol_nonneg
#print axioms runRates_nonneg
#print axioms runScale_nonneg
#print axioms autoGamma_nonneg
#print axioms runScale_mul_autoGamma_nonneg
#print axioms runRates_nonneg_autoGamma
#print axioms ttcRates_nonneg

end Ttc

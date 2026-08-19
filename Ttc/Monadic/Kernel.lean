/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Api
import Ttc.Coupling.Family

/-!
# `Monadic/Kernel`: the coin-indexed family of trajectory laws is measurable

The headline `Ttc.ttc_volume` states its accuracy conjunct as an iterated
integral,

```
∫⁻ c, trajLaw (ttcRates … c) S ∂(MonteCarlo.coins n)
```

— the outer integral over the volume oracle's coins `c`, the inner measure the law
of the coupled sampling family at the rates that run produced.  To read that as a
*single* measure on `(coins, trajectory)` — that is, as `Measure.bind` — one needs
exactly one fact:

**`c ↦ trajLaw (ttcRates … c)` is a measurable map into `Measure (ℕ → Fin L → ℕ)`.**

This file proves it, in dependency order:

* `Ttc.measurable_mcVol`, `Ttc.measurable_rates_of_measurable_vol`,
  `Ttc.measurable_ttcRates` — the coin dependence of the rate vector.  All of it
  runs through `Ttc.MonteCarlo.measurable_est`; `Ttc.rates` is a product of that
  with a coin-independent factor.
* `Ttc.measurable_poissonMeasure` — `r ↦ Po(r)` is measurable as a map
  `ℝ≥0 → Measure ℕ`.  Not in Mathlib; proved here from
  `ProbabilityTheory.poissonMeasure_singleton` and
  `MeasureTheory.Measure.tsum_indicator_apply_singleton`, `ℕ` being countable and
  discrete.
* `Ttc.measurable_pi_poissonMeasure` — `θ ↦ ⨂ s, Po((θ s)⁺)` is measurable as a map
  `(Fin L → ℝ) → Measure (Fin L → ℕ)`.  Mathlib has no measurability of
  `MeasureTheory.Measure.pi` in its factors and no `Kernel.pi`; but the target
  `Fin L → ℕ` is again countable and discrete, so the same singleton argument
  applies, with `MeasureTheory.Measure.pi_singleton` for the singleton masses.
* `Ttc.measurable_trajMeasure` — `μ₀ ↦ Kernel.trajMeasure μ₀ κ` is measurable, for
  *any* Ionescu–Tulcea family `κ`.  This is immediate from the definition
  `trajMeasure μ₀ κ = traj κ 0 ∘ₘ (μ₀.map _)`, `MeasureTheory.Measure.measurable_bind'`
  and `MeasureTheory.Measure.measurable_map`; the Ionescu–Tulcea kernel is *fixed*,
  only the initial measure varies.
* `Ttc.measurable_trajLaw`, `Ttc.measurable_trajLaw_ttcRates` — the two halves
  composed.
* `Ttc.lintegral_trajLaw_ttcRates_eq_bind` — the payoff: the headline's iterated
  integral *is* the bind, for every measurable event of the trajectory space.

## What is *not* proved here

`Ttc.lintegral_trajLaw_ttcRates_eq_bind` takes `MeasurableSet S` as a hypothesis,
because `MeasureTheory.Measure.bind_apply` does.  The headline's own event

```
{t | ttcAlgOutput … (ttcOracleBundle … c t) ∈ relErr ε (volSol (atomSet atoms) φ)}
```

is *not* shown measurable here — that is a separate obligation about
`Ttc.ttcAlgOutput`'s dependence on the trajectory `t`, and it is the next thing that
has to be established before the headline can be rewritten.  Nothing in this file
assumes it.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Part 1.  The rate vector depends measurably on the volume oracle's coins -/

section Rates

variable {A : Type*} {n : ℕ}

/-- **The constructed volume estimate is measurable in the coins**, at every cube.
Off the DNF it is the constant `0`; on it, it is `γ̂ⁿ` times
`Ttc.MonteCarlo.est`, and that is `Ttc.MonteCarlo.measurable_est`. -/
theorem measurable_mcVol (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) (i : Cube A) :
    Measurable fun c : ℕ → Space n => mcVol M D cen γ ε' δ' c i := by
  classical
  by_cases hi : i ∈ D
  · simp only [mcVol, dif_pos hi]
    exact measurable_const.mul (MonteCarlo.measurable_est _ _ _)
  · simp only [mcVol, dif_neg hi]
    exact measurable_const

/-- **`Ttc.rates` is measurable in whatever its volume estimate is measurable in.**
Coordinate `s` of the rate vector is `sampD` at a coin-independent point times the
volume estimate of a coin-independent cube, so only the second factor moves. -/
theorem measurable_rates_of_measurable_vol (M : A → Set (Space n)) (φ : BForm A)
    (D : DNF A) (ρ : ℤ) (sampD : Cube A → Space n → ℝ)
    (vol : (ℕ → Space n) → Cube A → ℝ)
    (hvol : ∀ i, Measurable fun c : ℕ → Space n => vol c i) :
    Measurable fun c : ℕ → Space n => rates M φ D ρ sampD (vol c) :=
  measurable_pi_lambda _ fun s => measurable_const.mul (hvol (cubeAt M φ D ρ s))

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

/-- **Half (a): the run's rate vector is a measurable function of the volume
oracle's coins.**  `Ttc.ttcRates` is `Ttc.rates` at the constructed volume estimate
`Ttc.mcVol`, whose only coin dependence is `Ttc.MonteCarlo.est`. -/
theorem measurable_ttcRates :
    Measurable fun c : ℕ → Space n => ttcRates atoms φ ε δ c :=
  measurable_rates_of_measurable_vol _ _ _ _ _ _ fun i => measurable_mcVol _ _ _ _ _ _ i

end Rates

/-! ## Part 2.  The Poisson measure is a measurable function of its rate

Mathlib has `ProbabilityTheory.poissonMeasure` but no measurability of the map
`r ↦ Po(r)` into the Giry monad.  `ℕ` is countable with measurable singletons, so a
measure on it is the sum of its singleton masses, and each singleton mass is a
continuous function of `r`. -/

/-- **`r ↦ Po(r)` is measurable.**  For a measurable `s ⊆ ℕ`,
`Po(r) s = ∑' k, s.indicator (fun a ↦ e^{-r} r^a / a!) k`, a countable sum of
continuous functions of `r`. -/
theorem measurable_poissonMeasure : Measurable (poissonMeasure) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have key : (fun r : ℝ≥0 => poissonMeasure r s)
      = fun r : ℝ≥0 => ∑' k : ℕ,
          s.indicator (fun a : ℕ => ENNReal.ofReal
            (Real.exp (-(r : ℝ)) * (r : ℝ) ^ a / (Nat.factorial a : ℝ))) k := by
    funext r
    rw [← (poissonMeasure r).tsum_indicator_apply_singleton s hs]
    simp only [poissonMeasure_singleton]
  rw [key]
  refine Measurable.tsum fun k => ?_
  by_cases hk : k ∈ s
  · simp only [Set.indicator_of_mem hk]
    fun_prop
  · simp only [Set.indicator_of_notMem hk]
    exact measurable_const

/-- **`θ ↦ ⨂ s, Po((θ s)⁺)` is measurable.**  Mathlib has neither measurability of
`MeasureTheory.Measure.pi` in its factors nor a `Kernel.pi`; but `Fin L → ℕ` is
countable with measurable singletons, and `MeasureTheory.Measure.pi_singleton` gives
the singleton masses as a finite product of the factors' singleton masses. -/
theorem measurable_pi_poissonMeasure (L : ℕ) :
    Measurable fun θ : Fin L → ℝ =>
      Measure.pi fun s : Fin L => poissonMeasure (θ s).toNNReal := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hfac : ∀ (i : Fin L) (k : ℕ),
      Measurable fun θ : Fin L → ℝ => poissonMeasure (θ i).toNNReal {k} :=
    fun i k => (Measure.measurable_coe (measurableSet_singleton k)).comp
      (measurable_poissonMeasure.comp
        (measurable_real_toNNReal.comp (measurable_pi_apply i)))
  have key : (fun θ : Fin L → ℝ =>
        (Measure.pi fun i : Fin L => poissonMeasure (θ i).toNNReal) s)
      = fun θ : Fin L → ℝ => ∑' x : Fin L → ℕ,
          s.indicator (fun y : Fin L → ℕ =>
            ∏ i : Fin L, poissonMeasure (θ i).toNNReal {y i}) x := by
    funext θ
    rw [← (Measure.pi fun i : Fin L =>
      poissonMeasure (θ i).toNNReal).tsum_indicator_apply_singleton s hs]
    simp only [Measure.pi_singleton]
  rw [key]
  refine Measurable.tsum fun x => ?_
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
    exact Finset.measurable_prod _ fun i _ => hfac i (x i)
  · simp only [Set.indicator_of_notMem hx]
    exact measurable_const

/-! ## Part 3.  Ionescu–Tulcea is measurable in the initial measure

`ProbabilityTheory.Kernel.trajMeasure μ₀ κ` is by definition `traj κ 0 ∘ₘ (μ₀.map e)`
for the fixed Ionescu–Tulcea kernel `traj κ 0` and the measurable equivalence
`e : X 0 ≃ᵐ (Π i : Iic 0, X i)`.  Both `MeasureTheory.Measure.map` at a fixed
measurable function and `MeasureTheory.Measure.bind` at a fixed kernel are
measurable operations on the Giry monad, so their composite is. -/

/-- **Half (b), the hard half, in general form: `μ₀ ↦ trajMeasure μ₀ κ` is
measurable.**  No hypothesis beyond what `ProbabilityTheory.Kernel.trajMeasure`
itself needs. -/
theorem measurable_trajMeasure {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ : (i : ℕ) → Kernel ((j : ↥(Finset.Iic i)) → X j) (X (i + 1)))
    [∀ i, IsMarkovKernel (κ i)] :
    Measurable fun μ₀ : Measure (X 0) => Kernel.trajMeasure μ₀ κ :=
  (Measure.measurable_bind' (Kernel.measurable _)).comp
    (Measure.measurable_map _ (MeasurableEquiv.measurable _))

/-! ## Part 4.  The two halves composed -/

/-- **Half (b): the coupled family's law is a measurable function of the rates.**
`Ttc.trajLaw θ` is Ionescu–Tulcea from the product of Poissons at `θ`, and both
stages are measurable in `θ`. -/
theorem measurable_trajLaw {L : ℕ} :
    Measurable fun θ : Fin L → ℝ => trajLaw θ :=
  (measurable_trajMeasure (X := fun _ : ℕ => Fin L → ℕ) (chainKernel L)).comp
    (measurable_pi_poissonMeasure L)

section Payoff

variable {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

/-- **The identified risk, discharged.**  The coin-indexed family of trajectory
laws the headline integrates is a measurable family — equivalently, a kernel from
the volume oracle's coin space to the trajectory space. -/
theorem measurable_trajLaw_ttcRates :
    Measurable fun c : ℕ → Space n =>
      trajLaw (ttcRates atoms φ ε δ c) :=
  measurable_trajLaw.comp (measurable_ttcRates atoms φ ε δ)

/-- **The coin-indexed family as an honest kernel.**  This is `Ttc.trajLaw ∘ ttcRates`
packaged as `ProbabilityTheory.Kernel`; it is a Markov kernel because each
`Ttc.trajLaw θ` is a probability measure. -/
noncomputable def ttcTrajKernel :
    Kernel (ℕ → Space n)
      (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ) where
  toFun c := trajLaw (ttcRates atoms φ ε δ c)
  measurable' := measurable_trajLaw_ttcRates atoms φ ε δ

instance isMarkovKernel_ttcTrajKernel :
    IsMarkovKernel (ttcTrajKernel atoms φ ε δ) :=
  ⟨fun _ => isProbabilityMeasure_trajLaw _⟩

/-- **The payoff.**  The headline's iterated integral is a single measure applied to
the event: the `Measure.bind` of the coins with the coin-indexed trajectory law. -/
theorem lintegral_trajLaw_ttcRates_eq_bind
    {S : Set (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ)}
    (hS : MeasurableSet S) :
    (∫⁻ c, trajLaw (ttcRates atoms φ ε δ c) S ∂(MonteCarlo.coins n))
      = ((MonteCarlo.coins n).bind
          fun c => trajLaw (ttcRates atoms φ ε δ c)) S :=
  (Measure.bind_apply hS
    (measurable_trajLaw_ttcRates atoms φ ε δ).aemeasurable).symm

end Payoff

#print axioms measurable_mcVol
#print axioms measurable_rates_of_measurable_vol
#print axioms measurable_ttcRates
#print axioms measurable_poissonMeasure
#print axioms measurable_pi_poissonMeasure
#print axioms measurable_trajMeasure
#print axioms measurable_trajLaw
#print axioms measurable_trajLaw_ttcRates
#print axioms ttcTrajKernel
#print axioms lintegral_trajLaw_ttcRates_eq_bind

end Ttc

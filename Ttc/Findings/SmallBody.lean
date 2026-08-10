/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Regime

/-!
# `Findings/SmallBody`: on a small body the printed algorithm returns `0`

**What is proved.**  `alg:ttc` sets `p ← 1` and only ever halves it, so `p ≤ 1`
throughout the run (`Ttc.SmallBody.p_run_le_one`) — every Poisson rate `t·p` is at
most the cube's volume estimate `t`.  The quantitative form of that, `∑ θ` is
`Vol(Sol F)` up to `(1 ± ε')²`, is `Ttc.Box.sum_rates_box_window` (`Exec/Regime`)
and is used, not re-derived.  On a small body the level-`0` count vector of the
coupled family is therefore already the zero vector with probability `e^(−Λ)`,
`Λ = ∑ θ` (`Ttc.SmallBody.trajLaw_level_zero`).  On that event the modelled run
never leaves level `0`, `𝒳` stays empty, and the output is `|𝒳|/p = 0`
(`Ttc.SmallBody.run_eq_zero_of_pois_zero`).  Since `0 ∉ (1 ± ε)·Vol(Sol F)` as soon
as `Vol(Sol F) > 0` and `ε < 1` (`Ttc.SmallBody.output_zero_not_mem_relErr`), the
probability that `alg:ttc` answers correctly is at most `1 − e^(−Λ)`
(`Ttc.SmallBody.trajLaw_relErr_le`), which is **less than `1 − δ`** whenever
`Λ < log(1/δ)` (`Ttc.SmallBody.not_accuracy_of_small_rate`).

That last statement is the negation of `thm:volumettc`'s accuracy conclusion, in the
exact shape `Ttc.ttc_volume` states it.  Two witnesses exhibit instances of it, both
a box `[0,a]ⁿ` of small side with a coin of the constructed volume oracle's *good*
event:

* `Ttc.SmallBody.small_box_refutes_accuracy` — negates `Ttc.ttc_volume`'s accuracy
  conjunct (a fixed volume estimate `vol`), for every `ε ∈ (0,1)`, `δ ∈ (0,1)`;
* `Ttc.SmallBody.small_box_refutes_final_accuracy` — negates the capstone
  `Ttc.ttc_volume_final`'s accuracy conjunct (the `Ttc.MonteCarlo.coins`-integral of
  the same quantity), for every `ε ∈ (0,1)`, `δ ∈ (0, 5/6)`.

`Ttc.SmallBody.final_accuracy_shape` is the guard against refuting a lookalike: it
**proves** the negated proposition, verbatim, from `Ttc.ttc_volume_final` at the same
instance with the regime binder `big` as its only hypothesis.  It elaborates, so the
proposition is the capstone's own and `big` is the only thing between the capstone
and a contradiction.

So `thm:volumettc` as printed — i.e. without the regime binder `big` — is false, not
merely unproved.  This sharpens README finding 20 and `Ttc.Box.big_not_derivable`
(`Exec/Regime`), which only refuted a hypothesis.

## What is **not** proved — read this before quoting the file

* **The coins-integrated refutation covers `δ ∈ (0, 5/6)`, not all of `(0,1)`.**
  The bound proved is `Pr[correct] ≤ (1 − e^(−Λ)) + Pr[volume oracle fails]`, and
  the development supplies `Pr[volume oracle fails] ≤ δ/5` (`Ttc.measure_mcGood_ge`
  at the internal `4δ/5`).  That beats `1 − δ` only when `e^(−Λ) > 6δ/5`, which
  needs `6δ/5 < 1`.  Nothing is claimed about `δ ∈ [5/6, 1)`, where the volume
  oracle's own failure budget already exhausts the slack — even though
  `Ttc.ttc_volume_final`'s bound is stated there too.  The per-coin refutation
  `Ttc.SmallBody.small_box_refutes_accuracy` has no such restriction.
* **The empty-sketch event is `{ω | ω 0 = 0}`, not `{ω | ∀ j, ω j = 0}`.**  The
  argument therefore needs the run to stay at level `0`, which is the hypothesis
  `hvol : ∀ i ∈ D, ¬ P.thresh / O.vol i ≤ 1` — "every cube's volume estimate is
  below `Thresh`", the small-body regime read off `alg:ttc` line 32.  It is
  discharged at the box, not assumed away.  The probability of the *whole*
  trajectory being zero is not computed; it is not needed.
* **No claim is made about the real algorithm's floating-point behaviour**, nor
  about `Ttc.trajLaw` being the law of anything other than the modelled coupled
  family — that identification is `Ttc.TtcProb`'s `law_eq` field and is untouched.
-/

namespace Ttc

namespace SmallBody

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {n : ℕ} {ι : Type*}

/-! ## 1.  `p ≤ 1` along the run

`alg:ttc` line 21 sets `p ← 1` and lines 33 and 40 are the only writes, both
`p ← p/2`.  In the transcription `p = 2^(−level)` and both `while` loops are exit
levels at or above the entry level (`Ttc.le_haltLevel`, `Ttc.le_absorbLevel`), so
the level is nondecreasing along the fold and `p` is nonincreasing.  Starting from
level `0` this gives `p ≤ 1` at every state the run reaches.
-/

/-- The rate is positive at every level: `p = 2^(−j) > 0`. -/
theorem p_pos (st : SketchState n) : 0 < st.p := by
  rw [SketchState.p]; positivity

/-- **`p ≤ 1` at every state** — `p = 2^(−level)` and `level ≥ 0`. -/
theorem p_le_one (st : SketchState n) : st.p ≤ 1 := by
  rw [SketchState.p]
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- **The level never rewinds along the main loop.**  The `List.foldl` form of
`Ttc.le_step_level`. -/
theorem level_le_foldl_step (P : Params) (O : Oracles n ι) (ρ : ℤ) :
    ∀ (cubes : List ι) (st : SketchState n),
      st.level ≤ (cubes.foldl (step P O ρ) st).level := by
  intro cubes
  induction cubes with
  | nil => intro st; exact le_rfl
  | cons i rest ih => intro st; exact le_trans (le_step_level P O ρ st i) (ih _)

/-- **`p` never grows along the main loop** — the sampling rate of `alg:ttc` is
only ever halved. -/
theorem p_foldl_step_le (P : Params) (O : Oracles n ι) (ρ : ℤ) (cubes : List ι)
    (st : SketchState n) : (cubes.foldl (step P O ρ) st).p ≤ st.p := by
  rw [SketchState.p, SketchState.p]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (level_le_foldl_step P O ρ cubes st)

/-- The sampling rate of an explicitly built state: `p = 2^(−j)` by definition.
Lived in `Model/Pseudocode` beside `Ttc.SketchState.p`; it is a `rfl` lemma about
that definition rather than a step of the algorithm, and this is its only
consumer. -/
@[simp] theorem _root_.Ttc.SketchState.p_mk {n : ℕ} (X : Multiset (Space n)) (j : ℕ) :
    (⟨X, j⟩ : SketchState n).p = (1 / 2 : ℝ) ^ j := rfl

/-- **`p ≤ 1` along the whole run** (`alg:ttc` line 21 and lines 33, 40).  This is
the fact that bounds every Poisson rate `t·p` by the cube volume `t`, and hence the
sketch's total rate by `Vol(Sol F)`. -/
theorem p_run_le_one (P : Params) (O : Oracles n ι) (ρ : ℤ) (cubes : List ι) :
    (cubes.foldl (step P O ρ) (⟨0, 0⟩ : SketchState n)).p ≤ 1 := by
  refine le_trans (p_foldl_step_le P O ρ cubes ⟨0, 0⟩) ?_
  rw [SketchState.p_mk]
  norm_num

/-! ## 2.  An empty sketch outputs `0`

`alg:ttc` line 46 outputs `|𝒳|/p`.  Mathlib's `x / 0 = 0` convention is not in
play: `p > 0` always (`Ttc.SmallBody.p_pos`).  The output is `0` because the
numerator is.
-/

/-- **`|𝒳| = 0` ⟹ the output is `0`.**  `alg:ttc` line 46 divides by `p`, which is
positive, so nothing but the empty numerator is doing the work. -/
theorem run_eq_zero_of_card_eq_zero (P : Params) (O : Oracles n ι) (ρ : ℤ)
    (cubes : List ι)
    (h : Multiset.card (cubes.foldl (step P O ρ) (⟨0, 0⟩ : SketchState n)).X = 0) :
    run P O ρ cubes = 0 := by
  rw [run_eq, h, Nat.cast_zero, zero_div]

/-! ## 3.  `0` is never an admissible answer

`Ttc.relErr ε V = [(1−ε)V, (1+ε)V]`, so `0` belongs to it exactly when
`(1−ε)V ≤ 0`.  For a body of positive volume and an accuracy `ε < 1` — and
`thm:volumettc` assumes `ε ≤ 1`, with `ε = 1` the only excluded point — that fails.
This is the step that turns "returns `0`" into "returns the *wrong* answer".
-/

/-- **`0 ∉ (1 ± ε)·V` for a body of positive volume and accuracy `ε < 1`.** -/
theorem output_zero_not_mem_relErr {ε V : ℝ} (hV : 0 < V) (hε : ε < 1) :
    (0 : ℝ) ∉ relErr ε V := by
  intro h
  have hlo : (1 - ε) * V ≤ 0 := (Set.mem_Icc.1 h).1
  nlinarith

/-! ## 4.  The run that never leaves level `0`

The modelled run is a `List.foldl` of `Ttc.step` from `⟨∅, 0⟩`.  Three facts about
*any* oracle bundle make one iteration a no-op on that state:

* thinning the empty multiset gives the empty multiset (`Ttc.Oracles.thin_le`);
* `GenerateSamples` asked for `0` points returns `0` points (`Ttc.Oracles.gen_card`);
* the coverage filter of `∅` is `∅`.

What is *not* automatic is that the two `while` loops do not move the level.  The
first stays at `0` exactly when its guard `Thresh/t ≤ p` already fails at `p = 1`,
i.e. when `Thresh / t > 1` — the small-body regime.  The second stays at `0` as
soon as the level-`0` Poisson draw is `0`.  Both are hypotheses here and are
discharged at the box in §7.
-/

/-- Thinning the empty sketch leaves it empty — `Ttc.Oracles.thin_le` at `X = ∅`. -/
theorem thin_zero (O : Oracles n ι) (j₀ j' : ℕ) :
    O.thin j₀ j' (0 : Multiset (Space n)) = 0 :=
  Multiset.le_zero.1 (O.thin_le j₀ j' 0)

/-- `GenerateSamples(P(cᵢ), 0, ρ)` is empty — `Ttc.Oracles.gen_card` at `N = 0`. -/
theorem gen_zero (O : Oracles n ι) (i : ι) (j : ℕ) (ρ : ℤ) : O.gen i j 0 ρ = 0 :=
  Multiset.card_eq_zero.1 (O.gen_card i j 0 ρ)

/-- **The first `while` loop does not move off level `0`** when its guard already
fails at `p = 1`, i.e. when `Thresh/t > 1` (`alg:ttc` line 32). -/
theorem haltLevel_eq_zero (P : Params) {t : ℝ} (ht : ¬ P.thresh / t ≤ 1) :
    haltLevel P t 0 = 0 := by
  have hmem : (0 : ℕ) ∈ {j' | ¬ P.thresh / t ≤ (1 / 2 : ℝ) ^ j'} := by
    simpa using ht
  rw [haltLevel, Nat.le_zero.1 (Nat.sInf_le hmem), max_self]

/-- **The second `while` loop does not move off level `0`** when the level-`0`
Poisson draw is `0` and the sketch entering it is empty (`alg:ttc` line 39). -/
theorem absorbLevel_eq_zero (P : Params) (O : Oracles n ι) (i : ι) (t : ℝ)
    (hT : 0 ≤ P.thresh) (hp : O.pois i 0 (t * (1 / 2 : ℝ) ^ (0 : ℕ)) = 0) :
    absorbLevel P O i t (0 : Multiset (Space n)) 0 0 = 0 := by
  have hmem : (0 : ℕ) ∈ {j' | 0 ≤ j' ∧ ¬ P.thresh <
      (O.pois i j' (t * (1 / 2 : ℝ) ^ j') : ℝ)
        + (Multiset.card (O.thin 0 j' (0 : Multiset (Space n))) : ℝ)} := by
    refine ⟨Nat.zero_le _, ?_⟩
    rw [hp, thin_zero O 0 0]
    simpa using hT
  rw [absorbLevel, Nat.le_zero.1 (Nat.sInf_le hmem), max_self]

/-- **One iteration of `alg:ttc` is a no-op on the empty sketch at level `0`**,
provided the cube's volume estimate is below `Thresh` and the level-`0` Poisson
draw came back `0`.  No hypothesis on `thin`, `gen` or `covered` beyond the two
laws `Ttc.Oracles` already carries. -/
theorem step_eq_empty (P : Params) (O : Oracles n ι) (ρ : ℤ) (i : ι)
    (hT : 0 ≤ P.thresh) (hi : ¬ P.thresh / O.vol i ≤ 1)
    (hp : O.pois i 0 (O.vol i * (1 / 2 : ℝ) ^ (0 : ℕ)) = 0) :
    step P O ρ (⟨0, 0⟩ : SketchState n) i = ⟨0, 0⟩ := by
  have hdrop : dropCovered O i (0 : Multiset (Space n)) = 0 := by
    rw [dropCovered, Multiset.filter_zero]
  have hpre : stepPre P O (⟨0, 0⟩ : SketchState n) i = (⟨0, 0⟩, 0) := by
    simp only [stepPre, hdrop, haltLevel_eq_zero P hi,
      absorbLevel_eq_zero P O i (O.vol i) hT hp, thin_zero, hp]
  rw [step, hpre]
  simp [gen_zero]

/-- **The whole main loop is a no-op on the empty sketch**, cube by cube. -/
theorem foldl_step_eq_empty (P : Params) (O : Oracles n ι) (ρ : ℤ) (hT : 0 ≤ P.thresh) :
    ∀ cubes : List ι,
      (∀ i ∈ cubes, ¬ P.thresh / O.vol i ≤ 1) →
      (∀ i ∈ cubes, O.pois i 0 (O.vol i * (1 / 2 : ℝ) ^ (0 : ℕ)) = 0) →
      cubes.foldl (step P O ρ) (⟨0, 0⟩ : SketchState n) = ⟨0, 0⟩ := by
  intro cubes
  induction cubes with
  | nil => intro _ _; rfl
  | cons i rest ih =>
      intro hvol hpois
      rw [List.foldl_cons,
        step_eq_empty P O ρ i hT (hvol i (List.mem_cons_self ..))
          (hpois i (List.mem_cons_self ..))]
      exact ih (fun i' hi' => hvol i' (List.mem_cons_of_mem _ hi'))
        (fun i' hi' => hpois i' (List.mem_cons_of_mem _ hi'))

/-- **`alg:ttc` outputs `0`.**  If every cube's `Vol_ED` is below `Thresh` and every
level-`0` Poisson draw is `0`, the sketch is never fed and line 46 divides `0` by
`p = 1`. -/
theorem run_eq_zero_of_pois_zero (P : Params) (O : Oracles n ι) (ρ : ℤ)
    (cubes : List ι) (hT : 0 ≤ P.thresh)
    (hvol : ∀ i ∈ cubes, ¬ P.thresh / O.vol i ≤ 1)
    (hpois : ∀ i ∈ cubes, O.pois i 0 (O.vol i * (1 / 2 : ℝ) ^ (0 : ℕ)) = 0) :
    run P O ρ cubes = 0 :=
  run_eq_zero_of_card_eq_zero P O ρ cubes
    (by rw [foldl_step_eq_empty P O ρ hT cubes hvol hpois]; simp)

/-! ## 5.  The coupled family's level `0`, and the event that it is empty

`Ttc.trajOracles` is the concrete oracle bundle the development couples the run to:
`pois i j _` reads off the total of the level-`j` count vector over cube `i`.  So
the hypothesis of §4 — "every level-`0` Poisson draw is `0`" — is implied by the
single event `ω 0 = 0`, the level-`0` count vector being the zero vector.

`Ttc.map_trajLaw_zero` says the level-`0` marginal of `Ttc.trajLaw θ` is the
product of `Pois(θ s)`, so that event has probability `∏ e^(−θ s) = e^(−∑ θ)`.
-/

/-- **The level-`0` Poisson draw is `0` when the family's level-`0` vector is.** -/
theorem pois_trajOracles_zero {L : ℕ} {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    {ω : ℕ → (Fin L → ℕ)} (hω : ω 0 = 0) (i : ι) (lam : ℝ) :
    (trajOracles hpt vol covered mem ω).pois i 0 lam = 0 := by
  show ∑ s ∈ Finset.univ.filter (fun s => mem i s = true), ω 0 s = 0
  simp [hω]

/-- **`alg:ttc` outputs `0` on the empty level-`0` vector.**  The only remaining
hypothesis is the small-body regime `Vol_ED(P(cᵢ)) < Thresh`, which is what keeps
the run at level `0` — see `Ttc.SmallBody.haltLevel_eq_zero`. -/
theorem run_trajOracles_eq_zero (P : Params) {L : ℕ} {pt : Fin L → Space n}
    (hpt : Function.Injective pt) (vol : ι → ℝ) (covered : Space n → ι → Bool)
    (mem : ι → Fin L → Bool) {ω : ℕ → (Fin L → ℕ)} (hω : ω 0 = 0) (ρ : ℤ)
    (cubes : List ι) (hT : 0 ≤ P.thresh) (hvol : ∀ i ∈ cubes, ¬ P.thresh / vol i ≤ 1) :
    run P (trajOracles hpt vol covered mem ω) ρ cubes = 0 :=
  run_eq_zero_of_pois_zero P _ ρ cubes hT hvol
    (fun i _ => pois_trajOracles_zero hpt vol covered mem hω i _)

/-- **`Pr[ the level-`0` count vector is `0` ] = e^(−∑ θ)`.**  The level-`0`
marginal of the coupled family is `⨂ₛ Pois(θ s)` (`Ttc.map_trajLaw_zero`), and a
product of Poisson point masses at `0` is `∏ e^(−θ s)`. -/
theorem trajLaw_level_zero {L : ℕ} {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) :
    trajLaw θ {ω : ℕ → (Fin L → ℕ) | ω 0 = 0}
      = ENNReal.ofReal (Real.exp (-∑ s, θ s)) := by
  have hmeas : MeasurableSet ({0} : Set (Fin L → ℕ)) := MeasurableSet.singleton 0
  have hpre : {ω : ℕ → (Fin L → ℕ) | ω 0 = 0}
      = (fun ω : ℕ → (Fin L → ℕ) => ω 0) ⁻¹' {0} := rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) hmeas, map_trajLaw_zero,
    pi_poisson_singleton]
  congr 1
  have hpt : ∀ s : Fin L, poissonPMF (((θ s).toNNReal : ℝ)) ((0 : Fin L → ℕ) s)
      = Real.exp (-θ s) := by
    intro s
    rw [Pi.zero_apply, poissonPMF_def, Real.coe_toNNReal _ (hθ s)]
    simp
  rw [Finset.prod_congr rfl (fun s _ => hpt s), ← Real.exp_sum]
  congr 1
  simp

/-- The empty-level-`0` event is measurable. -/
theorem measurableSet_level_zero (L : ℕ) :
    MeasurableSet {ω : ℕ → (Fin L → ℕ) | ω 0 = 0} :=
  (measurable_pi_apply 0) (MeasurableSet.singleton 0)

/-- **`Pr[ `alg:ttc` answers within `(1 ± ε)·V` ] ≤ 1 − e^(−∑ θ)`.**

On the event `ω 0 = 0` — probability `e^(−∑ θ)` — the run outputs `0`, and `0` is
not in `(1 ± ε)·V`.  So the correct-answer event is contained in the complement.

The two regime hypotheses are `hV` (the body has positive volume — otherwise `0` is
a correct answer) and `hvol` (every cube's volume estimate is below `Thresh`, so
the run never leaves level `0`). -/
theorem trajLaw_run_mem_relErr_le {L : ℕ} {pt : Fin L → Space n}
    (hpt : Function.Injective pt) (P : Params) (vol : ι → ℝ)
    (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool) (ρ : ℤ) (cubes : List ι)
    {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) {ε V : ℝ} (hV : 0 < V) (hε : ε < 1)
    (hT : 0 ≤ P.thresh) (hvol : ∀ i ∈ cubes, ¬ P.thresh / vol i ≤ 1) :
    trajLaw θ {ω : ℕ → (Fin L → ℕ) |
        run P (trajOracles hpt vol covered mem ω) ρ cubes ∈ relErr ε V}
      ≤ 1 - ENNReal.ofReal (Real.exp (-∑ s, θ s)) := by
  have hsub : {ω : ℕ → (Fin L → ℕ) |
        run P (trajOracles hpt vol covered mem ω) ρ cubes ∈ relErr ε V}
      ⊆ {ω : ℕ → (Fin L → ℕ) | ω 0 = 0}ᶜ := by
    intro ω hgood hzero
    simp only [Set.mem_setOf_eq] at hgood hzero
    refine output_zero_not_mem_relErr hV hε ?_
    rwa [run_trajOracles_eq_zero P hpt vol covered mem hzero ρ cubes hT hvol] at hgood
  refine le_trans (measure_mono hsub) (le_of_eq ?_)
  rw [measure_compl (measurableSet_level_zero L) (measure_ne_top _ _),
    trajLaw_level_zero hθ, measure_univ]

/-! ## 6.  The accuracy conclusion of `thm:volumettc`, negated

`Ttc.ttc_volume`'s accuracy conjunct is `1 − δ ≤ (trajLaw θ {t | output ∈ (1±ε)·Vol})ᵣ`.
§5 caps that probability at `1 − e^(−∑ θ)`, so the conjunct **fails** as soon as
`δ < e^(−∑ θ)`, i.e. as soon as the total rate is below `log(1/δ)`.

Nothing here is about a particular body; the two hypotheses that carry the content
are `hV : 0 < Vol(Sol F)` and `hvol : Vol_ED(P(cᵢ)) < Thresh`, and both are facts
about *small* instances.  §7 exhibits one.
-/

variable {A : Type*}

open Box

/-- §5 in the shape `Ttc.ttc_volume` states its conclusion: at the constructed
oracle bundle `Ttc.coveredOracles`, and about `Ttc.ttcOutput`. -/
theorem trajLaw_relErr_le (M : A → Set (Space n)) (φ : BForm A) (P : Params) (ρ : ℤ)
    (vol : Cube A → ℝ) (toDNF : BForm A → DNF A)
    {θ : Fin (latticeCount M φ ρ) → ℝ} (hθ : ∀ s, 0 ≤ θ s) {ε : ℝ} (hε : ε < 1)
    (hV : 0 < volSol M φ) (hT : 0 ≤ P.thresh)
    (hvol : ∀ i ∈ toDNF φ, ¬ P.thresh / vol i ≤ 1) :
    trajLaw θ {t : ℕ → Fin (latticeCount M φ ρ) → ℕ |
        ttcOutput P (coveredOracles M φ ρ vol) toDNF ρ φ t ∈ relErr ε (volSol M φ)}
      ≤ 1 - ENNReal.ofReal (Real.exp (-∑ s, θ s)) :=
  trajLaw_run_mem_relErr_le (latticeEnum_injective M φ ρ) P vol _ _ ρ (toDNF φ) hθ hV hε
    hT hvol

/-- **`thm:volumettc`'s accuracy conclusion is false on a small body.**

If the body has positive volume, every cube's volume estimate is under `Thresh`
(so the run never halves `p`), and the total rate is below `log(1/δ)`, then the
probability that `alg:ttc` answers within `(1 ± ε)` is strictly below `1 − δ`. -/
theorem not_accuracy_of_small_rate (M : A → Set (Space n)) (φ : BForm A) (P : Params)
    (ρ : ℤ) (vol : Cube A → ℝ) (toDNF : BForm A → DNF A)
    {θ : Fin (latticeCount M φ ρ) → ℝ} (hθ : ∀ s, 0 ≤ θ s) {ε δ : ℝ} (hε : ε < 1)
    (hV : 0 < volSol M φ) (hT : 0 ≤ P.thresh)
    (hvol : ∀ i ∈ toDNF φ, ¬ P.thresh / vol i ≤ 1)
    (hδ : δ < Real.exp (-∑ s, θ s)) :
    ¬ (1 - δ ≤ (trajLaw θ {t : ℕ → Fin (latticeCount M φ ρ) → ℕ |
        ttcOutput P (coveredOracles M φ ρ vol) toDNF ρ φ t
          ∈ relErr ε (volSol M φ)}).toReal) := by
  intro hacc
  have hsum : (0 : ℝ) ≤ ∑ s, θ s := Finset.sum_nonneg fun s _ => hθ s
  have hexp1 : Real.exp (-∑ s, θ s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hofr : ENNReal.ofReal (Real.exp (-∑ s, θ s)) ≤ 1 := ENNReal.ofReal_le_one.2 hexp1
  have hne : (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-∑ s, θ s)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hmono := ENNReal.toReal_mono hne
    (trajLaw_relErr_le M φ P ρ vol toDNF hθ hε hV hT hvol)
  rw [ENNReal.toReal_sub_of_le hofr ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hmono
  linarith

/-! ## 7.  The witness: a box of small side

Everything in §6 is discharged at `[0,a]ⁿ` for `a` small, reusing the machinery of
`Exec/Regime`: `Ttc.Box.sum_rates_box_window` caps the total rate by
`(1+ε')²·Vol([0,a]ⁿ)`, `Ttc.mcVol_mem_relErr` caps the volume estimate by
`(1+ε')·Vol([0,a]ⁿ)`, and `Ttc.Box.volume_bxOf_eq` makes both `O(aⁿ)`.
`Ttc.SmallBody.exists_small_side` then picks

  `a = min 1 (B/(2K))`,  `K = (1+ε')²·Vol([0,1]ⁿ)`,

for any prescribed target `B > 0`; taking `B = min Thresh (log(1/δ))` puts the
estimate under `Thresh` **and** the total rate under `log(1/δ)`.

The coin is a *good* coin of the constructed Monte-Carlo volume oracle
(`Ttc.Box.mcGood_box_nonempty`), so the refutation is not an artefact of a bad
volume estimate: the oracle did its job, and the algorithm still answers `0`.
-/

/-- **A side length at which the box is smaller than any prescribed target.**
`Vol([0,a]ⁿ) = aⁿ·Vol([0,1]ⁿ) ≤ a·Vol([0,1]ⁿ)` for `a ≤ 1` and `n ≥ 1`. -/
theorem exists_small_side (n : ℕ) (hn : 1 ≤ n) (P : Params) (hep0 : 0 < P.epsPrime)
    {B : ℝ} (hB : 0 < B) :
    ∃ a : ℝ, 0 < a ∧ (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal < B := by
  have hV1 : 0 < (volume (bxOf n 1)).toReal := volume_bxOf_pos n one_pos
  set K : ℝ := (1 + P.epsPrime) ^ 2 * (volume (bxOf n 1)).toReal with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have ha0 : 0 < min 1 (B / (2 * K)) :=
    lt_min one_pos (div_pos hB (by linarith))
  refine ⟨min 1 (B / (2 * K)), ha0, ?_⟩
  set a := min 1 (B / (2 * K)) with hadef
  have ha1 : a ≤ 1 := min_le_left _ _
  have haB : a ≤ B / (2 * K) := min_le_right _ _
  have hvolbox : (volume (bxOf n a)).toReal = a ^ n * (volume (bxOf n 1)).toReal :=
    Box.volume_bxOf_eq n ha0
  have han : a ^ n ≤ a := by
    calc a ^ n ≤ a ^ 1 := pow_le_pow_of_le_one ha0.le ha1 hn
      _ = a := pow_one a
  calc (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal
      = K * a ^ n := by rw [hvolbox, hKdef]; ring
    _ ≤ K * a := mul_le_mul_of_nonneg_left han hKpos.le
    _ ≤ K * (B / (2 * K)) := mul_le_mul_of_nonneg_left haB hKpos.le
    _ = B / 2 := by field_simp
    _ < B := by linarith

/-- **The volume oracle fails on at most a `δ₀/4` share of its coins, at the box.**
`Ttc.measure_mcGood_ge`, complemented. -/
theorem coins_mcGood_compl_le (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (P : Params)
    {δ₀ : ℝ} (hδeq : P.δ = δ₀) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) :
    (MonteCarlo.coins n (mcGood (fun x => (boxAtoms n a x).halfspace)
        (Ttc.toDNF (boxForm n hn)) (fun _ => boxCentre n a) (a / 2)
        P.epsPrime P.deltaPrime)ᶜ).toReal ≤ δ₀ / 4 := by
  have hlen : ((Ttc.toDNF (boxForm n hn)).length : ℝ) ≤ (P.m : ℝ) := by
    rw [length_toDNF_boxForm n hn]
    exact_mod_cast P.hm
  have hmeas := measure_mcGood_ge (fun x => (boxAtoms n a x).halfspace)
    (Ttc.toDNF (boxForm n hn)) P hδeq hδ0 hδ1 (by positivity : (0 : ℝ) < a / 2)
    (fun _ => boxCentre n a) (ball_subset_bxOf n a hn)
    (fun i => convex_region (boxAtoms n a) i.val)
    (volume_region_ne_top_of_isBounded (toDNF_isDNFOf (boxForm n hn))
      (isBounded_sol_bxOf n a hn)) hlen
  rw [measure_compl (measurableSet_mcGood _ _ _ _ _ _) (measure_ne_top _ _), measure_univ,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  linarith

/-- **What a good coin gives at a small box**: nonnegative rates, every volume
estimate under `Thresh`, and a total rate capped by `(1+ε')²·Vol([0,a]ⁿ)`.  These
are exactly the three hypotheses §6 and §8 consume. -/
theorem box_good_coin_bounds (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (P : Params)
    (hep0 : 0 < P.epsPrime) (hep : P.epsPrime ≤ 1 / 2)
    (hsmall : (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal < P.thresh)
    (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
      (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime) :
    (∀ s, 0 ≤ rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
        (Ttc.toDNF (boxForm n hn)) (P.precision (a / 2))
        (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
          (fun _ => boxCentre n a) (a / 2))
        (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
          (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s)
      ∧ (∀ i ∈ Ttc.toDNF (boxForm n hn),
          ¬ P.thresh / mcVol (fun x => (boxAtoms n a x).halfspace)
            (Ttc.toDNF (boxForm n hn)) (fun _ => boxCentre n a) (a / 2)
            P.epsPrime P.deltaPrime c i ≤ 1)
      ∧ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
          (Ttc.toDNF (boxForm n hn)) (P.precision (a / 2))
          (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
            (fun _ => boxCentre n a) (a / 2))
          (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
            (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s
        ≤ (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal := by
  have hep1 : P.epsPrime < 1 := by linarith
  set M := fun x => (boxAtoms n a x).halfspace with hMdef
  set D := Ttc.toDNF (boxForm n hn) with hDdef
  set ρ := P.precision (a / 2) with hρdef
  set vol := mcVol M D (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c with hvoldef
  have hfin : ∀ i : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ D}, volume (region M i.val) ≠ ⊤ :=
    volume_region_ne_top_of_isBounded (toDNF_isDNFOf (boxForm n hn))
      (isBounded_sol_bxOf n a hn)
  have hvolpos : ∀ i ∈ D, 0 < vol i :=
    mcVol_pos M D (fun _ => boxCentre n a) (by positivity) hep1
      (ball_subset_bxOf n a hn) hfin hc
  have hAU := Box.canonSampD_box_almostUniform n hn ha P hep0 hep
  refine ⟨?_, ?_, (Box.sum_rates_box_window n hn ha P hep0 hep hc).2⟩
  · intro s
    refine le_of_lt (rates_pos_of_almostUniform (toDNF_isDNFOf (boxForm n hn))
      (hasLatticeEnum_bxOf n a hn ρ) hvolpos hep1 ?_ s)
    intro i hi
    have hib : i = boxCube n := by
      simpa only [hDdef, toDNF_boxForm hn, boxDNF, List.mem_singleton] using hi
    subst hib
    exact hAU
  · intro i hi
    have hup : vol i ≤ (1 + P.epsPrime) * (volume (region M i)).toReal :=
      (mcVol_mem_relErr M D (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime hc
        i hi).2
    rw [region_eq_bxOf n a hn hi] at hup
    have h1 : (1 + P.epsPrime) * (volume (bxOf n a)).toReal
        ≤ (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal := by
      have hnn : (0 : ℝ) ≤ (volume (bxOf n a)).toReal := ENNReal.toReal_nonneg
      have hcross : (0 : ℝ) ≤ (1 + P.epsPrime) * P.epsPrime * (volume (bxOf n a)).toReal :=
        mul_nonneg (mul_nonneg (by linarith) hep0.le) hnn
      nlinarith [hcross]
    exact not_le.2 ((one_lt_div (hvolpos i hi)).2 (by linarith))

set_option maxHeartbeats 2000000 in
/-- **On a small box, `thm:volumettc`'s accuracy conclusion fails at a good coin of
the constructed volume oracle.**

For every dimension `n ≥ 1` and every `(ε, δ) ∈ (0,1) × (0,1)` there is a side
`a > 0` and a coin `c` in the volume oracle's good event such that the box
`[0,a]ⁿ` has positive volume and the accuracy conjunct of `Ttc.ttc_volume` — written
here with the capstone's own `Ttc.e2eSampD`, `Ttc.mcVol`, `Ttc.rates` and
`Ttc.coveredOracles` terms — is **false**.

Together with `Ttc.Box.ttc_volume_final_at_box` (which checks that the same terms
are the capstone's) this says: `thm:volumettc` *as printed*, i.e. without the regime
binder `big`, is false — not merely unproved. -/
theorem small_box_refutes_accuracy (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (a : ℝ) (c : ℕ → Space n), 0 < a ∧
      c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
        (fun _ => boxCentre n a) (a / 2)
        (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
        (parS n hn ε (4 * δ / 5) hε0 hε1.le).deltaPrime ∧
      0 < volSol (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) ∧
      ¬ (1 - δ ≤
        (trajLaw (rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
              (Ttc.toDNF (boxForm n hn))
              ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
              (e2eSampD (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
                (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
                (canonRfac (Ttc.toDNF (boxForm n hn)))
                (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
                (canonAm (boxAtoms n a) (Ttc.toDNF (boxForm n hn)))
                (canonBv (boxAtoms n a) (Ttc.toDNF (boxForm n hn))
                  (latticeScale ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))))
                (fun _ => boxCentre n a) (a / 2)
                (canonDm (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                  ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))))
              (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                (fun _ => boxCentre n a) (a / 2)
                (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
                (parS n hn ε (4 * δ / 5) hε0 hε1.le).deltaPrime c))
            {t : ℕ → Fin (latticeCount (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
                ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))) → ℕ |
              ttcOutput (parS n hn ε (4 * δ / 5) hε0 hε1.le)
                  (coveredOracles (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
                    ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
                    (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                      (fun _ => boxCentre n a) (a / 2)
                      (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
                      (parS n hn ε (4 * δ / 5) hε0 hε1.le).deltaPrime c))
                  Ttc.toDNF ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
                  (boxForm n hn) t
                ∈ relErr ε
                    (volSol (fun x => (boxAtoms n a x).halfspace) (boxForm n hn))}).toReal) := by
  classical
  have hd0 : (0 : ℝ) < 4 * δ / 5 := by linarith
  have hd1 : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  set P := parS n hn ε (4 * δ / 5) hε0 hε1.le with hPdef
  have hep0 : 0 < P.epsPrime := parS_epsPrime_pos (n := n) (δ := 4 * δ / 5) hn hε0 hε1.le
  have hep12 : P.epsPrime ≤ 1 / 12 := parS_epsPrime_le (n := n) (δ := 4 * δ / 5) hn hε0 hε1.le
  have hT0 : 0 < P.thresh := parS_thresh_pos (n := n) hn hε0 hε1.le hd0 hd1
  set Lg : ℝ := -Real.log δ with hLgdef
  have hLg : 0 < Lg := by
    rw [hLgdef]; have := Real.log_neg hδ0 hδ1; linarith
  obtain ⟨a, ha0, hsmall⟩ :=
    exists_small_side n hn P hep0 (B := min P.thresh Lg) (lt_min hT0 hLg)
  set Λ : ℝ := (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal with hΛdef
  have hΛT : Λ < P.thresh := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hΛL : Λ < Lg := lt_of_lt_of_le hsmall (min_le_right _ _)
  obtain ⟨c, hc⟩ := Box.mcGood_box_nonempty n hn ha0 P rfl hd0 hd1
  obtain ⟨hθ, hvolT, hsum⟩ := box_good_coin_bounds n hn ha0 P hep0 (by linarith) hΛT c hc
  have hVpos : 0 < volSol (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) := by
    rw [volSol, sol_eq_bxOf n a hn]; exact volume_bxOf_pos n ha0
  refine ⟨a, c, ha0, hc, hVpos, ?_⟩
  have hδexp : δ < Real.exp (-∑ s,
      rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) (Ttc.toDNF (boxForm n hn))
        (P.precision (a / 2))
        (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
          (fun _ => boxCentre n a) (a / 2))
        (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
          (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s) := by
    have hlt : Real.log δ < -∑ s,
        rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) (Ttc.toDNF (boxForm n hn))
          (P.precision (a / 2))
          (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
            (fun _ => boxCentre n a) (a / 2))
          (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
            (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s := by
      rw [hLgdef] at hΛL; linarith
    calc δ = Real.exp (Real.log δ) := (Real.exp_log hδ0).symm
      _ < _ := Real.exp_lt_exp.2 hlt
  exact not_accuracy_of_small_rate (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) P
    (P.precision (a / 2))
    (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
      (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c)
    Ttc.toDNF hθ hε1 hVpos hT0.le hvolT hδexp

/-! ## 8.  The same, integrated over the volume oracle's coins

`Ttc.ttc_volume_final`'s accuracy conjunct integrates §6's quantity against
`Ttc.MonteCarlo.coins`.  Splitting the coin space into the volume oracle's good
event `G` and its complement bounds that integral by
`(1 − e^(−Λ)) + Pr[Gᶜ]` whenever `Λ` caps the total rate on `G` — nothing is
assumed off `G`, where the trivial bound `Pr ≤ 1` is used.

At the box, `Ttc.measure_mcGood_ge` puts `Pr[Gᶜ] ≤ δ/5` (the internal failure
parameter is `4δ/5`), so the bound reads `(1 − e^(−Λ)) + δ/5`, and it is below
`1 − δ` exactly when `e^(−Λ) > 6δ/5`.  That needs `δ < 5/6`: above it, the
`δ/5` the analysis already spends on the volume oracle exceeds what is left to
contradict, and this argument says nothing.  `Ttc.ttc_volume_final`'s bound is
informative on all of `δ ∈ (0,1)`, so the refutation below covers `(0, 5/6)` of it.
-/

/-- **The coins-integrated correctness probability, bounded.**  `G` is the volume
oracle's good event and `Λ` a cap on the total rate there; off `G` nothing is
assumed. -/
theorem lintegral_trajLaw_relErr_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {G : Set Ω} (hG : MeasurableSet G)
    (M : A → Set (Space n)) (φ : BForm A) (P : Params) (ρ : ℤ)
    (vol : Ω → Cube A → ℝ) (toDNF : BForm A → DNF A)
    (θ : Ω → Fin (latticeCount M φ ρ) → ℝ) {ε Λ : ℝ} (hε : ε < 1) (hV : 0 < volSol M φ)
    (hT : 0 ≤ P.thresh)
    (hgood : ∀ c ∈ G, (∀ s, 0 ≤ θ c s)
      ∧ (∀ i ∈ toDNF φ, ¬ P.thresh / vol c i ≤ 1) ∧ ∑ s, θ c s ≤ Λ) :
    (∫⁻ c, trajLaw (θ c) {t : ℕ → Fin (latticeCount M φ ρ) → ℕ |
          ttcOutput P (coveredOracles M φ ρ (vol c)) toDNF ρ φ t
            ∈ relErr ε (volSol M φ)} ∂μ)
      ≤ (1 - ENNReal.ofReal (Real.exp (-Λ))) + μ Gᶜ := by
  have hpt : ∀ c : Ω, trajLaw (θ c) {t : ℕ → Fin (latticeCount M φ ρ) → ℕ |
        ttcOutput P (coveredOracles M φ ρ (vol c)) toDNF ρ φ t
          ∈ relErr ε (volSol M φ)}
      ≤ (1 - ENNReal.ofReal (Real.exp (-Λ))) + Gᶜ.indicator 1 c := by
    intro c
    by_cases hcG : c ∈ G
    · obtain ⟨hθ, hvl, hΛ⟩ := hgood c hcG
      refine le_trans (trajLaw_relErr_le M φ P ρ (vol c) toDNF hθ hε hV hT hvl) ?_
      refine le_trans (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal ?_) 1) le_self_add
      exact Real.exp_le_exp.2 (by linarith)
    · rw [Set.indicator_of_mem (Set.mem_compl hcG), Pi.one_apply]
      exact le_trans prob_le_one le_add_self
  refine le_trans (lintegral_mono hpt) (le_of_eq ?_)
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_indicator_one hG.compl]

set_option maxHeartbeats 2000000 in
/-- **The refuted proposition really is the capstone's.**

`Ttc.SmallBody.small_box_refutes_final_accuracy` negates a proposition; this checks
that the proposition is not a lookalike.  `Ttc.ttc_volume_final`, applied at the box
via `Ttc.Box.ttc_volume_final_at_box` with the regime binder `big` as its only
hypothesis, **proves** it — written out here character for character as the
refutation states it.  It elaborates, so the two are the same proposition, at the
same `M`, `P`, `cen`, `γ̂` and precision, and `big` is the only thing standing
between the capstone and a contradiction.  (`Ttc.Box.canonSampD_eq_e2eSampD` records
by `rfl` that the shorter `Ttc.canonSampD` spelling used inside the proofs is the
same law.) -/
theorem final_accuracy_shape (n : ℕ) (hn : 1 ≤ n) (ε δ a : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a)
    (big : ∀ c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
        (fun _ => boxCentre n a) (a / 2) (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
        (parS n hn ε (4 * δ / 5) hε0 hε1.le).deltaPrime,
      (1 - (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime)
          * (parS n hn ε (4 * δ / 5) hε0 hε1.le).thresh / 8
        ≤ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
            (Ttc.toDNF (boxForm n hn))
            ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
            (e2eSampD (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
              (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
              (canonRfac (Ttc.toDNF (boxForm n hn)))
              (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
              (canonAm (boxAtoms n a) (Ttc.toDNF (boxForm n hn)))
              (canonBv (boxAtoms n a) (Ttc.toDNF (boxForm n hn))
                (latticeScale ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))))
              (fun _ => boxCentre n a) (a / 2)
              (canonDm (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))))
            (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2)
              (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
              (parS n hn ε (4 * δ / 5) hε0 hε1.le).deltaPrime c) s) :
    (1 - δ ≤
      (∫⁻ c, trajLaw (rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
            (Ttc.toDNF (boxForm n hn))
            ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
            (e2eSampD (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
              (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
              (canonRfac (Ttc.toDNF (boxForm n hn)))
              (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
              (canonAm (boxAtoms n a) (Ttc.toDNF (boxForm n hn)))
              (canonBv (boxAtoms n a) (Ttc.toDNF (boxForm n hn))
                (latticeScale ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))))
              (fun _ => boxCentre n a) (a / 2)
              (canonDm (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))))
            (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2)
              (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
              (parS n hn ε (4 * δ / 5) hε0 hε1.le).deltaPrime c))
          {t : ℕ → Fin (latticeCount (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
              ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))) → ℕ |
            ttcOutput (parS n hn ε (4 * δ / 5) hε0 hε1.le)
                (coveredOracles (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
                  ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
                  (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                    (fun _ => boxCentre n a) (a / 2)
                    (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
                    (parS n hn ε (4 * δ / 5) hε0 hε1.le).deltaPrime c))
                Ttc.toDNF ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
                (boxForm n hn) t
              ∈ relErr ε
                  (volSol (fun x => (boxAtoms n a x).halfspace) (boxForm n hn))}
        ∂(MonteCarlo.coins n)).toReal) :=
  (Box.ttc_volume_final_at_box n hn ε δ a hε0 hε1.le hδ0 hδ1 ha big).1

set_option maxHeartbeats 2000000 in
/-- **`Ttc.ttc_volume_final`'s accuracy conclusion fails on a small box**, for every
dimension `n ≥ 1`, every `ε ∈ (0,1)` and every `δ ∈ (0, 5/6)`.

The statement is the accuracy conjunct of `Ttc.ttc_volume_final` — the
`Ttc.MonteCarlo.coins`-integral, written with the capstone's own `Ttc.e2eSampD`,
`Ttc.mcVol`, `Ttc.rates` and `Ttc.coveredOracles` terms — at the box `[0,a]ⁿ`, and
it is **negated**.  Every other hypothesis of `Ttc.ttc_volume_final` holds at that
instance (`Ttc.Box.big_not_derivable` produces them, one per conjunct, at the same
kind of witness); only `big` fails, and `big` is precisely what a small body cannot
supply.

Restriction to `δ < 5/6`: the bound proved here is
`Pr[correct] ≤ (1 − e^(−Λ)) + Pr[volume oracle fails] ≤ (1 − e^(−Λ)) + δ/5`, and it
beats `1 − δ` only when `e^(−Λ) > 6δ/5`, which needs `6δ/5 < 1`.  See §8. -/
theorem small_box_refutes_final_accuracy (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 5 / 6) :
    ∃ a : ℝ, 0 < a ∧
      ¬ (1 - δ ≤
        (∫⁻ c, trajLaw (rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
              (Ttc.toDNF (boxForm n hn))
              ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
              (e2eSampD (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
                (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
                (canonRfac (Ttc.toDNF (boxForm n hn)))
                (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
                (canonAm (boxAtoms n a) (Ttc.toDNF (boxForm n hn)))
                (canonBv (boxAtoms n a) (Ttc.toDNF (boxForm n hn))
                  (latticeScale ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))))
                (fun _ => boxCentre n a) (a / 2)
                (canonDm (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                  ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))))
              (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                (fun _ => boxCentre n a) (a / 2)
                (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
                (parS n hn ε (4 * δ / 5) hε0 hε1.le).deltaPrime c))
            {t : ℕ → Fin (latticeCount (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
                ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))) → ℕ |
              ttcOutput (parS n hn ε (4 * δ / 5) hε0 hε1.le)
                  (coveredOracles (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
                    ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
                    (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                      (fun _ => boxCentre n a) (a / 2)
                      (parS n hn ε (4 * δ / 5) hε0 hε1.le).epsPrime
                      (parS n hn ε (4 * δ / 5) hε0 hε1.le).deltaPrime c))
                  Ttc.toDNF ((parS n hn ε (4 * δ / 5) hε0 hε1.le).precision (a / 2))
                  (boxForm n hn) t
                ∈ relErr ε
                    (volSol (fun x => (boxAtoms n a x).halfspace) (boxForm n hn))}
          ∂(MonteCarlo.coins n)).toReal) := by
  classical
  have hd0 : (0 : ℝ) < 4 * δ / 5 := by linarith
  have hd1 : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  set P := parS n hn ε (4 * δ / 5) hε0 hε1.le with hPdef
  have hep0 : 0 < P.epsPrime := parS_epsPrime_pos (n := n) (δ := 4 * δ / 5) hn hε0 hε1.le
  have hep12 : P.epsPrime ≤ 1 / 12 := parS_epsPrime_le (n := n) (δ := 4 * δ / 5) hn hε0 hε1.le
  have hT0 : 0 < P.thresh := parS_thresh_pos (n := n) hn hε0 hε1.le hd0 hd1
  -- the target the total rate must beat
  have h65 : (0 : ℝ) < 6 * δ / 5 := by linarith
  have h65' : (6 : ℝ) * δ / 5 < 1 := by linarith
  set Lg : ℝ := -Real.log (6 * δ / 5) with hLgdef
  have hLg : 0 < Lg := by
    rw [hLgdef]; have := Real.log_neg h65 h65'; linarith
  obtain ⟨a, ha0, hsmall⟩ :=
    exists_small_side n hn P hep0 (B := min P.thresh Lg) (lt_min hT0 hLg)
  refine ⟨a, ha0, ?_⟩
  set M := fun x => (boxAtoms n a x).halfspace with hMdef
  set ρ := P.precision (a / 2) with hρdef
  set Λ : ℝ := (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  have hΛT : Λ < P.thresh := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hΛL : Λ < Lg := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hVpos : 0 < volSol M (boxForm n hn) := by
    rw [volSol, sol_eq_bxOf n a hn]; exact volume_bxOf_pos n ha0
  -- the coin-wise bound, integrated
  have hlint := lintegral_trajLaw_relErr_le (MonteCarlo.coins n)
    (measurableSet_mcGood M (Ttc.toDNF (boxForm n hn)) (fun _ => boxCentre n a) (a / 2)
      P.epsPrime P.deltaPrime)
    M (boxForm n hn) P ρ
    (fun c => mcVol M (Ttc.toDNF (boxForm n hn)) (fun _ => boxCentre n a) (a / 2)
      P.epsPrime P.deltaPrime c)
    Ttc.toDNF
    (fun c => rates M (boxForm n hn) (Ttc.toDNF (boxForm n hn)) ρ
      (e2eSampD M (Ttc.toDNF (boxForm n hn)) ρ P.epsPrime
        (canonRfac (Ttc.toDNF (boxForm n hn)))
        (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
        (canonAm (boxAtoms n a) (Ttc.toDNF (boxForm n hn)))
        (canonBv (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) (latticeScale ρ))
        (fun _ => boxCentre n a) (a / 2)
        (canonDm M (Ttc.toDNF (boxForm n hn)) ρ))
      (mcVol M (Ttc.toDNF (boxForm n hn)) (fun _ => boxCentre n a) (a / 2)
        P.epsPrime P.deltaPrime c))
    (Λ := Λ) hε1 hVpos hT0.le
    (fun c hc => box_good_coin_bounds n hn ha0 P hep0 (by linarith) hΛT c hc)
  -- the numbers
  intro hacc
  have hAne : (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-Λ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hofr : ENNReal.ofReal (Real.exp (-Λ)) ≤ 1 :=
    ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by linarith))
  have hsum := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨hAne, measure_ne_top _ _⟩) hlint
  rw [ENNReal.toReal_add hAne (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le hofr ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hsum
  have hcompl := coins_mcGood_compl_le n hn ha0 P (δ₀ := 4 * δ / 5) rfl hd0 hd1
  rw [← hMdef] at hcompl
  have hexp : 6 * δ / 5 < Real.exp (-Λ) := by
    have hlt : Real.log (6 * δ / 5) < -Λ := by rw [hLgdef] at hΛL; linarith
    calc 6 * δ / 5 = Real.exp (Real.log (6 * δ / 5)) := (Real.exp_log h65).symm
      _ < _ := Real.exp_lt_exp.2 hlt
  linarith

/-! ## 9.  Verification -/

#print axioms Ttc.SmallBody.p_pos
#print axioms Ttc.SmallBody.p_le_one
#print axioms Ttc.SmallBody.level_le_foldl_step
#print axioms Ttc.SmallBody.p_foldl_step_le
#print axioms Ttc.SmallBody.p_run_le_one
#print axioms Ttc.SmallBody.run_eq_zero_of_card_eq_zero
#print axioms Ttc.SmallBody.output_zero_not_mem_relErr
#print axioms Ttc.SmallBody.thin_zero
#print axioms Ttc.SmallBody.gen_zero
#print axioms Ttc.SmallBody.haltLevel_eq_zero
#print axioms Ttc.SmallBody.absorbLevel_eq_zero
#print axioms Ttc.SmallBody.step_eq_empty
#print axioms Ttc.SmallBody.foldl_step_eq_empty
#print axioms Ttc.SmallBody.run_eq_zero_of_pois_zero
#print axioms Ttc.SmallBody.pois_trajOracles_zero
#print axioms Ttc.SmallBody.run_trajOracles_eq_zero
#print axioms Ttc.SmallBody.trajLaw_level_zero
#print axioms Ttc.SmallBody.measurableSet_level_zero
#print axioms Ttc.SmallBody.trajLaw_run_mem_relErr_le
#print axioms Ttc.SmallBody.trajLaw_relErr_le
#print axioms Ttc.SmallBody.not_accuracy_of_small_rate
#print axioms Ttc.SmallBody.exists_small_side
#print axioms Ttc.SmallBody.coins_mcGood_compl_le
#print axioms Ttc.SmallBody.box_good_coin_bounds
#print axioms Ttc.SmallBody.small_box_refutes_accuracy
#print axioms Ttc.SmallBody.lintegral_trajLaw_relErr_le
#print axioms Ttc.SmallBody.final_accuracy_shape
#print axioms Ttc.SmallBody.small_box_refutes_final_accuracy

end SmallBody

end Ttc

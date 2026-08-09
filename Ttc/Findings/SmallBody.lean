/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Regime

/-!
# `Findings/SmallBody`: on a small body the printed algorithm returns `0`

**What is proved.**  `alg:ttc` sets `p ← 1` and only ever halves it, so `p ≤ 1`
throughout the run (`Ttc.SmallBody.p_run_le_one`).  Consequently the whole sketch
`𝒳` is fed by draws `Nᵢ ∼ Pois(t·p)` whose rates are at most the cube volumes, and
when the body is small the very first level of the coupled family is already empty
with probability `e^(−Λ)`, `Λ = ∑ θ`.  On that event the modelled run never leaves
level `0`, `𝒳` stays empty, and the output is `|𝒳|/p = 0`
(`Ttc.SmallBody.run_eq_zero_of_pois_zero`).  Since `0 ∉ (1 ± ε)·Vol(Sol F)` as soon
as `Vol(Sol F) > 0` and `ε < 1` (`Ttc.SmallBody.output_zero_not_mem_relErr`), the
probability that `alg:ttc` answers correctly is at most `1 − e^(−Λ)`
(`Ttc.SmallBody.trajLaw_relErr_le`), which is **less than `1 − δ`** whenever
`Λ < log(1/δ)` (`Ttc.SmallBody.not_accuracy_of_small_rate`).

That last statement is the negation of `thm:volumettc`'s accuracy conclusion, in the
exact shape `Ttc.ttc_volume` states it.  `Ttc.SmallBody.small_box_refutes_accuracy`
exhibits an instance: a box `[0,a]ⁿ` of small side, a coin of the constructed volume
oracle's good event, and a proof that the accuracy conclusion **fails** there.  So
`thm:volumettc` as printed — i.e. without the regime binder `big` — is false, not
merely unproved.  This sharpens README finding 20 and `Ttc.Box.big_not_derivable`
(`Exec/Regime`), which only refuted a hypothesis.

## What is **not** proved — read this before quoting the file

* **The refutation is per volume-oracle coin, not integrated over coins.**
  `Ttc.ttc_volume`'s accuracy conclusion is `1 − δ ≤ (trajLaw θ {…}).toReal` at a
  *fixed* volume estimate `vol`; that is what `Ttc.SmallBody.not_accuracy_of_small_rate`
  and `Ttc.SmallBody.small_box_refutes_accuracy` negate.  `Ttc.ttc_volume_final`'s
  conclusion is the *`MonteCarlo.coins`-integral* of the same quantity, and
  `Ttc.SmallBody.lintegral_trajLaw_relErr_le` bounds that integral by
  `(1 − e^(−Λ)) + Pr[coins bad]`; turning it into a refutation of
  `Ttc.ttc_volume_final` needs `Pr[coins bad]` at the *user's* `δ`, which the
  development supplies only through `Ttc.measure_mcGood_ge`.  That last composition
  is **not** carried out here.
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
`(1+ε')·Vol([0,a]ⁿ)`, and `Ttc.Box.volume_bxOf_eq` makes both `O(aⁿ)`.  Picking

  `a = min 1 (min (Thresh/(2K)) (log(1/δ)/(2K)))`,  `K = (1+ε')²·Vol([0,1]ⁿ)`,

puts the estimate under `Thresh` **and** the total rate under `log(1/δ)`.

The coin is a *good* coin of the constructed Monte-Carlo volume oracle
(`Ttc.Box.mcGood_box_nonempty`), so the refutation is not an artefact of a bad
volume estimate: the oracle did its job, and the algorithm still answers `0`.
-/

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
  have hep1 : P.epsPrime < 1 := by linarith
  have hT0 : 0 < P.thresh := parS_thresh_pos (n := n) hn hε0 hε1.le hd0 hd1
  have hV1 : 0 < (volume (bxOf n 1)).toReal := volume_bxOf_pos n one_pos
  -- the two smallness targets
  set Lg : ℝ := -Real.log δ with hLgdef
  have hLg : 0 < Lg := by
    rw [hLgdef]
    have := Real.log_neg hδ0 hδ1
    linarith
  set K : ℝ := (1 + P.epsPrime) ^ 2 * (volume (bxOf n 1)).toReal with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set a : ℝ := min 1 (min (P.thresh / (2 * K)) (Lg / (2 * K))) with hadef
  have ha1 : a ≤ 1 := min_le_left _ _
  have ha0 : 0 < a :=
    lt_min one_pos (lt_min (div_pos hT0 (by linarith)) (div_pos hLg (by linarith)))
  have haT : a ≤ P.thresh / (2 * K) := le_trans (min_le_right _ _) (min_le_left _ _)
  have haL : a ≤ Lg / (2 * K) := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the volume of the small box
  have hvolbox : (volume (bxOf n a)).toReal = a ^ n * (volume (bxOf n 1)).toReal :=
    Box.volume_bxOf_eq n ha0
  have han : a ^ n ≤ a := by
    calc a ^ n ≤ a ^ 1 := pow_le_pow_of_le_one ha0.le ha1 hn
      _ = a := pow_one a
  have hbound : (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal ≤ K * a := by
    rw [hvolbox, hKdef]
    calc (1 + P.epsPrime) ^ 2 * (a ^ n * (volume (bxOf n 1)).toReal)
        = ((1 + P.epsPrime) ^ 2 * (volume (bxOf n 1)).toReal) * a ^ n := by ring
      _ ≤ ((1 + P.epsPrime) ^ 2 * (volume (bxOf n 1)).toReal) * a :=
          mul_le_mul_of_nonneg_left han (by positivity)
  have hKaT : K * a ≤ P.thresh / 2 := by
    calc K * a ≤ K * (P.thresh / (2 * K)) := mul_le_mul_of_nonneg_left haT hKpos.le
      _ = P.thresh / 2 := by field_simp
  have hKaL : K * a ≤ Lg / 2 := by
    calc K * a ≤ K * (Lg / (2 * K)) := mul_le_mul_of_nonneg_left haL hKpos.le
      _ = Lg / 2 := by field_simp
  -- the good coin
  obtain ⟨c, hc⟩ := Box.mcGood_box_nonempty n hn ha0 P rfl hd0 hd1
  refine ⟨a, c, ha0, hc, ?_, ?_⟩
  · rw [volSol, sol_eq_bxOf n a hn]
    exact volume_bxOf_pos n ha0
  · -- abbreviations
    set M := fun x => (boxAtoms n a x).halfspace with hMdef
    set D := Ttc.toDNF (boxForm n hn) with hDdef
    set ρ := P.precision (a / 2) with hρdef
    set vol := mcVol M D (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c with hvoldef
    have hVpos : 0 < volSol M (boxForm n hn) := by
      rw [volSol, sol_eq_bxOf n a hn]; exact volume_bxOf_pos n ha0
    have hfin : ∀ i : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ D}, volume (region M i.val) ≠ ⊤ :=
      volume_region_ne_top_of_isBounded (toDNF_isDNFOf (boxForm n hn))
        (isBounded_sol_bxOf n a hn)
    have hvolpos : ∀ i ∈ D, 0 < vol i :=
      mcVol_pos M D (fun _ => boxCentre n a) (by positivity) hep1
        (ball_subset_bxOf n a hn) hfin hc
    -- every cube's volume estimate is below `Thresh`
    have hvolT : ∀ i ∈ D, ¬ P.thresh / vol i ≤ 1 := by
      intro i hi
      have hup : vol i ≤ (1 + P.epsPrime) * (volume (region M i)).toReal :=
        (mcVol_mem_relErr M D (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime hc
          i hi).2
      rw [region_eq_bxOf n a hn hi] at hup
      have h1 : (1 + P.epsPrime) * (volume (bxOf n a)).toReal
          ≤ (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal := by
        have hnn : (0 : ℝ) ≤ (volume (bxOf n a)).toReal := ENNReal.toReal_nonneg
        have hcross : (0 : ℝ)
            ≤ (1 + P.epsPrime) * P.epsPrime * (volume (bxOf n a)).toReal :=
          mul_nonneg (mul_nonneg (by linarith) hep0.le) hnn
        nlinarith [hcross]
      have hlt : vol i < P.thresh := by linarith
      exact not_le.2 ((one_lt_div (hvolpos i hi)).2 hlt)
    -- the rates
    set sampD := canonSampD (boxAtoms n a) D P (fun _ => boxCentre n a) (a / 2) with hsampdef
    have hAU := Box.canonSampD_box_almostUniform n hn ha0 P hep0 (by linarith)
    have hθ : ∀ s, 0 ≤ rates M (boxForm n hn) D ρ sampD vol s := by
      intro s
      refine le_of_lt (rates_pos_of_almostUniform (toDNF_isDNFOf (boxForm n hn))
        (hasLatticeEnum_bxOf n a hn ρ) hvolpos hep1 ?_ s)
      intro i hi
      have : i = boxCube n := by
        simpa only [hDdef, toDNF_boxForm hn, boxDNF, List.mem_singleton] using hi
      subst this
      exact hAU
    -- the total rate is small
    have hsum : ∑ s, rates M (boxForm n hn) D ρ sampD vol s
        ≤ (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal :=
      (Box.sum_rates_box_window n hn ha0 P hep0 (by linarith) hc).2
    have hsumL : ∑ s, rates M (boxForm n hn) D ρ sampD vol s < Lg := by
      have : (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal ≤ Lg / 2 :=
        le_trans hbound hKaL
      linarith
    have hδexp : δ < Real.exp (-∑ s, rates M (boxForm n hn) D ρ sampD vol s) := by
      have hlt : Real.log δ < -∑ s, rates M (boxForm n hn) D ρ sampD vol s := by
        rw [hLgdef] at hsumL; linarith
      calc δ = Real.exp (Real.log δ) := (Real.exp_log hδ0).symm
        _ < _ := Real.exp_lt_exp.2 hlt
    exact not_accuracy_of_small_rate M (boxForm n hn) P ρ vol Ttc.toDNF hθ hε1 hVpos
      hT0.le hvolT hδexp

end SmallBody

end Ttc

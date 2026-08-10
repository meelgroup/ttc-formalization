/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Util.Notation3

/-!
# `Pr[…]` / `All[…]` over a `MeasureTheory.Measure`

This is the `Measure`-level analogue of nfalean's `ApproxNFA/Monadic/PMFPr.lean`.  It exists for
the same reason: an FPRAS guarantee is an inequality between **reals**, `1 - δ ≤ Pr[good]`, and a
measure assigns mass in `ℝ≥0∞`, where subtraction is truncated and `1 - δ` is not the `1 - δ`
anyone means.  We cross that bridge once, here, and everything downstream speaks only `ℝ`.

## Why `Measure` and not `PMF`

nfalean's randomness is a finite coin sequence, so its programs are honest `PMF`s and its `Pr[…]`
is `(p.toOuterMeasure s).toReal`.  Ours is not: `Ttc.MonteCarlo.coins` is
`Measure.infinitePi` of the uniform law on a Euclidean unit ball — an atomless measure on an
uncountable space.  There is no `PMF` whose `toOuterMeasure` it is, so the `PMF` API is simply
unavailable and the notation must be stated over `MeasureTheory.Measure`.  This is a fact about
the object, not a stylistic choice.

The practical consequences, all visible in the hypotheses below:

* **Measurability side conditions are real.**  A `PMF`'s outer measure is a `tsum` and its
  Carathéodory σ-algebra is `⊤`, so nfalean's lemmas need no measurability at all.  Here,
  additivity on complements, pushforward along `map`, and the `dirac` computation each need the
  event to be (null-)measurable.  Every lemma that can avoid the hypothesis does
  (`PrR_or_le`, `PrR_exists_le`, `one_sub_le_PrR_of_compl_le` — see below).
* **Finiteness is a hypothesis, not a theorem.**  `PMF.toOuterMeasure` is bounded by `1` for free.
  The type `Measure α` is general, so `toReal` is faithful only under `[IsFiniteMeasure μ]`, and
  `Pr ≤ 1` needs `[IsProbabilityMeasure μ]`.  These are added exactly where a law genuinely needs
  them rather than globally, so nothing here is silently false for a sub-probability measure.

## `All[…]` is almost-everywhere, **not** support-based

nfalean's `All[x ← p; E x]` is `PMF.support p ⊆ {x | E x}`: *no* exceptional outcome exists at
all.  We deliberately do **not** copy that.  Mathlib's `MeasureTheory.Measure.support` is the
topological support, `{x | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}`, and it requires a
`[TopologicalSpace α]` instance — which would drag topology into the *statement* of the headline
theorem, and which is not available for a general carrier.  Worse, for a general measure it is not
even the right notion: `μ (μ.support)ᶜ = 0` needs second countability, so a support-based `All`
would not imply `Pr = 1` without extra hypotheses.

So `All[x ← μ; E x]` is Mathlib's `∀ᵐ x ∂μ, E x`.  **This is strictly weaker than nfalean's
`All`**: it permits a set of exceptional points, provided that set is null.  For an atomless `μ`
such a set can be large (uncountable, dense) — it just cannot be seen by `μ`.  What it buys is
that `PrR_of_all` below is unconditional in the event: an a.e.-true event has probability exactly
`1`, no measurability required.  Under nfalean's discrete reading the two agree, because a `PMF`
has no nonempty null sets inside its support; the divergence is a genuine feature of the
continuous setting, and it is why the docstrings below say "a.e." wherever nfalean says "every".

## Design

`Pr[x ← μ; E x]` is `notation3` elaborating to `(μ {x | E x}).toReal` — Mathlib's own measure
applied to Mathlib's own `setOf`, read as a real.  Nothing of ours appears in a statement written
with it; in particular `Ttc.MonteCarlo.correct` already reads
`1 - pf ≤ (coins n {ω | …}).toReal`, which is *syntactically* this notation's expansion.

`MeasureTheory.Measure.PrR` is the same term under a name, declared in Mathlib's `Measure`
namespace so that `μ.PrR E` dot-notation parses; `PrR_eq_pr` is the (definitional) bridge, and
`PrR_eq_measureReal` is the (definitional) bridge to Mathlib's `μ.real` API, which is where most
of the proofs below come from.

The event is a predicate `E : α → Prop`, not a `Set α`, for the same reason as in nfalean:
downstream events are predicates on an algorithm's output, and `PrR_congr` / `PrR_mono` are what
let a chain of sufficient conditions become a probability bound.
-/

open scoped ENNReal
open Set MeasureTheory

namespace MeasureTheory.Measure

/-- **Probability of an event under a measure, as a real number.**

The event is a predicate; `{x | E x}` is its extension.  `toReal` is lossless exactly when the
event has finite measure, which holds for every `[IsFiniteMeasure μ]` (`Ttc.Monadic.PrR_ne_top`);
for a probability measure the value lies in `[0,1]` (`Ttc.Monadic.PrR_mem_Icc`).

Declared in the `MeasureTheory.Measure` namespace so that `μ.PrR E` parses; the API is in
`Ttc.Monadic`. -/
noncomputable def PrR {α : Type*} [MeasurableSpace α] (μ : Measure α) (E : α → Prop) : ℝ :=
  (μ {x | E x}).toReal

end MeasureTheory.Measure

namespace Ttc.Monadic

/-- **`Pr[x ← μ; E x]` — the probability that a draw from the measure `μ` satisfies `E`.**

Notation only: it elaborates to `(μ {x | E x}).toReal`, i.e. Mathlib's measure applied to the
event's extension, read as a real.  Nothing of ours occurs in a statement written with it.
`MeasureTheory.Measure.PrR` is the same term under a name, kept because the API lemmas below read
better stated about a constant; `PrR_eq_pr` is the definitional bridge. -/
notation3 "Pr["(...)" ← "μ"; "r:(scoped E => (((μ : MeasureTheory.Measure _)) (setOf E)).toReal)"]" => r

/-- **`All[x ← μ; E x]` — `E` holds at `μ`-almost every point.**

Notation only: it elaborates to Mathlib's `∀ᵐ x ∂μ, E x` (that is, `Filter.Eventually E (ae μ)`),
so nothing of ours appears in a statement written with it either.  It shares the `x ← μ` draw
syntax with `Pr[…]` so that two guarantees about the same program read the same way, and
`filter_upwards`/`Filter.Eventually.mono` open it.

**This is weaker than nfalean's `All`,** which is `PMF.support p ⊆ {x | E x}` — *no* exceptional
outcome at all.  See the module docstring: Mathlib's `Measure.support` is topological, needs a
`[TopologicalSpace α]` instance we do not want in the headline's statement, and for a general
measure does not even carry full mass.  `∀ᵐ` permits an exceptional set, provided `μ` cannot see
it.  For the atomless `Ttc.MonteCarlo.coins` that is the honest statement.

It is deliberately not written as `Pr[x ← μ; E x] = 1`: `PrR_of_all` converts (and needs
`[IsProbabilityMeasure μ]` to do so), but the `∀ᵐ` form is what proofs actually produce, and it
survives without any measurability hypothesis on the event. -/
notation3 "All["(...)" ← "μ"; "r:(scoped E => Filter.Eventually E (MeasureTheory.ae μ))"]" => r

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}

/-! ## The three definitional bridges -/

/-- The API constant unfolds to its definition. -/
theorem PrR_def (μ : Measure α) (E : α → Prop) : μ.PrR E = (μ {x | E x}).toReal := rfl

/-- The API constant and the `Pr[…]` notation are the same term. -/
theorem PrR_eq_pr (μ : Measure α) (E : α → Prop) : μ.PrR E = Pr[x ← μ; E x] := rfl

/-- The API constant is Mathlib's `μ.real` at the event's extension.  This is the workhorse: every
proof below that is not pure `ENNReal` arithmetic goes through it and reuses
`MeasureTheory.measureReal_*`. -/
theorem PrR_eq_measureReal (μ : Measure α) (E : α → Prop) : μ.PrR E = μ.real {x | E x} := rfl

/-- `All[…]` and Mathlib's `∀ᵐ` are the same term. -/
theorem all_eq_ae (μ : Measure α) (E : α → Prop) : (All[x ← μ; E x]) = ∀ᵐ x ∂μ, E x := rfl

/-! ## Basic properties

`PrR` is a `toReal`, so nonnegativity is free; everything else is where the `Measure` setting
starts costing hypotheses that the `PMF` setting did not. -/

/-- `PrR` is a `toReal`, hence nonnegative — no hypotheses needed, exactly as for a `PMF`. -/
theorem PrR_nonneg (μ : Measure α) (E : α → Prop) : 0 ≤ μ.PrR E :=
  ENNReal.toReal_nonneg

/-- **The underlying `ℝ≥0∞` mass of an event is finite.**  Every arithmetic lemma below needs this,
since `toReal` is additive and monotone only away from `∞`.  For a `PMF` this was a theorem
(total mass `1`); here it is exactly the content of `[IsFiniteMeasure μ]`. -/
theorem PrR_ne_top (μ : Measure α) [IsFiniteMeasure μ] (E : α → Prop) : μ {x | E x} ≠ ∞ :=
  measure_ne_top μ _

/-- Probabilities do not exceed `1`.  Needs `[IsProbabilityMeasure μ]`: for a general measure the
statement is false, and for a sub-probability measure it is `IsZeroOrProbabilityMeasure` that
Mathlib's `prob_le_one` actually asks for. -/
theorem PrR_le_one (μ : Measure α) [IsProbabilityMeasure μ] (E : α → Prop) : μ.PrR E ≤ 1 := by
  rw [PrR_def, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

theorem PrR_mem_Icc (μ : Measure α) [IsProbabilityMeasure μ] (E : α → Prop) :
    μ.PrR E ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨PrR_nonneg μ E, PrR_le_one μ E⟩

/-! ## Rewriting and monotonicity -/

/-- **Rewriting an event pointwise.**  The main use: replace the algorithm's literal output
condition by whichever equivalent form the current estimate is phrased in, without touching the
probability.  Transfers from `PMF` verbatim — it is set equality, so no measurability enters. -/
theorem PrR_congr {E F : α → Prop} (h : ∀ x, E x ↔ F x) : μ.PrR E = μ.PrR F := by
  rw [PrR_def, PrR_def, Set.ext h]

/-- **Rewriting an event a.e.**  The genuinely new one: in the continuous setting an event may be
replaced by another that differs on a null set.  This is the form `All[…]` feeds into. -/
theorem PrR_ae_congr {E F : α → Prop} (h : All[x ← μ; (E x ↔ F x)]) : μ.PrR E = μ.PrR F :=
  measureReal_congr (Filter.eventuallyEq_set.2 h)

/-- **Monotonicity.**  A weaker event is more likely.  This is how a chain of sufficient conditions
becomes a probability bound.  Unlike the `PMF` version this needs `[IsFiniteMeasure μ]`: `toReal`
is monotone only when the larger value is finite, and `μ.real` sends `∞` to `0`. -/
theorem PrR_mono [IsFiniteMeasure μ] {E F : α → Prop} (h : ∀ x, E x → F x) : μ.PrR E ≤ μ.PrR F :=
  measureReal_mono (fun x hx => h x hx) (PrR_ne_top μ F)

/-- **Monotonicity, a.e. form.**  The implication need only hold off a null set. -/
theorem PrR_ae_mono [IsFiniteMeasure μ] {E F : α → Prop} (h : All[x ← μ; (E x → F x)]) :
    μ.PrR E ≤ μ.PrR F :=
  ENNReal.toReal_mono (PrR_ne_top μ F) (measure_mono_ae (by filter_upwards [h] with x hx using hx))

/-! ## Pushforward

This is the one the headline uses: the theorem is stated about the distribution of the algorithm's
*output*, `Measure.map output coins`, while the proof works with the raw coins.  Both hypotheses
are unavoidable here — `Measure.map` is defined to be `0` for a non-measurable map, and
`Measure.map_apply` evaluates only at measurable sets. -/

/-- **`Pr` under `Measure.map`.**  An event about the image is the corresponding event about the
source.  Compare `PMF.PrR_map`, which needs no hypotheses because a `PMF`'s outer measure is
defined on every set. -/
theorem PrR_map {f : α → β} (hf : Measurable f) {E : β → Prop} (hE : MeasurableSet {y | E y}) :
    (μ.map f).PrR E = μ.PrR (fun x => E (f x)) := by
  rw [PrR_eq_measureReal, PrR_eq_measureReal, map_measureReal_apply hf hE]
  rfl

/-- The `AEMeasurable` refinement, for when the map is only a.e. measurable. -/
theorem PrR_map_of_aemeasurable {f : α → β} (hf : AEMeasurable f μ) {E : β → Prop}
    (hE : MeasurableSet {y | E y}) : (μ.map f).PrR E = μ.PrR (fun x => E (f x)) := by
  rw [PrR_eq_measureReal, PrR_eq_measureReal, map_measureReal_apply_of_aemeasurable hf hE]
  rfl

/-! ## Failure bounds become success bounds

Every estimate in the analysis is naturally an upper bound on a *failure* event; the theorem is a
lower bound on the *success* event.  These lemmas are the only place that conversion happens.

The asymmetry here is worth noting.  `1 ≤ Pr[E] + Pr[¬E]` is **subadditivity**, which holds for
arbitrary sets — so `one_sub_le_PrR_of_compl_le`, the direction the headline is proved in, needs
no measurability at all.  The reverse inequality is additivity on a disjoint pair, which genuinely
needs the event to be null-measurable. -/

/-- **Subadditivity across a complement.**  `{x | E x} ∪ {x | ¬ E x} = univ` and measures are
subadditive on arbitrary sets, so no measurability hypothesis is needed. -/
theorem one_le_PrR_add_compl (μ : Measure α) [IsProbabilityMeasure μ] (E : α → Prop) :
    1 ≤ μ.PrR E + μ.PrR (fun x => ¬ E x) := by
  have huniv : (Set.univ : Set α) = {x | E x} ∪ {x | ¬ E x} := by
    ext x; simpa using em (E x)
  have hle : (1 : ℝ≥0∞) ≤ μ {x | E x} + μ {x | ¬ E x} := by
    calc (1 : ℝ≥0∞) = μ Set.univ := (measure_univ).symm
      _ = μ ({x | E x} ∪ {x | ¬ E x}) := by rw [← huniv]
      _ ≤ μ {x | E x} + μ {x | ¬ E x} := measure_union_le _ _
  have := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨PrR_ne_top μ E, PrR_ne_top μ fun x => ¬ E x⟩) hle
  rwa [ENNReal.toReal_one,
    ENNReal.toReal_add (PrR_ne_top μ E) (PrR_ne_top μ fun x => ¬ E x)] at this

/-- **The real-valued complement law.**  `toReal` is additive here because both summands are
finite; this is precisely the step that would go wrong had we tried to run the development in
`ℝ≥0∞` with truncated subtraction.  Needs null-measurability of the event, which the `PMF` version
did not: additivity on a disjoint pair is not available for arbitrary sets. -/
theorem PrR_add_compl [IsProbabilityMeasure μ] {E : α → Prop}
    (hE : NullMeasurableSet {x | E x} μ) : μ.PrR E + μ.PrR (fun x => ¬ E x) = 1 := by
  have hcompl : {x | ¬ E x} = ({x | E x} : Set α)ᶜ := rfl
  rw [PrR_eq_measureReal, PrR_eq_measureReal, hcompl, measureReal_add_measureReal_compl₀ hE,
    probReal_univ]

/-- The success probability is exactly one minus the failure probability. -/
theorem PrR_compl [IsProbabilityMeasure μ] {E : α → Prop}
    (hE : NullMeasurableSet {x | E x} μ) : μ.PrR (fun x => ¬ E x) = 1 - μ.PrR E := by
  rw [eq_sub_iff_add_eq, add_comm]
  exact PrR_add_compl hE

/-- **The shape the headline theorem is proved in.**  Bound the failure probability by `d`;
conclude `1 - d ≤ Pr[success]`.  No measurability hypothesis — see the section docstring. -/
theorem one_sub_le_PrR_of_compl_le [IsProbabilityMeasure μ] {E : α → Prop} {d : ℝ}
    (h : μ.PrR (fun x => ¬ E x) ≤ d) : 1 - d ≤ μ.PrR E := by
  have := one_le_PrR_add_compl μ E
  linarith

/-- The converse, occasionally handier when an estimate is already stated positively.  This
direction *does* need null-measurability: it is the additivity half. -/
theorem PrR_compl_le_of_one_sub_le [IsProbabilityMeasure μ] {E : α → Prop} {d : ℝ}
    (hE : NullMeasurableSet {x | E x} μ) (h : 1 - d ≤ μ.PrR E) :
    μ.PrR (fun x => ¬ E x) ≤ d := by
  have := PrR_add_compl hE
  linarith

/-! ## Union bounds

Both transfer with *no* hypotheses, because Mathlib's `measureReal_union_le` and
`measureReal_biUnion_finset_le` are already stated unconditionally (they dispose of the `∞` case
by hand, `μ.real` being `0` there). -/

/-- **Union bound, two events.**  Stated on the failure side, because that is how it is used: two
ways to fail, each rare. -/
theorem PrR_or_le (μ : Measure α) (E F : α → Prop) :
    μ.PrR (fun x => E x ∨ F x) ≤ μ.PrR E + μ.PrR F := by
  have hunion : {x | E x ∨ F x} = {x | E x} ∪ {x | F x} := rfl
  rw [PrR_eq_measureReal, PrR_eq_measureReal, PrR_eq_measureReal, hunion]
  exact measureReal_union_le _ _

/-- **Union bound over a `Finset` of failure modes.**  The analysis fails in one of finitely many
ways (one per run, per block, per layer); this is the form the accounting actually uses. -/
theorem PrR_exists_le (μ : Measure α) (s : Finset ι) (E : ι → α → Prop) :
    μ.PrR (fun x => ∃ i ∈ s, E i x) ≤ ∑ i ∈ s, μ.PrR (E i) := by
  have hset : {x : α | ∃ i ∈ s, E i x} = ⋃ i ∈ s, {x | E i x} := by ext x; simp
  rw [PrR_eq_measureReal, hset]
  exact measureReal_biUnion_finset_le s _

/-! ## `All[…]` and its interaction with `Pr[…]` -/

/-- A fact true everywhere is true a.e. -/
theorem all_of_forall {E : α → Prop} (h : ∀ x, E x) : All[x ← μ; E x] :=
  Filter.Eventually.of_forall h

/-- `All[…]` is monotone in the event. -/
theorem all_mono {E F : α → Prop} (h : ∀ x, E x → F x) (hE : All[x ← μ; E x]) :
    All[x ← μ; F x] :=
  hE.mono h

/-- `All[…]` is closed under conjunction — the routine step when several a.e. guarantees about the
same draw are combined. -/
theorem all_and {E F : α → Prop} (hE : All[x ← μ; E x]) (hF : All[x ← μ; F x]) :
    All[x ← μ; (E x ∧ F x)] :=
  hE.and hF

/-- **An almost-sure event has probability one.**  The `Measure` analogue of `PMF.PrR_of_forall`,
and the payoff of choosing `∀ᵐ` for `All`: no measurability hypothesis on the event is needed,
because `{x | E x}` differs from `univ` by a null set and `measureReal_congr` is unconditional. -/
theorem PrR_of_all [IsProbabilityMeasure μ] {E : α → Prop} (h : All[x ← μ; E x]) :
    μ.PrR E = 1 := by
  have hset : ({x | E x} : Set α) =ᵐ[μ] Set.univ :=
    Filter.eventuallyEq_set.2 (by filter_upwards [h] with x hx using by simp [hx])
  rw [PrR_eq_measureReal, measureReal_congr hset, probReal_univ]

/-- The converse for a null-measurable event: probability one is a.e. truth.  (Without
null-measurability this can fail, which is the precise sense in which `All` is the stronger of the
two statements.) -/
theorem all_of_PrR_eq_one [IsProbabilityMeasure μ] {E : α → Prop}
    (hE : NullMeasurableSet {x | E x} μ) (h : μ.PrR E = 1) : All[x ← μ; E x] := by
  have hcompl : μ ({x | E x} : Set α)ᶜ = 0 := by
    have hadd := PrR_add_compl (μ := μ) hE
    have hzero : μ.PrR (fun x => ¬ E x) = 0 := by rw [h] at hadd; linarith
    have := (measureReal_eq_zero_iff (μ := μ) (s := {x | ¬ E x})
      (PrR_ne_top μ fun x => ¬ E x)).1 hzero
    exact this
  exact MeasureTheory.ae_iff.2 hcompl

/-! ## Small computations -/

/-- The certain event. -/
@[simp] theorem PrR_true (μ : Measure α) [IsProbabilityMeasure μ] :
    μ.PrR (fun _ => True) = 1 :=
  PrR_of_all (all_of_forall fun _ => trivial)

/-- The impossible event.  No hypotheses at all: `{x | False} = ∅`. -/
@[simp] theorem PrR_false (μ : Measure α) : μ.PrR (fun _ => False) = 0 := by
  have hempty : {_x : α | False} = (∅ : Set α) := by ext; simp
  rw [PrR_def, hempty, measure_empty, ENNReal.toReal_zero]

open scoped Classical in
/-- **A deterministic program succeeds iff its single outcome is good.**  The `Measure` analogue of
`PMF.PrR_pure`; `Measure.dirac` needs the event measurable to be evaluated at it, and the `if`
uses classical decidability of `E a`. -/
theorem PrR_dirac (a : α) {E : α → Prop} (hE : MeasurableSet {x | E x}) :
    (Measure.dirac a).PrR E = if E a then 1 else 0 := by
  rw [PrR_def, Measure.dirac_apply' a hE]
  by_cases h : E a
  · rw [Set.indicator_of_mem (show a ∈ {x | E x} from h), if_pos h, Pi.one_apply,
      ENNReal.toReal_one]
  · rw [Set.indicator_of_notMem (show a ∉ {x | E x} from h), if_neg h, ENNReal.toReal_zero]

/-! ## Axiom audit -/

#print axioms MeasureTheory.Measure.PrR
#print axioms Ttc.Monadic.PrR_def
#print axioms Ttc.Monadic.PrR_eq_pr
#print axioms Ttc.Monadic.PrR_eq_measureReal
#print axioms Ttc.Monadic.all_eq_ae
#print axioms Ttc.Monadic.PrR_nonneg
#print axioms Ttc.Monadic.PrR_ne_top
#print axioms Ttc.Monadic.PrR_le_one
#print axioms Ttc.Monadic.PrR_mem_Icc
#print axioms Ttc.Monadic.PrR_congr
#print axioms Ttc.Monadic.PrR_ae_congr
#print axioms Ttc.Monadic.PrR_mono
#print axioms Ttc.Monadic.PrR_ae_mono
#print axioms Ttc.Monadic.PrR_map
#print axioms Ttc.Monadic.PrR_map_of_aemeasurable
#print axioms Ttc.Monadic.one_le_PrR_add_compl
#print axioms Ttc.Monadic.PrR_add_compl
#print axioms Ttc.Monadic.PrR_compl
#print axioms Ttc.Monadic.one_sub_le_PrR_of_compl_le
#print axioms Ttc.Monadic.PrR_compl_le_of_one_sub_le
#print axioms Ttc.Monadic.PrR_or_le
#print axioms Ttc.Monadic.PrR_exists_le
#print axioms Ttc.Monadic.all_of_forall
#print axioms Ttc.Monadic.all_mono
#print axioms Ttc.Monadic.all_and
#print axioms Ttc.Monadic.PrR_of_all
#print axioms Ttc.Monadic.all_of_PrR_eq_one
#print axioms Ttc.Monadic.PrR_true
#print axioms Ttc.Monadic.PrR_false
#print axioms Ttc.Monadic.PrR_dirac

end Ttc.Monadic

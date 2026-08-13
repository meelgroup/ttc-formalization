/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.LovaszVempalaIso

/-!
# The Localization Lemma at indicator integrands: what Theorem 2.1 must be given

**Read this first — the target was not reached.**  This file does **not** contain
`hloc_indicator` and does **not** contain `thm21_uncond`.  It does not discharge the binder
`hloc` of `Arlib.thm21_of_localization` (`Arlib/Convexity/LovaszVempalaIso.lean:733`), and it
does not prove Lovász–Vempala Theorem 2.1 unconditionally.  What it does contain is a
determination about *which* localisation conclusion Theorem 2.1 needs, one third of it
machine-checked as a counterexample, together with the one-dimensional and needle-level halves
of the statement that conclusion feeds.

## The task, and the verdict

`hloc` is the Localization Lemma applied to the **indicator-based** pair

    g₁ = 1_{T₁} − A·1_K,     g₂ = A·h·1_K − 1_{(K∖T₁)∖T₂},

and the two routes to it are the ones named in `AUDIT.md` items **(C)** and **(F)**:
mollify-and-pass-to-the-limit, or weaken `Continuous` inside the needle extraction.

**Both are closed, and neither closure is new to this file — they are recorded, not
discovered.**

* **Weakening `Continuous` is refuted in this repository.**
  `Arlib.exists_transverse_oscillation_eq_one`
  (`Arlib/Convexity/LocalizationMeasurable.lean`) exhibits a measurable set whose transverse
  oscillation is `1` on *every* body of positive volume, so the moduli of
  `Arlib.exists_tendsto_transverse_modulus` (`Arlib/Convexity/LocalizationTransverse.lean:112`)
  — the **unique** place the limit passage consumes continuity — do not tend to `0` for
  indicators.  And `Arlib.exists_null_measurableSet_needleIntegral_eq_one` shows a *null* set
  can carry needle mass `1`, which kills every almost-everywhere reroute (`L¹` density, Lusin,
  Vitali–Carathéodory, in-measure approximation) at once.

* **Mollification is closed at the *equality* slot.**  The approximation machinery already
  exists: `Arlib.Convexity.LocalizationLSC` reaches lower semicontinuous integrands, and
  `Arlib.Convexity.IsoOpenClosed` even removes its `η`-slack, by **scaling** a nonnegative
  minorant instead of shifting it, so that `∫_K g₁ = 0` holds *exactly*
  (`Arlib.exists_compact_body_continuous_pair`).  But a minorant is one-sided: the needle
  conclusion it transports is

      0 ≤ ∫ W · (1_{T₁} − A·1_K) ∘ γ,    i.e.   A·∫_α^β D ≤ ∫_{γ⁻¹T₁ ∩ [α,β]} D,

  the `≥`-half of `hloc`'s equality and nothing more.  Getting the `≤`-half back needs a
  continuous **majorant** of `1_{T₁}` with the same exact mass, i.e. `T₁` closed as well as
  open; inside a connected `K` that forces `T₁ ∈ {∅, K}`.

  **The `≥`-half alone is not enough, and that is the new content here.**
  `Arlib.needle_iso` — the one-dimensional core of §2 — consumes its `hmass` in *both*
  directions: `≥` at `hT₁pos`/`hkey` (`LovaszVempalaIso.lean:467-473`), and `≤` (through
  `A ≤ 1/2`) in the closing `nlinarith`.  `Arlib.not_needle_iso_of_one_lower` below refutes
  the `≥`-only statement outright, keeping `0 ≤ A` and `A ≤ 1/2`, so this is a fact about the
  statement and not an artefact of one proof.

## What *would* suffice, and why it is a different development

Two lower bounds — one on each of `T₁` and `T₂` — do suffice, with no equality anywhere:
`Arlib.needle_iso_two_lower`.  Both are of the form "the needle mass of an open set is at
least its ambient fraction", which is exactly what a minorant delivers.  So the obstruction
is **not** the one-sidedness; it is the *count*.

A single run of the chain `Arlib.exists_flat_cut_chain_collinear_compact_ge` maintains one
equality `∫_{D m} g₁ = 0` and one inequality `0 < ∫_{D m} g₂`: the cut bisects `g₁`, so both
halves inherit the equality, and at least one half inherits the strict inequality.  Two
inequalities besides the positivity means **two** quantities to bisect on a one-parameter
pencil, which is a two-parameter cut family and Borsuk–Ulam — absent from Mathlib, and the
very thing `Arlib/Convexity/LocalizationAssembly.lean:42-44` was able to avoid precisely
because only one integrand ever needed bisecting.

The other escape, a genuine limit passage over a *sequence* of needles, needs compactness of
the family of needle profiles plus continuity of `(γ, W) ↦ ∫ W · 1_{T₁} ∘ γ` — and the second
is false for indicators for the same reason as above (needle integrals see Lebesgue-null
sets).  `Arlib.Convexity.LocalizationLSC` says as much in its own docstring.

## Main results

* `Arlib.needle_iso_two_lower` — **the one-dimensional theorem from two lower bounds.**
  `Arlib.needle_iso` with `∫_{Z₁} D = A·∫_α^β D` replaced by `A·∫_α^β D ≤ ∫_{Z₁} D` *and*
  `A·∫_α^β D ≤ ∫_{Z₂} D`.  `0 ≤ A` and `A ≤ 1/2` become unnecessary; `0 ≤ G` on `[α,β]` is
  added (every consumer has it).  Proved from `Arlib.needle_iso` as a black box.
* `Arlib.counter_isPartition3`, `Arlib.not_needle_iso_of_one_lower` — **the refutation of the
  one-sided form**, in the idiom of `Arlib.not_hIso_two`: the `≥`-only statement written out
  verbatim and negated, with an explicit interval witness.
* `Arlib.needle_iso_of_chord_two_lower` — the same on a needle inside the body: this is
  `Arlib.needle_iso_of_chord` with its closing call redirected.
* `Arlib.thm21_of_localization_two_lower` — **Theorem 2.1 for the uniform density from the
  two-sided binder `hloc₂`**, whose ambient antecedents are `A·vol K ≤ vol T₁` and
  `A·vol K ≤ vol T₂` — exactly the `min(vol T₁, vol T₂)` shape the `hIso` binder of
  `Arlib.MarkovChains.conductance_hitAndRun_ge` wants, and with no `A ≤ 1/2` side condition.

## Honesty

`hloc₂` is **not weaker** than `hloc`, and it is not claimed to be: `hloc`'s equality gives
the `T₁` bound but says nothing about `T₂`, and for the present one-bisection chain `hloc₂` is
strictly *harder* (three constraints against two).  Its value is that it is the **sharp**
interface — `Arlib.not_needle_iso_of_one_lower` shows the `T₂` bound cannot be dropped — and
that both of its clauses are of the one-sided shape an approximation argument can produce, so
it is the statement a future two-constraint (Borsuk–Ulam) chain should be pointed at.

Nothing below is a `def`, `structure`, `class` or named `Prop`; every declaration is a
`theorem`, and none of them is named for a statement it does not prove.  The two binders that
do appear — `hloc₂` of `Arlib.thm21_of_localization_two_lower` and the universally quantified
statement negated by `Arlib.not_needle_iso_of_one_lower` — are written out inline at their
declarations.
-/

namespace Arlib

open MeasureTheory Set

/-! ### The one-dimensional needle inequality from two lower bounds -/

section OneDim

/-- **The one-dimensional needle inequality of Lovász–Vempala §2, from two *lower* bounds
instead of the mass equality.**

`Arlib.needle_iso` asks for the exact needle mass identity `∫_{Z₁} D = A·∫_α^β D`.  This
variant asks instead for the two one-sided bounds

    A · ∫_α^β D ≤ ∫_{Z₁} D    and    A · ∫_α^β D ≤ ∫_{Z₂} D,

and reaches the same conclusion.  Two interface improvements come for free:

* the hypothesis `A ≤ 1/2` of `Arlib.needle_iso` is **not needed** — in each branch of the
  proof the constant actually fed to `Arlib.needle_iso` is `∫_{Zᵢ} D / ∫_α^β D` for the
  *smaller* of the two parts, which is `≤ 1/2` automatically;
* `0 ≤ A` is not needed either.

The price is `hG0`, nonnegativity of `G` on `[α, β]` (`Arlib.needle_iso` does not ask for it),
which is what makes the conclusion monotone in `A`.  Every consumer has it: `G` is the
step-length weight `h`, which is nonnegative by hypothesis.

The proof is a case split on which of `∫_{Z₁} D`, `∫_{Z₂} D` is at most half of `∫_α^β D` —
at least one is, since the three parts sum to the whole — followed by `Arlib.needle_iso`
applied at that part's exact fraction, used as a black box.  In the second branch the two
parts are exchanged by `Arlib.IsPartition3.symm` and `min_comm`/`max_comm`.

**This hypothesis is genuinely stronger than the `≥`-half of the equality alone**: see
`Arlib.not_needle_iso_of_one_lower`, which refutes the statement obtained by dropping
`hmass₂`. -/
theorem needle_iso_two_lower {D G : ℝ → ℝ} {α β A M : ℝ} (hαβ : α ≤ β)
    (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hlc : LogConcaveOn (Set.Icc α β) D)
    (hDint : IntervalIntegrable D volume α β)
    (hG0 : ∀ t ∈ Set.Icc α β, 0 ≤ G t)
    (hGM : ∀ t ∈ Set.Icc α β, G t ≤ M) (hM0 : 0 ≤ M) (hM3 : M ≤ 1 / 3)
    (hGDint : IntervalIntegrable (fun t => G t * D t) volume α β)
    {Z₁ Z₂ Z₃ : Set ℝ} (hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃)
    (hm₁ : MeasurableSet Z₁) (hm₂ : MeasurableSet Z₂) (hm₃ : MeasurableSet Z₃)
    (hmass₁ : A * (∫ t in α..β, D t) ≤ ∫ t in Z₁, D t)
    (hmass₂ : A * (∫ t in α..β, D t) ≤ ∫ t in Z₂, D t)
    (hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂,
      3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t)) :
    A * (∫ t in α..β, G t * D t) ≤ ∫ t in Z₃, D t := by
  have hT0 : 0 ≤ ∫ t in α..β, D t := intervalIntegral.integral_nonneg hαβ hD0
  have hT₁0 : 0 ≤ ∫ t in Z₁, D t :=
    setIntegral_nonneg hm₁ fun t ht => hD0 t (hpart.subset₁ ht)
  have hT₂0 : 0 ≤ ∫ t in Z₂, D t :=
    setIntegral_nonneg hm₂ fun t ht => hD0 t (hpart.subset₂ ht)
  have hT₃0 : 0 ≤ ∫ t in Z₃, D t :=
    setIntegral_nonneg hm₃ fun t ht => hD0 t (hpart.subset₃ ht)
  have hsum : (∫ t in α..β, D t) = (∫ t in Z₁, D t) + (∫ t in Z₂, D t) + ∫ t in Z₃, D t :=
    integral_of_isPartition3 hαβ hDint hpart hm₂ hm₃
  have hGDnn : 0 ≤ ∫ t in α..β, G t * D t :=
    intervalIntegral.integral_nonneg hαβ fun t ht => mul_nonneg (hG0 t ht) (hD0 t ht)
  have hGD : (∫ t in α..β, G t * D t) ≤ M * ∫ t in α..β, D t := by
    have hmono : (∫ t in α..β, G t * D t) ≤ ∫ t in α..β, M * D t := by
      refine intervalIntegral.integral_mono_on hαβ hGDint (hDint.const_mul M) ?_
      intro t ht
      exact mul_le_mul_of_nonneg_right (hGM t ht) (hD0 t ht)
    rwa [intervalIntegral.integral_const_mul] at hmono
  rcases eq_or_lt_of_le hT0 with hT | hTpos
  · -- the whole needle carries no mass: then `∫ G·D = 0` and the claim is `0 ≤ ∫_{Z₃} D`
    have hzero : (∫ t in α..β, G t * D t) = 0 := by
      refine le_antisymm ?_ hGDnn
      rw [← hT] at hGD
      simpa using hGD
    rw [hzero, mul_zero]
    exact hT₃0
  · by_cases hhalf : (∫ t in Z₁, D t) ≤ (∫ t in α..β, D t) / 2
    · -- run `needle_iso` at the exact fraction of `Z₁`
      have hstar : (∫ t in Z₁, D t)
          = ((∫ t in Z₁, D t) / ∫ t in α..β, D t) * ∫ t in α..β, D t :=
        (div_mul_cancel₀ _ hTpos.ne').symm
      have hmain := needle_iso hαβ hD0 hlc hDint hGM hM0 hM3 hGDint hpart hm₁ hm₂ hm₃
        (div_nonneg hT₁0 hT0) (by rw [div_le_iff₀ hTpos]; linarith) hstar hcross
      have hAle : A ≤ (∫ t in Z₁, D t) / ∫ t in α..β, D t := by
        rw [le_div_iff₀ hTpos]; exact hmass₁
      exact le_trans (mul_le_mul_of_nonneg_right hAle hGDnn) hmain
    · -- otherwise `Z₂` is the small part; exchange the roles of `Z₁` and `Z₂`
      have hhalf' : (∫ t in α..β, D t) / 2 < ∫ t in Z₁, D t := not_le.mp hhalf
      have hhalf₂ : (∫ t in Z₂, D t) ≤ (∫ t in α..β, D t) / 2 := by linarith
      have hstar : (∫ t in Z₂, D t)
          = ((∫ t in Z₂, D t) / ∫ t in α..β, D t) * ∫ t in α..β, D t :=
        (div_mul_cancel₀ _ hTpos.ne').symm
      have hcross' : ∀ s ∈ Z₂, ∀ t ∈ Z₁,
          3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t) := by
        intro s hs t ht
        rw [min_comm, max_comm]
        exact hcross t ht s hs
      have hmain := needle_iso hαβ hD0 hlc hDint hGM hM0 hM3 hGDint hpart.symm hm₂ hm₁ hm₃
        (div_nonneg hT₂0 hT0) (by rw [div_le_iff₀ hTpos]; linarith) hstar hcross'
      have hAle : A ≤ (∫ t in Z₂, D t) / ∫ t in α..β, D t := by
        rw [le_div_iff₀ hTpos]; exact hmass₂
      exact le_trans (mul_le_mul_of_nonneg_right hAle hGDnn) hmain

/-- The three intervals of `Arlib.not_needle_iso_of_one_lower` really do partition `[0,1]`. -/
theorem counter_isPartition3 :
    IsPartition3 (Set.Icc (0 : ℝ) 1) (Set.Ico 0 (83 / 100)) (Set.Ioc (98 / 100) 1)
      (Set.Icc (83 / 100) (98 / 100)) := by
  refine ⟨Set.Subset.antisymm ?_ ?_, ?_, ?_, ?_⟩
  · rintro x ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;> constructor <;> linarith
  · rintro x ⟨h1, h2⟩
    rcases lt_or_ge x (83 / 100) with h | h
    · exact Or.inl (Or.inl ⟨h1, h⟩)
    rcases le_or_gt x (98 / 100) with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl (Or.inr ⟨h', h2⟩)
  · exact Set.disjoint_left.mpr fun x hx hx' => by
      have := hx.2; have := hx'.1; linarith
  · exact Set.disjoint_left.mpr fun x hx hx' => by
      have := hx.2; have := hx'.1; linarith
  · exact Set.disjoint_left.mpr fun x hx hx' => by
      have := hx.1; have := hx'.2; linarith

/-- **One lower bound is not enough: `Arlib.needle_iso_two_lower` is false without `hmass₂`.**

This is the negation, written out verbatim, of the statement obtained from
`Arlib.needle_iso_two_lower` by deleting the second mass hypothesis
`A · ∫_α^β D ≤ ∫_{Z₂} D`.  Since the witness has `G ≡ 1/3 ≥ 0`, it refutes *a fortiori* the
same statement without `hG0` — hence also `Arlib.needle_iso` with its mass *equality*
`∫_{Z₁} D = A·∫_α^β D` relaxed to the `≥`-half, which is the only half that any approximation
of `1_{T₁}` from below can deliver (see the module docstring).  The hypotheses `0 ≤ A` and
`A ≤ 1/2` of `Arlib.needle_iso` are kept, so the refutation is not an artefact of dropping
them.

**The witness.**  `α = 0`, `β = 1`, `D ≡ 1` (log-concave), `G ≡ 1/3`, `M = 1/3`, `A = 1/2`, and

    Z₁ = [0, 83/100),   Z₂ = (98/100, 1],   Z₃ = [83/100, 98/100].

The cross-ratio hypothesis holds with room to spare: for `s ∈ Z₁`, `t ∈ Z₂` one has `s < t`,
so the inequality reads `s·(1 − t) ≤ t − s`, and `s(1−t) < (83/100)(2/100) = 83/5000` while
`t − s > 15/100`.  The mass hypothesis holds: `A·∫D = 1/2 ≤ 83/100 = ∫_{Z₁} D`.  But the
conclusion fails: `A·∫ G·D = 1/6 > 15/100 = ∫_{Z₃} D`.

So the needle carrying most of its mass in `Z₁` and almost none in `Z₂` is admissible for the
one-sided hypothesis and defeats the conclusion.  This is exactly the configuration that the
*equality* `∫_{Z₁} D = A·∫_α^β D` excludes through its `≤`-half — the half that no lower
approximation of an indicator can produce. -/
theorem not_needle_iso_of_one_lower :
    ¬ ∀ (D G : ℝ → ℝ) (α β A M : ℝ), α ≤ β →
      (∀ t ∈ Set.Icc α β, 0 ≤ D t) → LogConcaveOn (Set.Icc α β) D →
      IntervalIntegrable D volume α β →
      (∀ t ∈ Set.Icc α β, 0 ≤ G t) → (∀ t ∈ Set.Icc α β, G t ≤ M) → 0 ≤ M → M ≤ 1 / 3 →
      IntervalIntegrable (fun t => G t * D t) volume α β →
      ∀ Z₁ Z₂ Z₃ : Set ℝ, IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃ →
      MeasurableSet Z₁ → MeasurableSet Z₂ → MeasurableSet Z₃ →
      0 ≤ A → A ≤ 1 / 2 →
      A * (∫ t in α..β, D t) ≤ (∫ t in Z₁, D t) →
      (∀ s ∈ Z₁, ∀ t ∈ Z₂,
        3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t)) →
      A * (∫ t in α..β, G t * D t) ≤ ∫ t in Z₃, D t := by
  intro H
  -- the three set integrals of the constant weight
  have hIco : (∫ _t in Set.Ico (0 : ℝ) (83 / 100), (1 : ℝ)) = 83 / 100 := by
    rw [setIntegral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def, Real.volume_Ico]
    norm_num
  have hIcc : (∫ _t in Set.Icc (83 / 100 : ℝ) (98 / 100), (1 : ℝ)) = 15 / 100 := by
    rw [setIntegral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def, Real.volume_Icc]
    norm_num
  have hcross : ∀ s ∈ Set.Ico (0 : ℝ) (83 / 100), ∀ t ∈ Set.Ioc (98 / 100 : ℝ) 1,
      3 * (1 / 3 : ℝ) * ((min s t - 0) * (1 - max s t))
        ≤ (1 - 0) * (max s t - min s t) := by
    rintro s ⟨hs1, hs2⟩ t ⟨ht1, ht2⟩
    have hst : s ≤ t := by linarith
    rw [min_eq_left hst, max_eq_right hst]
    nlinarith
  have hcon := H (fun _ => 1) (fun _ => 1 / 3) 0 1 (1 / 2) (1 / 3) zero_le_one
    (fun _ _ => zero_le_one) (logConcaveOn_const (convex_Icc 0 1) zero_le_one)
    intervalIntegrable_const (fun _ _ => by norm_num) (fun _ _ => le_rfl) (by norm_num) le_rfl
    (by simp)
    (Set.Ico 0 (83 / 100)) (Set.Ioc (98 / 100) 1) (Set.Icc (83 / 100) (98 / 100))
    counter_isPartition3 measurableSet_Ico measurableSet_Ioc measurableSet_Icc
    (by norm_num) le_rfl
    (by rw [intervalIntegral.integral_const, hIco]; norm_num) hcross
  rw [intervalIntegral.integral_const, hIcc] at hcon
  norm_num at hcon

end OneDim

/-! ### The same on a needle inside the body, and Theorem 2.1 from the two-sided binder -/

section Ambient

variable {n : ℕ}

/-- **`Arlib.needle_iso_of_chord` with the mass equality replaced by the two lower bounds.**

Every hypothesis except the mass one is verbatim that of `Arlib.needle_iso_of_chord`, and the
proof is that theorem's proof with its closing call to `Arlib.needle_iso` replaced by
`Arlib.needle_iso_two_lower`; the construction of the needle supremum `M` and of the
cross-ratio condition on the needle is untouched, because neither ever mentions the mass
hypothesis.  As there, `0 ≤ A` and `A ≤ 1/2` are not needed.

The copy is forced by the one-declaration-per-file discipline: nothing between the statement of
`Arlib.needle_iso_of_chord` and its final line can be reused as a lemma, because the
intermediate data (`M`, `Z₁`, `Z₂`, `Z₃`, `hcross`) is built inside its proof. -/
theorem needle_iso_of_chord_two_lower {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hdisj : Disjoint T₁ T₂)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3)
    {p e : EuclideanSpace ℝ (Fin n)} {α β : ℝ} (hαβ : α ≤ β)
    (hseg : ∀ r ∈ Set.Icc α β, needleMap p e r ∈ K)
    {D : ℝ → ℝ} (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hlc : LogConcaveOn (Set.Icc α β) D)
    (hDint : IntervalIntegrable D volume α β)
    (hGDint : IntervalIntegrable (fun t => h (needleMap p e t) * D t) volume α β)
    {A : ℝ}
    (hmass₁ : A * (∫ t in α..β, D t)
      ≤ ∫ t in needleMap p e ⁻¹' T₁ ∩ Set.Icc α β, D t)
    (hmass₂ : A * (∫ t in α..β, D t)
      ≤ ∫ t in needleMap p e ⁻¹' T₂ ∩ Set.Icc α β, D t) :
    A * (∫ t in α..β, h (needleMap p e t) * D t)
      ≤ ∫ t in needleMap p e ⁻¹' ((K \ T₁) \ T₂) ∩ Set.Icc α β, D t := by
  classical
  have hcont : Continuous (needleMap p e) := by
    show Continuous fun t : ℝ => p + t • e
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hmeas : Measurable (needleMap p e) := hcont.measurable
  set Z₁ := needleMap p e ⁻¹' T₁ ∩ Set.Icc α β with hZ₁def
  set Z₂ := needleMap p e ⁻¹' T₂ ∩ Set.Icc α β with hZ₂def
  set Z₃ := needleMap p e ⁻¹' ((K \ T₁) \ T₂) ∩ Set.Icc α β with hZ₃def
  have hm₁ : MeasurableSet Z₁ := (hT₁.preimage hmeas).inter measurableSet_Icc
  have hm₂ : MeasurableSet Z₂ := (hT₂.preimage hmeas).inter measurableSet_Icc
  -- the three parameter sets partition `[α, β]`
  have hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine Set.Subset.antisymm ?_ ?_
      · rintro r ((⟨-, hr⟩ | ⟨-, hr⟩) | ⟨-, hr⟩) <;> exact hr
      · intro r hr
        by_cases h1 : needleMap p e r ∈ T₁
        · exact Or.inl (Or.inl ⟨h1, hr⟩)
        by_cases h2 : needleMap p e r ∈ T₂
        · exact Or.inl (Or.inr ⟨h2, hr⟩)
        · exact Or.inr ⟨⟨⟨hseg r hr, h1⟩, h2⟩, hr⟩
    · exact Set.disjoint_left.mpr fun r hr₁ hr₂ =>
        Set.disjoint_left.mp hdisj hr₁.1 hr₂.1
    · exact Set.disjoint_left.mpr fun r hr₁ hr₃ => hr₃.1.1.2 hr₁.1
    · exact Set.disjoint_left.mpr fun r hr₂ hr₃ => hr₃.1.2 hr₂.1
  have hm₃ : MeasurableSet Z₃ := by
    have : Z₃ = Set.Icc α β \ (Z₁ ∪ Z₂) := by
      refine Set.Subset.antisymm (fun r hr => ⟨hr.2, ?_⟩) (fun r hr => ?_)
      · rintro (h1 | h2)
        exacts [hr.1.1.2 h1.1, hr.1.2 h2.1]
      · have hr3 : r ∈ Z₁ ∪ Z₂ ∪ Z₃ := by rw [hpart.union]; exact hr.1
        rcases hr3 with (h1 | h2) | h3
        exacts [absurd (Or.inl h1) hr.2, absurd (Or.inr h2) hr.2, h3]
    rw [this]
    exact measurableSet_Icc.diff (hm₁.union hm₂)
  -- the supremum of `h` along the needle
  set M := sSup ((fun r => h (needleMap p e r)) '' Set.Icc α β) with hMdef
  have hIccne : (Set.Icc α β).Nonempty := Set.nonempty_Icc.mpr hαβ
  have hbdd : BddAbove ((fun r => h (needleMap p e r)) '' Set.Icc α β) := by
    refine ⟨1 / 3, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact hh3 _ (hseg r hr)
  have hGM : ∀ r ∈ Set.Icc α β, h (needleMap p e r) ≤ M := fun r hr =>
    le_csSup hbdd ⟨r, hr, rfl⟩
  have hM3 : M ≤ 1 / 3 := by
    refine csSup_le (hIccne.image _) ?_
    rintro y ⟨r, hr, rfl⟩
    exact hh3 _ (hseg r hr)
  have hM0 : 0 ≤ M := le_trans (hh0 _) (hGM α ⟨le_rfl, hαβ⟩)
  -- the cross condition on the needle
  have hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂,
      3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t) := by
    intro s hs t ht
    have hsK : needleMap p e s ∈ K := hseg s hs.2
    have htK : needleMap p e t ∈ K := hseg t ht.2
    have hnee : needleMap p e s ≠ needleMap p e t := fun heq =>
      Set.disjoint_left.mp hdisj hs.1 (heq ▸ ht.1)
    have hst : s ≠ t := fun heq => hnee (by rw [heq])
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
      refine needle_crossRatio_transfer hKb hs.2.1 hlt ht.2.2
        (hseg α ⟨le_rfl, hαβ⟩) (hseg β ⟨hαβ, le_rfl⟩) hsK htK hnee ?_
      exact three_mul_sSup_le_crossRatioDist hchord hαβ hseg hs.1 ht.1 hst
    · rw [min_eq_right hgt.le, max_eq_left hgt.le]
      refine needle_crossRatio_transfer hKb ht.2.1 hgt hs.2.2
        (hseg α ⟨le_rfl, hαβ⟩) (hseg β ⟨hαβ, le_rfl⟩) htK hsK (Ne.symm hnee) ?_
      rw [crossRatioDist_comm hKb (Ne.symm hnee) htK hsK]
      exact three_mul_sSup_le_crossRatioDist hchord hαβ hseg hs.1 ht.1 hst
  exact needle_iso_two_lower hαβ hD0 hlc hDint (fun r _ => hh0 _) hGM hM0 hM3 hGDint hpart
    hm₁ hm₂ hm₃ hmass₁ hmass₂ hcross

/-- **Theorem 2.1 of Lovász–Vempala for the uniform density, from the two-sided localisation
binder.**

This is `Arlib.thm21_of_localization` with its binder `hloc` replaced by the binder `hloc₂`
below, whose needle conclusion asks for **two lower bounds**

    A·∫_α^β D ≤ ∫_{γ⁻¹T₁ ∩ [α,β]} D    and    A·∫_α^β D ≤ ∫_{γ⁻¹T₂ ∩ [α,β]} D

in place of the single equality `∫_{γ⁻¹T₁ ∩ [α,β]} D = A·∫_α^β D`, and whose ambient antecedent
is likewise two-sided.  `0 ≤ A` and `A ≤ 1/2` are no longer needed anywhere.

**The two ambient antecedents are exactly the `min` the consumer wants.**  At
`A = min(vol T₁, vol T₂)/vol K` both read as identities, and the conclusion becomes
`E(h)·min(vol T₁, vol T₂) ≤ vol((K∖T₁)∖T₂)` — the shape of the `hIso` binder of
`Arlib.MarkovChains.conductance_hitAndRun_ge`, without the `A ≤ 1/2` side condition that
`Arlib.thm21_of_localization` needs to get there.

**`hloc₂` is *not* weaker than `hloc`, and this file does not discharge it.**  See the module
docstring: `hloc` gives the `T₁` bound but not the `T₂` one, and `hloc₂` is *harder* for a
one-bisection chain, being three simultaneous constraints rather than two.  What
`Arlib.not_needle_iso_of_one_lower` establishes is that the `T₂` bound cannot simply be
dropped — so `hloc₂` is the sharp interface, not a convenience. -/
theorem thm21_of_localization_two_lower {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hdisj : Disjoint T₁ T₂)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3)
    {A : ℝ}
    (hmassK₁ : A * (volume K).toReal ≤ (volume T₁).toReal)
    (hmassK₂ : A * (volume K).toReal ≤ (volume T₂).toReal)
    (hloc₂ : A * (volume K).toReal ≤ (volume T₁).toReal →
      A * (volume K).toReal ≤ (volume T₂).toReal →
      (volume ((K \ T₁) \ T₂)).toReal < A * ∫ x in K, h x →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        IntervalIntegrable (fun t => h (needleMap p e t) * D t) volume α β ∧
        A * (∫ t in α..β, D t) ≤ (∫ t in needleMap p e ⁻¹' T₁ ∩ Set.Icc α β, D t) ∧
        A * (∫ t in α..β, D t) ≤ (∫ t in needleMap p e ⁻¹' T₂ ∩ Set.Icc α β, D t) ∧
        (∫ t in needleMap p e ⁻¹' ((K \ T₁) \ T₂) ∩ Set.Icc α β, D t)
          < A * ∫ t in α..β, h (needleMap p e t) * D t) :
    A * (∫ x in K, h x) ≤ (volume ((K \ T₁) \ T₂)).toReal := by
  by_contra hcon
  obtain ⟨p, e, α, β, D, hαβ, hseg, hD0, hlc, hDint, hGDint, hmass₁, hmass₂, hstrict⟩ :=
    hloc₂ hmassK₁ hmassK₂ (not_le.mp hcon)
  exact absurd (needle_iso_of_chord_two_lower hKb hT₁ hT₂ hdisj hh0 hh3 hchord hαβ hseg hD0 hlc
    hDint hGDint hmass₁ hmass₂) (not_le.mpr hstrict)

end Ambient

/-! ### Axiom audit -/

section AxiomCheck

#print axioms Arlib.needle_iso_two_lower
#print axioms Arlib.counter_isPartition3
#print axioms Arlib.not_needle_iso_of_one_lower
#print axioms Arlib.needle_iso_of_chord_two_lower
#print axioms Arlib.thm21_of_localization_two_lower

end AxiomCheck

end Arlib

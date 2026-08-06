/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Rounding.Hoeffding
import Ttc.Model.Prelude

/-!
# `claim:cl` (a), (b), (c) over an abstract rounding kernel

`Ttc.Rounding.Hoeffding` proves the *quantitative* content of `claim:cl` — the tail
bound `Pr[A·Y ≥ κ‖A‖] ≤ exp(−κ²/2)`, its value `η/(4r)` at the paper's `κ`, and
the union bound over the `r` facets. What it does not do is get from there to the
three statements the paper actually uses. This file does that.

## The model

The paper says only "let `rnd` be the randomized rounding process **as defined in**
`KV97`", so there is no construction to transcribe. We therefore work with the
object the proof actually manipulates: the **kernel density**

  `k p x  =  Pr[rnd p = x]`,

bundled with the properties the proof uses — it is nonnegative, it vanishes off a
region `supp x` around `x` (the paper's side-2 cube `C(x)`, since the displacement
`Y = p − rnd p` lies in `[−1,1]ⁿ`), and it is **normalised in `p`**:

  `∫_{ℝⁿ} k p x dp = 1`   (`Ttc.RoundingKernel.normalised`).

That last one is the substantive property. It is *not* the trivial
`∑ₓ k p x = 1`; it says the kernel is doubly stochastic, integrating to `1` in the
`p` variable for each fixed lattice point `x`. Independent coordinatewise rounding
(`xₖ = ⌊pₖ⌋ + Bernoulli(pₖ − ⌊pₖ⌋)`) has it — per coordinate,
`∫_{x−1}^{x+1} = ½ + ½ = 1` — but it is a property of the construction, not a
generic fact, which is why it is a field here.

`Ttc.roundProb K S x` is the paper's `Pr[rnd p = x]` for `p` drawn uniformly from
`S`, namely `(1/vol S)·∫_{S} k p x dp`.

## What is proved, and what is still assumed

Proved from the fields alone: `claim:cl`(a) (`Ttc.claim_cl_a`), (b)
(`Ttc.claim_cl_b`) and (c) (`Ttc.claim_cl_c`), in the paper's form.

Still assumed: (a) takes the **escape mass** `∫_{C(x) ∖ S} k p x dp ≤ e` as a
hypothesis, with `e = η/4`. That number is exactly what
`Ttc.rounding_union_bound` bounds — a point `p ∈ C(x) ∖ Q'` violates some inflated
facet, so `A_ij·Y ≥ κ‖A_ij‖` there, and the union bound over the `r` facets gives
`η/4`. Making that a proof needs the displacement law under `k(·, x)` identified
with the `Y` of `Ttc.rounding_tail_bound` (independent, mean-zero, `[−1,1]`-valued),
which is the one remaining measure-theoretic step. The residual assumption is now
a single explicit integral inequality whose bound is separately proved, rather
than the whole reduction.
-/

namespace Ttc

open MeasureTheory Set

variable {n : ℕ}

/-- **The randomized rounding, as the kernel its analysis uses.** `k p x` is
`Pr[rnd p = x]`; `supp x` is the region off which it vanishes (the paper's `C(x)`).
See the module docstring for why `normalised` is the substantive field. -/
structure RoundingKernel (n : ℕ) where
  /-- `k p x = Pr[rnd p = x]`. -/
  k : Space n → Space n → ℝ
  /-- The region off which `k · x` vanishes — the paper's `C(x)`. -/
  supp : Space n → Set (Space n)
  /-- `supp x` is measurable. -/
  supp_meas : ∀ x, MeasurableSet (supp x)
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ p x, 0 ≤ k p x
  /-- `k · x` is integrable. -/
  integrable : ∀ x, Integrable (fun p => k p x)
  /-- `k p x = 0` for `p` outside `C(x)`: the displacement is bounded. -/
  vanishes : ∀ x, ∀ p ∉ supp x, k p x = 0
  /-- **Double stochasticity**: `∫ k p x dp = 1` for each lattice point `x`. -/
  normalised : ∀ x, ∫ p, k p x = 1

namespace RoundingKernel

variable (K : RoundingKernel n)

/-- `∫_{C(x)} k p x dp = 1`: the normalisation, localised to the support. -/
theorem integral_supp (x : Space n) : ∫ p in K.supp x, K.k p x = 1 := by
  have hzero : ∫ p in (K.supp x)ᶜ, K.k p x = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun p hp => K.vanishes x p hp
  have hadd := integral_add_compl (K.supp_meas x) (K.integrable x)
  rw [hzero, add_zero] at hadd
  rw [hadd, K.normalised x]

/-- The mass over any set is at most the total mass `1`. -/
theorem integral_le_one (S : Set (Space n)) (x : Space n) :
    ∫ p in S, K.k p x ≤ 1 := by
  have h : ∫ p in S, K.k p x ≤ ∫ p in Set.univ, K.k p x := by
    refine setIntegral_mono_set ((K.integrable x).integrableOn) ?_ ?_
    · filter_upwards with p using K.nonneg p x
    · exact (Set.subset_univ S).eventuallyLE
  rwa [setIntegral_univ, K.normalised x] at h

end RoundingKernel

/-- **`Pr[rnd p = x]` for `p` uniform on `S`** — the paper's
`(1/vol S)·∫_{S} Pr[rnd p = x] dp`. -/
noncomputable def roundProb (K : RoundingKernel n) (S : Set (Space n)) (x : Space n) : ℝ :=
  (∫ p in S, K.k p x) / (volume S).toReal

/-! ## The three parts of `claim:cl` -/

/-- **`claim:cl`(c).** For `p` uniform on `S`, `Pr[rnd p = x] ≤ 1/vol S` for every
lattice point `x`. Immediate from normalisation: the mass over `S` is at most the
total mass `1`. -/
theorem claim_cl_c (K : RoundingKernel n) (S : Set (Space n)) (x : Space n)
    (hS : 0 ≤ (volume S).toReal) :
    roundProb K S x ≤ 1 / (volume S).toReal := by
  unfold roundProb
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (K.integral_le_one S x) (inv_nonneg.2 hS)

/-- **`claim:cl`(a).** For `p` uniform on `S` and a lattice point `x`: if the mass
escaping `S` within `C(x)` is at most `e`, then `Pr[rnd p = x] ≥ (1−e)/vol S`.

This is the paper's chain `∫_{S} = ∫_{C(x)} − ∫_{C(x)∖S} = 1 − (escape) ≥ 1 − η/4`,
with `e = η/4` supplied by `Ttc.rounding_union_bound`. -/
theorem claim_cl_a (K : RoundingKernel n) {S : Set (Space n)} (hSmeas : MeasurableSet S)
    (x : Space n) {e : ℝ} (hS : 0 ≤ (volume S).toReal)
    (hesc : ∫ p in K.supp x \ S, K.k p x ≤ e) :
    (1 - e) / (volume S).toReal ≤ roundProb K S x := by
  have hsplit : (∫ p in K.supp x ∩ S, K.k p x) + ∫ p in K.supp x \ S, K.k p x
      = ∫ p in K.supp x, K.k p x :=
    integral_inter_add_sdiff hSmeas ((K.integrable x).integrableOn)
  rw [K.integral_supp x] at hsplit
  have hmono : ∫ p in K.supp x ∩ S, K.k p x ≤ ∫ p in S, K.k p x := by
    refine setIntegral_mono_set ((K.integrable x).integrableOn) ?_ ?_
    · filter_upwards with p using K.nonneg p x
    · exact Set.inter_subset_right.eventuallyLE
  have hge : 1 - e ≤ ∫ p in S, K.k p x := by linarith
  unfold roundProb
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hge (inv_nonneg.2 hS)

/-- **`claim:cl`(b).** If at every `p ∈ S` the rounding lands in `Q` with
probability at least `1 − e`, then so does a uniform draw from `S`. This is the
paper's `Pr[rnd p ∈ Q] ≥ ∫_{Q''} (1−η/4)/vol Q'' dp ≥ 1 − η/4` — an averaging
step, which is why it needs nothing from the kernel. -/
theorem claim_cl_b {S : Set (Space n)} {g : Space n → ℝ} {e : ℝ}
    (hSmeas : MeasurableSet S) (hg_int : IntegrableOn g S) (hg : ∀ p ∈ S, 1 - e ≤ g p)
    (hS : 0 < (volume S).toReal) (hSfin : volume S ≠ ⊤) :
    1 - e ≤ (∫ p in S, g p) / (volume S).toReal := by
  have hconst : ∫ _p in S, (1 - e) = (volume S).toReal * (1 - e) := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def]
  have hmono : ∫ _p in S, (1 - e) ≤ ∫ p in S, g p :=
    setIntegral_mono_on (integrableOn_const hSfin) hg_int hSmeas hg
  rw [hconst] at hmono
  rw [le_div_iff₀ hS]
  linarith

/-! ## The escape bound, reduced to the tail bound

`Ttc.claim_cl_a` takes the escape mass `∫_{C(x)∖S} k p x dp ≤ e` as a hypothesis.
This section discharges it from two inputs that are *not* about integrals:

* a **geometric covering** — a point of `C(x) ∖ Q'` violates some inflated facet,
  so it lies in one of finitely many "bad" sets;
* the **per-facet tail bound** under the displacement law, which is what
  `Ttc.rounding_tail_bound_kappa` provides.

The bridge is `Ttc.RoundingKernel.dispLaw`: the law of `p` with density `k(·,x)`.
It is a probability measure precisely because of the `normalised` field.
-/

/-- **The displacement law at `x`**: `p` distributed with density `k(·, x)`. The
`normalised` field makes this a probability measure
(`Ttc.RoundingKernel.isProbabilityMeasure_dispLaw`). -/
noncomputable def RoundingKernel.dispLaw (K : RoundingKernel n) (x : Space n) :
    Measure (Space n) :=
  volume.withDensity (fun p => ENNReal.ofReal (K.k p x))

namespace RoundingKernel

variable (K : RoundingKernel n)

/-- The law's mass on a measurable set is the integral of the density there. -/
theorem dispLaw_apply (x : Space n) {T : Set (Space n)} (hT : MeasurableSet T) :
    K.dispLaw x T = ENNReal.ofReal (∫ p in T, K.k p x) := by
  rw [dispLaw, withDensity_apply _ hT,
    ofReal_integral_eq_lintegral_ofReal ((K.integrable x).integrableOn)
      (Filter.Eventually.of_forall fun p => K.nonneg p x)]

instance isProbabilityMeasure_dispLaw (x : Space n) :
    IsProbabilityMeasure (K.dispLaw x) := by
  constructor
  rw [K.dispLaw_apply x MeasurableSet.univ, setIntegral_univ, K.normalised x,
    ENNReal.ofReal_one]

/-- The escape mass, as the law's mass on the escaping set. -/
theorem integral_eq_measureReal (x : Space n) {T : Set (Space n)} (hT : MeasurableSet T) :
    ∫ p in T, K.k p x = (K.dispLaw x).real T := by
  rw [Measure.real, K.dispLaw_apply x hT,
    ENNReal.toReal_ofReal (setIntegral_nonneg hT fun p _ => K.nonneg p x)]

end RoundingKernel

/-- **The escape bound, from a covering plus per-facet tail bounds.**

If every point escaping `S` inside `C(x)` lies in one of the finitely many sets
`bad j`, and the displacement law gives each `bad j` mass at most `η/(4r)`, then
the escape mass is at most `η/4` — the hypothesis `hesc` of `Ttc.claim_cl_a`.

The covering is the paper's step "for `x ∈ Q` and `p ∈ C(x) ∖ Q'` we have
`A_ij Y ≥ κ‖A_ij‖`"; the per-facet bound is `Ttc.rounding_tail_bound_kappa`; the
sum is `Ttc.rounding_union_bound`. -/
theorem escape_of_cover {K : RoundingKernel n} {x : Space n} {S : Set (Space n)}
    {ι : Type*} (T : Finset ι) (bad : ι → Set (Space n))
    (hSmeas : MeasurableSet S)
    (hcover : K.supp x \ S ⊆ ⋃ j ∈ T, bad j)
    {e : ℝ}
    (htail : ∑ j ∈ T, (K.dispLaw x).real (bad j) ≤ e) :
    ∫ p in K.supp x \ S, K.k p x ≤ e := by
  have hmeasT : MeasurableSet (K.supp x \ S) := (K.supp_meas x).diff hSmeas
  rw [K.integral_eq_measureReal x hmeasT]
  calc (K.dispLaw x).real (K.supp x \ S)
      ≤ (K.dispLaw x).real (⋃ j ∈ T, bad j) :=
        measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ j ∈ T, (K.dispLaw x).real (bad j) := measureReal_biUnion_finset_le _ _
    _ ≤ e := htail

/-! ## Non-vacuity

`Ttc.RoundingKernel` bundles four conditions; if nothing satisfied them the three
theorems above would be vacuous. The uniform density on a unit ball does, so the
conditions are consistent.

This is a *satisfiability* witness only. It is not a rounding — it does not send
points to a lattice — and in particular it says nothing about whether the escape
bound of `Ttc.claim_cl_a` is achievable. Its job is to rule out the structure
being empty. -/
noncomputable def uniformKernel (n : ℕ) : RoundingKernel n where
  k := fun p x =>
    (Metric.closedBall x 1).indicator
      (fun _ => ((volume (Metric.closedBall x 1)).toReal)⁻¹) p
  supp := fun x => Metric.closedBall x 1
  supp_meas := fun _ => measurableSet_closedBall
  nonneg := by
    intro p x
    refine Set.indicator_nonneg (fun _ _ => ?_) p
    exact inv_nonneg.2 ENNReal.toReal_nonneg
  integrable := by
    intro x
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    exact integrableOn_const (IsCompact.measure_lt_top (isCompact_closedBall x 1)).ne
  vanishes := fun x p hp => Set.indicator_of_notMem hp _
  normalised := by
    intro x
    have hpos : 0 < volume (Metric.closedBall x (1 : ℝ)) :=
      Metric.measure_closedBall_pos volume x one_pos
    have htop : volume (Metric.closedBall x (1 : ℝ)) ≠ ⊤ :=
      (IsCompact.measure_lt_top (isCompact_closedBall x 1)).ne
    have hne : (volume (Metric.closedBall x (1 : ℝ))).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨hpos.ne', htop⟩
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul,
      measureReal_def, mul_inv_cancel₀ hne]

end Ttc

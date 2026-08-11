/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Sampler.Construct
import Ttc.Sampler.HitAndRunTheorem11

/-!
# `Sampler/ConstructHitAndRun`: a `Ttc.KV97Sampler` driven by hit-and-run

`Ttc/Sampler/Construct.lean` builds a `Ttc.KV97Sampler` whose continuous draw is the
**lazy ball walk**.  That construction's `law_tv` is a *theorem*
(`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`), and it stays exactly where it
is: this file is **additive**.  Nothing here deletes, rewrites, or rewires
`Ttc.kv97SamplerOfBallWalk`, which remains the development's unconditional instantiation
and its non-vacuity witness.

What this file adds is a *second* `Ttc.KV97Sampler`, on the same interface, whose
continuous draw is the **hit-and-run walk** of Lovász–Vempala, *Hit-and-Run from a Corner*
(2005).  The trade it makes is stated in full in `Ttc.kv97SamplerOfHitAndRun`'s docstring
and summarised here.

## The cost, quoted with the guarantee (`AUDIT.md` check 5)

| construction | steps | proved? |
| --- | --- | --- |
| `Ttc.kv97SamplerOfBallWalk` | `Ttc.mixSteps …` = `2^Θ(n) · log(M·Vol(P')/ε')` | `law_tv` is a **theorem** |
| `Ttc.kv97SamplerOfHitAndRun` | `Ttc.hitAndRunTheorem11Steps n r R M eps` = `⌊10^10·n²·R²/r²·log(M/eps)⌋₊ + 1` | `law_tv` is discharged from an **assumed** `Ttc.HitAndRunTheorem11Input` |

The ball walk's step count is **exponential in the dimension**: the local-conductance floor
it uses is `(γ/(γ+D))ⁿ` and the isoperimetric constant behind it is `2⁻ⁿ/D`, so
`Ttc.mixSteps` is `2^{Θ(n)}·log(…)`.  Hit-and-run's is **polynomial in `n`** — that is the
entire point of this file.  Three qualifications, none of which may be dropped when the
number is quoted:

* the constant is `10^10`, so the bound is useless for any concrete small instance;
* the dependence is `R²/r²`, the squared ratio of a circumscribed to an inscribed ball
  radius.  That is `O(n)` for a body in isotropic position and `O(n²)`-ish after a
  rounding preprocess, but it is **unbounded** for a general body: for a badly-shaped `P'`
  the "polynomial" bound is polynomial in `n` and arbitrarily large in the geometry.  The
  bound is only small for a **well-rounded** body, and this file assumes rather than
  achieves well-roundedness (`rin`/`Rout` are binders);
* it counts *transitions*, not arithmetic operations.  Sampling a direction and finding a
  chord endpoint is not a unit-cost step.

## The constant `10^10` in the contract is known to be too small

This is a defect of the contract this file consumes, recorded here so that no reader takes
the table above as a validated step count.

`Ttc.hitAndRunTheorem11Threshold` (`Ttc/Sampler/HitAndRunTheorem11.lean:35`) transcribes
the `10^10 n² (R²/r²) log(M/ε)` printed in Theorem 1.1 of the paper.  The mixing
formalisation in `Arlib/MarkovChains/Continuous/HitAndRunMixing.lean` shows that this
constant **does not follow from the paper's own Theorem 4.2**: that theorem gives
conductance `Φ ≥ 1/(2²⁴ n D)` at inradius `1`; rescaling to inradius `r` with `D ≤ 2R`
gives `Φ ≥ r/(2²⁵ n R)`; and the Lovász–Simonovits decay lemma then needs
`m ≳ (2/Φ²)·ln(√M/ε) = 2⁵¹ n² (R²/r²) ln(…)`, with `2⁵¹ ≈ 2.25·10¹⁵` — about `2·10⁵`
times larger than the printed `10^10`.  The theorem is true with a larger constant; only
the printed one is wrong, and the paper's §5 never performs this arithmetic, so the error
is invisible in its text.  The **proved** shape is
`Arlib.MarkovChains.lvThreshold n r R M eps = 2⁵⁶ · n² · (R²/r²) · log(8M/ε²)`, via
`Arlib.MarkovChains.tvLe_iterate_hitAndRun`.

**Nothing in this file depends on the shape of the threshold.**  Every declaration below
consumes `Ttc.HitAndRunTheorem11Input.at_steps` as a black box, and
`Ttc.hitAndRunTheorem11Steps` occurs only as an opaque `ℕ` argument to
`Arlib.MarkovChains.iterate`.  Replacing `Ttc.hitAndRunTheorem11Threshold` by
`Arlib.MarkovChains.lvThreshold` — changing `log(M/eps)` to `log(8M/ε²)` and `10^10` to
`2⁵⁶` — would leave every statement and every proof here unchanged.

## What is proved and what is assumed

*Proved here.*  That the hit-and-run law, run for `Ttc.hitAndRunTheorem11Steps` steps from
the supplied start, satisfies **every** field of `Ttc.KV97Sampler` once the contract `H`
is supplied: the fourteen descriptive fields exactly as in
`Ttc.kv97SamplerOfBallWalk`, and `law_tv` by `Ttc.HitAndRunTheorem11Input.at_steps`
instantiated at `K = P'ᵢ` and `eps = ε'/(4·Vol(P'ᵢ))`.  The two shapes agree on the nose:
`at_steps`'s conclusion *is* `law_tv`'s statement under that substitution, so the
discharge is a direct application, not an approximation.

*Assumed.*  `H : Ttc.HitAndRunTheorem11Input` — the analytic content of Theorem 1.1
itself.  **This is a real regression in what is proved relative to the ball walk**, whose
`law_tv` needs no such input.  The exchange is: a conditional accuracy guarantee, for a
step count that is polynomial rather than exponential in `n`.  A reader comparing the two
constructions must weigh exactly that.  `Ttc.HitAndRunTheorem11Input` is *not* inhabited
anywhere in this development, and this file does not pretend otherwise; see the
non-vacuity section.

## The trap this file also had to avoid

`Ttc/Sampler/Construct.lean` (module docstring, "Non-vacuity") records that the cheap way
to discharge `law_tv` is to take `contLaw i` to *be* `Arlib.uniformOn volume P'ᵢ`,
whereupon `law_tv` is `Arlib.TVLe.refl`.  That is the disguised-oracle failure of
`CLAUDE.md` §11 and it is **not** what happens here:
`Ttc.kv97HitAndRunContLaw_eq_iterate` exhibits `contLaw` as an iterate of the hit-and-run
kernel, and the target measure occurs nowhere in the construction.

## Non-vacuity (`CLAUDE.md` §11)

`Ttc.exists_hitAndRun_binders_box` exhibits a **fully concrete** instance — the box
`{x | ∀ i, |xᵢ| ≤ 1}` and its Kannan–Vempala inflation — of every binder this file adds:
the inscribed and circumscribed closed balls, the warm start with its exceptional set, the
warmness parameter, and the `eps ≤ 1` side condition.  It is stated **conditionally on
`H`**, and it carries the same non-degeneracy conjuncts the ball-walk witness does: the
tolerance is `≤ 1/2` (so `law_tv` is not the vacuous `≥ 1` bound), the law is an `iterate`
of the hit-and-run kernel, and the start is proved **different from the target**.

What it does **not** do is inhabit `Ttc.HitAndRunTheorem11Input`.  That structure is
Lovász–Vempala Theorem 1.1; inhabiting it means proving the paper's
weighted-isoperimetry/localisation argument, which this development does not do (and which,
as recorded above, is false at the printed constant).  So the witness certifies exactly
this: *given the contract, the remaining hypotheses of this construction are simultaneously
satisfiable at non-degenerate parameters* — and nothing more.

## Main results

* `Ttc.kv97HitAndRunContLaw` — the continuous law: an iterate of the hit-and-run kernel.
* `Ttc.kv97HitAndRunContLaw_eq_iterate` — the anti-trap lemma.
* `Ttc.toReal_volume_inflated_pos_of_closedBalls` — `0 < Vol(P') < ∞` from the two balls.
* `Ttc.tvLe_hitAndRunLaw_inflated` — the quantitative core, from `H`.
* `Ttc.kv97SamplerOfHitAndRun` — **the `KV97Sampler` term**.
* `Ttc.exists_hitAndRun_binders_box` — non-degenerate inhabitation of the added binders.
-/

namespace Ttc

open MeasureTheory Pointwise
open scoped ENNReal

/-! ## The chain

`Ttc.mixSteps`/`Ttc.ballWalkLaw` have no analogue to define here:
`Ttc.hitAndRunTheorem11Steps` is already the step count, and the law is a bare
`Arlib.MarkovChains.iterate`. -/

/-- **The sampler's continuous law, hit-and-run version.**  For each cube `i`, the law of
the hit-and-run walk on the inflated dilated polytope `P'ᵢ`, run from the start `sigma i`
for `Ttc.hitAndRunTheorem11Steps` steps at tolerance `ε'/(4·Vol(P'ᵢ))`.

`rin i`, `Rout i` are the inscribed/circumscribed radii and `Mw i` the warmness of the
start; they enter only through the step count.  Nothing about the target measure appears
here — compare `Ttc.kv97ContLaw`, which this mirrors. -/
noncomputable def kv97HitAndRunContLaw {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n)) :
    {c : Cube A // c ∈ D} → Measure (Space n) := fun i =>
  Arlib.MarkovChains.iterate
    (Arlib.MarkovChains.hitAndRun
      (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf))
    (sigma i)
    (hitAndRunTheorem11Steps n (rin i) (Rout i) (Mw i)
      (epsPrime / (4 *
        (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)).toReal)))

/-- **`contLaw` is a chain iterate, spelled out.**  The anti-trap lemma of
`Ttc/Sampler/Construct.lean`, for the hit-and-run construction: the law is
`iterate (hitAndRun P'ᵢ) (sigma i) t`, so a reader can see the target measure does not
occur in it. -/
theorem kv97HitAndRunContLaw_eq_iterate {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (i : {c : Cube A // c ∈ D}) :
    kv97HitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma i
      = Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.hitAndRun
            (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf))
          (sigma i)
          (hitAndRunTheorem11Steps n (rin i) (Rout i) (Mw i)
            (epsPrime / (4 *
              (volume (Arlib.KV97.inflated (Am i) (bv i)
                (Arlib.KV97.cOf epsPrime) rf)).toReal))) := rfl

/-- The output law is a probability measure: hit-and-run is a Markov kernel for *every*
`K` (`Arlib.MarkovChains.isMarkovKernel_hitAndRun`), so no measurability side condition is
needed here. -/
instance isProbabilityMeasure_kv97HitAndRunContLaw {A : Type*} {n : ℕ} {D : DNF A}
    {Jt : Type} (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (i : {c : Cube A // c ∈ D}) [IsProbabilityMeasure (sigma i)] :
    IsProbabilityMeasure (kv97HitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma i) :=
  Arlib.MarkovChains.isProbabilityMeasure_iterate _ _ _

/-! ## Guards on the volume of `P'`

`Ttc/Sampler/Construct.lean` derives `0 < Vol(P') < ∞` from an *open* inscribed ball and a
diameter bound.  The hit-and-run contract supplies *closed* inscribed and circumscribed
balls instead, which give the same two facts more directly. -/

/-- `0 < Vol(P').toReal`, i.e. the two side conditions `Vol(P') ∉ {0, ∞}` that
`Ttc.KV97Sampler.contVol_pos` asks for, from the inscribed and circumscribed balls the
hit-and-run contract already needs. -/
theorem toReal_volume_inflated_pos_of_closedBalls {n : ℕ} {ι : Type*} {Am : ι → Space n}
    {bv : ι → ℝ} {cc rf : ℝ} {zin zout : Space n} {rin Rout : ℝ} (hr : 0 < rin)
    (hin : Metric.closedBall zin rin ⊆ Arlib.KV97.inflated Am bv cc rf)
    (hout : Arlib.KV97.inflated Am bv cc rf ⊆ Metric.closedBall zout Rout) :
    0 < (volume (Arlib.KV97.inflated Am bv cc rf)).toReal :=
  ENNReal.toReal_pos
    (Arlib.MarkovChains.volume_ne_zero_of_ball_subset hr
      (Metric.ball_subset_closedBall.trans hin))
    ((measure_mono hout).trans_lt measure_closedBall_lt_top).ne

/-! ## The quantitative core -/

/-- **The `Ttc.hitAndRunTheorem11Steps`-step law of hit-and-run on the Kannan–Vempala
inflated polytope is within `eps` of uniform on it, in total variation** — *given the
Theorem 1.1 contract `H`*.

This is `Ttc.HitAndRunTheorem11Input.at_steps` restated for `Arlib.KV97.inflated`, with the
body's measurability, convexity and closedness discharged from
`Arlib.KV97.measurableSet_inflated`, `Arlib.KV97.convex_inflated`,
`Arlib.KV97.isClosed_inflated`.  Those three are the only side conditions of `at_steps`
that this file can prove; the geometry (`hin`, `hout`) and the warm start
(`sigma`, `Mw`, `S`) remain hypotheses, exactly as they are in the contract.

This is the whole content of `Ttc.KV97Sampler.law_tv` for the hit-and-run construction —
the analogue of `Ttc.tvLe_ballWalkLaw_inflated`, with the crucial difference that that one
is unconditional and this one consumes `H`. -/
theorem tvLe_hitAndRunLaw_inflated (H : HitAndRunTheorem11Input) {n : ℕ} {ι : Type*}
    (hn : 1 ≤ n) (Am : ι → Space n) (bv : ι → ℝ) (cc rf : ℝ)
    {zin zout : Space n} {rin Rout : ℝ} (hr : 0 < rin) (hR : 0 ≤ Rout)
    (hin : Metric.closedBall zin rin ⊆ Arlib.KV97.inflated Am bv cc rf)
    (hout : Arlib.KV97.inflated Am bv cc rf ⊆ Metric.closedBall zout Rout)
    {sigma : Measure (Space n)} [IsProbabilityMeasure sigma]
    {Mw eps : ℝ} (hM : 1 ≤ Mw) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (Space n)} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ T, MeasurableSet T → sigma (T \ S) ≤ ENNReal.ofReal Mw *
      Arlib.uniformOn volume (Arlib.KV97.inflated Am bv cc rf) (T \ S)) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.hitAndRun (Arlib.KV97.inflated Am bv cc rf)) sigma
        (hitAndRunTheorem11Steps n rin Rout Mw eps))
      (Arlib.uniformOn volume (Arlib.KV97.inflated Am bv cc rf)) (ENNReal.ofReal eps) :=
  H.at_steps hn (Arlib.KV97.measurableSet_inflated _ _ _ _)
    (Arlib.KV97.convex_inflated _ _ _ _) (Arlib.KV97.isClosed_inflated _ _ _ _)
    hr hR hin hout hM heps0 heps1 hSm hS hdom

/-! ## The `KV97Sampler` term -/

/-- **A `Ttc.KV97Sampler` whose continuous draw is the hit-and-run walk.**

Fourteen fields are descriptive and are supplied exactly as in
`Ttc.kv97SamplerOfBallWalk`: the caller's linear description of the dilated polytopes
(`Am`, `bv`, `hdil`, `rf`, `hr1`, `hcard`), the construction `contLaw =
Ttc.kv97HitAndRunContLaw`, `contVol = Vol(P')`, `sampD = Ttc.kv97SampD`.  The fifteenth,
`law_tv`, is `Ttc.tvLe_hitAndRunLaw_inflated` at `eps = ε'/(4·Vol(P'ᵢ))`.

## The cost, and the regression, in one breath

The chain is run for

    Ttc.hitAndRunTheorem11Steps n (rin i) (Rout i) (Mw i) (ε'/(4·Vol(P'ᵢ)))
      = ⌊10^10 · n² · Rout i ² / rin i ² · log (Mw i / (ε'/(4·Vol(P'ᵢ))))⌋₊ + 1

steps — **polynomial in the dimension `n`**, where `Ttc.kv97SamplerOfBallWalk` needs
`Ttc.mixSteps …` = `2^Θ(n)·log(…)`, **exponential** in `n`.  Replacing an exponential step
count by a polynomial one is the entire purpose of this definition.

Three things must be said in the same breath as that number:

1. the constant is `10^10`, and it is **known to be too small**: the paper's own
   Theorem 4.2 yields only `2^51 ≈ 2.25·10^15` (module docstring).  So the step count
   quoted above is not a validated bound; the proved shape is
   `Arlib.MarkovChains.lvThreshold`.  Nothing here depends on which of the two is used.
2. `Rout i ²/rin i ²` is the squared ratio of a circumscribed to an inscribed ball radius.
   It is small only for a **well-rounded** body.  `rin`/`Rout` are binders of this
   definition: well-roundedness is assumed, not achieved.
3. **`law_tv` here is discharged from an assumed `H : Ttc.HitAndRunTheorem11Input`,
   whereas `Ttc.kv97SamplerOfBallWalk`'s `law_tv` is a theorem**
   (`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`, unconditional).  That is a
   genuine regression in what is *proved*, and it is the price of the polynomial step
   count.  This definition is additive: the ball-walk construction is untouched and
   remains the development's unconditional instantiation.

## The open hypotheses

Beyond `H`, and beyond the linear description that `Ttc.kv97SamplerOfBallWalk` also takes:

* `hrin`, `hin` — an inscribed **closed** ball `B̄(zin i, rin i) ⊆ P'ᵢ`, with `0 < rin i`;
* `hRout`, `hout` — a circumscribed **closed** ball `P'ᵢ ⊆ B̄(zout i, Rout i)`,
  `0 ≤ Rout i`;
* `heps1` — the tolerance `ε'/(4·Vol(P'ᵢ))` is at most `1`.  This is *not* derivable from
  the interface: `Ttc.KV97Sampler` bounds neither `ε'` above nor `Vol(P')` below, so a
  large `ε'` on a thin body would violate it.  It is a real binder;
* `sigma`, `hsigma`, `Mw`, `hM`, `Sx`, `hSm`, `hS`, `hdom` — the warm start, in the
  contract's own exceptional-set form: off a measurable `Sx i` of `sigma i`-mass at most
  `eps/2`, the start is dominated by `Mw i` times uniform on `P'ᵢ`.

None of these is an assumption *about the sampler's accuracy* — they are properties of the
body it runs on and of the start it is handed, and
`Ttc.HitAndRunTheorem11Input.mixing` carries exactly the same ones.
`Ttc.exists_hitAndRun_binders_box` discharges all of them for a concrete body. -/
noncomputable def kv97SamplerOfHitAndRun
    {A : Type*} {n : ℕ} {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ} {epsPrime : ℝ}
    (H : HitAndRunTheorem11Input) (hn : 1 ≤ n) (hEps : 0 < epsPrime)
    (Jt : Type) [Fintype Jt]
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (hdil : ∀ i, latticeScale ρ • region M i.val ⊆ Arlib.Polytope.body (Am i) (bv i))
    (rf : ℝ) (hr1 : 1 ≤ rf) (hcard : (Fintype.card Jt : ℝ) ≤ rf)
    (zin : {c : Cube A // c ∈ D} → Space n) (rin : {c : Cube A // c ∈ D} → ℝ)
    (hrin : ∀ i, 0 < rin i)
    (hin : ∀ i, Metric.closedBall (zin i) (rin i) ⊆
      Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)
    (zout : {c : Cube A // c ∈ D} → Space n) (Rout : {c : Cube A // c ∈ D} → ℝ)
    (hRout : ∀ i, 0 ≤ Rout i)
    (hout : ∀ i, Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf ⊆
      Metric.closedBall (zout i) (Rout i))
    (heps1 : ∀ i, epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)).toReal) ≤ 1)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (Mw : {c : Cube A // c ∈ D} → ℝ) (hM : ∀ i, 1 ≤ Mw i)
    (Sx : {c : Cube A // c ∈ D} → Set (Space n)) (hSm : ∀ i, MeasurableSet (Sx i))
    (hS : ∀ i, sigma i (Sx i) ≤ ENNReal.ofReal
      (epsPrime / (4 *
        (volume (Arlib.KV97.inflated (Am i) (bv i)
          (Arlib.KV97.cOf epsPrime) rf)).toReal) / 2))
    (hdom : ∀ i, ∀ T, MeasurableSet T →
      sigma i (T \ Sx i) ≤ ENNReal.ofReal (Mw i) *
        Arlib.uniformOn volume
          (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf) (T \ Sx i)) :
    KV97Sampler A n M D ρ epsPrime
      (kv97SampD M D ρ (kv97HitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma)) where
  J := Jt
  fintypeJ := inferInstance
  Amat := Am
  bvec := bv
  dilate_eq := hdil
  facetBound := rf
  one_le_facetBound := hr1
  card_le_facetBound := hcard
  contLaw := kv97HitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma
  isProbContLaw := by
    intro i
    haveI := hsigma i
    exact isProbabilityMeasure_kv97HitAndRunContLaw _ _ _ _ _ _ _ _ _
  contVol := fun i =>
    (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)).toReal
  contVol_pos := fun i =>
    toReal_volume_inflated_pos_of_closedBalls (hrin i) (hin i) (hout i)
  contVol_eq := fun _ => rfl
  law_tv := by
    intro i
    haveI := hsigma i
    have hpos : 0 < (volume
        (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)).toReal :=
      toReal_volume_inflated_pos_of_closedBalls (hrin i) (hin i) (hout i)
    exact tvLe_hitAndRunLaw_inflated H hn (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf
      (hrin i) (hRout i) (hin i) (hout i) (hM i)
      (div_pos hEps (by linarith)) (heps1 i) (hSm i) (hS i) (hdom i)
  sampD_eq := fun i x _ => kv97SampD_apply M ρ _ i x

/-! ## Two box facts the closed-ball binders need

`Ttc/Sampler/Construct.lean` proves the *open*-ball inclusion `ball_subset_boxInflate` and
the diameter bound `dist_le_of_mem_boxInflate`.  The hit-and-run contract wants closed
balls on both sides, so two small bridges are needed. -/

/-- A **closed** ball of radius at most the half-width sits inside the inflated box. -/
theorem closedBall_subset_boxInflate {n : ℕ} {B κ R : ℝ} (hR : R ≤ B + κ) :
    Metric.closedBall (0 : Space n) R ⊆
      Arlib.Polytope.inflate (boxNormals n) (fun _ => B) κ := by
  intro x hx
  have hxn : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  refine mem_boxInflate.2 fun i => ?_
  have hle := PiLp.norm_apply_le (p := 2) x i
  rw [Real.norm_eq_abs] at hle
  linarith

/-- The centre is in the inflated box, so the diameter bound turns into a circumscribed
closed ball. -/
theorem zero_mem_boxInflate {n : ℕ} {B κ : ℝ} (h : 0 ≤ B + κ) :
    (0 : Space n) ∈ Arlib.Polytope.inflate (boxNormals n) (fun _ => B) κ :=
  mem_boxInflate.2 fun _ => by simpa using h

/-! ## Non-vacuity: every binder this file adds, at a concrete body

`CLAUDE.md` §11.  The construction above adds nine hypothesis groups to
`Ttc.kv97SamplerOfBallWalk`'s list — the two closed balls, the `eps ≤ 1` side condition,
and the exceptional-set warm start.  A capstone quantified over them certifies nothing
unless they are simultaneously satisfiable at parameters that are not degenerate.

`Ttc.exists_hitAndRun_binders_box` exhibits them all on the box `{x | ∀ i, |xᵢ| ≤ 1}` and
its Kannan–Vempala inflation, with the same three non-degeneracy conjuncts
`Ttc.exists_kv97Sampler_box` carries:

* `0 < ε'`;
* the tolerance is `≤ 1/2`, hence **not** the vacuous `≥ 1`, so `law_tv` really constrains
  the law;
* the law is an `iterate` of the *hit-and-run* kernel from a start proved **different from
  the target** `Arlib.uniformOn volume P'`.

**What this does not certify.**  It takes `H : Ttc.HitAndRunTheorem11Input` as a
hypothesis and does not construct one.  `H` is Lovász–Vempala Theorem 1.1 itself, which
this development does not prove — and which, at the constant printed in
`Ttc.hitAndRunTheorem11Threshold`, is **false** (module docstring).  So the honest reading
is: *conditional on the contract, the rest of this construction is inhabited
non-degenerately.*  It is not a proof that the contract is inhabited.  Compare
`Ttc.exists_kv97Sampler_box`, which is unconditional.

What is *not* claimed here, exactly as in `Ttc/Sampler/Construct.lean`: that the `t`-step
law itself differs from the target. -/
theorem exists_hitAndRun_binders_box (H : HitAndRunTheorem11Input) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (epsPrime : ℝ) (sampD : Cube Unit → Space n → ℝ)
      (S : KV97Sampler Unit n (fun _ => Metric.closedBall 0 (1 / 2))
        [[(⟨(), true⟩ : Lit Unit)]] 0 epsPrime sampD),
      0 < epsPrime ∧
      Nonempty {c : Cube Unit // c ∈ [[(⟨(), true⟩ : Lit Unit)]]} ∧
      ∀ i, ENNReal.ofReal (epsPrime / (4 * S.contVol i)) ≤ ENNReal.ofReal (1 / 2) ∧
        ∃ (sigma : Measure (Space n)) (t : ℕ),
          S.contLaw i = Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.hitAndRun
              (Arlib.KV97.inflated (S.Amat i) (S.bvec i) (Arlib.KV97.cOf epsPrime)
                S.facetBound)) sigma t ∧
          sigma ≠ Arlib.uniformOn volume
            (Arlib.KV97.inflated (S.Amat i) (S.bvec i) (Arlib.KV97.cOf epsPrime)
              S.facetBound) := by
  classical
  -- the inscribed unit ball, and its volume
  have hb0 : volume (Metric.ball (0 : Space n) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hbtop : volume (Metric.ball (0 : Space n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hv0 : 0 < (volume (Metric.ball (0 : Space n) 1)).toReal := ENNReal.toReal_pos hb0 hbtop
  -- the accuracy parameter: positive, at most `1/12`, and small compared to the volume
  set ep : ℝ := min (1 / 12) (2 * (volume (Metric.ball (0 : Space n) 1)).toReal) with hepdef
  have hep0 : 0 < ep := lt_min (by norm_num) (by linarith)
  have hep4 : ep < 4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  set rr : ℝ := max 1 (2 * (n : ℝ)) with hrrdef
  have hr1 : (1 : ℝ) ≤ rr := le_max_left _ _
  have hk0 : 0 < Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr := kappaOf_cOf_pos hep0 hep4
  -- the body: the `κ`-inflation of the box of half-width `1`
  set K : Set (Space n) :=
    Arlib.KV97.inflated (boxNormals n) (fun _ => (1 : ℝ)) (Arlib.KV97.cOf ep) rr with hKdef
  have hKmeas : MeasurableSet K := Arlib.KV97.measurableSet_inflated _ _ _ _
  have hball1 : Metric.ball (0 : Space n) 1 ⊆ K := ball_subset_boxInflate (by linarith)
  have hballBig : Metric.ball (0 : Space n)
      (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) ⊆ K := ball_subset_boxInflate le_rfl
  -- the inscribed *closed* ball, and the circumscribed *closed* ball
  have hin1 : Metric.closedBall (0 : Space n) 1 ⊆ K :=
    closedBall_subset_boxInflate (by linarith)
  have hDK : ∀ x ∈ K, ∀ y ∈ K,
      dist x y ≤ 2 * (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) * Real.sqrt n :=
    dist_le_of_mem_boxInflate (by linarith)
  have hzero : (0 : Space n) ∈ K := zero_mem_boxInflate (by linarith)
  have hRout0 : (0 : ℝ)
      ≤ 2 * (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) * Real.sqrt n := by positivity
  have hout1 : K ⊆ Metric.closedBall (0 : Space n)
      (2 * (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) * Real.sqrt n) := fun x hx => by
    simpa [Metric.mem_closedBall] using hDK x hx 0 hzero
  have hK0 : volume K ≠ 0 := Arlib.MarkovChains.volume_ne_zero_of_ball_subset one_pos hball1
  have hKtop : volume K ≠ ⊤ := ((measure_mono hout1).trans_lt measure_closedBall_lt_top).ne
  -- the body is strictly bigger than the inscribed unit ball
  have hvolLt : volume (Metric.ball (0 : Space n) 1) < volume K := by
    refine lt_of_lt_of_le ?_ (measure_mono hballBig)
    have hbig := MeasureTheory.Measure.addHaar_ball_of_pos (volume : Measure (Space n)) 0
      (show (0 : ℝ) < 1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr by linarith)
    rw [finrank_euclideanSpace_fin] at hbig
    rw [hbig]
    have h1 : (1 : ℝ) < (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) ^ n :=
      one_lt_pow₀ (by linarith) (by omega)
    have h2 : (1 : ℝ≥0∞)
        < ENNReal.ofReal ((1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) ^ n) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 h1
    calc volume (Metric.ball (0 : Space n) 1)
        = volume (Metric.ball (0 : Space n) 1) * 1 := (mul_one _).symm
      _ < volume (Metric.ball (0 : Space n) 1)
            * ENNReal.ofReal ((1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) ^ n) :=
          ENNReal.mul_lt_mul_right hb0 hbtop h2
      _ = _ := mul_comm _ _
  have hvle : (volume (Metric.ball (0 : Space n) 1)).toReal ≤ (volume K).toReal :=
    (ENNReal.toReal_le_toReal hbtop hKtop).2 hvolLt.le
  have hKpos : 0 < (volume K).toReal := lt_of_lt_of_le hv0 hvle
  -- the tolerance is at most `1/2`
  have htol : ep / (4 * (volume K).toReal) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have : ep ≤ 2 * (volume (Metric.ball (0 : Space n) 1)).toReal := min_le_right _ _
    linarith
  -- the warm start: uniform on the inscribed unit ball, with an empty exceptional set
  haveI hmu0 : IsProbabilityMeasure (Arlib.uniformOn volume (Metric.ball (0 : Space n) 1)) :=
    Arlib.isProbabilityMeasure_uniformOn volume hb0 hbtop
  have hMw1 : (1 : ℝ)
      ≤ (volume K).toReal / (volume (Metric.ball (0 : Space n) 1)).toReal := by
    rw [le_div_iff₀ hv0]; linarith
  have hwarm := isWarm_uniformOn_subset measurableSet_ball hKmeas hball1 hb0 hbtop hK0 hKtop
  -- the linear description contains the (undilated) region
  have hdil : ∀ i : {c : Cube Unit // c ∈ [[(⟨(), true⟩ : Lit Unit)]]},
      latticeScale (0 : ℤ) • region (fun _ => Metric.closedBall (0 : Space n) (1 / 2)) i.val
        ⊆ Arlib.Polytope.body (boxNormals n) (fun _ => (1 : ℝ)) := by
    intro i
    have hls : latticeScale (0 : ℤ) = (1 : ℝ) := by simp [latticeScale]
    rw [hls, one_smul]
    have hival : i.val = [(⟨(), true⟩ : Lit Unit)] := by simpa using i.2
    rw [hival]
    intro x hx
    have hmem : x ∈ Metric.closedBall (0 : Space n) (1 / 2) := by
      simpa [region, Cube.holds, Lit.holds, induced] using hx
    have hxn : ‖x‖ ≤ 1 / 2 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hmem
    refine mem_boxBody.2 fun j => ?_
    have hle := PiLp.norm_apply_le (p := 2) x j
    rw [Real.norm_eq_abs] at hle
    linarith
  have hcard : ((Fintype.card (Fin n × Bool) : ℕ) : ℝ) ≤ rr := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
      Nat.cast_ofNat]
    have : (2 : ℝ) * (n : ℝ) ≤ rr := le_max_right _ _
    linarith
  -- the sampler
  refine ⟨ep, _, kv97SamplerOfHitAndRun H hn hep0 (Fin n × Bool)
    (fun _ => boxNormals n) (fun _ _ => (1 : ℝ)) hdil rr hr1 hcard
    (fun _ => 0) (fun _ => 1) (fun _ => one_pos) (fun _ => hin1)
    (fun _ => 0) (fun _ => 2 * (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) * Real.sqrt n)
    (fun _ => hRout0) (fun _ => hout1) (fun _ => le_trans htol (by norm_num))
    (fun _ => Arlib.uniformOn volume (Metric.ball (0 : Space n) 1)) (fun _ => hmu0)
    (fun _ => (volume K).toReal / (volume (Metric.ball (0 : Space n) 1)).toReal)
    (fun _ => hMw1) (fun _ => ∅) (fun _ => MeasurableSet.empty) (fun _ => by simp)
    (fun _ T hT => by rw [Set.sdiff_empty]; exact hwarm T hT),
    hep0, ⟨⟨[(⟨(), true⟩ : Lit Unit)], by simp⟩⟩, ?_⟩
  intro i
  refine ⟨?_, _, _, rfl, ?_⟩
  · show ENNReal.ofReal (ep / (4 * (volume K).toReal)) ≤ ENNReal.ofReal (1 / 2)
    exact ENNReal.ofReal_le_ofReal htol
  · exact uniformOn_ne_uniformOn_of_volume_lt measurableSet_ball hKmeas hball1 hb0 hbtop
      hK0 hKtop hvolLt

/-! ### Axiom audit (`CLAUDE.md` §4)

Every declaration in this file must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms kv97HitAndRunContLaw
#print axioms kv97HitAndRunContLaw_eq_iterate
#print axioms isProbabilityMeasure_kv97HitAndRunContLaw
#print axioms toReal_volume_inflated_pos_of_closedBalls
#print axioms tvLe_hitAndRunLaw_inflated
#print axioms kv97SamplerOfHitAndRun
#print axioms closedBall_subset_boxInflate
#print axioms zero_mem_boxInflate
#print axioms exists_hitAndRun_binders_box

end Ttc

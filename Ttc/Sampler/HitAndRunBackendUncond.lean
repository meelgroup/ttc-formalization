/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.HitAndRunMixingUncond
import Ttc.Sampler.HitAndRunBackend

/-!
# The sampler contract's conclusion, with every mathematical hypothesis discharged

`Ttc/Sampler/HitAndRunBackend.lean` closes every *bookkeeping* seam between the proved
Lovász–Vempala mixing theorem and `Ttc.HitAndRunTheorem11Input`: the general inradius `r`
(via similarity-equivariance of hit-and-run), the `hdom` shape, the threshold spelling.  What
it could not close were the two *mathematical* binders `hLem41` (Lemma 4.1) and `hIso`
(Theorem 2.1, corrected).

**Both are now gone.**  `Arlib.conductance_hitAndRun_ge_uncond`
(`Arlib/Convexity/HitAndRunConductanceUncond.lean:99`) proves Theorem 4.2 with no
mathematical hypothesis, and `Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_uncond_ball`
(`Arlib/MarkovChains/Continuous/HitAndRunMixingUncond.lean:177`) carries it into Theorem 1.1
for the **lazy** kernel.  This file transports that through the `r → 1` chart into the
contract's own shape.

## Main results

| name | content |
|---|---|
| `Ttc.diam_le_two_mul_of_subset_closedBall` (§1) | `K ⊆ closedBall zout R → diam K ≤ 2R` |
| `Ttc.hrBallDeadline_eq_contract` (§2) | `2⁶⁶·n²·(R/r)²·log(8M/ε²) = 4·(2⁸·hitAndRunTheorem11Threshold n r R M ε)` |
| **`Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond`** (§3) | **the contract's conclusion over `lazy (hitAndRun K)`, with every mathematical hypothesis discharged** |
| `Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond_ballOne_dim1100` (§4) | the non-vacuity witness: `n = 1100`, `K = closedBall 0 1`, no hypotheses at all |
| `Ttc.tvLe_iterate_hitAndRun_at_contract_shape_uncond_of_plainLS` (§5) | the **plain**-kernel conclusion from one binder: `hLS` for the plain kernel |

Every declaration is a `theorem`.  There is no `def`, no `structure`, no `class`, no `axiom`,
no `sorry`, no `admit`, no `native_decide`.  Nothing in `Ttc/Sampler/HitAndRunTheorem11.lean`
is edited, shadowed or redefined.

## What survives as a hypothesis in §3, and why

* `1100 ≤ n` — inherited from `Arlib.conductance_hitAndRun_ge_uncond`, whose Lemma 4.1
  discharge (`Arlib.MarkovChains.hLem41_interior_uncond`) needs it.  **Live**: the contract
  quantifies over `n ≥ 1`.
* the geometry — `closedBall zin r ⊆ K ⊆ closedBall zout R`, convex, closed, measurable.
* the accuracy `0 < ε ≤ 1` and the step count `hm`.
* the warm-start clause `M`, `S`, `hM`, `hS`, `hdom` — this is **Theorem 1.1's own
  hypothesis** on the starting distribution.  It is owner-authorised, and no mixing theorem
  can drop it: an arbitrary start has no mixing bound at any finite time.

`hR : 0 ≤ R` is retained purely so the binder list matches
`Ttc.HitAndRunTheorem11Input.mixing` position for position; it is unused, since `0 < R`
already follows from `hin`, `hout` and `Ttc.inradius_le_circumradius`.  Lean's unused-variable
linter warns about it, and that warning is intentional.

## The contract question, handled honestly

`Ttc.HitAndRunTheorem11Input.mixing` is stated over the **plain** kernel
`Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun K)`.  What is provable is the
**lazy** one, `Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun K)`.  These are different
Markov chains, and §3 does **not** inhabit `Ttc.HitAndRunTheorem11Input`.

The obstruction is precise.  The plain-kernel route needs `hLS` — Corollary 1.5 of
Lovász–Simonovits — for a chain with no laziness or spectral hypothesis, and that statement
is **false** for a general reversible chain: `HitAndRunMixing.lean:127-148` refutes it with
the swap kernel on `Bool` (reversible, conductance `1`, `2`-warm start, TV distance exactly
`1/2` at every time, against a bound tending to `0`).  For `lazy P` it is a theorem
(`Arlib.MarkovChains.ls_lazy`), which is why the lazy route carries one binder fewer.
`Ttc.tvLe_iterate_hitAndRun_at_contract_shape_uncond_of_plainLS` (§5) isolates exactly that
one fact: assume it at the normalised body and the contract's conclusion follows verbatim,
plain kernel and all, at `n ≥ 1100`.

**Two honest options.  The interface decision belongs to the human, and this file takes
neither.**

1. **Amend the contract to the lazy kernel.**  Change `HitAndRunTheorem11Input.mixing` to
   read `iterate (lazy (hitAndRun K)) sigma m`.  §3 then discharges it for `n ≥ 1100` with no
   mathematical hypothesis.  Cost: a longer deadline.  **The factor is `2¹⁰`, not `4`** — the
   `4` is laziness, and a further `2⁸ = (8000/500)²` is the price of the Lemma 4.1 overlap
   constant this repository *proves* (`1 − 1/8000`) against the one the paper *prints*
   (`1 − 1/500`), which is what `Ttc.hitAndRunTheorem11Threshold`'s `2⁵⁶` was computed from.
   Any deadline budget that assumed only the factor `4` is short by `256`.
2. **Find a plain-kernel route.**  This means proving `hLS` for `hitAndRun K` specifically —
   a hit-and-run-specific spectral fact.  The `Bool` counterexample forbids proving it from
   reversibility alone, and the paper never states the hypothesis it would need.  Hit-and-run
   does hold at its current point with positive probability when the chord is short, which is
   morally the missing laziness; whether that suffices is open.

Even under option 2, **two further residuals** stand between §5 and a
`Ttc.HitAndRunTheorem11Input`, and they are independent of the kernel question: the threshold
`1100 ≤ n` (the contract quantifies from `n ≥ 1`), and the constant (`2⁸ ·
hitAndRunTheorem11Threshold` is proved; `hitAndRunTheorem11Threshold` is asked).  So no single
fact constructs the contract, and this file deliberately contains no
`hitAndRunTheorem11Input_of_...` declaration: a constructor named for a structure it cannot
build would be exactly the kind of green-but-empty artefact `CLAUDE.md` §11 warns against.

## What this does NOT do

In the register of `Ttc/Sampler/SpeedyBackend.lean` — this file proves a mixing bound and
nothing else.

* **`Ttc.ttc` and `Ttc.ttcPoly` are not rewired.**  Neither calls anything here.  The headline
  theorem's sampler is unchanged, and this file does not appear in its dependency tree.
* **`Ttc.ttcSampPrice` is unchanged, and still exponential.**  The price the headline charges
  per sample is what it was; §3's deadline is `2¹⁰ · 2⁵⁶ · n² (R²/r²) log(8M/ε²)`
  transitions, which is polynomial in `n`, `R/r` and `log(1/ε)` — but nothing in this file
  connects that count to `ttcSampPrice`, and no such connection is claimed.
* **The `n ≥ 1100` threshold is live.**  Every statement in §3–§5 assumes it.  It is not a
  formality: it comes from the Lemma 4.1 discharge and rules out every dimension a reader
  might test by hand.
* **A hit-and-run transition is not costed.**  The count is transitions, not bit or arithmetic
  operations; sampling a direction and locating a chord endpoint are assumed unit cost, which
  they are not.
* **This file alone makes nothing polynomial-time.**  It removes mathematical hypotheses from
  a mixing bound.  Wiring, pricing and the end-to-end runtime claim are elsewhere and
  untouched.
-/

namespace Ttc

open MeasureTheory Metric
open scoped ENNReal

/-! ## 1. Geometry: a circumball bounds the diameter -/

/-- **A body inside a ball of radius `R` has diameter at most `2R`.**  The triangle
inequality through the ball's centre; `Metric.diam_closedBall` would give the same for the
ball itself, but `Metric.diam_mono` then needs boundedness of the ambient set, so the direct
form is shorter. -/
theorem diam_le_two_mul_of_subset_closedBall {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {zout : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 ≤ R) (hout : K ⊆ closedBall zout R) :
    Metric.diam K ≤ 2 * R := by
  refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
  have hx' := Metric.mem_closedBall.1 (hout hx)
  have hy' := Metric.mem_closedBall.1 (hout hy)
  calc dist x y ≤ dist x zout + dist zout y := dist_triangle x zout y
    _ = dist x zout + dist y zout := by rw [dist_comm zout y]
    _ ≤ R + R := by gcongr
    _ = 2 * R := by ring

/-! ## 2. The deadline, in the contract's own units -/

/-- **The unconditional deadline is `2¹⁰` times the contract's.**

`Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_uncond_ball` asks for
`2⁶⁶·n²·R'²·log(8M/ε²)` steps on a body of inradius `1` and circumradius `R'`.  Run at
`R' = R/r` — the circumradius of the normalised body `(r • · + zin) ⁻¹' K` — that is exactly

    4 · (2⁸ · hitAndRunTheorem11Threshold n r R M eps),

since `hitAndRunTheorem11Threshold n r R M eps = 2⁵⁶·n²·(R²/r²)·log(8M/ε²)` and
`4 · 2⁸ · 2⁵⁶ = 2⁶⁶`.  No hypothesis on `r` is needed: `(R/r)² = R²/r²` is `div_pow`, which
holds even at `r = 0` under Lean's `x/0 = 0`.

**Where the `2¹⁰` comes from, and why it is not a formalisation loss.**  A factor `4` is
laziness (`Arlib.MarkovChains.conductance_lazy` halves `Φ`, and the deadline is quadratic in
`1/Φ`).  The remaining `2⁸ = 256` is `(8000/500)²`: the contract's `2⁵⁶` was computed from
the paper's *printed* Lemma 4.1 overlap constant `1 − 1/500`, and the constant this
repository actually **proves** is `1 − 1/8000`
(`Arlib.MarkovChains.hLem41_interior_uncond`).  So `2⁸` is the price of replacing an
assumed constant by a proved one, and `4` is the price of the lazy kernel. -/
theorem hrBallDeadline_eq_contract {n : ℕ} (r R M eps : ℝ) :
    2 ^ 66 * (n : ℝ) ^ 2 * (R / r) ^ 2 * Real.log (8 * M / eps ^ 2)
      = 4 * (2 ^ 8 * hitAndRunTheorem11Threshold n r R M eps) := by
  rw [hitAndRunTheorem11Threshold, div_pow]
  ring

/-! ## 3. The contract's conclusion over the lazy kernel, with no mathematical hypothesis -/

/-- **The conclusion of `Ttc.HitAndRunTheorem11Input.mixing`, byte for byte, over the lazy
kernel — with every mathematical hypothesis discharged.**

    TVLe (iterate (lazy (hitAndRun K)) σ m) (uniformOn volume K) (ofReal ε)

Compare `Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape`
(`Ttc/Sampler/HitAndRunBackend.lean`), which is the same statement carrying two further
binders.  **Both are gone here**, and nothing replaces them:

| binder of the conditional form | discharged by |
|---|---|
| `hLem41` (Lovász–Vempala Lemma 4.1, on the normalised body, at `1 − 1/500`) | `Arlib.MarkovChains.hLem41_interior_uncond`, at the proved `1 − 1/8000`, inside `Arlib.conductance_hitAndRun_ge_uncond` |
| `hIso` (their Theorem 2.1, corrected) | `Arlib.hIso_lowerSemicontinuous`, likewise inside `Arlib.conductance_hitAndRun_ge_uncond` |

What remains is exactly what the brief allows to remain, and no more:

* `1100 ≤ n` — live, and inherited from `Arlib.conductance_hitAndRun_ge_uncond`;
* the geometry `closedBall zin r ⊆ K ⊆ closedBall zout R`, `Convex`, `IsClosed`,
  `MeasurableSet`;
* the accuracy `0 < ε ≤ 1`;
* the step count `hm`;
* the warm-start clause `M`, `S`, `hM`, `hS`, `hdom` — **Theorem 1.1's own hypothesis on the
  starting distribution**, which no mixing theorem can drop, and which is stated here in the
  contract's `A \ S`-on-both-sides shape (`Ttc.hdom_of_contract` weakens it to the shape the
  Arlib theorem consumes).

**Note the two constants that differ from the contract**, both loud in the statement:

* the kernel is `Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun K)`, **not**
  `Arlib.MarkovChains.hitAndRun K`.  These are different Markov chains and this theorem does
  **not** inhabit `Ttc.HitAndRunTheorem11Input`.  See §5 and the module docstring;
* the deadline is `4 · (2⁸ · Ttc.hitAndRunTheorem11Threshold n r R M eps)`, i.e. `2¹⁰` times
  the contract's.  The factor `4` is laziness; the factor `2⁸ = (8000/500)²` is the price of
  a *proved* Lemma 4.1 constant in place of the paper's printed one.  See
  `Ttc.hrBallDeadline_eq_contract`.

The `r → 1` normalisation is free: `Ttc.map_hitAndRun_chart` makes hit-and-run equivariant
under the similarity `z ↦ r • z + zin`, `Arlib.MarkovChains.map_lazy_of_map_kernel` lifts
that through `lazy`, and `Ttc.tvLe_of_tvLe_chart` transports the conclusion back. -/
theorem tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    {zin zout : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R)
    (hin : closedBall zin r ⊆ K) (hout : K ⊆ closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {Sx : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet Sx)
    (hS : sigma Sx ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ Sx) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K (A \ Sx))
    {m : ℕ} (hm : 4 * (2 ^ 8 * hitAndRunTheorem11Threshold n r R M eps) ≤ (m : ℝ)) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun K)) sigma m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  have hchart : Measurable (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) :=
    Arlib.MarkovChains.measurable_affineChart r zin
  have hT : Measurable (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) :=
    measurable_invChart r zin
  haveI : IsProbabilityMeasure
      (Measure.map (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) sigma) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  refine tvLe_of_tvLe_chart hKm hr zin
    (fun y => Arlib.MarkovChains.map_lazy_of_map_kernel hchart
      (fun w => map_hitAndRun_chart hKm hr zin w) y) ?_
  refine Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_uncond_ball hn
    (convex_chartPreimage r zin hKc) (isClosed_chartPreimage r zin hKcl) (hKm.preimage hchart)
    (closedBall_one_subset_chartPreimage hr hin)
    (chartPreimage_subset_closedBall hr hout) hM heps0 heps1 (hSm.preimage hchart) ?_
    (hdom_chartPreimage hKm hSm hr zin hdom) ?_
  · rw [Measure.map_apply hT (hSm.preimage hchart),
      preimage_invChart_preimage_chart hr.ne' zin]
    exact hS
  · rw [hrBallDeadline_eq_contract]
    exact hm

/-! ## 4. Non-vacuity (`CLAUDE.md` §11) -/

/-- **Every hypothesis of §3 discharged at once, on a concrete body, in a concrete
dimension — a theorem with no hypotheses at all.**

`n = 1100`, `K = closedBall 0 1 ⊆ ℝ¹¹⁰⁰`, `zin = zout = 0`, `r = R = 1`, `M = 1`, `S = ∅`,
`ε = 1/2`, `m = 2⁶⁶ · 37510000`.

The step count is past the deadline because
`4 · (2⁸ · hitAndRunTheorem11Threshold 1100 1 1 1 (1/2)) = 2⁶⁶ · 1100² · log 32` and
`log 32 ≤ 31`, while `1100² · 31 = 37510000`.

**What this certifies, and what it does not.**  It certifies that the hypothesis bundle of
`Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond` is *simultaneously satisfiable* —
the theorem is not vacuous — and that its conclusion is derived *through* that theorem rather
than directly.  The tolerance `ε = 1/2` is a real bound (`ENNReal.ofReal 1` would be the
vacuous total-variation bound between any two probability measures).

It does **not** certify a non-stationary start: `σ = uniformOn volume K` is the target
itself, which is the `M = 1`, `S = ∅` warm start — the smallest legal warm-start datum, and
the only one whose `hdom` is available without a Radon–Nikodym computation.  For that start
the conclusion is also true for a trivial reason (the chain is stationary), so the witness
establishes satisfiability of the binders, not sharpness of the bound.  This is the same
caveat that `Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_uncond_witness` carries, and it is
inherited from it. -/
theorem tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond_ballOne_dim1100 :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun
          (closedBall (0 : EuclideanSpace ℝ (Fin 1100)) 1)))
        (Arlib.uniformOn volume (closedBall (0 : EuclideanSpace ℝ (Fin 1100)) 1))
        (2 ^ 66 * 37510000))
      (Arlib.uniformOn volume (closedBall (0 : EuclideanSpace ℝ (Fin 1100)) 1))
      (ENNReal.ofReal (1 / 2)) := by
  set K : Set (EuclideanSpace ℝ (Fin 1100)) := closedBall 0 1 with hK
  have hK0 : volume K ≠ 0 := (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hKtop : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  have h32 : (8 : ℝ) * 1 / ((1 : ℝ) / 2) ^ 2 = 32 := by norm_num
  have hlog : Real.log 32 ≤ 31 := by
    have := Real.log_le_sub_one_of_pos (x := (32 : ℝ)) (by norm_num)
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  refine tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond (n := 1100) (by norm_num)
    measurableSet_closedBall (convex_closedBall 0 1) Metric.isClosed_closedBall
    (zin := 0) (zout := 0) (r := 1) (R := 1) one_pos zero_le_one subset_rfl subset_rfl
    (M := 1) (eps := 1 / 2) le_rfl (by norm_num) (by norm_num)
    (Sx := ∅) MeasurableSet.empty (by simp)
    (fun A _ => by rw [ENNReal.ofReal_one, one_mul]) ?_
  rw [hitAndRunTheorem11Threshold, h32]
  push_cast
  nlinarith [hlog, hlog0]

/-! ## 5. The plain kernel: exactly what is still missing -/

/-- **The single additional fact that would close the plain/lazy gap, isolated.**

`Ttc.HitAndRunTheorem11Input.mixing` is stated over the **plain** kernel
`Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun K)`; §3 proves the **lazy** one.
These are different Markov chains, and the plain-kernel route needs one thing that the lazy
route does not: `hLS`, Corollary 1.5 of Lovász–Simonovits, for a chain with no laziness or
spectral hypothesis.  For `lazy P` that is a theorem (`Arlib.MarkovChains.ls_lazy`); for a
general reversible kernel it is **false**, refuted at
`Arlib/MarkovChains/Continuous/HitAndRunMixing.lean:127-148` by the swap kernel on `Bool`
(reversible, conductance `1`, started at a `2`-warm `dirac true`, TV distance exactly `1/2`
for every `t`).  Whether the hit-and-run kernel escapes that counterexample — it does hold at
its current point with positive probability whenever the chord is short, which is morally the
missing laziness — is open here and unaddressed in the paper.

This theorem takes that one fact as its **only** binder, at the normalised body
`(r • · + zin) ⁻¹' K`, and returns the contract's conclusion **verbatim** — plain kernel,
same `sigma`, same target, same `eps`.  Everything else is discharged: `hLem41`, `hIso` and
the conductance itself come from `Arlib.conductance_hitAndRun_ge_uncond_pow`.  Compare
`Ttc.tvLe_iterate_hitAndRun_at_contract_shape` (`Ttc/Sampler/HitAndRunBackend.lean`), the
same statement with **three** binders.

Note the deadline is `2⁸ · Ttc.hitAndRunTheorem11Threshold`, without the factor `4`: laziness
is what costs the `4`, and there is no laziness here.

**Three residuals still separate this from a `Ttc.HitAndRunTheorem11Input`**, and they are
independent — see the module docstring, "The contract question":

1. `hplainLS` — this theorem's binder, the Bool-refuted route;
2. `n < 1100` — `Arlib.conductance_hitAndRun_ge_uncond` is stated for `n ≥ 1100` only, while
   the contract quantifies over `n ≥ 1`;
3. the constant — the contract's deadline is `hitAndRunTheorem11Threshold`, and what is
   proved is `2⁸` times that.

So this theorem is deliberately **not** named `hitAndRunTheorem11Input_of_...`: it does not
construct one, and no single fact does. -/
theorem tvLe_iterate_hitAndRun_at_contract_shape_uncond_of_plainLS {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    {zin zout : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R)
    (hin : closedBall zin r ⊆ K) (hout : K ⊆ closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {Sx : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet Sx)
    (hS : sigma Sx ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ Sx) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K (A \ Sx))
    (hplainLS : ∀ ph W : ℝ, 0 < ph → ph ≤ 1 → 1 ≤ W →
      ENNReal.ofReal ph ≤ Arlib.MarkovChains.conductance
        (Arlib.MarkovChains.hitAndRun
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K))
        (Arlib.uniformOn volume
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K)) →
      ∀ mu : Measure (EuclideanSpace ℝ (Fin n)), IsProbabilityMeasure mu →
        Arlib.IsWarm (ENNReal.ofReal W) mu (Arlib.uniformOn volume
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K)) →
        ∀ t : ℕ, Arlib.TVLe
          (Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun
            ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K)) mu t)
          (Arlib.uniformOn volume
            ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K))
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t)))
    {m : ℕ} (hm : 2 ^ 8 * hitAndRunTheorem11Threshold n r R M eps ≤ (m : ℝ)) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun K) sigma m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hrR : r ≤ R := inradius_le_circumradius hn1 hr hin hout
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le hr hrR
  have hRr : (1 : ℝ) ≤ R / r := (one_le_div hr).2 hrR
  have hRr0 : (0 : ℝ) < R / r := lt_of_lt_of_le zero_lt_one hRr
  have hchart : Measurable (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) :=
    Arlib.MarkovChains.measurable_affineChart r zin
  have hT : Measurable (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) :=
    measurable_invChart r zin
  haveI : IsProbabilityMeasure
      (Measure.map (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) sigma) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have hphi0 : (0 : ℝ) < 1 / (2 ^ 31 * (n : ℝ) * (2 * (R / r))) := by positivity
  have hphi1 : 1 / (2 ^ 31 * (n : ℝ) * (2 * (R / r))) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hcond := Arlib.conductance_hitAndRun_ge_uncond_pow hn
    (convex_chartPreimage r zin hKc) (isClosed_chartPreimage r zin hKcl)
    (hKm.preimage hchart) (Metric.isBounded_closedBall.subset
      (chartPreimage_subset_closedBall hr hout))
    (closedBall_one_subset_chartPreimage hr hin)
    (diam_le_two_mul_of_subset_closedBall hRr0.le
      (chartPreimage_subset_closedBall hr hout))
  have heq : Arlib.MarkovChains.lsThreshold M (1 / (2 ^ 31 * (n : ℝ) * (2 * (R / r)))) eps
      = 2 ^ 8 * hitAndRunTheorem11Threshold n r R M eps := by
    rw [Arlib.MarkovChains.lsThreshold, hitAndRunTheorem11Threshold, div_pow, one_pow]
    field_simp
  refine tvLe_of_tvLe_chart hKm hr zin (fun y => map_hitAndRun_chart hKm hr zin y) ?_
  refine Arlib.MarkovChains.tvLe_iterate_of_exceptional_of_ls hM hphi0 hphi1 heps0 heps1
    (hSm.preimage hchart) ?_ (hdom_chartPreimage hKm hSm hr zin hdom) hcond hplainLS ?_
  · rw [Measure.map_apply hT (hSm.preimage hchart),
      preimage_invChart_preimage_chart hr.ne' zin]
    exact hS
  · rw [heq]
    exact hm

end Ttc

/-! ### Axiom audit (`CLAUDE.md` §4)

Every declaration in this file must report exactly `[propext, Classical.choice, Quot.sound]`.
Note what `#print axioms` cannot see: the `hplainLS` binder of §5 lives in that theorem's
*type*, not its proof, so it is invisible here — which is why §5's docstring and the module
docstring say what it is and why it is false in general. §3 and §4 have no such binder. -/

section AxiomCheck

#print axioms Ttc.diam_le_two_mul_of_subset_closedBall
#print axioms Ttc.hrBallDeadline_eq_contract
#print axioms Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond
#print axioms Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond_ballOne_dim1100
#print axioms Ttc.tvLe_iterate_hitAndRun_at_contract_shape_uncond_of_plainLS

end AxiomCheck

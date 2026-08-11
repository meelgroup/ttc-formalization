/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.InflateBound
import Ttc.Exec.RegimeInputs

/-!
# `Exec/SampleDischarge`: the sampler's open hypotheses, discharged at the run's own data

`Ttc.ttcSampleSteps_le` (`Exec/SampleBound` §5) is the closed form for `cSample` at the
run's own five quantities, and it carried **six undischarged hypotheses**:

| | hypothesis | `Exec/SampleBound` |
| --- | --- | --- |
| ① | `hγ   : 0 < ttcSampInradius atoms φ ε δ` | line 499 |
| ② | `hDm  : 0 < ttcSampDiam atoms φ ε δ ⟨i, hi⟩` | line 500 |
| ③ | `hdl  : 0 < ttcSampStep atoms φ ε δ` | line 501 |
| ④ | `hMw  : 1 ≤ ttcSampWarm atoms φ ε δ ⟨i, hi⟩` | line 502 |
| ⑤ | `heps0: 0 < ttcSampTol atoms φ ε δ ⟨i, hi⟩` | line 503 |
| ⑥ | `heps1: ttcSampTol atoms φ ε δ ⟨i, hi⟩ ≤ 1` | line 504 |

**All six are discharged here**, from the five conditions on the *input* that the
headline already carries — `0 < ε`, `ε ≤ 1`, `1 ≤ n`, `φ.IsPositive`,
`0 < volSol (atomSet atoms) φ` — and nothing else.  `Ttc.ttcSampleSteps_le_run` is the
result: `Ttc.ttcSampleSteps` bounded by `Ttc.mixStepsBound` with no binder about the
geometry left.  `Ttc.ttcSampleSteps_le_branchTwo_run` is the sharper branch-② form, whose
two extra geometric hypotheses (`step ≤ inradius ≤ diameter`) are discharged too.

The same is done for `Ttc.mixCost_le_ceil_mixStepsBound`'s **ten** hypotheses, giving
`Ttc.mixCost_le_ceil_ttcSampStepsBound` — the derived cost `Ttc.mixCost`, which is what
`cSample` denotes, bounded by `⌈Ttc.mixStepsBound⌉₊` at the run's own data.

## How each is discharged

* ③ `10^ρ > 0` and `Ttc.algGamma_pos` (`Exec/PriceList`) — the dilated inscribed radius
  is positive because every preprocessed cube is full-dimensional.
* ① `κ = Ttc.kappaOf (Ttc.cOf ε') r ≥ 0`, so the inradius `step + κ` exceeds the step.
  The same fact gives `hδγ : step ≤ inradius` unconditionally.
* ② `Ttc.canon_body_eq_smul_region` identifies the cube's body with the dilated region,
  which is bounded (`Ttc.isBounded_sol_algAtoms`) and contains a ball of radius `step`
  (`Ttc.ball_subset_region_algAtoms` carried through the dilation by
  `Ttc.ball_radius_scales`).  A bounded set containing a ball of radius `r` has diameter
  at least `r` (`Ttc.radius_le_diam_of_ball_subset`) — that gives both `0 < Dm` and
  `inradius ≤ Dm`.
* ④ The start's ball `B(10^ρ·cᵢ, step + κ)` is *inside* `P'ᵢ`
  (`Arlib.KV97.ball_subset_inflated`), and `Vol(P'ᵢ) < ∞` because the uninflated body is
  bounded, so the ratio `Vol(P'ᵢ)/Vol(B)` is at least `1`.
* ⑤ `ε' = ε/12 > 0` and `Vol(P'ᵢ) > 0`.

## ⑥ is the one with content, and it needs a **lower** bound on `Vol(P'ᵢ)`

`heps1` says `ε' ≤ 4·Vol(P'ᵢ)`.  That is the *opposite* direction from the `hD` of
`Ttc.mixCost_le_mixSteps` and from any uniform upper bound on `Vol(P'ᵢ)`: it is a lower
bound, and no lower bound on the inflated body existed in the development.  Two new facts
supply it.

* `Ttc.cube_le_unitBallVol` : `(2/√n)ⁿ ≤ Vₙ`.  `Ttc.unitBallVol` was deliberately opaque
  (`Model/Pseudocode` — "the Gamma-function formula is never needed"); this is the first
  quantitative statement about it.  The unit ball contains the open cube of half-side
  `1/√n`, whose volume is `(2/√n)ⁿ`, because `∑ xᵢ² < n·(1/n) = 1`.
* `Ttc.dim_le_ttcSampStep` : `64n ≤ 10^ρ·γ̂`.  The precision `ρ = ⌈log₁₀(γ/γ̂)⌉` is a
  *ceiling*, so `10^ρ·γ̂ ≥ γ` (`Ttc.gamma_le_latticeScale_mul`, `Lattice/Assembled`), and
  `γ ≥ 64n` (`Ttc.Params.mul_dim_le_gamma`, `Exec/RegimeInputs`).

Together (`Ttc.one_le_pow_mul_unitBallVol`) the two exponentials cancel:
`(64n)ⁿ·(2/√n)ⁿ = (128√n)ⁿ ≥ 1`, so `Vol(P'ᵢ) ≥ 1` in **every** dimension, while
`ε'/4 = ε/48 ≤ 1/48`.  The margin is not tight and is not meant to be; what matters is
that it does not degrade with `n`, which is why the crude cube bound suffices.

Note where the dilation is and is not used: `Ttc.thresh_le_scaled_ball_volume` is *not*
enough here, because the lattice precision `10^ρ` may be `< 1` (it is, exactly when the
input's own inscribed radius already exceeds `γ`), and then the threshold information the
dilation buys is scaled away.  What survives in every regime is `10^ρ·γ̂ ≥ γ`, and that is
what this file uses.

## `hD` does **not** resist either

`Ttc.mixCost_le_mixSteps`' `hD` is a **diameter** bound on `P'ᵢ`, not a volume bound, and
`Ttc.dist_le_ttcSampDiam` discharges it at the run's own cubes:
`Ttc.canon_dist_le_canonDm` (`Exec/CanonPolytope`) bounds the uninflated body's diameter
by `Ttc.canonDm`, and `Arlib.KV97.dist_le_of_mem_inflated` inflates that to
`(1 + κ/step)·canonDm`, which *is* `Ttc.ttcSampDiam`.  `hwarm` likewise follows from
`Ttc.isWarm_uniformOn_subset` (`Sampler/Construct`) at the inclusion of the start's ball.

## The uniform price, with nothing left over

Everything above is **per cube**, and `Ttc.runCost` charges one price at every cube.
`Exec/InflateBound` supplies the missing half — the uniform *upper* bound on `Vol(P'ᵢ)`,
the monotonicity of `Ttc.mixStepsBound` that consumes it, and the uniform price
`Ttc.ttcSampStepsPrice` — leaving `hγ`, `hDm`, `hMw` and `heps1` as open binders of
`Ttc.ttcSampleSteps_le_ttcSampStepsPrice`.  All four are theorems of this file, so

```
Ttc.ttcSampleSteps_le_ttcSampStepsPrice_run
  : ttcSampleSteps atoms φ ε δ i ≤ ttcSampStepsPrice atoms φ ε δ
```

holds under the five input conditions and cube membership alone.  Note the two files pull
in **opposite directions on the same quantity** and both are needed: `Exec/InflateBound`
bounds `Vol(P'ᵢ)` above (so the tolerance is bounded below), and §5 here bounds it below
(so the tolerance is at most `1`).

What this does **not** repair are the three undercounts `Exec/PriceList` records:
`Ttc.kv97SampD`'s rejection rounds are counted nowhere, `alg:ttc`'s `while` loops are
uncharged, and `Ttc.mixSteps` prices the chain the sampler's *law* is defined by rather
than steps `Ttc.ttcRun` takes.  A bound on an undercount is not a bound on the count.

No `sorry`, no new `axiom`, and no `def` at all: every declaration below is a theorem
about names that already existed.
-/

namespace Ttc

open MeasureTheory Metric Set Pointwise

variable {A : Type*} {n : ℕ}

/-! # §1  The body the ball walk runs in, at the run's own data -/

section AtTheRun

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The uninflated body of cube `i` is the dilated region** — `Ttc.canon_body_eq_smul_region`
at the run's own dilation, positivity coming from `Ttc.ttcInput_isPositive`. -/
theorem ttcSampCanonBody_eq (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    Arlib.Polytope.body
        (canonAm (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ)) i)
        (canonBv (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ))
          (latticeScale (ttcPrec atoms φ ε δ)) i)
      = latticeScale (ttcPrec atoms φ ε δ)
          • region (atomSet (ttcAtoms atoms φ ε δ)) i.val :=
  canon_body_eq_smul_region _ (toDNFd_isPositive (ttcInput_isPositive atoms φ))
    (latticeScale_pos _) i

/-- **The Kannan–Vempala displacement is nonnegative** — `κ = c + √(2 log r)` with
`c = Ttc.cOf …` itself a square root. -/
theorem ttcSampKappa_nonneg_run :
    0 ≤ Arlib.KV97.kappaOf
        (Arlib.KV97.cOf
          (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime)
        (canonRfac (toDNFd (ttcInput atoms φ))) :=
  Arlib.KV97.kappaOf_nonneg (Real.sqrt_nonneg _)

/-- **The run's inscribed radius is positive** — step plus a nonnegative displacement. -/
theorem ttcSampInradius_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : 0 < ttcSampInradius atoms φ ε δ := by
  have h1 := ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have h2 := ttcSampKappa_nonneg_run atoms φ ε δ
  simpa [ttcSampInradius] using by linarith

/-- **`hδγ`: the ball-walk step is at most the inscribed radius** — the displacement is
nonnegative, so this is unconditional. -/
theorem ttcSampStep_le_ttcSampInradius :
    ttcSampStep atoms φ ε δ ≤ ttcSampInradius atoms φ ε δ := by
  have h2 := ttcSampKappa_nonneg_run atoms φ ε δ
  simpa [ttcSampInradius] using by linarith

/-- **The dilated inscribed ball sits in the uninflated body.**
`Ttc.ball_subset_region_algAtoms` at the dilated atoms, carried through the lattice
dilation by `Ttc.ball_radius_scales`. -/
theorem ball_subset_ttcSampCanonBody (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    Metric.ball (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
        (ttcSampStep atoms φ ε δ)
      ⊆ Arlib.Polytope.body
          (canonAm (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ)) i)
          (canonBv (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ))
            (latticeScale (ttcPrec atoms φ ε δ)) i) := by
  rw [ttcSampCanonBody_eq atoms φ ε δ i]
  exact ball_radius_scales (latticeScale_pos _) _ _
    (ball_subset_region_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos i)

/-- **The inflated body's inscribed ball**, of radius `Ttc.ttcSampInradius` — the
uninflated ball of radius `Ttc.ttcSampStep` grown by `κ`
(`Arlib.KV97.ball_subset_inflated`). -/
theorem ball_subset_ttcSampBody (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    Metric.ball (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
        (ttcSampInradius atoms φ ε δ)
      ⊆ ttcSampBody atoms φ ε δ i :=
  Arlib.KV97.ball_subset_inflated (ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ball_subset_ttcSampCanonBody atoms φ ε δ hε0 hε1 hn hφ hpos i)

/-- **The uninflated body is bounded** — the dilated region of a cube of a DNF of the
preprocessed formula, whose `Sol` is bounded (`Ttc.isBounded_sol_algAtoms`). -/
theorem isBounded_ttcSampCanonBody (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    Bornology.IsBounded
      (Arlib.Polytope.body
        (canonAm (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ)) i)
        (canonBv (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ))
          (latticeScale (ttcPrec atoms φ ε δ)) i)) := by
  rw [ttcSampCanonBody_eq atoms φ ε δ i]
  exact isBounded_smul_region (toDNFd_isDNFOf (ttcInput atoms φ))
    (isBounded_sol_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) _ i

end AtTheRun

/-! # §2  A bounded body with an inscribed ball has positive diameter -/

/-- **A bounded set containing a ball of radius `r` has diameter at least `r`.**
The two points `z ± (r/2)·e₀` are both in the ball and are `r` apart.  `1 ≤ n` is what
makes `Ttc.Space n` big enough to have a direction `e₀` at all; `hb` is what makes
`Metric.diam` a diameter rather than the `0` Mathlib returns for an unbounded set. -/
theorem radius_le_diam_of_ball_subset (hn : 1 ≤ n) {S : Set (Space n)} {z : Space n}
    {r : ℝ} (hr : 0 < r) (hsub : Metric.ball z r ⊆ S) (hb : Bornology.IsBounded S) :
    r ≤ Metric.diam S := by
  have hn0 : 0 < n := hn
  set u : Space n := EuclideanSpace.single (⟨0, hn0⟩ : Fin n) (r / 2) with hu_def
  have hu : ‖u‖ = r / 2 := by
    rw [hu_def, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hx : z + u ∈ S := by
    refine hsub ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hu]
    linarith
  have hy : z - u ∈ S := by
    refine hsub ?_
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, hu]
    linarith
  have hdist : dist (z + u) (z - u) = r := by
    rw [dist_eq_norm, show z + u - (z - u) = (2 : ℝ) • u by rw [two_smul]; abel,
      norm_smul, Real.norm_eq_abs, hu]
    norm_num
    ring
  rw [← hdist]
  exact Metric.dist_le_diam_of_mem hb hx hy

/-- **A bounded set containing a ball of positive radius has positive diameter.** -/
theorem diam_pos_of_ball_subset (hn : 1 ≤ n) {S : Set (Space n)} {z : Space n} {r : ℝ}
    (hr : 0 < r) (hsub : Metric.ball z r ⊆ S) (hb : Bornology.IsBounded S) :
    0 < Metric.diam S :=
  lt_of_lt_of_le hr (radius_le_diam_of_ball_subset hn hr hsub hb)

/-! # §3  The volumes, the warmness and the tolerance -/

section Volumes

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- `Vol(P'ᵢ) ≠ 0` — the inflated body contains the dilated inscribed ball. -/
theorem ttcSampBody_volume_ne_zero (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    volume (ttcSampBody atoms φ ε δ i) ≠ 0 :=
  Arlib.KV97.volume_inflated_ne_zero
    (ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos) (Real.sqrt_nonneg _)
    (ball_subset_ttcSampCanonBody atoms φ ε δ hε0 hε1 hn hφ hpos i)

/-- `Vol(P'ᵢ) ≠ ∞` — the uninflated body is bounded (`Ttc.isBounded_ttcSampCanonBody`), and
inflating a body of finite volume by a finite displacement keeps it finite. -/
theorem ttcSampBody_volume_ne_top (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    volume (ttcSampBody atoms φ ε δ i) ≠ ⊤ :=
  Arlib.KV97.volume_inflated_ne_top
    (ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos) (Real.sqrt_nonneg _)
    (ball_subset_ttcSampCanonBody atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (isBounded_ttcSampCanonBody atoms φ ε δ hε0 hε1 hn hφ hpos i).measure_lt_top.ne

/-- `0 < Vol(P'ᵢ)` as a real number — both guards of `Ttc.ttcSampBody_volume_ne_zero`
and `Ttc.ttcSampBody_volume_ne_top`. -/
theorem ttcSampBody_toReal_volume_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    0 < (volume (ttcSampBody atoms φ ε δ i)).toReal :=
  ENNReal.toReal_pos (ttcSampBody_volume_ne_zero atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (ttcSampBody_volume_ne_top atoms φ ε δ hε0 hε1 hn hφ hpos i)

/-- **`hMw`, discharged: the warm-start ratio is at least `1`.**  The enclosing ball is
*inside* the inflated body (`Ttc.ball_subset_ttcSampBody`), so the ratio
`Vol(P'ᵢ)/Vol(B)` is a ratio of a larger to a smaller finite positive number. -/
theorem one_le_ttcSampWarm (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    1 ≤ ttcSampWarm atoms φ ε δ i := by
  have hrad := ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have hball := ball_subset_ttcSampBody atoms φ ε δ hε0 hε1 hn hφ hpos i
  have hb0 : 0 < volume (Metric.ball
      (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
      (ttcSampInradius atoms φ ε δ)) := Metric.measure_ball_pos volume _ hrad
  have hbtop : volume (Metric.ball
      (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
      (ttcSampInradius atoms φ ε δ)) ≠ ⊤ := measure_ball_lt_top.ne
  have hb0R : 0 < (volume (Metric.ball
      (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
      (ttcSampInradius atoms φ ε δ))).toReal := ENNReal.toReal_pos hb0.ne' hbtop
  have hle : (volume (Metric.ball
        (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
        (ttcSampInradius atoms φ ε δ))).toReal
      ≤ (volume (ttcSampBody atoms φ ε δ i)).toReal :=
    ENNReal.toReal_mono (ttcSampBody_volume_ne_top atoms φ ε δ hε0 hε1 hn hφ hpos i)
      (measure_mono hball)
  rw [ttcSampWarm, ENNReal.toReal_div, le_div_iff₀ hb0R, one_mul]
  exact hle

/-- **`heps0`, discharged: the TV tolerance is positive.**  `ε' = ε/12 > 0` and
`Vol(P'ᵢ) > 0`. -/
theorem ttcSampTol_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    0 < ttcSampTol atoms φ ε δ i := by
  have hV := ttcSampBody_toReal_volume_pos atoms φ ε δ hε0 hε1 hn hφ hpos i
  have hε' : 0 < (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime :=
    Params.epsPrime_pos _
  rw [ttcSampTol]
  positivity

/-- **`hDm`, discharged: the run's diameter bound is positive.**  `κ/step ≥ 0` makes the
first factor at least `1`, and the dilated region is bounded with an inscribed ball, so
its diameter is positive (`Ttc.diam_pos_of_ball_subset`). -/
theorem ttcSampDiam_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    0 < ttcSampDiam atoms φ ε δ i := by
  have hstep := ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have hkap := ttcSampKappa_nonneg_run atoms φ ε δ
  have hfac : 0 < 1 + Arlib.KV97.kappaOf
      (Arlib.KV97.cOf (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime)
      (canonRfac (toDNFd (ttcInput atoms φ))) / ttcSampStep atoms φ ε δ := by
    have : 0 ≤ Arlib.KV97.kappaOf
        (Arlib.KV97.cOf
          (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime)
        (canonRfac (toDNFd (ttcInput atoms φ))) / ttcSampStep atoms φ ε δ :=
      div_nonneg hkap hstep.le
    linarith
  have hdiam : 0 < canonDm (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
      (ttcPrec atoms φ ε δ) i := by
    have hsub := ball_subset_ttcSampCanonBody atoms φ ε δ hε0 hε1 hn hφ hpos i
    have hb := isBounded_ttcSampCanonBody atoms φ ε δ hε0 hε1 hn hφ hpos i
    rw [ttcSampCanonBody_eq atoms φ ε δ i] at hsub hb
    exact diam_pos_of_ball_subset hn hstep hsub hb
  rw [ttcSampDiam]
  exact mul_pos hfac hdiam

/-- **`hγDm`: the inscribed radius is at most the diameter bound.**  The dilated region
contains a ball of radius `Ttc.ttcSampStep`, so its diameter is at least that
(`Ttc.radius_le_diam_of_ball_subset`); multiplying by `1 + κ/step` turns `step` into
`step + κ`, which is `Ttc.ttcSampInradius`. -/
theorem ttcSampInradius_le_ttcSampDiam (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    ttcSampInradius atoms φ ε δ ≤ ttcSampDiam atoms φ ε δ i := by
  have hstep := ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have hkap := ttcSampKappa_nonneg_run atoms φ ε δ
  have hdiam : ttcSampStep atoms φ ε δ
      ≤ canonDm (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
          (ttcPrec atoms φ ε δ) i := by
    have hsub := ball_subset_ttcSampCanonBody atoms φ ε δ hε0 hε1 hn hφ hpos i
    have hb := isBounded_ttcSampCanonBody atoms φ ε δ hε0 hε1 hn hφ hpos i
    rw [ttcSampCanonBody_eq atoms φ ε δ i] at hsub hb
    exact radius_le_diam_of_ball_subset hn hstep hsub hb
  set κ := Arlib.KV97.kappaOf
    (Arlib.KV97.cOf (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime)
    (canonRfac (toDNFd (ttcInput atoms φ))) with hκ
  have hfac : (1 : ℝ) ≤ 1 + κ / ttcSampStep atoms φ ε δ := by
    have : 0 ≤ κ / ttcSampStep atoms φ ε δ := div_nonneg hkap hstep.le
    linarith
  have hkey : (1 + κ / ttcSampStep atoms φ ε δ) * ttcSampStep atoms φ ε δ
      = ttcSampStep atoms φ ε δ + κ := by
    field_simp
  show ttcSampStep atoms φ ε δ + κ ≤ _
  rw [ttcSampDiam, ← hkey]
  exact mul_le_mul_of_nonneg_left hdiam (by linarith)

end Volumes

/-! # §4  A lower bound on `Vₙ`, and the resulting lower bound on `Vol(P'ᵢ)` -/

/-- **`(2/√n)ⁿ ≤ Vₙ`.**  The unit ball of `Ttc.Space n` contains the open cube of
half-side `1/√n`, whose volume is `(2/√n)ⁿ`: if every `|xᵢ| < 1/√n` then
`‖x‖² = ∑ xᵢ² < n·(1/n) = 1`.

`Ttc.unitBallVol` is deliberately opaque (`Model/Pseudocode`), so this is the first
*quantitative* fact about it in the development.  It is what keeps the sampler's TV
tolerance below `1` in every dimension: `Vₙ → 0` as `n → ∞`, and this says it does not
go to zero faster than `(2/√n)ⁿ`. -/
theorem cube_le_unitBallVol (n : ℕ) (hn : 1 ≤ n) :
    (2 / Real.sqrt n) ^ n ≤ unitBallVol n := by
  have hn0 : 0 < n := hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  set a : ℝ := 1 / Real.sqrt n with ha_def
  have ha : 0 < a := by positivity
  have ha2 : a ^ 2 = 1 / (n : ℝ) := by
    rw [ha_def, div_pow, one_pow, Real.sq_sqrt hnR.le]
  set S : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Ioo (-a) a) with hS_def
  have hSmeas : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  set C : Set (Space n) := (WithLp.ofLp : Space n → (Fin n → ℝ)) ⁻¹' S with hC_def
  -- the cube's volume
  have hvolC : volume C = ENNReal.ofReal (2 * a) ^ n := by
    rw [hC_def,
      (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hSmeas.nullMeasurableSet,
      hS_def, volume_pi_pi]
    simp only [Real.volume_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    congr 1
    ring
  -- the cube sits inside the unit ball
  have hsub : C ⊆ Metric.ball (0 : Space n) 1 := by
    intro x hx
    have hxi : ∀ i, ‖x i‖ ^ 2 < a ^ 2 := by
      intro i
      have hxa : x i ∈ Set.Ioo (-a) a := hx i (Set.mem_univ i)
      have : |x i| < a := abs_lt.2 ⟨hxa.1, hxa.2⟩
      rw [Real.norm_eq_abs]
      exact pow_lt_pow_left₀ this (abs_nonneg _) (by norm_num)
    have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn0)
    have hsum : ∑ i, ‖x i‖ ^ 2 < 1 := by
      have h1 : ∑ i : Fin n, ‖x i‖ ^ 2 < ∑ _i : Fin n, a ^ 2 :=
        Finset.sum_lt_sum_of_nonempty hne fun i _ => hxi i
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha2] at h1
      rw [show (n : ℝ) * (1 / (n : ℝ)) = 1 by field_simp] at h1
      exact h1
    rw [Metric.mem_ball, dist_zero_right, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i, ‖x i‖ ^ 2) < Real.sqrt 1 :=
          Real.sqrt_lt_sqrt (Finset.sum_nonneg fun i _ => by positivity) hsum
      _ = 1 := Real.sqrt_one
  -- compare the two volumes
  have htop : volume (Metric.ball (0 : Space n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hmono := ENNReal.toReal_mono htop (measure_mono hsub)
  rw [hvolC, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at hmono
  have h2a : 2 * a = 2 / Real.sqrt n := by rw [ha_def]; ring
  rw [h2a] at hmono
  exact hmono

/-- **`1 ≤ γⁿ·Vₙ` whenever `64n ≤ γ`** — the two exponentials cancel: `(64n)·(2/√n)
= 128·√n ≥ 1`, so `γⁿ·Vₙ ≥ (128√n)ⁿ ≥ 1`.  This is the fact that keeps
`ε'/(4·Vol P'ᵢ) ≤ 1` in every dimension. -/
theorem one_le_pow_mul_unitBallVol (n : ℕ) (hn : 1 ≤ n) {r : ℝ}
    (hr : 64 * (n : ℝ) ≤ r) : 1 ≤ r ^ n * unitBallVol n := by
  have hn0 : 0 < n := hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hs1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hnR
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by linarith)
  have hr0 : 0 < r := by linarith
  have hbase : (1 : ℝ) ≤ 64 * (n : ℝ) * (2 / Real.sqrt n) := by
    have : 64 * (n : ℝ) * (2 / Real.sqrt n) = 128 * Real.sqrt n := by
      field_simp
      nlinarith [hsq]
    rw [this]
    nlinarith
  calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
    _ ≤ (64 * (n : ℝ) * (2 / Real.sqrt n)) ^ n := pow_le_pow_left₀ zero_le_one hbase n
    _ = (64 * (n : ℝ)) ^ n * (2 / Real.sqrt n) ^ n := by rw [mul_pow]
    _ ≤ r ^ n * (2 / Real.sqrt n) ^ n :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr n) (by positivity)
    _ ≤ r ^ n * unitBallVol n :=
        mul_le_mul_of_nonneg_left (cube_le_unitBallVol n hn) (by positivity)

/-! # §5  `heps1`: the TV tolerance is at most `1` -/

section Tol

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **`64n ≤ Ttc.ttcSampStep`.**  The run's ball-walk step is `10^ρ·γ̂`, and
`Ttc.gamma_le_latticeScale_mul` bounds that below by the parameter block's own target
radius `γ`, which is at least `64n` (`Ttc.Params.mul_dim_le_gamma`). -/
theorem dim_le_ttcSampStep (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    64 * (n : ℝ) ≤ ttcSampStep atoms φ ε δ := by
  have hg : 0 < ttcScaledRadius atoms φ ε δ := algGamma_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have h1 : (ttcBlock atoms φ ε δ).gamma
      ≤ latticeScale ((ttcBlock atoms φ ε δ).precision (ttcScaledRadius atoms φ ε δ))
        * ttcScaledRadius atoms φ ε δ :=
    gamma_le_latticeScale_mul (ttcBlock atoms φ ε δ) hg
  have h2 : 64 * ((ttcBlock atoms φ ε δ).n : ℝ) ≤ (ttcBlock atoms φ ε δ).gamma :=
    Params.mul_dim_le_gamma _
  rw [ttcBlock_n atoms φ ε δ hε0 hε1 hn hφ hpos] at h2
  exact le_trans h2 h1

/-- **`1 ≤ Vol(P'ᵢ)`.**  The inflated body contains a ball of radius at least `64n`
(`Ttc.dim_le_ttcSampStep`), and `Ttc.one_le_pow_mul_unitBallVol` says a ball of that
radius has volume at least `1` in every dimension. -/
theorem one_le_ttcSampBody_volume (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    1 ≤ (volume (ttcSampBody atoms φ ε δ i)).toReal := by
  have hrad := ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have hstep := dim_le_ttcSampStep atoms φ ε δ hε0 hε1 hn hφ hpos
  have hle := ttcSampStep_le_ttcSampInradius atoms φ ε δ
  have hball : 64 * (n : ℝ) ≤ ttcSampInradius atoms φ ε δ := le_trans hstep hle
  have hvol : (volume (Metric.ball
        (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
        (ttcSampInradius atoms φ ε δ))).toReal
      = ttcSampInradius atoms φ ε δ ^ n * unitBallVol n := volume_ball_eq n _ hrad
  have hone : 1 ≤ (volume (Metric.ball
      (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
      (ttcSampInradius atoms φ ε δ))).toReal := by
    rw [hvol]
    exact one_le_pow_mul_unitBallVol n hn hball
  refine le_trans hone (ENNReal.toReal_mono
    (ttcSampBody_volume_ne_top atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (measure_mono (ball_subset_ttcSampBody atoms φ ε δ hε0 hε1 hn hφ hpos i)))

/-- **`heps1`, discharged: the run's TV tolerance is at most `1`.**

`ε' = ε/12 ≤ 1/12` and `Vol(P'ᵢ) ≥ 1` (`Ttc.one_le_ttcSampBody_volume`), so
`ε'/(4·Vol P'ᵢ) ≤ 1/48 ≤ 1`.  Note the direction: this needs a **lower** bound on the
inflated body's volume, which is the opposite of the upper bound `hD` asks for. -/
theorem ttcSampTol_le_one (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    ttcSampTol atoms φ ε δ i ≤ 1 := by
  have hV := one_le_ttcSampBody_volume atoms φ ε δ hε0 hε1 hn hφ hpos i
  have hε' : (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime
      = ε / 12 := by
    show (ttcBlock atoms φ ε δ).ε / 12 = ε / 12
    rw [ttcBlock_eps atoms φ ε δ hε0 hε1 hn hφ hpos]
  rw [ttcSampTol, hε', div_le_one (by linarith)]
  linarith

end Tol

/-! # §6  `hD` and `hwarm`, and the two assembled statements -/

section Assemble

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **`hD`, discharged: the inflated body's diameter is at most `Ttc.ttcSampDiam`.**

`Ttc.canon_dist_le_canonDm` bounds the *uninflated* body's diameter by `Ttc.canonDm`,
and `Arlib.KV97.dist_le_of_mem_inflated` inflates that bound to
`(1 + κ/step)·canonDm`, which is `Ttc.ttcSampDiam` by definition.  So the diameter
hypothesis of `Ttc.mixCost_le_mixSteps` is not an open assumption at the run's own
cubes. -/
theorem dist_le_ttcSampDiam (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    ∀ x ∈ ttcSampBody atoms φ ε δ i, ∀ y ∈ ttcSampBody atoms φ ε δ i,
      dist x y ≤ ttcSampDiam atoms φ ε δ i :=
  Arlib.KV97.dist_le_of_mem_inflated
    (ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos) (Real.sqrt_nonneg _)
    (ball_subset_ttcSampCanonBody atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (canon_dist_le_canonDm (ttcAtoms atoms φ ε δ)
      (toDNFd_isPositive (ttcInput_isPositive atoms φ))
      (toDNFd_isDNFOf (ttcInput atoms φ))
      (isBounded_sol_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcPrec atoms φ ε δ) i)

/-- **`hwarm`, discharged: uniform on the inscribed ball is a
`Ttc.ttcSampWarm`-warm start** for uniform on the inflated body
(`Ttc.isWarm_uniformOn_subset`, at the inclusion `Ttc.ball_subset_ttcSampBody`). -/
theorem isWarm_ttcSampWarm (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    Arlib.IsWarm (ENNReal.ofReal (ttcSampWarm atoms φ ε δ i))
      (Arlib.uniformOn volume (Metric.ball
        (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
        (ttcSampInradius atoms φ ε δ)))
      (Arlib.uniformOn volume (ttcSampBody atoms φ ε δ i)) := by
  have hrad := ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have hb0 : volume (Metric.ball
      (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
      (ttcSampInradius atoms φ ε δ)) ≠ 0 :=
    (Metric.measure_ball_pos volume _ hrad).ne'
  have hbtop : volume (Metric.ball
      (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
      (ttcSampInradius atoms φ ε δ)) ≠ ⊤ := measure_ball_lt_top.ne
  have hw : ttcSampWarm atoms φ ε δ i
      = (volume (ttcSampBody atoms φ ε δ i)).toReal
        / (volume (Metric.ball
            (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
            (ttcSampInradius atoms φ ε δ))).toReal := by
    rw [ttcSampWarm, ENNReal.toReal_div]
  rw [hw]
  exact isWarm_uniformOn_subset measurableSet_ball
    (Arlib.KV97.measurableSet_inflated _ _ _ _)
    (ball_subset_ttcSampBody atoms φ ε δ hε0 hε1 hn hφ hpos i) hb0 hbtop
    (ttcSampBody_volume_ne_zero atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (ttcSampBody_volume_ne_top atoms φ ε δ hε0 hε1 hn hφ hpos i)

/-- **The closed form for `cSample` at the run's own data, with all six hypotheses of
`Ttc.ttcSampleSteps_le` discharged.**

```
ttcSampleSteps atoms φ ε δ i
  ≤ (log Mwᵢ + 2·log(1/epsᵢ))
      · ( 1024·((γ+Dmᵢ)/γ)^(2n) + 16384·4ⁿ·n²·Dmᵢ²/δ²·((γ+Dmᵢ)/γ)^(4n) ) + 1
```

The only hypotheses left are the five conditions on the *input* — the FPRAS accuracy
range, `1 ≤ n`, syntactic positivity of `φ`, and `Vol(Sol φ) > 0` — plus membership of
the cube in the DNF.  **Exponential in `n`**, as `Exec/SampleBound` records. -/
theorem ttcSampleSteps_le_run (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) {i : Cube A}
    (hi : i ∈ toDNFd (ttcInput atoms φ)) :
    (ttcSampleSteps atoms φ ε δ i : ℝ)
      ≤ mixStepsBound n (ttcSampInradius atoms φ ε δ) (ttcSampDiam atoms φ ε δ ⟨i, hi⟩)
          (ttcSampStep atoms φ ε δ) (ttcSampWarm atoms φ ε δ ⟨i, hi⟩)
          (ttcSampTol atoms φ ε δ ⟨i, hi⟩) :=
  ttcSampleSteps_le atoms φ ε δ hi hn
    (ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcSampDiam_pos atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (one_le_ttcSampWarm atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (ttcSampTol_pos atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (ttcSampTol_le_one atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)

/-- **The sharper, branch-②-only closed form at the run's own data**, with its two
extra geometric hypotheses discharged as well: the ball-walk step is at most the
inscribed radius (`Ttc.ttcSampStep_le_ttcSampInradius`, because `κ ≥ 0`) and the
inscribed radius is at most the diameter bound
(`Ttc.ttcSampInradius_le_ttcSampDiam`). -/
theorem ttcSampleSteps_le_branchTwo_run (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) {i : Cube A}
    (hi : i ∈ toDNFd (ttcInput atoms φ)) :
    (ttcSampleSteps atoms φ ε δ i : ℝ)
      ≤ (Real.log (ttcSampWarm atoms φ ε δ ⟨i, hi⟩)
            + 2 * Real.log (1 / ttcSampTol atoms φ ε δ ⟨i, hi⟩))
          * (16384 * 4 ^ n * (n : ℝ) ^ 2 * ttcSampDiam atoms φ ε δ ⟨i, hi⟩ ^ 2
              / ttcSampStep atoms φ ε δ ^ 2
              * ((ttcSampInradius atoms φ ε δ + ttcSampDiam atoms φ ε δ ⟨i, hi⟩)
                  / ttcSampInradius atoms φ ε δ) ^ (4 * n))
        + 1 :=
  ttcSampleSteps_le_branchTwo atoms φ ε δ hi hn
    (ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcSampDiam_pos atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcSampStep_le_ttcSampInradius atoms φ ε δ)
    (ttcSampInradius_le_ttcSampDiam atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (one_le_ttcSampWarm atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (ttcSampTol_pos atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (ttcSampTol_le_one atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)

/-- **`Ttc.mixCost_le_ceil_mixStepsBound` at the run's own data, with every one of its
ten hypotheses discharged.**

`Ttc.mixCost` — the object `cSample` denotes (`Ttc/CostModel.lean` §3) — at the run's
own inflated body, ball-walk step, warm start and TV tolerance is bounded by
`⌈Ttc.mixStepsBound⌉₊` at the run's own five quantities.  Nothing about the sampler is
assumed; what is assumed is the input. -/
theorem mixCost_le_ceil_ttcSampStepsBound (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    mixCost (ttcSampBody atoms φ ε δ i) (ttcSampStep atoms φ ε δ)
        (Arlib.uniformOn volume (Metric.ball
          (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
          (ttcSampInradius atoms φ ε δ)))
        (Arlib.uniformOn volume (ttcSampBody atoms φ ε δ i))
        (ENNReal.ofReal (ttcSampTol atoms φ ε δ i))
      ≤ ((⌈mixStepsBound n (ttcSampInradius atoms φ ε δ) (ttcSampDiam atoms φ ε δ i)
            (ttcSampStep atoms φ ε δ) (ttcSampWarm atoms φ ε δ i)
            (ttcSampTol atoms φ ε δ i)⌉₊ : ℕ) : ℕ∞) :=
  mixCost_le_ceil_mixStepsBound hn (ttcPrec atoms φ ε δ)
    (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime
    (canonRfac (toDNFd (ttcInput atoms φ)))
    (canonAm (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ)))
    (canonBv (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ))
      (latticeScale (ttcPrec atoms φ ε δ)))
    (ttcCen atoms φ ε δ) (ttcScaledRadius atoms φ ε δ)
    (canonDm (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
      (ttcPrec atoms φ ε δ)) i
    (dist_le_ttcSampDiam atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ball_subset_ttcSampBody atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcSampStep_le_ttcSampInradius atoms φ ε δ)
    (one_le_ttcSampWarm atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (isWarm_ttcSampWarm atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (ttcSampTol_pos atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (ttcSampDiam_pos atoms φ ε δ hε0 hε1 hn hφ hpos i)
    (ttcSampTol_le_one atoms φ ε δ hε0 hε1 hn hφ hpos i)

/-- **The uniform `cSample` price, with every side condition discharged.**

`Ttc.ttcSampleSteps_le_ttcSampStepsPrice` (`Exec/InflateBound` §4) carries four open
hypotheses — `hγ`, `hDm`, `hMw` and `heps1`.  All four are theorems of this file, so the
uniform price holds under the **five conditions on the input alone**:

```
0 < ε,  ε ≤ 1,  1 ≤ n,  φ.IsPositive,  0 < volSol (atomSet atoms) φ.
```

Together with `Ttc.ttcVolCoins_le_ttcVolPrice` (`Exec/PriceList`) this is the pair of
per-cube-free prices the run's charge is built from, both now unconditional on the
geometry.  **Exponential in `n`** — twice over, see `Exec/InflateBound`'s docstring — and
still a price for the chain the sampler's *law* is defined by, not for steps
`Ttc.ttcRun` takes. -/
theorem ttcSampleSteps_le_ttcSampStepsPrice_run (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) {i : Cube A}
    (hi : i ∈ toDNFd (ttcInput atoms φ)) :
    (ttcSampleSteps atoms φ ε δ i : ℝ) ≤ ttcSampStepsPrice atoms φ ε δ :=
  ttcSampleSteps_le_ttcSampStepsPrice atoms φ ε δ hε0 hε1 hn hφ hpos hi
    (ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcSampDiam_pos atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (one_le_ttcSampWarm atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (ttcSampTol_le_one atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)

end Assemble

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ttcSampCanonBody_eq
#print axioms Ttc.ttcSampKappa_nonneg_run
#print axioms Ttc.ttcSampInradius_pos
#print axioms Ttc.ttcSampStep_le_ttcSampInradius
#print axioms Ttc.ball_subset_ttcSampCanonBody
#print axioms Ttc.ball_subset_ttcSampBody
#print axioms Ttc.isBounded_ttcSampCanonBody
#print axioms Ttc.radius_le_diam_of_ball_subset
#print axioms Ttc.diam_pos_of_ball_subset
#print axioms Ttc.ttcSampBody_volume_ne_zero
#print axioms Ttc.ttcSampBody_volume_ne_top
#print axioms Ttc.ttcSampBody_toReal_volume_pos
#print axioms Ttc.one_le_ttcSampWarm
#print axioms Ttc.ttcSampTol_pos
#print axioms Ttc.ttcSampDiam_pos
#print axioms Ttc.ttcSampInradius_le_ttcSampDiam
#print axioms Ttc.cube_le_unitBallVol
#print axioms Ttc.one_le_pow_mul_unitBallVol
#print axioms Ttc.dim_le_ttcSampStep
#print axioms Ttc.one_le_ttcSampBody_volume
#print axioms Ttc.ttcSampTol_le_one
#print axioms Ttc.dist_le_ttcSampDiam
#print axioms Ttc.isWarm_ttcSampWarm
#print axioms Ttc.ttcSampleSteps_le_run
#print axioms Ttc.ttcSampleSteps_le_branchTwo_run
#print axioms Ttc.mixCost_le_ceil_ttcSampStepsBound
#print axioms Ttc.ttcSampleSteps_le_ttcSampStepsPrice_run





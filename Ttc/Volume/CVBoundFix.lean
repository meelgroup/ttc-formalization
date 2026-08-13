/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVInstantiate

/-!
# `Volume/CVBoundFix`: the `hgb` obstruction, diagnosed, refuted where it is real, repaired

Purely additive.  Nothing under `Ttc/` or `Arlib/` is edited; every existing capstone still
builds.

## 0.  The obstruction, as previously recorded

`Ttc/Volume/CVInstantiate.lean:629-633` and `Ttc/Volume/CVAmended.lean:105-114` record that
`hgb`, the hypothesis

    hgb : ∀ K ε p j i x, |g K ε p j i x| ≤ B     (`B : ℝ`, a single constant)

of `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`, is **uniform in `K`**, and reason
that it cannot be relaxed because it feeds `Arlib.Probability.memLp_two_natRunProd` through
the base constructor's `hprodLp` obligation, which is *unguarded* — it sits outside the
`Convex ℝ K` / `ball 0 1 ⊆ K` / `volume K ≠ ⊤` guard the other per-`K` binders carry
(`Ttc/Volume/CousinsVempala.lean:2079`).

## 1.  Diagnosis: that reasoning conflates two different defects

**(a) Unguardedness does not force uniformity.**  `hprodLp` is
`∀ K ε p j, MemLp (fun ω => ∏ i, W K ε p j i ω) 2 μ` — a statement *about each `K`
separately*.  `Arlib.Probability.memLp_two_natRunProd`
(`Arlib/Probability/RunPlumbing.lean:544`) takes its bound `{B : ℝ}` **implicitly** and is
applied at one fixed `K` (`Ttc/Volume/CVInstantiate.lean:544`,
`… memLp_two_natRunProd ν (hg K ε p) (hgb K ε p) j _`), so a `K`-**dependent** bound
`B : Set (Space n) → ℝ → ℝ → ℝ` elaborates through the *same* application with no change to
`Arlib` at all.  Nothing in the `hprodLp` obligation, and nothing in `memLp_two_natRunProd`,
asks for one constant serving every body.  The uniformity is an artifact of the
`(B : ℝ)` binder in `cousinsVempalaOfRunsApproxMean`'s own signature.

**(b) Unguardedness is incidental, not essential.**  `hprodLp` is consumed at exactly two
places, `Ttc/Volume/CousinsVempala.lean:2013` (in `cousinsVempala`) and `:2132` (in
`cousinsVempalaOfApproxMean`), and at *both* the full guard `hε hp hp1 hconv hball hfin` is
already in scope — they occur inside `fun K ε p hε hp hp1 hconv hball hfin j => …`.  The
zero-phase branch of `cousinsVempalaOfApproxMean` (`:2107-2123`) never touches `hprodLp` at
all.  A guarded `hprodLp` would therefore have typechecked in the original proofs; the
binder is stated unguarded only because it is grouped with the "admissibility" block.

Since this file may not edit `CousinsVempala.lean`, (b) is worked around rather than fixed:
the score is **clamped to `0` off the guard** (`Ttc.CVGuard`, `Ttc.clampScore`), which makes
the unguarded `hprodLp` provable from a *guarded* bound while changing nothing under the
guard — `VolumeAlgorithm.correct` (`Ttc/Volume/Oracle.lean:91-93`) is itself quantified
under exactly that guard, so no guarantee is weakened.

## 2.  Is a uniform `B` impossible, or merely absent?  Three-way answer

* **Impossible at a constant phase count — proved.**  `Ttc.no_uniform_score_bound_of_phases_one`
  below takes the binders `hg`, `hgb`, `hphase_mean` of
  `cousinsVempalaOfRunsApproxMean` *verbatim*, at `phases ≡ 1` and a constant variance
  schedule `σsq ≡ s`, and derives `False`.  The mechanism is the one the docstring at
  `CVInstantiate.lean:630-633` guessed at, now machine-checked: `chain 1 σsq K 1 = Vol(K)`
  is unbounded over admissible bodies while `chain 1 σsq K 0 ≤ (2πs)^{n/2}` is bounded, so
  the phase ratio `chain(1)/chain(0)` is unbounded, while `hphase_mean` forces the score's
  mean to within a relative `< 1/2` of it and `hgb` caps that mean at `B`.
  `Ttc.exists_no_uniform_score_bound_of_phases_one` packages the same fact in the
  existential shape of `Arlib.GaussianCooling.hterm_not_dischargeable`.
* **Open for a `K`-dependent phase count.**  The blanket claim at `CVInstantiate.lean:630-633`
  — that *no* witness with `m ≥ 1` exists — is **not** established by the above and is
  plausibly false: `phases` is caller data indexed by `K`, and a caller taking
  `phases K ε p ≈ n·log(Rad K)` could in principle keep every chain ratio below a fixed
  constant, at which point a uniform `B` would exist.  Constructing such a schedule and
  proving the ratio bound *is* the Cousins–Vempala annealing analysis and is not attempted
  here.  Stated plainly so the docstring's claim is not read as proved in full.
* **Moot.**  By §1(a) a uniform `B` was never needed.  §3 is the repair.

## 3.  The repair

`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanGuardedBound` is
`cousinsVempalaOfRunsApproxMean` with

    (B : ℝ)                                        ↦  (B : Set (Space n) → ℝ → ℝ → ℝ)
    (hgb : ∀ K ε p j i x, |g K ε p j i x| ≤ B)     ↦  hgb guarded exactly as the other
                                                       per-`K` binders are, at `B K ε p`

and *everything else identical*: same coin space `Arlib.Probability.NatRunSpace E`, same
coin law `Arlib.Probability.natRunMeasure ν`, same median selector, same schedule data, same
hard-wired accuracy split, same `hphase_mean` and `hphase_var` binders character for
character, hence the same `VolumeAlgorithm n` guarantee.  It is built by applying
`Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean` directly (one level below the constructor
it repairs), because that is where `hprodLp` lives; `hprodLp` is discharged by
`Arlib.Probability.memLp_two_natRunProd` in both branches of a case split on the guard —
with `B K ε p` under it and with `0` off it.

The `K`-dependent shape is exactly the shape of the score's natural bound
`e^{R²/(2σᵢ²)}` (`Arlib.GaussianCooling.coolRatio_le_exp`,
`Arlib.GaussianCooling.phaseScore_le`), which depends on `K` through the radius `R` and can
therefore never be a single `B : ℝ`.

## 4.  What this buys, concretely

`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanGuardedBoundWitnessOnePhase` is a
witness of the repaired bundle at **`phases ≡ 1`** — a non-degenerate phase count, which
§2's refutation shows the *unrepaired* constructor cannot have at a constant schedule.  So
the repair is not cosmetic: it strictly enlarges the set of instantiable data.

## 5.  Hypotheses carried unproved

The repaired constructor assumes exactly what the base one assumes, minus the false
uniformity: `hσ`, `hg`, the guarded `hgb`, `hphase_mean` and `hphase_var`.  Nothing here
produces a sampler, a mixing bound, a phase count or a running time.  The refutation
theorems assume nothing beyond their explicitly listed binders.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open Arlib.GaussianCooling (IsMedian)

/-! ## 1.  The admissibility guard, as a predicate -/

/-- **The guard the `VolumeAlgorithm` contract is stated under.**  Literally the conjunction
of the six side conditions of `Ttc.VolumeAlgorithm.correct` (`Ttc/Volume/Oracle.lean:91-93`)
and of every per-`K` binder of `Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean` except
`hprodLp`. -/
def CVGuard {n : ℕ} (K : Set (Space n)) (ε p : ℝ) : Prop :=
  0 < ε ∧ 0 < p ∧ p < 1 ∧ Convex ℝ K ∧ Metric.ball (0 : Space n) 1 ⊆ K ∧ volume K ≠ ⊤

/-! ## 2.  The clamped score

`hprodLp` is unguarded (`Ttc/Volume/CousinsVempala.lean:2079`) though both of its consumers
have the guard in scope (`:2013`, `:2132`).  Clamping the score to `0` off the guard makes
the unguarded obligation provable from a guarded bound and changes nothing under the guard,
where `VolumeAlgorithm.correct` alone claims anything. -/

open scoped Classical in
/-- The score `g`, clamped to `0` on inputs that fail `Ttc.CVGuard`. -/
noncomputable def clampScore {n : ℕ} {E : Type} (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ)
    (K : Set (Space n)) (ε p : ℝ) (j i : ℕ) (x : E) : ℝ :=
  if CVGuard K ε p then g K ε p j i x else 0

section Clamp

variable {n : ℕ} {E : Type}

open scoped Classical in
/-- Under the guard the clamped score *is* the score, as a function. -/
theorem clampScore_of_guard {g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ}
    {K : Set (Space n)} {ε p : ℝ} (h : CVGuard K ε p) (j i : ℕ) :
    clampScore g K ε p j i = g K ε p j i := by
  funext x; simp [clampScore, h]

open scoped Classical in
/-- Off the guard the clamped score is the zero function. -/
theorem clampScore_of_not_guard {g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ}
    {K : Set (Space n)} {ε p : ℝ} (h : ¬ CVGuard K ε p) (j i : ℕ) :
    clampScore g K ε p j i = fun _ => (0 : ℝ) := by
  funext x; simp [clampScore, h]

open scoped Classical in
/-- Clamping preserves measurability: the test does not depend on the argument. -/
theorem measurable_clampScore [MeasurableSpace E]
    {g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ} {K : Set (Space n)} {ε p : ℝ}
    (hg : ∀ j i, Measurable (g K ε p j i)) (j i : ℕ) :
    Measurable (clampScore g K ε p j i) := by
  by_cases h : CVGuard K ε p
  · rw [clampScore_of_guard h]; exact hg j i
  · rw [clampScore_of_not_guard h]; exact measurable_const

/-- **The unguarded `L²` obligation, from a guarded `K`-dependent bound.**  This is the one
step the base constructor's uniform `B` was there to supply, and it needs neither
uniformity in `K` nor a `K`-guarded `hprodLp`: at each `K` the clamped score is bounded —
by `B K ε p` under the guard, by `0` off it — and `Arlib.Probability.memLp_two_natRunProd`
takes its bound implicitly, so it accepts a different one at each `K`. -/
theorem memLp_two_clampScore [MeasurableSpace E] (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)]
    {g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ} {B : Set (Space n) → ℝ → ℝ → ℝ}
    {K : Set (Space n)} {ε p : ℝ} (hg : ∀ j i, Measurable (g K ε p j i))
    (hgb : CVGuard K ε p → ∀ j i x, |g K ε p j i x| ≤ B K ε p) (j m : ℕ) :
    MemLp (fun ω => ∏ i : Fin m,
        Arlib.Probability.natScore (clampScore g K ε p) j (i : ℕ) ω) 2
      (Arlib.Probability.natRunMeasure ν) := by
  by_cases h : CVGuard K ε p
  · refine Arlib.Probability.memLp_two_natRunProd ν (measurable_clampScore hg)
      (B := B K ε p) (fun j' i' x => ?_) j m
    rw [clampScore_of_guard h]
    exact hgb h j' i' x
  · refine Arlib.Probability.memLp_two_natRunProd ν (measurable_clampScore hg)
      (B := 0) (fun j' i' x => ?_) j m
    rw [clampScore_of_not_guard h]
    simp

end Clamp

/-! ## 3.  The refutation: at a constant phase count there is no uniform bound

`Ttc/Volume/CVInstantiate.lean:630-633` asserts that a witness of
`cousinsVempalaOfRunsApproxMean` with `m ≥ 1` is unavailable "because `hgb` asks for a
**uniform** bound on the score while the chain ratio `chain(i+1)/chain(i)` is unbounded over
the bodies `K` the hypotheses range over".  This section makes that argument
machine-checked at the constant phase count `1`. -/

section Refutation

open Metric

/-- `EuclideanSpace ℝ (Fin n)` is nontrivial in dimension `≥ 1`. -/
theorem nontrivial_space {n : ℕ} (hn : 1 ≤ n) : Nontrivial (Space n) := by
  refine Module.nontrivial_of_finrank_pos (R := ℝ) ?_
  simpa [finrank_euclideanSpace_fin] using hn

/-- The volume of a ball of radius `R ≥ 0`, in units of the unit ball. -/
theorem volume_ball_toReal (n : ℕ) (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R) :
    (volume (ball (0 : Space n) R)).toReal
      = R ^ n * (volume (ball (0 : Space n) 1)).toReal := by
  haveI := nontrivial_space hn
  rw [Measure.addHaar_ball volume (0 : Space n) hR, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp

/-- **Admissible bodies have unbounded volume** (in dimension `≥ 1`): for every `M` there is
a convex `K` containing the unit ball, of finite volume, with `Vol(K) > M`.  Balls of large
radius do it. -/
theorem exists_admissible_volume_gt (n : ℕ) (hn : 1 ≤ n) (M : ℝ) :
    ∃ K : Set (Space n), Convex ℝ K ∧ ball (0 : Space n) 1 ⊆ K ∧ volume K ≠ ⊤ ∧
      M < (volume K).toReal := by
  set V1 := (volume (ball (0 : Space n) 1)).toReal with hV1def
  have hV1 : 0 < V1 :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  refine ⟨ball (0 : Space n) (max 1 (M / V1 + 1)), convex_ball _ _,
    ball_subset_ball (le_max_left _ _), measure_ball_lt_top.ne, ?_⟩
  have hR1 : (1 : ℝ) ≤ max 1 (M / V1 + 1) := le_max_left _ _
  have hR0 : (0 : ℝ) ≤ max 1 (M / V1 + 1) := by linarith
  rw [volume_ball_toReal n hn hR0]
  have hpow : max 1 (M / V1 + 1) ≤ (max 1 (M / V1 + 1)) ^ n :=
    calc max 1 (M / V1 + 1) = (max 1 (M / V1 + 1)) ^ 1 := (pow_one _).symm
      _ ≤ (max 1 (M / V1 + 1)) ^ n := pow_le_pow_right₀ hR1 hn
  have hgt : M / V1 < max 1 (M / V1 + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hMeq : M = M / V1 * V1 := by field_simp
  nlinarith

/-- **The uniform-bound binder `hgb` is FALSE at a constant phase count.**

The binders `hg`, `hgb`, `hphase_mean` are those of
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean` (`Ttc/Volume/CVInstantiate.lean:467`,
`:468`, `:470-475`), copied character for character, with `phases` pinned to the constant `1`
and `σsq` to the constant `s > 0`.  They are jointly **unsatisfiable**, in every dimension
`n ≥ 1` and at every admissible `(ε, p)`.

The mechanism, exactly the one `CVInstantiate.lean:630-633` conjectures:
`Arlib.GaussianCooling.chain 1 σsq K 1 = Vol(K)` (`chain_end`) is unbounded over admissible
bodies, while `Arlib.GaussianCooling.chain_zero_le` caps the cold endpoint at the
`K`-independent constant `(2πs)^{n/2}`.  So the phase ratio is unbounded; `hphase_mean` pins
the score's mean to within a relative `ε/(2(2+ε)) < 1/2` of it; and `hgb` caps that same
mean by `B`.

**Scope.**  This refutes uniformity at a *constant* phase count.  It does **not** refute the
blanket claim for a `K`-dependent `phases` — see §2 of the module docstring; that remains
open, and is plausibly false. -/
theorem no_uniform_score_bound_of_phases_one (n : ℕ) (hn : 1 ≤ n) (E : Type)
    [MeasurableSpace E] (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    (phases : Set (Space n) → ℝ → ℝ → ℕ) (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (s : ℝ) (hs : 0 < s)
    (hphases : ∀ K ε p, phases K ε p = 1)
    (hconst : ∀ K ε p j, σsq K ε p j = s)
    (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ) (B : ℝ)
    (hg : ∀ K ε p j i, Measurable (g K ε p j i))
    (hgb : ∀ K ε p j i x, |g K ε p j i x| ≤ B)
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) ∈
        relErr (ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
          (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
            Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)))
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) : False := by
  -- pin the two schedule functions, so nothing below depends on `phases` or `σsq`
  have hpf : phases = fun _ _ _ => 1 := by funext K ε p; exact hphases K ε p
  have hsf : σsq = fun _ _ _ _ => s := by funext K ε p j; exact hconst K ε p j
  subst hpf
  subst hsf
  -- the two `K`-independent constants
  set Cs := (2 * Real.pi * s) ^ ((n : ℝ) / 2) with hCsdef
  have hCspos : 0 < Cs := Real.rpow_pos_of_pos (by positivity) _
  set η := ε / (2 * (2 + ε)) with hηdef
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  have hη1 : η < 1 := by rw [hηdef, div_lt_one (by positivity)]; linarith
  -- a body whose volume exceeds everything the two constants allow
  obtain ⟨K, hconv, hball, hfin, hVM⟩ :=
    exists_admissible_volume_gt n hn (max 0 B * Cs / (1 - η))
  have hσpos : ∀ j, 0 < (fun _ : ℕ => s) j := fun _ => hs
  -- the two ends of the one-phase chain
  have hc0pos : 0 < Arlib.GaussianCooling.chain 1 (fun _ : ℕ => s) K 0 :=
    Arlib.GaussianCooling.chain_pos hσpos hball hfin 0
  have hc0le : Arlib.GaussianCooling.chain 1 (fun _ : ℕ => s) K 0 ≤ Cs :=
    Arlib.GaussianCooling.chain_zero_le one_pos hs K
  have hc1 : Arlib.GaussianCooling.chain 1 (fun _ : ℕ => s) K 1 = (volume K).toReal :=
    Arlib.GaussianCooling.chain_end 1 (fun _ : ℕ => s) K
  -- the mean of the (only) phase score is pinned near the (unbounded) chain ratio
  have hmem := hphase_mean K ε p hε hp hp1 hconv hball hfin 0
    (⟨0, by norm_num⟩ : Fin 1)
  simp only [Nat.cast_one, mul_one, hc1, relErr, Set.mem_Icc, Fin.val_mk,
    zero_add] at hmem
  -- ... and is at most `B`, because `|g| ≤ B`
  have hint : Integrable (g K ε p 0 0) (ν 0 0) :=
    (memLp_top_of_bound (hg K ε p 0 0).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hgb K ε p 0 0 x)).integrable le_top
  have hB : ∫ x, g K ε p 0 0 x ∂(ν 0 0) ≤ B := by
    have h := integral_mono hint (integrable_const B)
      fun x => le_of_abs_le (hgb K ε p 0 0 x)
    simpa using h
  -- combine: `(1 − η)·Vol(K)/chain₀ ≤ B`, so `Vol(K) ≤ max 0 B · Cs /(1 − η)`
  have hstep : (1 - η) * ((volume K).toReal
      / Arlib.GaussianCooling.chain 1 (fun _ : ℕ => s) K 0) ≤ B := le_trans hmem.1 hB
  have hdiv : (volume K).toReal / Arlib.GaussianCooling.chain 1 (fun _ : ℕ => s) K 0
      * Arlib.GaussianCooling.chain 1 (fun _ : ℕ => s) K 0 = (volume K).toReal :=
    div_mul_cancel₀ _ hc0pos.ne'
  have hmul := mul_le_mul_of_nonneg_right hstep hc0pos.le
  have h1 : (1 - η) * (volume K).toReal
      ≤ B * Arlib.GaussianCooling.chain 1 (fun _ : ℕ => s) K 0 := by nlinarith
  have hBmax : B ≤ max 0 B := le_max_right _ _
  have hmax0 : (0 : ℝ) ≤ max 0 B := le_max_left _ _
  have h2 : (1 - η) * (volume K).toReal ≤ max 0 B * Cs := by nlinarith
  have h3 : (volume K).toReal ≤ max 0 B * Cs / (1 - η) :=
    (le_div_iff₀ (by linarith)).2 (by linarith)
  linarith

/-- **The same finding, in the existential shape of
`Arlib.GaussianCooling.hterm_not_dischargeable`**: at the constant one-phase schedule there
is *no* pair `(g, B)` satisfying the `hg`, `hgb` and `hphase_mean` binders of
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`. -/
theorem exists_no_uniform_score_bound_of_phases_one (n : ℕ) (hn : 1 ≤ n) (E : Type)
    [MeasurableSpace E] (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    (s : ℝ) (hs : 0 < s) (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) :
    ¬ ∃ (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ) (B : ℝ),
        (∀ K ε p j i, Measurable (g K ε p j i)) ∧
        (∀ K ε p j i x, |g K ε p j i x| ≤ B) ∧
        (∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
          Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
          ∀ j (i : Fin ((fun (_ : Set (Space n)) (_ _ : ℝ) => 1) K ε p)),
          ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) ∈
            relErr (ε / (2 * (2 + ε) *
                (((fun (_ : Set (Space n)) (_ _ : ℝ) => 1) K ε p : ℕ) : ℝ)))
              (Arlib.GaussianCooling.chain ((fun (_ : Set (Space n)) (_ _ : ℝ) => 1) K ε p)
                  ((fun (_ : Set (Space n)) (_ _ : ℝ) (_ : ℕ) => s) K ε p) K ((i : ℕ) + 1) /
                Arlib.GaussianCooling.chain ((fun (_ : Set (Space n)) (_ _ : ℝ) => 1) K ε p)
                  ((fun (_ : Set (Space n)) (_ _ : ℝ) (_ : ℕ) => s) K ε p) K (i : ℕ))) := by
  rintro ⟨g, B, hg, hgb, hmean⟩
  exact no_uniform_score_bound_of_phases_one n hn E ν _ _ s hs
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) g B hg hgb hmean ε p hε hp hp1

end Refutation

/-! ## 4.  The repaired constructor -/

/-- **`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean` with `hgb` `K`-dependent and
guarded.**

Binder diff against `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`
(`Ttc/Volume/CVInstantiate.lean:458`) — *two* lines change and nothing else:

| | base | here |
| --- | --- | --- |
| the bound | `(B : ℝ)` | `(B : Set (Space n) → ℝ → ℝ → ℝ)` |
| `hgb` | `∀ K ε p j i x, \|g K ε p j i x\| ≤ B` | guarded exactly as `hphase_mean` is, at `B K ε p` |

`n`, `E`, `ν` (+ its instance), `phases`, `σsq`, `g`, `hσ`, `hg`, `hphase_mean` and
`hphase_var` are unchanged, character for character.  The coin space
(`Arlib.Probability.NatRunSpace E`), the coin law (`Arlib.Probability.natRunMeasure ν`), the
schedule (`Arlib.GaussianCooling.reps`, `Arlib.GaussianCooling.varBudget (ε/2)`), the
hard-wired accuracy split (`ε/2`, `ε/(2+ε)`, `ε/(2(2+ε)m)`), the cooling chain, the median
selector and every one of the fourteen discharges are those of the base constructor, taken
from the same `Arlib` theorems.  So the `VolumeAlgorithm n` produced satisfies the same
`correct` field, proved the same way.

**Why the base constructor asked for more than it needed** — see §1 of the module
docstring.  Two independent points: `Arlib.Probability.memLp_two_natRunProd` takes its bound
implicitly and is applied at one fixed `K`, so `K`-dependence costs nothing; and the
unguardedness of `hprodLp` (`Ttc/Volume/CousinsVempala.lean:2079`) is worked around by
scoring `Ttc.clampScore g` rather than `g` — identical to `g` under the guard
(`Ttc.clampScore_of_guard`), and `Ttc.VolumeAlgorithm.correct` claims nothing off it.

**The estimator differs from the base one only off the guard.**  For admissible `(K, ε, p)`
the run is `chain … 0 · ∏ᵢ g K ε p j i (ω j i)`, the base expression verbatim; for
inadmissible `(K, ε, p)` the base constructor's run is whatever `g` happens to give and this
one's is `chain … 0 · 0^m`.  Neither is constrained by `VolumeAlgorithm.correct`.

**Carried unproved**: `hσ`, `hg`, `hgb`, `hphase_mean`, `hphase_var` — precisely the base
constructor's residual debt, minus the uniformity that §2 refutes at a constant phase
count. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanGuardedBound
    (n : ℕ) (E : Type) [MeasurableSpace E] (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)]
    -- the schedule data the caller picks (unchanged)
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    -- the score family (unchanged) and ★ the now `K`-dependent bound
    (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ) (B : Set (Space n) → ℝ → ℝ → ℝ)
    -- side conditions on that data (NOT among the fourteen)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hg : ∀ K ε p j i, Measurable (g K ε p j i))
    -- ★ `hgb`, guarded exactly as the two sampler binders are, at a `K`-dependent bound
    (hgb : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j i x,
      |g K ε p j i x| ≤ B K ε p)
    -- the two remaining hypotheses, both about the sampler (unchanged)
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) ∈
        relErr (ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
          (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
            Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)))
    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + Arlib.GaussianCooling.varBudget (ε / 2) / (phases K ε p : ℝ)) *
            (∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ))) ^ 2) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfApproxMean n (Arlib.Probability.NatRunSpace E)
    (Arlib.Probability.natRunMeasure ν) phases
    Arlib.GaussianCooling.reps
    (fun ε => Arlib.GaussianCooling.varBudget (ε / 2))
    (fun ε => ε / 2)
    (fun ε => ε / (2 + ε))
    (fun K ε p => ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
    (fun K ε p i => Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K i)
    -- `W`: the *clamped* phase score reads the coordinate of its own (run, phase) pair
    (fun K ε p => Arlib.Probability.natScore (clampScore g K ε p))
    -- `med`: the explicit measurable median selector of the `reps ε p` run products
    (fun K ε p ω => Arlib.Probability.medianSel
      fun j : Fin (Arlib.GaussianCooling.reps ε p) =>
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K 0 *
          ∏ i : Fin (phases K ε p),
            Arlib.Probability.natScore (clampScore g K ε p) (j : ℕ) (i : ℕ) ω)
    -- hreps_pos, hreps : from `Arlib/…/Schedule.lean`
    Arlib.GaussianCooling.reps_pos
    Arlib.GaussianCooling.reps_spec
    -- hbudget0 : the budget is taken at the *inner* accuracy `ε/2`
    (fun ε hε => Arlib.GaussianCooling.varBudget_nonneg (ε / 2) (by linarith))
    -- hinner_pos
    (fun ε hε => by linarith)
    -- hbias_nonneg
    (fun K ε p hε => by
      have h2 : (0 : ℝ) ≤ 2 + ε := by linarith
      have hm : (0 : ℝ) ≤ (phases K ε p : ℝ) := Nat.cast_nonneg _
      exact div_nonneg hε.le (by nlinarith))
    -- hmean_nonneg
    (fun ε hε => div_nonneg hε.le (by linarith))
    -- hmean_lt_one
    (fun ε hε => by rw [div_lt_one (by linarith)]; linarith)
    -- hphaseBudget : `2·m·phaseBias = meanBias` when `m > 0`, and `0 ≤ meanBias` when `m = 0`
    (fun K ε p hε => by
      have h2 : (0 : ℝ) < 2 + ε := by linarith
      rcases Nat.eq_zero_or_pos (phases K ε p) with h0 | hp
      · rw [h0]
        simp only [Nat.cast_zero, mul_zero, zero_mul]
        exact div_nonneg hε.le h2.le
      · have hm : ((phases K ε p : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
        have key : 2 * ((phases K ε p : ℝ)) * (ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
            = ε / (2 + ε) := by
          field_simp
        exact key.le)
    -- hcompose : the split meets the composition with equality
    (fun ε hε => by
      have h2 : (2 : ℝ) + ε ≠ 0 := by positivity
      have key : ε / 2 + ε / (2 + ε) + ε / 2 * (ε / (2 + ε)) = ε := by
        field_simp
        ring
      exact key.le)
    -- hbudget : `varBudget_spec` at the inner accuracy
    (fun ε hε => Arlib.GaussianCooling.varBudget_spec (ε / 2) (by linarith))
    -- hW_meas
    (fun K ε p => Arlib.Probability.measurable_natScore (measurable_clampScore (hg K ε p)))
    -- hmed_meas
    (fun K ε p =>
      Arlib.Probability.measurable_medianSel_natRuns (measurable_clampScore (hg K ε p)) _ _ _)
    -- hmed
    (fun K ε p ω =>
      Arlib.Probability.isMedian_medianSel_natRuns (clampScore g K ε p) _ _ _ ω)
    -- hindep_runs
    (fun K ε p =>
      Arlib.Probability.iIndepFun_natRuns ν (measurable_clampScore (hg K ε p)) _ _ _)
    -- ★ hprodLp : the unguarded `L²` obligation, from the guarded `K`-dependent bound
    (fun K ε p j =>
      memLp_two_clampScore ν (hg K ε p)
        (fun h => hgb K ε p h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) j _)
    -- hchain_pos, hchain_end : from `Arlib/…/Chain.lean`
    (fun K ε p _hε _hp _hp1 _hconv hball hfin i =>
      Arlib.GaussianCooling.chain_pos (hσ K ε p) hball hfin i)
    (fun K ε p _hε _hp _hp1 _hconv _hball _hfin =>
      Arlib.GaussianCooling.chain_end (phases K ε p) (σsq K ε p) K)
    -- hphase_indep
    (fun K ε p _ _ _ _ _ _ j =>
      Arlib.Probability.iIndepFun_natScore_phases ν (measurable_clampScore (hg K ε p)) j _)
    -- hphase_mean : transferred to the coordinate law, then unclamped by the guard
    (fun K ε p hε hp hp1 hconv hball hfin j i => by
      have hguard : CVGuard K ε p := ⟨hε, hp, hp1, hconv, hball, hfin⟩
      have hmean : ∫ ω, Arlib.Probability.natScore (clampScore g K ε p) j (i : ℕ) ω
            ∂(Arlib.Probability.natRunMeasure ν)
          = ∫ x, clampScore g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) :=
        integral_natRunCoord ν j (i : ℕ) (measurable_clampScore (hg K ε p) j (i : ℕ))
      rw [hmean, clampScore_of_guard hguard]
      exact hphase_mean K ε p hε hp hp1 hconv hball hfin j i)
    -- hphase_var : same transfer, on both the second moment and the mean
    (fun K ε p hε hp hp1 hconv hball hfin j i => by
      have hguard : CVGuard K ε p := ⟨hε, hp, hp1, hconv, hball, hfin⟩
      have hsq : ∫ ω, (Arlib.Probability.natScore (clampScore g K ε p) j (i : ℕ) ω) ^ 2
            ∂(Arlib.Probability.natRunMeasure ν)
          = ∫ x, (clampScore g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ)) :=
        integral_natRunCoord ν j (i : ℕ)
          ((measurable_clampScore (hg K ε p) j (i : ℕ)).pow_const 2)
      have hmean : ∫ ω, Arlib.Probability.natScore (clampScore g K ε p) j (i : ℕ) ω
            ∂(Arlib.Probability.natRunMeasure ν)
          = ∫ x, clampScore g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) :=
        integral_natRunCoord ν j (i : ℕ) (measurable_clampScore (hg K ε p) j (i : ℕ))
      rw [hsq, hmean, clampScore_of_guard hguard]
      exact hphase_var K ε p hε hp hp1 hconv hball hfin j i)

end Ttc

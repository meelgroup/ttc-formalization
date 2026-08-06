/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# `Model/VolOracle`: `Vol_ED`'s contract, stated as Cousins–Vempala Theorem 1.1

`Ttc.Oracles.vol` is the `Vol_ED(P(cᵢ), ε', δ')` call of `alg:ttc` line 24. In
`Ttc.TtcProb` its guarantee is currently the single field

```
volED_hi : ∀ i ∈ toDNF φ, vol i ≤ (1 + P.epsPrime) * (volume (region M i)).toReal
```

which is **deterministic** — it asserts the bound at every `ω`, i.e. that `Vol_ED`
never fails — and so is strictly stronger than what any randomized volume
algorithm delivers.

This file replaces that ad-hoc inequality with the published contract it is
supposed to be an instance of:

> **Theorem 1.1** (Cousins–Vempala, `vol3_journal.tex:144`). There is an
> algorithm that, for any `ε > 0`, `p > 0` and convex body `K` in `ℝⁿ` that
> contains the unit ball and has `E_K(‖X‖²) = O(n)`, with probability `1 − p`,
> approximates the volume of `K` within relative error `ε`.

`Ttc.VolumeAlgorithm` is that statement. Nothing here proves it — the
gaussian-cooling development formalizes the variance bound of §5.1 that licenses
the cooling schedule, not the algorithm — so this is an *interface* in the sense
of `CLAUDE.md` §1: the hypothesis bundle a future formalization instantiates.

**What this buys.** The residual assumption behind `Vol_ED` becomes exactly one
named published theorem, readable against the paper line by line, rather than a
bespoke deterministic inequality. `Ttc.VolumeAlgorithm.exact` witnesses
non-vacuity (`CLAUDE.md` §11), and `Ttc.VolumeAlgorithm.upper` extracts precisely
the half of the conclusion `volED_hi` consumes.

**Modelling notes.**

*The second-moment hypothesis is omitted from `correct`.* Theorem 1.1 states
`E_K(‖X‖²) = O(n)`, but that hypothesis governs the *complexity*, not the
accuracy: `vol3_journal.tex:152` gives the complexity for a general
`E_K(‖X‖²) = R²`, with the same `1 − p` accuracy conclusion. Since only accuracy
is consumed here, assuming it would weaken the interface for no gain. Complexity
is out of scope for this development (`Ttc/Runtime.lean`).

*`K` must contain the unit ball at the origin.* That is Theorem 1.1's hypothesis
verbatim, and it is **not** what `Ttc.TtcProb` supplies: `ball_subset` gives a
ball of radius `γ̂` about `cen i`. `Ttc.VolumeAlgorithm.of_ball` bridges the gap
by scaling, and is where that discrepancy is discharged rather than hidden.
-/

namespace Ttc

open MeasureTheory Set Pointwise

/-- **Cousins–Vempala, Theorem 1.1** (`vol3_journal.tex:144`), as the contract
`Vol_ED` is called under.

`est K ε p ω` is the number the algorithm returns on body `K` at accuracy `ε` and
confidence `p`, when its coins read `ω`. `correct` is the theorem: outside a set
of measure `p`, that number lies in `(1 ± ε)·Vol(K)`.

This is an assumption, not a theorem — see the file docstring. -/
structure VolumeAlgorithm (n : ℕ) where
  /-- The probability space the algorithm's own coins live on. -/
  Ω : Type
  /-- Its σ-algebra. -/
  mΩ : MeasurableSpace Ω
  /-- The law of the coins. -/
  μ : @MeasureTheory.Measure Ω mΩ
  /-- It is a probability measure. -/
  isProb : @MeasureTheory.IsProbabilityMeasure Ω mΩ μ
  /-- The estimate returned on `K` at accuracy `ε`, confidence `p`, coins `ω`. -/
  est : Set (Space n) → ℝ → ℝ → Ω → ℝ
  /-- **The guarantee.** With probability at least `1 − p`, the estimate lies
  within relative error `ε` of `Vol(K)`, for every convex `K` of finite volume
  containing the unit ball. -/
  correct : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 →
      Convex ℝ K → Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      1 - p ≤ (μ {ω | est K ε p ω ∈ relErr ε (volume K).toReal}).toReal

namespace VolumeAlgorithm

variable {n : ℕ}

/-- **Non-vacuity** (`CLAUDE.md` §11). The exact oracle — one that returns
`Vol(K)` on the nose and never fails — is a `Ttc.VolumeAlgorithm`. So the
interface is inhabited, and any theorem quantified over it is not vacuous.

This is the `ε = 0`, `p = 0` corner of the contract: it satisfies the guarantee
for *every* `ε, p`, so it witnesses the structure without witnessing that the
algorithm of the paper exists. -/
noncomputable def exact (n : ℕ) : VolumeAlgorithm n where
  Ω := Unit
  mΩ := inferInstance
  μ := Measure.dirac ()
  isProb := inferInstance
  est K _ _ _ := (volume K).toReal
  correct := by
    intro K ε p hε hp _ _ _ _
    have hb : (0 : ℝ) ≤ (volume K).toReal := ENNReal.toReal_nonneg
    have hmem : (volume K).toReal ∈ relErr ε (volume K).toReal := by
      simp only [relErr, Set.mem_Icc]
      constructor <;> nlinarith
    have hset : {_ω : Unit | (volume K).toReal ∈ relErr ε (volume K).toReal}
        = (univ : Set Unit) := by
      ext _; simp [hmem]
    rw [hset, measure_univ, ENNReal.toReal_one]
    linarith

/-- **The half `volED_hi` consumes.** On the good event, the estimate does not
exceed `(1 + ε)·Vol(K)`.

`Ttc.TtcProb.volED_hi` asserts exactly this inequality — but at *every* `ω`,
with no good event. That is the shape mismatch the file docstring describes: a
randomized algorithm supplies it only on a set of measure `1 − p`. -/
theorem upper {ε b x : ℝ} (h : x ∈ relErr ε b) : x ≤ (1 + ε) * b := h.2

/-- **The lower half**, which feeds the paper's Invariant (`theta_lo`). -/
theorem lower {ε b x : ℝ} (h : x ∈ relErr ε b) : (1 - ε) * b ≤ x := h.1

end VolumeAlgorithm

/-! ## The rounding bridge

Theorem 1.1 requires `K ⊇ B(0,1)`. `Ttc.TtcProb` supplies
`ball_subset : Metric.ball (cen i) gammaHat ⊆ region M i`
(`Model/ProblemSetting.lean:112`) — an inscribed ball of radius `γ̂` about a
centre that is *not* the origin. This section closes that gap rather than
assuming it away: `Ttc.roundBody` is the affine change of variable
`y ↦ γ⁻¹ · (y − c)` carrying the inscribed ball to the unit ball, and the four
lemmas below discharge Theorem 1.1's hypotheses for its image and transport the
conclusion back.

The paper's own preprocessing (`vol3_journal.tex:145`, "contains the unit ball")
is exactly this normalisation; here it is a theorem, not a hypothesis. -/

/-- `K` moved so that its inscribed ball becomes the unit ball at the origin:
the image of `K` under `y ↦ γ⁻¹ · (y − c)`. -/
noncomputable def roundBody {n : ℕ} (c : Space n) (γ : ℝ) (K : Set (Space n)) :
    Set (Space n) := γ⁻¹ • ((-c) +ᵥ K)

variable {n : ℕ} {c : Space n} {γ : ℝ} {K : Set (Space n)}

/-- **Theorem 1.1's containment hypothesis, discharged.** If `K` has an inscribed
ball of radius `γ` about `c`, its normalisation contains the unit ball. -/
theorem ball_subset_roundBody (hγ : 0 < γ) (h : Metric.ball c γ ⊆ K) :
    Metric.ball (0 : Space n) 1 ⊆ roundBody c γ K := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  have hγ0 : γ⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hγ)
  rw [roundBody, Set.mem_smul_set_iff_inv_smul_mem₀ hγ0, inv_inv]
  have hmem : γ • x + c ∈ K := by
    apply h
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [norm_smul, abs_of_pos hγ] using (mul_lt_of_lt_one_right hγ hx)
  refine ⟨γ • x + c, hmem, ?_⟩
  simp [vadd_eq_add]

/-- **Theorem 1.1's convexity hypothesis, discharged.** Normalisation is affine,
so it preserves convexity. -/
theorem convex_roundBody (h : Convex ℝ K) : Convex ℝ (roundBody c γ K) :=
  (h.vadd (-c)).smul γ⁻¹

/-- **How normalisation scales volume**: by `γ⁻ⁿ`, the Jacobian of `y ↦ γ⁻¹·(y−c)`.
Translation is Haar-invariant, so only the dilation contributes. -/
theorem volume_roundBody (hγ : 0 < γ) :
    volume (roundBody c γ K) = ENNReal.ofReal (γ⁻¹ ^ n) * volume K := by
  rw [roundBody, Measure.addHaar_smul_of_nonneg volume (le_of_lt (inv_pos.mpr hγ)),
    finrank_euclideanSpace_fin, measure_vadd]

/-- **Theorem 1.1's finiteness hypothesis, discharged.** -/
theorem volume_roundBody_ne_top (hγ : 0 < γ) (hfin : volume K ≠ ⊤) :
    volume (roundBody c γ K) ≠ ⊤ := by
  rw [volume_roundBody hγ]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin

/-- The volume of `K` recovered from that of its normalisation. -/
theorem toReal_volume_eq (hγ : 0 < γ) :
    (volume K).toReal = γ ^ n * (volume (roundBody c γ K)).toReal := by
  rw [volume_roundBody hγ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hγ), one_pow, one_mul]

/-- **Relative error is scale-invariant** — the reason the bridge costs nothing in
accuracy. -/
theorem mem_relErr_smul {ε b y r : ℝ} (hr : 0 < r) :
    r * y ∈ relErr ε (r * b) ↔ y ∈ relErr ε b := by
  simp only [relErr, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- **The rounding bridge.** A `Ttc.VolumeAlgorithm` — which by Theorem 1.1 only
speaks about bodies containing the unit ball — yields a `(1 ± ε)` estimate of
`Vol(K)` for *any* convex `K` of finite volume with an inscribed ball of radius
`γ > 0` about any centre `c`, with the same confidence `1 − p`: run it on the
normalisation and multiply the answer by `γⁿ`.

This is precisely the shape `Ttc.TtcProb` needs, and every hypothesis is already
available there — **no new assumption is introduced**:

* `hγ` ← `hgammaHat` (`Model/ProblemSetting.lean:111`)
* `hball` ← `ball_subset` (`:114`)
* `hfin` ← `volume_ne_top` (`:116`)
* `hconv` ← `Ttc.convex_region` (`Lattice/Decomposition.lean:76`), which is
  **proved**, not assumed, from `M_eq` (`:64`) -/
theorem VolumeAlgorithm.of_ball (V : VolumeAlgorithm n) {ε p : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (hball : Metric.ball c γ ⊆ K) (hconv : Convex ℝ K) (hfin : volume K ≠ ⊤) :
    1 - p ≤ (V.μ {ω | γ ^ n * V.est (roundBody c γ K) ε p ω
      ∈ relErr ε (volume K).toReal}).toReal := by
  have hset : {ω | γ ^ n * V.est (roundBody c γ K) ε p ω ∈ relErr ε (volume K).toReal}
      = {ω | V.est (roundBody c γ K) ε p ω
          ∈ relErr ε (volume (roundBody c γ K)).toReal} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [toReal_volume_eq hγ]
    exact mem_relErr_smul (by positivity)
  rw [hset]
  exact V.correct _ ε p hε hp hp1 (convex_roundBody hconv)
    (ball_subset_roundBody hγ hball) (volume_roundBody_ne_top hγ hfin)

end Ttc

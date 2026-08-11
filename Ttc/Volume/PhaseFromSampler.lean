/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CousinsVempala
import Arlib.Probability.RejectionRounds

/-!
# `Volume/PhaseFromSampler`: producing a Gaussian phase law from a uniform sampler

Every other file in this development that mentions `Arlib.GaussianCooling.coolLaw` — the
exact phase-`i` law `∝ 1_K(x)·e^{−‖x‖²/(2σᵢ²)}` — **consumes** a total-variation bound to
it as a hypothesis. `Arlib/Convexity/GaussianCooling/PhaseVar.lean`,
`.../PhaseMean.lean`, `.../PhaseSchedule.lean` and
`Ttc.VolumeAlgorithm.cousinsVempalaOfSamplerCooling` (`Ttc/Volume/CousinsVempala.lean`)
all take `hTV : Arlib.TVLe (μ.map X) (coolLaw …) ε` as an input. **Nothing in the
committed tree produces one** (checked by grep over every `coolLaw` occurrence at the time
this file was written; work in flight elsewhere in `Arlib/MarkovChains/Continuous/` may
change that). This file produces one, by a route that is not Cousins–Vempala's.

## The construction

Propose a uniform point `x` of the body `K` together with an independent uniform coin
`u ∈ [0,1]`; **accept** when `u ≤ e^{−‖x‖²/(2σᵢ²)}`. Then

* `Ttc.GaussianRejection.map_fst_condOn_proposal` — the law of the accepted point **is**
  `coolLaw m σsq K i`. An identity of measures, not an approximation.
* `Ttc.GaussianRejection.proposal_acceptRegion` — a round is accepted with probability
  exactly `chain m σsq K i / Vol(K)`.
* `Ttc.GaussianRejection.integral_phaseScore_rejection` — hence `hphase_mean` holds **as
  the equality it is stated as**, `∫ W = chain (i+1) / chain i`.
* `Ttc.GaussianRejection.integral_phaseScore_sq_rejection` — and `hphase_var` holds at
  whatever constant the exact-law bound gives, with **no TV slack spent**.

and, for a sampler that is only *approximately* uniform — which is all this development
actually has —

* `Ttc.GaussianRejection.tvLe_prod_right` — total variation survives tensoring with the
  coin, with **no** loss of constant.
* `Ttc.GaussianRejection.tvLe_condOn` — conditioning on the acceptance event inflates
  total variation by at most `4/Pr[accept]` (hypothesis: `2e ≤ ν A`). Stated for an
  arbitrary measurable space and acceptance event; nothing about Gaussians in it.
* `Ttc.GaussianRejection.tvLe_map_fst_condOn_of_uniform` — **the composite.** A uniform
  sampler within total variation `η` of `Arlib.uniformOn volume K` yields, through the
  filter, a law within total variation

    `4·η·Vol(K) / chain m σsq K i`

  of `coolLaw m σsq K i`. This is the missing `hTV` producer, modulo the plumbing listed
  under "Residual" below.

## What this corrects

`Ttc/Volume/CVInstantiate.lean:75-83` says of `hphase_mean`: "No mixing bound can deliver
this … Closing it requires either a perfect sampler or restating §5.2 with an
approximately-unbiased score. **This is where the development actually stops.**" Two
corrections, both `file:line`-checkable:

1. The claim about *mixing* bounds is right and this file does not contradict it.
   Rejection is not a mixing bound. It gives the equality outright — the third option the
   sentence does not list.
2. "Where the development actually stops" is **stale**.
   `Ttc.VolumeAlgorithm.cousinsVempalaOfSamplerCooling`
   (`Ttc/Volume/CousinsVempala.lean:2511`) already derives `hphase_mean` (in the honest
   approximate form) and `hphase_var` from `hTV`, and its own docstring
   (`Ttc/Volume/CousinsVempala.lean:138-144`) says "`hTV` is still the only mathematical
   debt". `CVInstantiate`'s two residual binders are the pre-`ofSampler` picture.

## ⚠ The cost, quoted (`AUDIT.md` 5) — and why Cousins–Vempala do not do this

`Ttc.GaussianRejection.expected_rounds_le`: the expected number of uniform draws per
accepted point is at most

  `e^{R²/(2σᵢ²)}`,

with `R` the enclosing radius. At the **cold** end of a cooling schedule (`σᵢ² ≳ R²`) that
is `O(1)`. At the **hot** end — where Gaussian cooling starts, `σ₀² ≈ R²/n` or smaller —
it is `e^{Θ(n)}`: **exponential**. That is exactly why Cousins–Vempala §4 run a
Metropolis-filtered ball walk against the Gaussian instead
(`Arlib/MarkovChains/Continuous/MetropolisGaussian.lean` builds that kernel and proves it
reversible for the Gaussian-restricted measure; it supplies no conductance bound).

The **same** exponential appears as the TV inflation factor in
`tvLe_map_fst_condOn_of_uniform` — `Vol(K)/chain i ≤ e^{R²/(2σᵢ²)}`
(`exp_mul_volume_le_chain`) — so the route pays it twice over, once in time and once in
accuracy. That is the honest accounting for this bridge, and it is stated, not hidden.

**Nothing in this file bounds any running time, and nothing here may be quoted towards
`O*(n³)`.** For the standing reason, see `Ttc/Volume/CVEstimator.lean`, whose sample count
is `Θ(n·L⁴·log(1/p)/κ³)` — *worse* than the paper's — and
`Arlib/Convexity/GaussianCooling/Unblock.lean` (≈ line 591), whose isoperimetric constant
is doubly exponentially bad in `n`.

## Residual: what is still needed to *instantiate* `cousinsVempalaOfSamplerCooling`

The mathematics of the bridge is complete. What is **not** done here is the plumbing that
turns `tvLe_map_fst_condOn_of_uniform` into that construction's `hTV` field, which asks for
`Arlib.TVLe (μ.map (X K ε p j i)) (coolLaw … (interior K) i) (tvErr K ε p)` on a *single*
fixed coin space `Ω` and measure `μ` chosen before the input `(K, ε, p)` is seen
(`Ttc/Volume/CousinsVempala.lean:2561-2564`). Three concrete gaps:

1. **A single coin space — the one genuinely missing lemma.** The accepted point here lives on
   `condOn (μhat ⊗ coin) A`, a measure that depends on `K` and on the phase index. Moving
   to `Ω` fixed with a *sampling map* `X K ε p j i : Ω → Space n` needs the rounds-space
   construction: `Arlib.Probability.roundsMeasure` gives independent rounds and
   `Arlib.Probability.roundCountNat` the first accepted index, but **no lemma in
   `Arlib/Probability/RejectionRounds.lean` identifies the law of the first accepted draw
   with `condOn ν A`** — only round *counts* are proved there. That lemma is the missing
   link and is not proved in this file.
2. **`interior K` versus `K`.** `cousinsVempalaOfSamplerCooling` runs the whole pipeline on
   `interior K`; the uniform sampler `Ttc.HitAndRunTheorem11Input.at_steps` produces
   `Arlib.uniformOn volume K` for a *closed* `K`. This one is **routine**, not a gap:
   `Ttc.CV.volume_interior_eq` gives `volume (interior K) = volume K` for convex `K` (the
   frontier is null, `Convex.addHaar_frontier`), so the two restrictions agree and hence so
   do the two `uniformOn` measures. It is listed only because it has not been written down.
3. **The uniform sampler's own hypotheses.** `HitAndRunTheorem11Input.mixing` needs a warm
   start `sigma` with an `M`-domination bound and an exceptional set of mass `≤ eps/2`;
   producing one per phase is a separate construction.

None of these is claimed here.

## Honesty

No `sorry`, no new `axiom`, no `Prop`-valued definition that packages a conclusion as a
hypothesis. `acceptRegion` and `proposal` are explicit data; every other declaration is a
theorem proved outright. Nothing here is imported by `Ttc.lean`.
-/

namespace Ttc.GaussianRejection

open MeasureTheory Set Arlib Arlib.GaussianCooling
open scoped ENNReal

variable {n : ℕ}

/-- The **acceptance region** of the Gaussian rejection filter for phase `i`:
the pair `(x, u)` is accepted when the auxiliary uniform coin `u` falls below the phase
weight `coolWeight m σsq i x ∈ (0, 1]`. -/
def acceptRegion (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) : Set (EuclSpace n × ℝ) :=
  {q | q.2 ≤ coolWeight m σsq i q.1}

theorem measurableSet_acceptRegion (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) :
    MeasurableSet (acceptRegion (n := n) m σsq i) :=
  measurableSet_le measurable_snd
    ((continuous_coolWeight m σsq i).measurable.comp measurable_fst)

/-- The `x`-slice of the acceptance region over a point of `S`: the coin interval. -/
theorem slice_acceptRegion_of_mem (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) {S : Set (EuclSpace n)}
    {x : EuclSpace n} (hx : x ∈ S) :
    Prod.mk x ⁻¹' (Prod.fst ⁻¹' S ∩ acceptRegion m σsq i) = Iic (coolWeight m σsq i x) := by
  ext u; simp [acceptRegion, hx]

/-- The `x`-slice over a point outside `S` is empty. -/
theorem slice_acceptRegion_of_notMem (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) {S : Set (EuclSpace n)}
    {x : EuclSpace n} (hx : x ∉ S) :
    Prod.mk x ⁻¹' (Prod.fst ⁻¹' S ∩ acceptRegion m σsq i) = (∅ : Set ℝ) := by
  ext u; simp [acceptRegion, hx]

/-- The uniform coin gives the slice exactly the mass `coolWeight`. -/
theorem restrict_Icc_Iic_coolWeight {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : 0 < σsq i)
    (x : EuclSpace n) :
    (volume.restrict (Icc (0 : ℝ) 1)) (Iic (coolWeight m σsq i x))
      = ENNReal.ofReal (coolWeight m σsq i x) := by
  have h0 := (coolWeight_pos m σsq i x).le
  have h1 := coolWeight_le_one (m := m) hσ x
  rw [Measure.restrict_apply measurableSet_Iic,
    show Iic (coolWeight m σsq i x) ∩ Icc (0 : ℝ) 1 = Icc 0 (coolWeight m σsq i x) by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
      · rintro ⟨hu, hu0, _⟩; exact ⟨hu0, hu⟩
      · rintro ⟨hu0, hu⟩; exact ⟨hu, hu0, hu.trans h1⟩,
    Real.volume_Icc, sub_zero]

/-- **The crux computation.** Against the product of *any* proposal law `μK` on the body
with the uniform coin on `[0,1]`, the mass the acceptance region puts on the cylinder over
`S` is the `μK`-integral of the phase weight over `S`. Fubini for one slice. -/
theorem prod_apply_acceptRegion (μK : Measure (EuclSpace n)) [SFinite μK]
    {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : 0 < σsq i)
    {S : Set (EuclSpace n)} (hS : MeasurableSet S) :
    (μK.prod (volume.restrict (Icc (0 : ℝ) 1)))
        (Prod.fst ⁻¹' S ∩ acceptRegion m σsq i)
      = ∫⁻ x in S, ENNReal.ofReal (coolWeight m σsq i x) ∂μK := by
  rw [Measure.prod_apply ((measurable_fst hS).inter (measurableSet_acceptRegion m σsq i)),
    ← lintegral_indicator hS]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, slice_acceptRegion_of_mem m σsq i hx,
      restrict_Icc_Iic_coolWeight hσ]
  · rw [Set.indicator_of_notMem hx, slice_acceptRegion_of_notMem m σsq i hx,
      measure_empty]

/-! ## The rejection bridge: uniform proposal + Gaussian filter = the phase law -/

section Bridge

variable {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} {K : Set (EuclSpace n)}

/-- The **rejection proposal**: a uniform draw from the body `K`, together with an
independent uniform coin on `[0,1]`. This is exactly what a uniform sampler for `K` plus
one fresh fair random real supplies. -/
noncomputable def proposal (K : Set (EuclSpace n)) : Measure (EuclSpace n × ℝ) :=
  (Arlib.uniformOn volume K).prod (volume.restrict (Icc (0 : ℝ) 1))

instance : SFinite (Arlib.uniformOn volume K) := by
  rw [Arlib.uniformOn, condOn_def]; infer_instance

/-- The auxiliary coin really is uniform on `[0,1]`: `volume (Icc 0 1) = 1`. -/
instance instIsProbabilityMeasureCoin :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [← Arlib.uniformOn_unitInterval_eq_restrict]
  exact Arlib.isProbabilityMeasure_uniformOn_unitInterval

/-- The proposal mass of the accepted part of a cylinder over `S`. -/
theorem proposal_apply (hσ : 0 < σsq i) {S : Set (EuclSpace n)} (hS : MeasurableSet S) :
    proposal K (Prod.fst ⁻¹' S ∩ acceptRegion m σsq i)
      = (volume K)⁻¹ * ∫⁻ x in S ∩ K, ENNReal.ofReal (coolWeight m σsq i x) := by
  rw [proposal, prod_apply_acceptRegion _ hσ hS, Arlib.uniformOn, condOn_def,
    Measure.restrict_smul, lintegral_smul_measure, Measure.restrict_restrict hS,
    smul_eq_mul]

/-- **The acceptance probability is the chain entry over the volume.**
A round is accepted with probability `chain m σsq K i / Vol(K)`, i.e. exactly the fraction
of the body's volume that the phase-`i` Gaussian weight retains. -/
theorem proposal_acceptRegion (hσ : 0 < σsq i) (hfin : volume K ≠ ⊤) :
    proposal K (acceptRegion m σsq i)
      = (volume K)⁻¹ * ENNReal.ofReal (chain m σsq K i) := by
  have h := proposal_apply (K := K) (m := m) (σsq := σsq) (i := i) hσ MeasurableSet.univ
  rw [Set.preimage_univ, Set.univ_inter, Set.univ_inter] at h
  rw [h, chain_def, ofReal_integral_eq_lintegral_ofReal
    (integrableOn_coolWeight (m := m) hσ hfin)
    (Filter.Eventually.of_forall fun x => (coolWeight_pos m σsq i x).le)]

/-- **The bridge.** The law of the *accepted* point — a uniform draw from `K` kept with
probability `e^{−‖x‖²/(2σᵢ²)}` — is **exactly** the phase-`i` cooling law `coolLaw`.
No approximation, no mixing bound: this is an identity of measures. -/
theorem map_fst_condOn_proposal (hσ : 0 < σsq i) (hV0 : volume K ≠ 0)
    (hfin : volume K ≠ ⊤) (hchain : 0 < chain m σsq K i) :
    (condOn (proposal K) (acceptRegion m σsq i)).map Prod.fst = coolLaw m σsq K i := by
  have hC0 : ENNReal.ofReal (chain m σsq K i) ≠ 0 := by
    simpa using ENNReal.ofReal_pos.2 hchain |>.ne'
  have hCt : ENNReal.ofReal (chain m σsq K i) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hVi0 : (volume K)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hfin
  have hVit : (volume K)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hV0
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply measurable_fst hS,
    condOn_apply _ (measurableSet_acceptRegion m σsq i) (measurable_fst hS),
    proposal_apply hσ hS, proposal_acceptRegion hσ hfin,
    ENNReal.mul_div_mul_left _ _ hVi0 hVit]
  -- the right-hand side, unfolded
  rw [coolLaw, withDensity_apply _ hS, Measure.restrict_restrict hS]
  rw [show (fun x => ENNReal.ofReal (coolWeight m σsq i x / chain m σsq K i))
      = fun x => ENNReal.ofReal (coolWeight m σsq i x)
          * (ENNReal.ofReal (chain m σsq K i))⁻¹ from
    funext fun x => by
      rw [ENNReal.ofReal_div_of_pos hchain, ENNReal.div_eq_inv_mul, mul_comm]]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hC0), ENNReal.div_eq_inv_mul,
    mul_comm]

end Bridge

/-! ## The cost of the bridge: how many uniform draws one accepted point costs -/

section Cost

variable {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} {K : Set (EuclSpace n)}

/-- **The chain entry is at least `e^{−R²/(2σᵢ²)}·Vol(K)` on a body of radius `R`.**
Pointwise `coolWeight ≥ e^{−R²/(2σᵢ²)}` on `R·Bₙ`, in both regimes of `coolWeight` (the
Gaussian one, and the terminal constant `1`). -/
theorem exp_mul_volume_le_chain (hσ : 0 < σsq i) (hKm : MeasurableSet K)
    (hfin : volume K ≠ ⊤) {R : ℝ} (hKR : K ⊆ Metric.closedBall (0 : EuclSpace n) R) :
    Real.exp (-(R ^ 2) / (2 * σsq i)) * (volume K).toReal ≤ chain m σsq K i := by
  have h2s : (0 : ℝ) < 2 * σsq i := by linarith
  have hpt : ∀ x ∈ K, Real.exp (-(R ^ 2) / (2 * σsq i)) ≤ coolWeight m σsq i x := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      have := hKR hx; rwa [mem_closedBall_zero_iff] at this
    have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x]
    unfold coolWeight
    split
    · exact Real.exp_le_exp.2 (by rw [div_le_div_iff_of_pos_right h2s]; linarith)
    · exact Real.exp_le_one_iff.2 (by
        rw [div_nonpos_iff]
        exact Or.inr ⟨by nlinarith [norm_nonneg x], h2s.le⟩)
  have hmono := setIntegral_mono_on
    (integrableOn_const' hfin (Real.exp (-(R ^ 2) / (2 * σsq i))))
    (integrableOn_coolWeight (m := m) hσ hfin) hKm hpt
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at hmono
  rw [chain_def]
  linarith [hmono]

/-- **The acceptance probability of one rejection round is at least `e^{−R²/(2σᵢ²)}`.**
Equivalently: the expected number of uniform draws per accepted point is at most
`e^{R²/(2σᵢ²)}` — see `expected_rounds_le`. -/
theorem ofReal_exp_le_proposal_acceptRegion (hσ : 0 < σsq i) (hKm : MeasurableSet K)
    (hV0 : volume K ≠ 0) (hfin : volume K ≠ ⊤) {R : ℝ}
    (hKR : K ⊆ Metric.closedBall (0 : EuclSpace n) R) :
    ENNReal.ofReal (Real.exp (-(R ^ 2) / (2 * σsq i)))
      ≤ proposal K (acceptRegion m σsq i) := by
  rw [proposal_acceptRegion hσ hfin]
  have hstep : ENNReal.ofReal (Real.exp (-(R ^ 2) / (2 * σsq i)) * (volume K).toReal)
      ≤ ENNReal.ofReal (chain m σsq K i) :=
    ENNReal.ofReal_le_ofReal (exp_mul_volume_le_chain (m := m) hσ hKm hfin hKR)
  calc ENNReal.ofReal (Real.exp (-(R ^ 2) / (2 * σsq i)))
      = (volume K)⁻¹
          * ENNReal.ofReal (Real.exp (-(R ^ 2) / (2 * σsq i)) * (volume K).toReal) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hfin,
          mul_comm (ENNReal.ofReal (Real.exp (-(R ^ 2) / (2 * σsq i)))) (volume K),
          ← mul_assoc, ENNReal.inv_mul_cancel hV0 hfin, one_mul]
    _ ≤ (volume K)⁻¹ * ENNReal.ofReal (chain m σsq K i) := by gcongr

/-- **The proposal really is a probability measure**: a uniform point of `K` and an
independent uniform coin. -/
theorem isProbabilityMeasure_proposal (hV0 : volume K ≠ 0) (hfin : volume K ≠ ⊤) :
    IsProbabilityMeasure (proposal K) := by
  haveI := Arlib.isProbabilityMeasure_uniformOn volume hV0 hfin
  unfold proposal
  infer_instance

/-- **The cost, quoted.** Running the rejection loop of `map_fst_condOn_proposal` until it
accepts costs, in expectation, at most

  `e^{R²/(2σᵢ²)}`

uniform draws from `K`. At the *hot* end of a Gaussian-cooling schedule (`σᵢ² ≈ R²/n` or
smaller) this is `e^{Θ(n)}` — exponential, which is precisely why Cousins–Vempala run a
Metropolis chain against the Gaussian instead of rejecting from the uniform law. At the
*cold* end (`σᵢ² ≳ R²`) it is `O(1)`. -/
theorem expected_rounds_le (hσ : 0 < σsq i) (hKm : MeasurableSet K)
    (hV0 : volume K ≠ 0) (hfin : volume K ≠ ⊤) {R : ℝ}
    (hKR : K ⊆ Metric.closedBall (0 : EuclSpace n) R) :
    ∫ ω, (Arlib.Probability.roundCountNat (acceptRegion m σsq i) ω : ℝ)
        ∂(Arlib.Probability.roundsMeasure (proposal K))
      ≤ Real.exp (R ^ 2 / (2 * σsq i)) := by
  haveI := isProbabilityMeasure_proposal (K := K) hV0 hfin
  have h := Arlib.Probability.integral_roundCountNat_le (proposal K)
    (measurableSet_acceptRegion m σsq i) (p := Real.exp (-(R ^ 2) / (2 * σsq i)))
    (Real.exp_pos _)
    (Real.exp_le_one_iff.2 (by
      rw [div_nonpos_iff]
      exact Or.inr ⟨by nlinarith [sq_nonneg R], by linarith⟩))
    (ofReal_exp_le_proposal_acceptRegion hσ hKm hV0 hfin hKR)
  refine h.trans (le_of_eq ?_)
  rw [neg_div, Real.exp_neg]
  field_simp

end Cost

/-! ## What an exact phase-law sampler buys: both residual hypotheses, discharged

`Ttc.VolumeAlgorithm.cousinsVempalaOfRuns` (`Ttc/Volume/CVInstantiate.lean:265`) leaves
exactly two hypotheses, `hphase_mean` (an **equality**) and `hphase_var`. This section
records the — entirely routine — fact that a sampler whose law *is* `coolLaw` discharges
both, the equality on the nose. The content is not here; it is that the bridge above
produces such a law from a uniform sampler. -/

section Exact

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} {K : Set (EuclSpace n)}

/-- **`hphase_mean`, as the equality it is, from an exact phase-law sampler.**
No `η`, no interval: if `X` has law exactly `coolLaw m σsq K i`, the phase score is
*exactly* unbiased for `chain (i+1) / chain i`. -/
theorem integral_phaseScore_of_exact {X : Ω → EuclSpace n} (hX : Measurable X)
    (hKm : MeasurableSet K) (hchain : 0 < chain m σsq K i)
    (hlaw : μ.map X = coolLaw m σsq K i) :
    ∫ ω, phaseScore m σsq K i (X ω) ∂μ
      = chain m σsq K (i + 1) / chain m σsq K i := by
  rw [← integral_map hX.aemeasurable
    ((measurable_phaseScore (m := m) (σsq := σsq) hKm i).aestronglyMeasurable), hlaw]
  exact integral_phaseScore_coolLaw hKm hchain

/-- **`hphase_var` from an exact phase-law sampler**: the exact-law bound transports with
no loss at all (the TV error is `0`, so `Arlib.GaussianCooling.sq_moment_le_of_tvLe`'s
slack is not needed). -/
theorem integral_phaseScore_sq_of_exact {X : Ω → EuclSpace n} (hX : Measurable X)
    (hKm : MeasurableSet K) {C : ℝ}
    (hlaw : μ.map X = coolLaw m σsq K i)
    (hexact : ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ C * (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2) :
    ∫ ω, phaseScore m σsq K i (X ω) ^ 2 ∂μ
      ≤ C * (∫ ω, phaseScore m σsq K i (X ω) ∂μ) ^ 2 := by
  have hm := measurable_phaseScore (m := m) (σsq := σsq) hKm i
  rw [← integral_map hX.aemeasurable (hm.aestronglyMeasurable),
    ← integral_map hX.aemeasurable ((hm.pow_const 2).aestronglyMeasurable), hlaw]
  exact hexact

end Exact

/-! ## The two hypotheses, discharged by the rejection sampler itself -/

section Discharge

variable {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} {K : Set (EuclSpace n)}

/-- **`hphase_mean` discharged by rejection from an exact uniform sampler — an equality.**

The sampling map is `Prod.fst`: the accepted pair's point. `map_fst_condOn_proposal` says
its law *is* `coolLaw`, so the phase score's mean is the chain ratio on the nose.

This is the honest resolution of `Ttc/Volume/CVInstantiate.lean:75-83`'s claim that "no
mixing bound can deliver this". Correct: no *mixing* bound can. Rejection is not a mixing
bound — it is exact — and it moves the entire debt onto the uniform sampler (which is only
TV-close) and onto the round count (which is `e^{R²/(2σᵢ²)}`, see `expected_rounds_le`). -/
theorem integral_phaseScore_rejection (hσ : 0 < σsq i) (hKm : MeasurableSet K)
    (hV0 : volume K ≠ 0) (hfin : volume K ≠ ⊤) (hchain : 0 < chain m σsq K i) :
    ∫ q, phaseScore m σsq K i q.1 ∂(condOn (proposal K) (acceptRegion m σsq i))
      = chain m σsq K (i + 1) / chain m σsq K i :=
  integral_phaseScore_of_exact measurable_fst hKm hchain
    (map_fst_condOn_proposal hσ hV0 hfin hchain)

/-- **`hphase_var` discharged by rejection**, at whatever constant the *exact-law* bound
gives (`Arlib.GaussianCooling.coolLaw_sq_moment_le_budget` on the annealing schedule,
`Ttc.CV.hvar_exact_of_coolRate_all` for every phase at once). No TV slack is spent. -/
theorem integral_phaseScore_sq_rejection (hσ : 0 < σsq i) (hKm : MeasurableSet K)
    (hV0 : volume K ≠ 0) (hfin : volume K ≠ ⊤) (hchain : 0 < chain m σsq K i) {C : ℝ}
    (hexact : ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ C * (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2) :
    ∫ q, phaseScore m σsq K i q.1 ^ 2 ∂(condOn (proposal K) (acceptRegion m σsq i))
      ≤ C * (∫ q, phaseScore m σsq K i q.1
          ∂(condOn (proposal K) (acceptRegion m σsq i))) ^ 2 :=
  integral_phaseScore_sq_of_exact measurable_fst hKm
    (map_fst_condOn_proposal hσ hV0 hfin hchain) hexact

end Discharge

/-! ## Total variation under conditioning

The lemma that makes the bridge composable with a sampler that is only *approximately*
uniform. It is about an arbitrary measurable space and an arbitrary acceptance event; the
rejection loop enters only through `ν A`, the acceptance probability. -/

section CondTV

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Conditioning inflates total variation by the reciprocal of the acceptance
probability.** If `μ` and `ν` are within total variation `e`, and the acceptance event `A`
has `ν`-probability at least `2e`, then the *conditioned* laws are within `4e / ν A`.

The arithmetic is `x/a − y/b = (b(x−y) + y(b−a))/(ab)`, whose numerator is at most
`2·b·e`, so the difference is at most `2e/a ≤ 4e/b` once `a ≥ b − e ≥ b/2`.

The factor `4` is not optimal (the true constant is `2/(1 − e/b)`); it is chosen so the
hypothesis is the single readable inequality `2e ≤ ν A`. -/
theorem tvLe_condOn {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set Ω} (hA : MeasurableSet A) {e : ℝ≥0∞} (hTV : Arlib.TVLe μ ν e) (he : e ≠ ⊤)
    (hsmall : 2 * e.toReal ≤ (ν A).toReal) :
    Arlib.TVLe (condOn μ A) (condOn ν A)
      (ENNReal.ofReal (4 * e.toReal / (ν A).toReal)) := by
  set ee : ℝ := e.toReal with heedef
  have hee0 : 0 ≤ ee := ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : (0 : ℝ) ≤ (ν A).toReal) with hb | hb
  · -- `ν A = 0` forces `e = 0`, hence `μ = ν`, and both conditioned laws coincide
    have heez : ee = 0 := le_antisymm (by linarith) hee0
    have he0 : e = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff e).1 heez with h | h
      · exact h
      · exact absurd h he
    rw [he0] at hTV
    rw [hTV.eq_of_zero]
    exact (Arlib.TVLe.refl _).mono bot_le
  -- the main case: the acceptance probability is positive
  have hbne : ν A ≠ 0 := by
    intro h; rw [h] at hb; simp at hb
  have hbtop : ν A ≠ ⊤ := measure_ne_top ν A
  have hab : |(μ A).toReal - (ν A).toReal| ≤ ee :=
    hTV.abs_measureReal_sub_le he hA
  have ha : (ν A).toReal / 2 ≤ (μ A).toReal := by
    rw [abs_le] at hab; linarith [hab.1]
  have hapos : 0 < (μ A).toReal := lt_of_lt_of_le (by linarith) ha
  have hane : μ A ≠ 0 := by
    intro h; rw [h] at hapos; simp at hapos
  have hatop : μ A ≠ ⊤ := measure_ne_top μ A
  haveI := Arlib.isProbabilityMeasure_condOn μ hane hatop
  haveI := Arlib.isProbabilityMeasure_condOn ν hbne hbtop
  refine Arlib.tvLe_of_forall_le fun T hT => ?_
  -- the real-valued ingredients
  have hxy : |(μ (T ∩ A)).toReal - (ν (T ∩ A)).toReal| ≤ ee :=
    hTV.abs_measureReal_sub_le he (hT.inter hA)
  have hy0 : 0 ≤ (ν (T ∩ A)).toReal := ENNReal.toReal_nonneg
  have hx0 : 0 ≤ (μ (T ∩ A)).toReal := ENNReal.toReal_nonneg
  have hyb : (ν (T ∩ A)).toReal ≤ (ν A).toReal :=
    ENNReal.toReal_mono hbtop (measure_mono Set.inter_subset_right)
  rw [abs_le] at hab hxy
  -- the real inequality
  have key : (μ (T ∩ A)).toReal / (μ A).toReal
      ≤ (ν (T ∩ A)).toReal / (ν A).toReal + 4 * ee / (ν A).toReal := by
    rw [← add_div, div_le_div_iff₀ hapos hb]
    nlinarith [hxy.1, hxy.2, hab.1, hab.2, hy0, hx0, hyb, hee0]
  -- lift it back to `ℝ≥0∞`
  have hcμ : condOn μ A T = ENNReal.ofReal ((μ (T ∩ A)).toReal / (μ A).toReal) := by
    rw [Arlib.condOn_apply μ hA hT, ENNReal.ofReal_div_of_pos hapos,
      ENNReal.ofReal_toReal (measure_ne_top μ (T ∩ A)), ENNReal.ofReal_toReal hatop]
  have hcν : condOn ν A T = ENNReal.ofReal ((ν (T ∩ A)).toReal / (ν A).toReal) := by
    rw [Arlib.condOn_apply ν hA hT, ENNReal.ofReal_div_of_pos hb,
      ENNReal.ofReal_toReal (measure_ne_top ν (T ∩ A)), ENNReal.ofReal_toReal hbtop]
  rw [hcμ, hcν, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal key

end CondTV

/-! ## Total variation under tensoring with a fixed factor -/

section ProdTV

variable {F : Type*} [MeasurableSpace F]

/-- A product mass, as the `ofReal` of an ordinary integral of the `[0,1]`-valued slice
function. This is what puts `Arlib.TVLe.integral_le` in reach on a product space. -/
theorem prod_apply_eq_ofReal_integral {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (ξ : Measure F) [IsProbabilityMeasure ξ]
    {S : Set (Ω × F)} (hS : MeasurableSet S) :
    (ρ.prod ξ) S = ENNReal.ofReal (∫ x, (ξ (Prod.mk x ⁻¹' S)).toReal ∂ρ) := by
  have hfm : Measurable fun x => (ξ (Prod.mk x ⁻¹' S)).toReal :=
    (measurable_measure_prodMk_left hS).ennreal_toReal
  have hf0 : ∀ x, (0 : ℝ) ≤ (ξ (Prod.mk x ⁻¹' S)).toReal := fun _ => ENNReal.toReal_nonneg
  have hf1 : ∀ x, (ξ (Prod.mk x ⁻¹' S)).toReal ≤ 1 := fun x => by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ξ))
  rw [ofReal_integral_eq_lintegral_ofReal
      (Arlib.integrable_of_forall_mem_Icc hfm hf0 hf1)
      (Filter.Eventually.of_forall hf0),
    Measure.prod_apply hS]
  exact lintegral_congr fun x => (ENNReal.ofReal_toReal (measure_ne_top ξ _)).symm

/-- **Total variation is preserved by tensoring with a fixed factor.** Adjoining the same
independent randomness `ξ` to two laws neither creates nor destroys distinguishability.

The proof is `Arlib.TVLe.integral_le` applied to the slice function
`x ↦ ξ (Prod.mk x ⁻¹' S)`, which takes values in `[0,1]` — the same constant `e`, no
loss. -/
theorem tvLe_prod_right {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ξ : Measure F)
    [IsProbabilityMeasure ξ] {e : ℝ≥0∞} (hTV : Arlib.TVLe μ ν e) (he : e ≠ ⊤) :
    Arlib.TVLe (μ.prod ξ) (ν.prod ξ) e := by
  refine Arlib.tvLe_of_forall_le fun S hS => ?_
  have hfm : Measurable fun x => (ξ (Prod.mk x ⁻¹' S)).toReal :=
    (measurable_measure_prodMk_left hS).ennreal_toReal
  have hf0 : ∀ x, (0 : ℝ) ≤ (ξ (Prod.mk x ⁻¹' S)).toReal := fun _ => ENNReal.toReal_nonneg
  have hf1 : ∀ x, (ξ (Prod.mk x ⁻¹' S)).toReal ≤ 1 := fun x => by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ξ))
  have hkey := hTV.integral_le he hfm hf0 hf1
  rw [abs_le] at hkey
  rw [prod_apply_eq_ofReal_integral μ ξ hS, prod_apply_eq_ofReal_integral ν ξ hS,
    ← ENNReal.ofReal_toReal he,
    ← ENNReal.ofReal_add (integral_nonneg hf0) ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (by linarith [hkey.2])

end ProdTV

/-! ## The composite: an approximately uniform sampler through the bridge -/

section Composite

variable {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} {K : Set (EuclSpace n)}

/-- The acceptance probability, as a real number: `chain i / Vol(K)`. -/
theorem toReal_proposal_acceptRegion (hσ : 0 < σsq i)
    (hfin : volume K ≠ ⊤) (hchain : 0 ≤ chain m σsq K i) :
    (proposal K (acceptRegion m σsq i)).toReal = chain m σsq K i / (volume K).toReal := by
  rw [proposal_acceptRegion hσ hfin, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hchain, mul_comm, ← div_eq_mul_inv]

/-- **The bridge, composed with a sampler that is only `η`-close to uniform.**

If the proposal's point-law `μhat` is within total variation `η` of `uniformOn volume K`,
then the *accepted* point's law is within total variation

  `4·η·Vol(K) / chain m σsq K i`

of the exact phase law `coolLaw m σsq K i`. Composition of three proved steps:
`tvLe_prod_right` (adjoining the coin is free), `tvLe_condOn` (conditioning on acceptance
costs the reciprocal of the acceptance probability), `Arlib.TVLe.map` (reading off the
point costs nothing), and finally `map_fst_condOn_proposal` to name the target.

**The inflation factor is the round count.** `Vol(K)/chain i ≤ e^{R²/(2σᵢ²)}
(`exp_mul_volume_le_chain`) is exactly the expected number of uniform draws per accepted
point (`expected_rounds_le`), so this route's TV price and its time price are the *same*
exponential — which is the honest accounting, and is why it is not a polynomial
algorithm. -/
theorem tvLe_map_fst_condOn_of_uniform (hσ : 0 < σsq i) (hV0 : volume K ≠ 0)
    (hfin : volume K ≠ ⊤) (hchain : 0 < chain m σsq K i)
    (μhat : Measure (EuclSpace n)) [IsProbabilityMeasure μhat] {η : ℝ≥0∞}
    (hTV : Arlib.TVLe μhat (Arlib.uniformOn volume K) η) (hη : η ≠ ⊤)
    (hsmall : 2 * η.toReal ≤ chain m σsq K i / (volume K).toReal) :
    Arlib.TVLe
      ((condOn (μhat.prod (volume.restrict (Icc (0 : ℝ) 1)))
          (acceptRegion m σsq i)).map Prod.fst)
      (coolLaw m σsq K i)
      (ENNReal.ofReal (4 * η.toReal * (volume K).toReal / chain m σsq K i)) := by
  haveI := Arlib.isProbabilityMeasure_uniformOn volume hV0 hfin
  haveI := isProbabilityMeasure_proposal (K := K) hV0 hfin
  have hVpos : 0 < (volume K).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨pos_of_ne_zero hV0, Ne.lt_top hfin⟩
  have hacc : (proposal K (acceptRegion m σsq i)).toReal
      = chain m σsq K i / (volume K).toReal :=
    toReal_proposal_acceptRegion hσ hfin hchain.le
  -- step 1: adjoining the coin is free
  have h1 : Arlib.TVLe (μhat.prod (volume.restrict (Icc (0 : ℝ) 1)))
      (proposal K) η := tvLe_prod_right _ hTV hη
  -- step 2: conditioning on acceptance
  have h2 := tvLe_condOn (measurableSet_acceptRegion m σsq i) h1 hη (by rw [hacc]; exact hsmall)
  -- step 3: read off the point
  have h3 := h2.map (measurable_fst (α := EuclSpace n) (β := ℝ))
  rw [map_fst_condOn_proposal hσ hV0 hfin hchain] at h3
  refine h3.mono (le_of_eq ?_)
  rw [hacc]
  congr 1
  field_simp

end Composite

/-! ## Non-vacuity (`CLAUDE.md` §11)

Every hypothesis of the bridge is satisfiable at once, at a body that is *not* degenerate
and with a *strictly positive* acceptance probability, so the rejection loop terminates
almost surely and the conclusions above are not statements about the zero measure. -/

section Witness

/-- **The non-vacuity witness for the whole bridge**, on the closed unit ball of any
dimension, at the flat schedule `σⱼ² = 1` and any phase index `i`. It certifies, all at
once:

1. the accepted law is a genuine probability measure (`IsProbabilityMeasure`);
2. the acceptance probability is **strictly positive** — the loop is not vacuous;
3. the accepted point's law is **exactly** `coolLaw`;
4. `hphase_mean` holds **as an equality** at that law;
5. the expected number of uniform draws per accepted point is at most `e^{1/2}` here.

6. `Ttc.GaussianRejection.tvLe_map_fst_condOn_of_uniform`'s smallness hypothesis
   `2η ≤ chain i / Vol(K)` is met at a **strictly positive** `η`, so the composite is not
   vacuously guarded either.

What it does **not** certify: that a *uniform sampler for a general body* exists at any
given TV error. That is the hit-and-run debt (see the module docstring's "Residual"). Nor
does it certify any running-time claim: `expected_rounds_le`'s bound is `e^{R²/(2σᵢ²)}`,
which is `e^{Θ(n)}` at the hot end of a real cooling schedule. -/
theorem rejection_witness (n m : ℕ) (i : ℕ) :
    letI K : Set (EuclSpace n) := Metric.closedBall 0 1
    letI σsq : ℕ → ℝ := fun _ => 1
    IsProbabilityMeasure (condOn (proposal K) (acceptRegion m σsq i)) ∧
    0 < proposal K (acceptRegion m σsq i) ∧
    (condOn (proposal K) (acceptRegion m σsq i)).map Prod.fst = coolLaw m σsq K i ∧
    (∫ q, phaseScore m σsq K i q.1 ∂(condOn (proposal K) (acceptRegion m σsq i))
      = chain m σsq K (i + 1) / chain m σsq K i) ∧
    (∫ ω, (Arlib.Probability.roundCountNat (acceptRegion m σsq i) ω : ℝ)
        ∂(Arlib.Probability.roundsMeasure (proposal K)) ≤ Real.exp (1 / 2)) ∧
    (∃ η : ℝ≥0∞, 0 < η ∧ η ≠ ⊤ ∧
      2 * η.toReal ≤ chain m σsq K i / (volume K).toReal) := by
  set K : Set (EuclSpace n) := Metric.closedBall 0 1 with hKdef
  set σsq : ℕ → ℝ := fun _ => 1 with hσdef
  have hσ : ∀ j, (0 : ℝ) < σsq j := fun _ => one_pos
  have hKm : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hball : Metric.ball (0 : EuclSpace n) 1 ⊆ K := Metric.ball_subset_closedBall
  have hfin : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hV0 : volume K ≠ 0 := by
    intro h
    have hle : volume (Metric.ball (0 : EuclSpace n) 1) ≤ 0 := h ▸ measure_mono hball
    have hpos := volume_unitBall_toReal_pos (n := n)
    rw [le_zero_iff.1 hle] at hpos
    simp at hpos
  have hchain : 0 < chain m σsq K i := chain_pos hσ hball hfin i
  haveI := isProbabilityMeasure_proposal (K := K) hV0 hfin
  have hC0 : ENNReal.ofReal (chain m σsq K i) ≠ 0 := (ENNReal.ofReal_pos.2 hchain).ne'
  have hacc : 0 < proposal K (acceptRegion m σsq i) := by
    rw [proposal_acceptRegion (m := m) (hσ i) hfin]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hfin) hC0
  refine ⟨Arlib.isProbabilityMeasure_condOn _ hacc.ne'
      (measure_ne_top (proposal K) _),
    hacc, map_fst_condOn_proposal (hσ i) hV0 hfin hchain,
    integral_phaseScore_rejection (hσ i) hKm hV0 hfin hchain, ?_⟩
  have hVpos : 0 < (volume K).toReal := by
    rw [ENNReal.toReal_pos_iff]; exact ⟨pos_of_ne_zero hV0, Ne.lt_top hfin⟩
  refine ⟨?_, ⟨ENNReal.ofReal (chain m σsq K i / (2 * (volume K).toReal)), ?_, ?_, ?_⟩⟩
  · have h := expected_rounds_le (m := m) (σsq := σsq) (i := i) (K := K) (R := 1)
      (hσ i) hKm hV0 hfin Subset.rfl
    simpa [hσdef] using h
  · exact ENNReal.ofReal_pos.2 (by positivity)
  · exact ENNReal.ofReal_ne_top
  · rw [ENNReal.toReal_ofReal (by positivity)]
    rw [mul_div_assoc', mul_comm (2 : ℝ), ← div_div,
      mul_div_assoc, div_self (two_ne_zero), mul_one]

end Witness

end Ttc.GaussianRejection

/-! ## Axiom audit (`CLAUDE.md` §4)

Every declaration above must rest on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Ttc.GaussianRejection.acceptRegion
#print axioms Ttc.GaussianRejection.measurableSet_acceptRegion
#print axioms Ttc.GaussianRejection.slice_acceptRegion_of_mem
#print axioms Ttc.GaussianRejection.slice_acceptRegion_of_notMem
#print axioms Ttc.GaussianRejection.restrict_Icc_Iic_coolWeight
#print axioms Ttc.GaussianRejection.prod_apply_acceptRegion
#print axioms Ttc.GaussianRejection.proposal
#print axioms Ttc.GaussianRejection.proposal_apply
#print axioms Ttc.GaussianRejection.proposal_acceptRegion
#print axioms Ttc.GaussianRejection.map_fst_condOn_proposal
#print axioms Ttc.GaussianRejection.exp_mul_volume_le_chain
#print axioms Ttc.GaussianRejection.ofReal_exp_le_proposal_acceptRegion
#print axioms Ttc.GaussianRejection.isProbabilityMeasure_proposal
#print axioms Ttc.GaussianRejection.expected_rounds_le
#print axioms Ttc.GaussianRejection.integral_phaseScore_of_exact
#print axioms Ttc.GaussianRejection.integral_phaseScore_sq_of_exact
#print axioms Ttc.GaussianRejection.integral_phaseScore_rejection
#print axioms Ttc.GaussianRejection.integral_phaseScore_sq_rejection
#print axioms Ttc.GaussianRejection.tvLe_condOn
#print axioms Ttc.GaussianRejection.prod_apply_eq_ofReal_integral
#print axioms Ttc.GaussianRejection.tvLe_prod_right
#print axioms Ttc.GaussianRejection.toReal_proposal_acceptRegion
#print axioms Ttc.GaussianRejection.tvLe_map_fst_condOn_of_uniform
#print axioms Ttc.GaussianRejection.rejection_witness

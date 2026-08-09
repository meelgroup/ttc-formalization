/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.TtcProb
import Ttc.Access

/-!
# `Volume/Bridge`: everything *proved* about `Vol_ED`

`Ttc.VolumeAlgorithm` (`Volume/Oracle`) states Cousins–Vempala Theorem 1.1
as the contract `Vol_ED` is called under. It is an assumption. This file holds
everything that is a **theorem** about it, so that `Model/` stays four files of
declarations and assumptions with no proofs worth the name — see `AUDIT.md`.

Three things live here.

**The non-vacuity witness.** `Ttc.VolumeAlgorithm.exact` — the oracle that returns
`Vol(K)` on the nose and never fails — inhabits the interface, so no theorem
quantified over it is vacuous (`CLAUDE.md` §11).

**The rounding bridge.** Theorem 1.1 requires `K ⊇ B(0,1)`; `Ttc.TtcProb` supplies
`ball_subset : Metric.ball (cen i) gammaHat ⊆ region M i`, an inscribed ball of
radius `γ̂` about a centre that is *not* the origin. `Ttc.roundBody`
(`Model/Prelude`) is the affine change of variable `y ↦ γ⁻¹·(y − c)` carrying one
to the other, and the lemmas below discharge Theorem 1.1's hypotheses for its
image and transport the conclusion back. The paper's own preprocessing
(`vol3_journal.tex:145`, "contains the unit ball") is exactly this normalisation;
here it is a theorem, not a hypothesis. **No new assumption is introduced**: every
hypothesis `Ttc.VolumeAlgorithm.of_ball` needs is already a field of
`Ttc.TtcProb`, and convexity is *proved* from `M_eq` via `Ttc.convex_region`.

**The union bound over the `m` calls.** `alg:ttc` line 24 calls `Vol_ED` once per
polytope at confidence `δ' = δ/(4m)`. `Ttc.measure_volGood_ge` bounds the failure
probability of all `m` calls by `m·δ'`, i.e. `δ/4` — the step `analysis.tex:269`
leaves out (README finding 13), and exactly the share of the failure budget
`Ttc.numlattice_failure_le` already reserves for the volume oracle.

The former deterministic field `volED_hi` comes back at the bottom as a
**theorem** with its statement unchanged, so every consumer downstream is
untouched; `Ttc.TtcProb.volED_lo` comes free, since Theorem 1.1's conclusion is
two-sided and the old field was not.
-/

namespace Ttc

open MeasureTheory Set Pointwise

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
  est_meas := fun _ _ _ => measurable_const
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

/-! ## The rounding bridge -/

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

* `hγ` ← `hgammaHat` (`Model/ProblemSetting.lean`)
* `hball` ← `ball_subset`
* `hfin` ← `volume_ne_top`
* `hconv` ← `Ttc.convex_region` (`Lattice/Decomposition.lean`), which is
  **proved**, not assumed, from `M_eq` -/
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

/-! ## The `m` calls, union-bounded

`alg:ttc` line 24 calls `Vol_ED` once per polytope, at confidence
`δ' = δ/(4m)` (`Ttc.Params.deltaPrime`, `alg:ttc` line 18). `Ttc.volGood`
(`Volume/Oracle`) is the event that *all* `m` calls succeed, and
`Ttc.measure_volGood_ge` bounds its failure probability by `m·δ'` — the union
bound the paper omits (README finding 13), now supplied. -/

namespace VolumeAlgorithm

/-- A single call's good event is measurable: `est` is measurable in the coins
(`Ttc.VolumeAlgorithm.est_meas`) and `relErr` is a closed interval. -/
theorem measurableSet_good (V : VolumeAlgorithm n) (c : Space n) (γ ε p : ℝ)
    (K : Set (Space n)) :
    MeasurableSet[V.mΩ]
      {ω | γ ^ n * V.est (roundBody c γ K) ε p ω ∈ relErr ε (volume K).toReal} := by
  letI := V.mΩ
  exact ((V.est_meas _ ε p).const_mul (γ ^ n)) measurableSet_Icc

/-- **A single call fails with probability at most `p`.** The complement form of
`Ttc.VolumeAlgorithm.of_ball` — this is what a union bound consumes, and it is
where `est_meas` is spent. -/
theorem measure_bad_le (V : VolumeAlgorithm n) {c : Space n} {γ ε p : ℝ}
    {K : Set (Space n)} (hγ : 0 < γ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (hball : Metric.ball c γ ⊆ K) (hconv : Convex ℝ K) (hfin : volume K ≠ ⊤) :
    V.μ {ω | γ ^ n * V.est (roundBody c γ K) ε p ω ∉ relErr ε (volume K).toReal}
      ≤ ENNReal.ofReal p := by
  letI := V.mΩ
  haveI := V.isProb
  set S := {ω | γ ^ n * V.est (roundBody c γ K) ε p ω
    ∈ relErr ε (volume K).toReal} with hS
  have hmeas : MeasurableSet S := V.measurableSet_good c γ ε p K
  have hgood : 1 - p ≤ (V.μ S).toReal := V.of_ball hγ hε hp hp1 hball hconv hfin
  have hsum : (V.μ S).toReal + (V.μ Sᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hmeas, measure_univ, ENNReal.toReal_one]
  have hbad : {ω | γ ^ n * V.est (roundBody c γ K) ε p ω
      ∉ relErr ε (volume K).toReal} = Sᶜ := rfl
  rw [hbad, ENNReal.le_ofReal_iff_toReal_le (by finiteness) hp.le]
  linarith

end VolumeAlgorithm

/-- **The union bound over the `m` calls.** All of them succeed with probability
at least `1 − m·δ'`.

This is the step `analysis.tex:269` leaves out: the paper reads off `Vol_ED`'s
guarantee for a single cube and never charges the `m` calls to a budget (README
finding 13). Here `δ'` is a parameter, so instantiating it at
`Ttc.Params.deltaPrime = δ/(4m)` turns the conclusion into `1 − δ/4`, exactly the
share `Ttc.Params.vol_failure_eq` reserves. -/
theorem measure_volGood_ge {m : ℕ} (V : VolumeAlgorithm n) {γ ε' δ' : ℝ}
    {cen : Fin m → Space n} {K : Fin m → Set (Space n)}
    (hγ : 0 < γ) (hε : 0 < ε') (hδ0 : 0 < δ') (hδ1 : δ' < 1)
    (hball : ∀ j, Metric.ball (cen j) γ ⊆ K j)
    (hconv : ∀ j, Convex ℝ (K j)) (hfin : ∀ j, volume (K j) ≠ ⊤) :
    1 - m * δ' ≤ (V.μ (volGood V γ ε' δ' cen K)).toReal := by
  letI := V.mΩ
  haveI := V.isProb
  set G := volGood V γ ε' δ' cen K with hG
  -- the failure event is the union of the `m` single-call failures
  have hcompl : Gᶜ = ⋃ j : Fin m,
      {ω | γ ^ n * V.est (roundBody (cen j) γ (K j)) ε' δ' ω
        ∉ relErr ε' (volume (K j)).toReal} := by
    ext ω; simp [hG, volGood, not_forall]
  have hbad : V.μ Gᶜ ≤ (m : ENNReal) * ENNReal.ofReal δ' := by
    rw [hcompl]
    refine le_trans (measure_iUnion_fintype_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun j _ =>
      V.measure_bad_le hγ hε hδ0 hδ1 (hball j) (hconv j) (hfin j))) ?_
    simp [Finset.sum_const, mul_comm]
  -- convert to reals; `G` itself needs no measurability, only subadditivity
  have hbadR : (V.μ Gᶜ).toReal ≤ (m : ℝ) * δ' := by
    refine le_trans (ENNReal.toReal_mono (by finiteness) hbad) ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hδ0.le]
  have hcov : (V.μ Set.univ).toReal ≤ (V.μ G).toReal + (V.μ Gᶜ).toReal := by
    have hsub : V.μ Set.univ ≤ V.μ G + V.μ Gᶜ := by
      rw [← Set.union_compl_self G]; exact measure_union_le _ _
    calc (V.μ Set.univ).toReal ≤ (V.μ G + V.μ Gᶜ).toReal :=
          ENNReal.toReal_mono (by finiteness) hsub
      _ = (V.μ G).toReal + (V.μ Gᶜ).toReal :=
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measure_univ, ENNReal.toReal_one] at hcov
  linarith

/-! ## `Vol_ED`'s contract for an actual `Ttc.TtcProb`

The former field `volED_hi` is recovered as a theorem, so every consumer
(`Ttc.TtcProb.vol_lt_two_total`, `Coupling/Transfer`) is unchanged; and the
assumption that replaced it, `volCoins_good`, is shown to be an event of
probability at least `1 − δ/4`. -/

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- **`Vol_ED`'s accuracy contract, upper half** (`analysis.tex:269`) — the field
this development used to assume, now derived from Theorem 1.1 holding at
`volCoins`. Consumed by `Ttc.TtcProb.vol_lt_two_total`. -/
theorem volED_hi : ∀ i ∈ T.toDNF T.φ,
    T.vol i ≤ (1 + T.P.epsPrime) * (volume (region T.M i)).toReal :=
  fun i hi => VolumeAlgorithm.upper (T.volCoins_good i hi)

/-- **`Vol_ED`'s accuracy contract, lower half.** Never available before: the old
field was one-sided. Theorem 1.1's conclusion is two-sided, so this comes free —
it is the half that justifies one of the two `(1±ε')` factors of the Invariant
(`theta_lo`). -/
theorem volED_lo : ∀ i ∈ T.toDNF T.φ,
    (1 - T.P.epsPrime) * (volume (region T.M i)).toReal ≤ T.vol i :=
  fun i hi => VolumeAlgorithm.lower (T.volCoins_good i hi)

/-- `δ' = δ/(4m)` is positive. -/
theorem deltaPrime_pos : 0 < T.P.deltaPrime := by
  have hm : (1:ℝ) ≤ (T.P.m : ℝ) := by exact_mod_cast T.P.hm
  have hδ : 0 < T.P.δ := by rw [T.delta_eq]; exact T.hδ0
  unfold Params.deltaPrime
  positivity

/-- `δ' = δ/(4m) ≤ 1/4 < 1`. -/
theorem deltaPrime_lt_one : T.P.deltaPrime < 1 := by
  have hm : (1:ℝ) ≤ (T.P.m : ℝ) := by exact_mod_cast T.P.hm
  have hδ1 : T.P.δ ≤ 1 := by rw [T.delta_eq]; exact T.hδ1
  have hδ0 : 0 < T.P.δ := by rw [T.delta_eq]; exact T.hδ0
  unfold Params.deltaPrime
  rw [div_lt_one (by linarith)]
  linarith

/-- **`volCoins_good` *is* membership in that event.** So the assumption the
structure carries is precisely the event whose probability `volGood_prob` bounds
— it is not a stronger side condition smuggled in beside it. -/
theorem volCoins_mem_volEvent : T.volCoins ∈ T.volEvent := by
  intro j
  have hmem : T.D.get j ∈ T.toDNF T.φ := List.get_mem _ _
  have h := T.volCoins_good (T.D.get j) hmem
  rw [T.volED_eq (T.D.get j) hmem] at h
  exact h

/-- **The `m` `Vol_ED` calls all succeed with probability at least `1 − m·δ'`.**

This is the union bound `analysis.tex:269` never takes (README finding 13): the
paper reads off `Vol_ED`'s guarantee for one cube and never charges the `m` calls
to a budget. Every hypothesis Theorem 1.1 needs is discharged from fields
`Ttc.TtcProb` already had — `hgammaHat`, `ball_subset`, `volume_ne_top`, and
convexity from `M_eq` via the *proved* `Ttc.convex_region` — so no new geometric
assumption enters. -/
theorem volGood_prob :
    1 - (T.numCubes : ℝ) * T.P.deltaPrime ≤ (T.volAlg.μ T.volEvent).toReal := by
  have hε : 0 < T.P.epsPrime := by
    have := T.P.hε0; unfold Params.epsPrime; linarith
  refine measure_volGood_ge T.volAlg T.hgammaHat hε T.deltaPrime_pos
    T.deltaPrime_lt_one (fun j => T.ball_subset (T.cubeAt j)) (fun j => ?_)
    (fun j => T.volume_ne_top (T.cubeAt j))
  rw [T.M_eq]
  exact convex_region T.atoms _

/-- **The volume oracle's total failure probability is at most `δ/4`** — exactly
the share `Ttc.Params.vol_failure_eq` reserves for it inside the `δ/2` that
`Ttc.numlattice_failure_le` allows the two oracle families. So the assumption
`volCoins_good` fits the budget the rest of the development was already carrying,
with nothing to re-prove downstream.

`hm` is the loop count against the parameter block's `m`. It is a hypothesis
rather than a field because `cubes_le` bounds the number of *distinct* cubes,
which is smaller than the list length when the AllSAT call returns duplicates. -/
theorem volGood_prob_budget (hm : (T.numCubes : ℝ) ≤ T.P.m) :
    1 - T.δ / 4 ≤ (T.volAlg.μ T.volEvent).toReal := by
  have hstep : (T.numCubes : ℝ) * T.P.deltaPrime ≤ (T.P.m : ℝ) * T.P.deltaPrime :=
    mul_le_mul_of_nonneg_right hm T.deltaPrime_pos.le
  rw [T.P.vol_failure_eq, T.delta_eq] at hstep
  linarith [T.volGood_prob]

end TtcProb

-- `Vol_ED`'s contract, now Cousins–Vempala Theorem 1.1 rather than a posited
-- inequality: the former field, re-derived; and the union bound over the `m`
-- calls that bounds the probability of the assumption which replaced it.
#print axioms TtcProb.volED_hi
#print axioms TtcProb.volGood_prob
#print axioms TtcProb.volGood_prob_budget

end Ttc

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Sampler.ConstructLazyHitAndRunUncond
import Ttc.Exec.SampleBound

/-!
# An all-dimensional unconditional KV97 sampler

For `n ≥ 1100` this uses the unconditional lazy hit-and-run sampler.  For the finitely many
dimensions `1 ≤ n < 1100` it uses the older unconditional lazy ball walk.  The branch is
part of the definition of the kernel and step count, so the result is one ordinary
`KV97Sampler`, not a dependent pair of incompatible laws.

The shared start assumption is genuine `M`-warmness.  The ball-walk theorem consumes it
directly; the hit-and-run theorem consumes the same inequality with exceptional set `∅`.
The low-dimensional transition count is absorbed into a finite 1100-term envelope.  This
is a polynomial expression of fixed (very large) degree in the geometric parameters and is
independent of the live dimension.  As in the high-dimensional file, this is a Markov
transition bound, not a facet-query or membership-query implementation of hit-and-run.
-/

namespace Ttc

open MeasureTheory Pointwise
open scoped ENNReal Classical BigOperators

/-- The dimension-dependent transition kernel. -/
noncomputable def kv97HybridKernel {n : ℕ} (K : Set (Space n)) (δ : ℝ) :
    ProbabilityTheory.Kernel (Space n) (Space n) :=
  if 21 ≤ n then
    Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun K)
  else
    Arlib.MarkovChains.lazy (Arlib.MarkovChains.ballWalk K δ)

/-- Hit-and-run above the proved dimension threshold, ball walk below it. -/
noncomputable def kv97HybridSteps
    (n : ℕ) (rin Rout δ Mw eps : ℝ) : ℕ :=
  if 21 ≤ n then
    lazyHitAndRunUncondSteps n rin Rout Mw eps
  else
    mixSteps n rin (2 * Rout) δ Mw eps

/-- The single all-dimensional continuous law. -/
noncomputable def kv97HybridContLaw {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout δ Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n)) :
    {c : Cube A // c ∈ D} → Measure (Space n) := fun i =>
  let K := Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf
  let eps := epsPrime / (4 * (volume K).toReal)
  Arlib.MarkovChains.iterate (kv97HybridKernel K (δ i)) (sigma i)
    (kv97HybridSteps n (rin i) (Rout i) (δ i) (Mw i) eps)

theorem kv97HybridContLaw_eq_iterate
    {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout δ Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (i : {c : Cube A // c ∈ D}) :
    kv97HybridContLaw epsPrime rf Am bv rin Rout δ Mw sigma i =
      Arlib.MarkovChains.iterate
        (kv97HybridKernel
          (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf) (δ i))
        (sigma i)
        (kv97HybridSteps n (rin i) (Rout i) (δ i) (Mw i)
          (epsPrime / (4 *
            (volume (Arlib.KV97.inflated (Am i) (bv i)
              (Arlib.KV97.cOf epsPrime) rf)).toReal))) := rfl

instance isMarkovKernel_kv97HybridKernel {n : ℕ} (K : Set (Space n)) (δ : ℝ) :
    ProbabilityTheory.IsMarkovKernel (kv97HybridKernel K δ) := by
  unfold kv97HybridKernel
  split <;> infer_instance

instance isProbabilityMeasure_kv97HybridContLaw
    {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout δ Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (i : {c : Cube A // c ∈ D}) [IsProbabilityMeasure (sigma i)] :
    IsProbabilityMeasure
      (kv97HybridContLaw epsPrime rf Am bv rin Rout δ Mw sigma i) := by
  unfold kv97HybridContLaw
  infer_instance

/-- A circumball gives the pointwise diameter bound used by the low-dimensional branch. -/
theorem dist_le_two_mul_of_subset_closedBall {n : ℕ} {K : Set (Space n)}
    {z : Space n} {R : ℝ} (hout : K ⊆ Metric.closedBall z R) :
    ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 2 * R := by
  intro x hx y hy
  have hx' := Metric.mem_closedBall.1 (hout hx)
  have hy' := Metric.mem_closedBall.1 (hout hy)
  calc
    dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
    _ = dist x z + dist y z := by rw [dist_comm z y]
    _ ≤ R + R := by gcongr
    _ = 2 * R := by ring

/-- One unconditional `KV97Sampler` in every positive dimension.  The high branch needs
only the proved theorem's `1100 ≤ n`; the low branch is selected automatically when that
test fails. -/
noncomputable def kv97SamplerOfHybridUncond
    {A : Type*} {n : ℕ} {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ} {epsPrime : ℝ}
    (hn : 1 ≤ n) (hEps : 0 < epsPrime)
    (Jt : Type) [Fintype Jt]
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (hdil : ∀ i, latticeScale ρ • region M i.val ⊆ Arlib.Polytope.body (Am i) (bv i))
    (rf : ℝ) (hr1 : 1 ≤ rf) (hcard : (Fintype.card Jt : ℝ) ≤ rf)
    (zin : {c : Cube A // c ∈ D} → Space n)
    (rin : {c : Cube A // c ∈ D} → ℝ)
    (hrin : ∀ i, 0 < rin i)
    (hin : ∀ i, Metric.closedBall (zin i) (rin i) ⊆
      Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)
    (zout : {c : Cube A // c ∈ D} → Space n)
    (Rout : {c : Cube A // c ∈ D} → ℝ)
    (hRout : ∀ i, 0 < Rout i)
    (hout : ∀ i, Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf ⊆
      Metric.closedBall (zout i) (Rout i))
    (δ : {c : Cube A // c ∈ D} → ℝ)
    (hδ : ∀ i, 0 < δ i) (hδrin : ∀ i, δ i ≤ rin i)
    (heps1 : ∀ i, epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rf)).toReal) ≤ 1)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (Mw : {c : Cube A // c ∈ D} → ℝ) (hM : ∀ i, 1 ≤ Mw i)
    (hwarm : ∀ i, Arlib.IsWarm (ENNReal.ofReal (Mw i)) (sigma i)
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf))) :
    KV97Sampler A n M D ρ epsPrime
      (kv97SampD M D ρ
        (kv97HybridContLaw epsPrime rf Am bv rin Rout δ Mw sigma)) where
  J := Jt
  fintypeJ := inferInstance
  Amat := Am
  bvec := bv
  dilate_eq := hdil
  facetBound := rf
  one_le_facetBound := hr1
  card_le_facetBound := hcard
  contLaw := kv97HybridContLaw epsPrime rf Am bv rin Rout δ Mw sigma
  isProbContLaw := by
    intro i
    haveI := hsigma i
    infer_instance
  contVol := fun i =>
    (volume (Arlib.KV97.inflated (Am i) (bv i)
      (Arlib.KV97.cOf epsPrime) rf)).toReal
  contVol_pos := fun i =>
    toReal_volume_inflated_pos_of_closedBalls (hrin i) (hin i) (hout i)
  contVol_eq := fun _ => rfl
  law_tv := by
    intro i
    haveI := hsigma i
    let K := Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf
    let eps := epsPrime / (4 * (volume K).toReal)
    have hpos : 0 < (volume K).toReal :=
      toReal_volume_inflated_pos_of_closedBalls (hrin i) (hin i) (hout i)
    have heps0 : 0 < eps := div_pos hEps (by positivity)
    by_cases hhigh : 21 ≤ n
    · have hdom : ∀ T, MeasurableSet T →
          sigma i (T \ (∅ : Set (Space n))) ≤ ENNReal.ofReal (Mw i) *
            Arlib.uniformOn volume K (T \ (∅ : Set (Space n))) := by
        intro T hT
        simpa using hwarm i T hT
      have htv := tvLe_lazyHitAndRunLaw_inflated hhigh (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rf (hrin i) (hRout i).le (hin i) (hout i)
        (hM i) heps0 (heps1 i) MeasurableSet.empty (by simp) hdom
      simpa [kv97HybridContLaw, kv97HybridKernel, kv97HybridSteps, hhigh, K, eps]
        using htv
    · have htv := tvLe_ballWalkLaw_inflated hn (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rf
        (dist_le_two_mul_of_subset_closedBall (hout i))
        (hrin i) (Metric.ball_subset_closedBall.trans (hin i))
        (hδ i) (hδrin i) (hM i) (hwarm i) heps0
      simpa [kv97HybridContLaw, kv97HybridKernel, kv97HybridSteps, hhigh, K, eps,
        ballWalkLaw] using htv
  sampD_eq := fun i x _ => kv97SampD_apply M ρ _ i x

/-! ## Finite low-dimensional envelope -/

/-- A fixed finite envelope for all ball-walk counts below dimension 1100. -/
noncomputable def lowDimBallWalkEnvelope
    (rin Rout δ Mw eps : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 21,
    max 0 (mixStepsBound k rin (2 * Rout) δ Mw eps)

/-- **The all-dimensional transition bound, branching on the dimension exactly as
`Ttc.kv97HybridSteps` does.**

⚠ **Until 2026-08-19 this was the high-dimensional polynomial `+ 1 +
`Ttc.lowDimBallWalkEnvelope`, added *unconditionally*** — a single expression covering both
branches.  That made it correct but ruinous: `Ttc.lowDimBallWalkEnvelope` sums
`Ttc.mixStepsBound k` over every `k < 1100`, and `mixStepsBound` carries `4^k` and
`((γ+Dm)/γ)^(4k)`, so at `k = 1099` the bound contained a term of order
`4^1099 · (radius ratio)^4396` **even at `1100 ≤ n`, where the walk being priced is
hit-and-run and that term is pure overhead**.  `Ttc.SamplerEnvelopeShape` proved it was
genuinely there, from below, with no hypotheses.

Since `Ttc.kv97HybridSteps` already branches, so does this: each branch prices its own walk
and nothing else.

**What this does not fix.**  On the low branch the bound is `Ttc.mixStepsBound n`, which is
`4^n · ((γ+Dm)/γ)^(4n)`-shaped — genuinely exponential in `n`.  That is the ball walk's own
bound at dimension `n`, not an artefact of the envelope.  So a *polynomial* transition bound
holds at `1100 ≤ n` and **not** below it; TTC's capstone admits `21 ≤ n`, so for
`21 ≤ n < 1100` the proved bound remains exponential until hit-and-run is established at
those dimensions. -/
noncomputable def hybridTransitionBound
    (n : ℕ) (rin Rout δ Mw eps : ℝ) : ℝ :=
  if 21 ≤ n then
    max 0 (2 ^ 66 * (n : ℝ) ^ 2 * Rout ^ 2 / rin ^ 2 *
      Real.log (8 * Mw / eps ^ 2)) + 1
  else
    max 0 (mixStepsBound n rin (2 * Rout) δ Mw eps) + 1

theorem kv97HybridSteps_le_transitionBound
    {n : ℕ} (hn : 1 ≤ n) {rin Rout δ Mw eps : ℝ}
    (hrin : 0 < rin) (hRout : 0 < Rout) (hδ : 0 < δ)
    (hM : 1 ≤ Mw) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    (kv97HybridSteps n rin Rout δ Mw eps : ℝ) ≤
      hybridTransitionBound n rin Rout δ Mw eps := by
  by_cases hhigh : 21 ≤ n
  · rw [kv97HybridSteps, if_pos hhigh]
    have hstep :=
      lazyHitAndRunUncondSteps_lt_deadline_add_one n rin Rout Mw eps
    unfold hybridTransitionBound
    rw [if_pos hhigh]
    exact hstep.le
  · rw [kv97HybridSteps, if_neg hhigh]
    have hmix : (mixSteps n rin (2 * Rout) δ Mw eps : ℝ) ≤
        mixStepsBound n rin (2 * Rout) δ Mw eps :=
      mixSteps_le hn hrin (by positivity) hδ hM heps0 heps1
    unfold hybridTransitionBound
    rw [if_neg hhigh]
    linarith [le_max_right 0 (mixStepsBound n rin (2 * Rout) δ Mw eps)]

section AxiomCheck

#print axioms kv97HybridContLaw_eq_iterate
#print axioms isProbabilityMeasure_kv97HybridContLaw
#print axioms dist_le_two_mul_of_subset_closedBall
#print axioms kv97SamplerOfHybridUncond
#print axioms kv97HybridSteps_le_transitionBound

end AxiomCheck

end Ttc

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.OldHalving

/-!
# The sealed program's constants are the old model's

For a component `P` read into the sealed world (`load (componentInput P)`), at precision
scale `10^b` and accuracy `η`, the walk constants the program computes
(`walkConstantsProg`) are the old model's: the walk's body is
`P.hitAndRunPresentation b η` (`presOf_walk`), its length is `normalizedHitAndRunSteps`
(`get_steps`), its chart is `samplerChart` (`chart_eq`), and the membership test of a
rounded point is the old acceptance test (`accepts_iff`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program

variable {n : ℕ}

/-- A component read into the sealed world, field by field. -/
abbrev loaded (P : ttc.PolytopeData n) : Loaded n where
  facets := P.presentation.facetCount
  normal := fun j i => (Num.lit (κ := Op) (κₛ := Cell) (P.presentation.normal j i)).val
  offset := fun j => (Num.lit (κ := Op) (κₛ := Cell) (P.presentation.offset j)).val
  inradius := (Num.lit (κ := Op) (κₛ := Cell) P.inradius).val
  incenter := fun i => (Num.lit (κ := Op) (κₛ := Cell) (P.incenter i)).val
  boundingRadius := (Num.lit (κ := Op) (κₛ := Cell) P.BoundingRadius).val
  facetReal := (Num.cast (κ := Op) (κₛ := Cell)
    (Num.lit (κ := Op) (κₛ := Cell) P.presentation.facetCount).val).val

/-- **Reading a component** gives its fields. -/
theorem val_load_componentInput (P : ttc.PolytopeData n) :
    (ttc.Program.load (ttc.SealedRun.componentInput P)).val = loaded P := by
  simp only [ttc.Program.load, Charged.val_bind, val_Apure, val_forEach, A.lit, A.cast]
  rfl

section Walk

variable (P : ttc.PolytopeData n) (b : ℕ) (eta : ℝ) (scale etaN dim : Num ℝ)

/-- The walk constants, computed. -/
abbrev walkC : WalkConstants n P.presentation.facetCount :=
  (walkConstantsProg (loaded P) scale etaN dim).val

theorem walkC_offsets (hs : scale.get = ttc.decimalScale b) (he : etaN.get = eta)
    (j : Fin P.presentation.facetCount) :
    ((walkC P scale etaN dim).offsets j).get = (P.hitAndRunOffsetsProg b eta).value j := by
  dsimp only [walkC, walkConstantsProg, Charged.val_bind, val_Apure]
  simp only [val_forEach, A.div, A.mul, A.add, A.sub, A.sqrt, A.log, A.divLit, A.litDiv, A.mulLit,
    A.lit, A.smul, A.normSq, get_dot, Num.get_div, Num.get_mul, Num.get_add, Num.get_sub,
    Num.get_sqrt, Num.get_log, Num.get_lit, Num.get_cast, Charged.val_bind, hs, he, A.cast]
  simp only [ttc.PolytopeData.hitAndRunOffsetsProg, ttc.Counted.bind_eq, ttc.Counted.andThen_value,
    ttc.Counted.forEach, ttc.Counted.div, ttc.Counted.mul, ttc.Counted.add, ttc.Counted.sub,
    ttc.Counted.sqrt, ttc.Counted.log, ttc.Counted.dot_value]

/-- **The walk's body is the old model's.** -/
theorem presOf_walk (hs : scale.get = ttc.decimalScale b) (he : etaN.get = eta) :
    presOf P.presentation.facetCount (loaded P).normal (walkC P scale etaN dim).offsets =
      P.hitAndRunPresentation b eta := by
  have h1 : getM (loaded P).normal = P.presentation.normal := by
    funext j i; simp [getM, loaded]
  have h2 : getV (walkC P scale etaN dim).offsets = (P.hitAndRunOffsetsProg b eta).value := by
    funext j; exact walkC_offsets P b eta scale etaN dim hs he j
  simp only [presOf, ttc.PolytopeData.hitAndRunPresentation, h1, h2]

/-- **The walk's length is the old model's.** -/
theorem walkC_steps (hs : scale.get = ttc.decimalScale b) (he : etaN.get = eta) (hd : dim.get = n) :
    (walkC P scale etaN dim).steps.get = ttc.normalizedHitAndRunSteps P b eta := by
  dsimp only [walkC, walkConstantsProg, Charged.val_bind, val_Apure]
  simp only [A.div, A.mul, A.add, A.sqrt, A.log, A.divLit, A.litDiv, A.mulLit, A.lit, A.smul,
    A.ceil, A.cast, get_Apow, Num.get_div, Num.get_mul, Num.get_add, Num.get_sqrt, Num.get_log,
    Num.get_lit, Num.get_cast, Num.get_ceil, Charged.val_bind, val_forEach, hs, he, hd]
  simp only [ttc.normalizedHitAndRunSteps, ttc.PolytopeData.samplerOuterRadius,
    ttc.PolytopeData.samplerKappa, ttc.PolytopeData.scaledInradius, ttc.samplerC,
    ArlibCommunity.Algorithms.KV97.kappaOf, ArlibCommunity.Algorithms.KV97.cOf,
    ttc.hitAndRunWalkConstant]

/-- **The chart is the old model's.** -/
theorem chart_eq (hs : scale.get = ttc.decimalScale b) (z : EuclideanSpace ℝ (Fin n)) :
    toPt (chartProg (walkC P scale etaN dim) (ofPt z)).val = P.samplerChart b z := by
  ext i
  dsimp only [chartProg, walkC, walkConstantsProg, Charged.val_bind, val_Apure]
  simp only [toPt_apply, val_forEach, A.mul, A.add, A.smul, Num.get_mul, Num.get_add,
    Charged.val_bind, hs, ofPt, get_sealVector, A.lit, Num.get_lit]
  simp [ttc.PolytopeData.samplerChart, ttc.PolytopeData.scaledInradius,
    ttc.PolytopeData.scaledIncenter, ttc.toEuclidean]

end Walk

section Accept

theorem val_allFacets_iff {d : ℕ} : ∀ (r : ℕ) (a : Fin r → NumPoint d) (β : Fin r → Num ℝ)
    (x : NumPoint d), (allFacets r a β x).val = true ↔
      ∀ j, dotProduct (fun i => (a j i).get) (fun i => (x i).get) ≤ (β j).get
  | 0, a, β, x => by simp [allFacets]
  | r + 1, a, β, x => by
      simp only [allFacets, Charged.val_bind, val_Apure, A.le, Num.val_le, get_dot,
        Bool.and_eq_true, decide_eq_true_eq, val_allFacets_iff r, Fin.forall_fin_succ]
      rfl

variable (P : ttc.PolytopeData n) (b : ℕ) (scale : Num ℝ)

/-- **The sealed membership test of a rounded point is the old acceptance test.** -/
theorem accepts_iff (hs : scale.get = ttc.decimalScale b) (w : Fin n → ℤ) :
    accepts (loaded P) (scaledOffsets (loaded P) scale).val w = true ↔
      w ∈ ttc.acceptedIntegers P b := by
  simp only [accepts, latticeMember, Charged.val_bind, val_allFacets_iff, ttc.acceptedIntegers,
    Set.mem_setOf_eq, ttc.HalfspacePresentation.memberProg, ttc.Counted.allFacets_value]
  simp [latticeReal, scaledOffsets, val_forEach, intCast, sealZ, A.mul, hs,
    ttc.PolytopeData.scaledPresentation, ttc.PolytopeData.scaledOffsetsProg, ttc.Counted.forEach,
    ttc.Counted.mul, loaded, dotProduct]

end Accept

section Proposal

open ArlibCommunity.Foundations.MarkovChainTheory (iterate)

variable (P : ttc.PolytopeData n) (b : ℕ) (eta : ℝ) (scale etaN dim : Num ℝ)

/-- **The sealed proposal law is the old one**: Hit-and-Run on the walk's body from the start
law, mapped by the chart, then rounded. -/
theorem proposalLaw_eq [NeZero n] (hs : scale.get = ttc.decimalScale b) (he : etaN.get = eta)
    (hd : dim.get = n)
    (hK : Bornology.IsBounded (ttc.HitAndRunLaw.body (P.hitAndRunPresentation b eta)))
    (hball : (ballStartLaw n) (ttc.HitAndRunLaw.body (P.hitAndRunPresentation b eta))ᶜ = 0) :
    proposalLaw (loaded P) (walkC P scale etaN dim) =
      ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw P b eta) := by
  have hW : walkKernel (loaded P) (walkC P scale etaN dim) =
      ttc.HitAndRunLaw.lazyKernel (P.hitAndRunPresentation b eta) := by
    simp only [walkKernel, presOf_walk P b eta scale etaN dim hs he]
  have hT := walkC_steps P b eta scale etaN dim hs he hd
  have hiter := (ttc.HitAndRunLaw.hitAndRunWalk_eq_iterate (P.hitAndRunPresentation b eta) hK
    (ballStartLaw n) hball (ttc.normalizedHitAndRunSteps P b eta)).1
  have hchart : Measurable (P.samplerChart b) := by
    unfold ttc.PolytopeData.samplerChart; fun_prop
  rw [proposalLaw, hW, hT, ttc.kv97RoundedMeasureLaw, ttc.normalizedHitAndRunContinuousLaw, hiter,
    Measure.bind_map hchart.aemeasurable measurable_roundPointLaw.aemeasurable]
  congr 1
  funext z
  rw [chart_eq P b scale etaN dim hs z]

end Proposal

section Sampler

open ttc.Tape.Tree

variable (P : ttc.PolytopeData n) (b : ℕ) (eta : ℝ) (scale etaN dim : Num ℝ)

theorem walkBody_eq (hs : scale.get = ttc.decimalScale b) (he : etaN.get = eta) :
    walkBody (loaded P) (walkC P scale etaN dim) =
      ttc.HitAndRunLaw.body (P.hitAndRunPresentation b eta) := by
  have h1 : getM (loaded P).normal = P.presentation.normal := by
    funext j i; simp [getM]
  have h2 : getV (walkC P scale etaN dim).offsets = (P.hitAndRunOffsetsProg b eta).value := by
    funext j; exact walkC_offsets P b eta scale etaN dim hs he j
  simp only [walkBody, bodyOf, h1, h2, ttc.HitAndRunLaw.body, ttc.PolytopeData.hitAndRunPresentation]

/-- **The sealed sampler with fuel is the old sampler**: with `R` the old rounded proposal
law and `A` the accepted lattice points, it stops with probability `R(Aᶜ)^fuel` and otherwise
returns the proposal on `A`, which normalised is the old `acceptedRoundedLatticeLaw`. -/
theorem sampler_eq_old [NeZero n] (hs : scale.get = ttc.decimalScale b) (he : etaN.get = eta)
    (hd : dim.get = n) (dimN : Num ℕ) (hdimN : dimN.get = n)
    (hK : Bornology.IsBounded (ttc.HitAndRunLaw.body (P.hitAndRunPresentation b eta)))
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆
      ttc.HitAndRunLaw.body (P.hitAndRunPresentation b eta)) (b' fuel : ℕ) :
    (vlaw (sampleUntilAcceptedT (loaded P) (walkC P scale etaN dim)
        (scaledOffsets (loaded P) scale).val dimN fuel) b').map (Option.map getZ) =
      (∑ j ∈ Finset.range fuel, ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw P b eta)
          (ttc.acceptedIntegers P b)ᶜ ^ j) •
        ((ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw P b eta)).restrict
          (ttc.acceptedIntegers P b)).map some +
      ttc.kv97RoundedMeasureLaw (ttc.normalizedHitAndRunContinuousLaw P b eta)
          (ttc.acceptedIntegers P b)ᶜ ^ fuel • Measure.dirac none := by
  have hB := walkBody_eq P b eta scale etaN dim hs he
  have hmeas : (ballStartLaw n) (ttc.HitAndRunLaw.body (P.hitAndRunPresentation b eta))ᶜ = 0 := by
    rw [BallStart.ballStartLaw_eq]
    refine measure_mono_null (fun y hy => ?_) (?_ : ArlibCommunity.Foundations.Convex.uniformOn
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) (Metric.ball 0 1)ᶜ = 0)
    · exact fun hb => hy (hball hb)
    · simp [ArlibCommunity.Foundations.Convex.uniformOn, ArlibCommunity.Foundations.Convex.condOn,
        Measure.restrict_apply measurableSet_ball.compl]
  have hA : {w | accepts (loaded P) (scaledOffsets (loaded P) scale).val w = true} =
      ttc.acceptedIntegers P b := by
    ext w; exact accepts_iff P b scale hs w
  have hAc : {w | accepts (loaded P) (scaledOffsets (loaded P) scale).val w = false} =
      (ttc.acceptedIntegers P b)ᶜ := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, ← accepts_iff P b scale hs w, Bool.not_eq_true]
  rw [vlaw_sampleUntilAcceptedT_eq (loaded P) (walkC P scale etaN dim) _ dimN hdimN (hB ▸ hK)
      (hB ▸ hball) b' fuel, proposalLaw_eq P b eta scale etaN dim hs he hd hK hmeas, hA, hAc]

end Sampler

end ttc.Tape

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.ChargedCV18.CountedArithmetic

/-!
# The constants of a call and of a phase, computed

`cv18Program` computes every number it uses: the constants of the call once
(`runConstantsProg`) and the constants of each phase once (`phaseConstantsProg`).  This
file proves that these programs hold the formulas of `Model/Prelude.lean`
(`runConstantsProg_value`, `phaseConstantsProg_value`), read through `RunConstants.view`
and `PhaseConstants.view`.  The cooling schedule is computed by a loop that stops when the
variance reaches `C²n`, over a fuel the program computes itself (`scheduleProg_spec`).
-/

open MeasureTheory
open Arlib.Computation (Num)

namespace ttc.ChargedCV18

open ArlibCommunity.Algorithms.CV18

/-! ## The fields of the records -/

@[simp] theorem runConstants_dimension (q : VolumeParams) : (runConstants q).dimension = (q.n : ℝ) := rfl
@[simp] theorem runConstants_dimensionCount (q : VolumeParams) : (runConstants q).dimensionCount = q.n := rfl
@[simp] theorem runConstants_terminal (q : VolumeParams) : (runConstants q).terminal = terminalVariance q := rfl
@[simp] theorem runConstants_rootTerminal (q : VolumeParams) : (runConstants q).rootTerminal = Real.sqrt (terminalVariance q) := rfl
@[simp] theorem runConstants_rootInitial (q : VolumeParams) : (runConstants q).rootInitial = Real.sqrt (initialVariance q) := rfl
@[simp] theorem runConstants_gaussianIntegral (q : VolumeParams) : (runConstants q).gaussianIntegral = initialGaussianIntegral q := rfl
@[simp] theorem runConstants_scale (q : VolumeParams) : (runConstants q).scale = scaleFactor q := rfl
@[simp] theorem runConstants_scaleInv (q : VolumeParams) : (runConstants q).scaleInv = (scaleFactor q)⁻¹ := rfl
@[simp] theorem runConstants_schedule (q : VolumeParams) : (runConstants q).schedule = coolingSchedule q := rfl
@[simp] theorem runConstants_sampleCount (q : VolumeParams) : (runConstants q).sampleCount = sampleCount q := rfl
@[simp] theorem runConstants_fixedRateSampleCount (q : VolumeParams) : (runConstants q).fixedRateSampleCount = fixedRateSampleCount q := rfl
@[simp] theorem runConstants_maxRetries (q : VolumeParams) : (runConstants q).maxRetries = maxRetries q := rfl
@[simp] theorem runConstants_accuracyLog (q : VolumeParams) : (runConstants q).accuracyLog = accuracyLog q := rfl
@[simp] theorem runConstants_blockError (q : VolumeParams) : (runConstants q).blockError = blockMixingError q (maxRetries q - 1) := rfl
@[simp] theorem runConstants_warm (q : VolumeParams) : (runConstants q).warm = warmConstant q := rfl
@[simp] theorem runConstants_queryBudget (q : VolumeParams) : (runConstants q).queryBudget = queryBudget q := rfl
@[simp] theorem runConstants_repetitions (q : VolumeParams) : (runConstants q).repetitions = confidenceRepetitions q := rfl

@[simp] theorem phaseConstants_radius (q : VolumeParams) (sigma2 : ℝ) :
    (phaseConstants q sigma2).radius = phaseRadius q sigma2 := rfl
@[simp] theorem phaseConstants_proposal (q : VolumeParams) (sigma2 : ℝ) :
    (phaseConstants q sigma2).proposal = proposalRadius q sigma2 := rfl
@[simp] theorem phaseConstants_steps (q : VolumeParams) (sigma2 : ℝ) :
    (phaseConstants q sigma2).steps = walkSteps q sigma2 := rfl
@[simp] theorem phaseConstants_cap (q : VolumeParams) (sigma2 : ℝ) :
    (phaseConstants q sigma2).cap = maxProposals q sigma2 := rfl
@[simp] theorem phaseConstants_samples (q : VolumeParams) (sigma2 : ℝ) :
    (phaseConstants q sigma2).samples = phaseSampleCount q sigma2 := rfl

/-- A held record of call constants that stands for `runConstants q`. -/
structure RunConstants.Holds (q : VolumeParams) (G : RunConstants) : Prop where
  view_eq : G.view = runConstants q

namespace RunConstants.Holds

variable {q : VolumeParams} {G : RunConstants} (h : G.Holds q)
include h

theorem dimension : G.dimension.get = q.n := congrArg RunValues.dimension h.view_eq
theorem dimensionCount : G.dimensionCount.get = q.n :=
  congrArg RunValues.dimensionCount h.view_eq
theorem terminal : G.terminal.get = terminalVariance q := congrArg RunValues.terminal h.view_eq
theorem rootTerminal : G.rootTerminal.get = Real.sqrt (terminalVariance q) :=
  congrArg RunValues.rootTerminal h.view_eq
theorem rootInitial : G.rootInitial.get = Real.sqrt (initialVariance q) :=
  congrArg RunValues.rootInitial h.view_eq
theorem gaussianIntegral : G.gaussianIntegral.get = initialGaussianIntegral q :=
  congrArg RunValues.gaussianIntegral h.view_eq
theorem scale : G.scale.get = scaleFactor q := congrArg RunValues.scale h.view_eq
theorem scaleInv : G.scaleInv.get = (scaleFactor q)⁻¹ := congrArg RunValues.scaleInv h.view_eq
theorem schedule : G.schedule.map Num.get = coolingSchedule q :=
  congrArg RunValues.schedule h.view_eq
theorem sampleCount : G.sampleCount.get = ArlibCommunity.Algorithms.CV18.sampleCount q :=
  congrArg RunValues.sampleCount h.view_eq
theorem fixedRateSampleCount : G.fixedRateSampleCount.get = ArlibCommunity.Algorithms.CV18.fixedRateSampleCount q :=
  congrArg RunValues.fixedRateSampleCount h.view_eq
theorem maxRetries : G.maxRetries.get = ArlibCommunity.Algorithms.CV18.maxRetries q :=
  congrArg RunValues.maxRetries h.view_eq
theorem accuracyLog : G.accuracyLog.get = ArlibCommunity.Algorithms.CV18.accuracyLog q :=
  congrArg RunValues.accuracyLog h.view_eq
theorem blockError : G.blockError.get = blockMixingError q (ArlibCommunity.Algorithms.CV18.maxRetries q - 1) :=
  congrArg RunValues.blockError h.view_eq
theorem warm : G.warm.get = warmConstant q := congrArg RunValues.warm h.view_eq
theorem queryBudget : G.queryBudget.get = ArlibCommunity.Algorithms.CV18.queryBudget q :=
  congrArg RunValues.queryBudget h.view_eq
theorem repetitions : G.repetitions.get = confidenceRepetitions q :=
  congrArg RunValues.repetitions h.view_eq

end RunConstants.Holds

/-! ## The schedule -/

theorem nextVarianceProg_value (q : VolumeParams) {d T : Num ℝ} (hd : d.get = q.n)
    (hT : T.get = terminalVariance q) (sigma2 : Num ℝ) :
    (nextVarianceProg d T sigma2).value.get = nextVariance q sigma2.get := by
  by_cases h : sigma2.get ≤ 1 <;>
    simp [nextVarianceProg, nextVariance, coolingRate, h, hd, hT]

/-- Before step `terminalPhaseSteps q` the schedule is strictly below `C²n`. -/
theorem scheduleValue_lt_terminal (q : VolumeParams) {k : ℕ} (hk : k < terminalPhaseSteps q) :
    scheduleValue q k < terminalVariance q := by
  refine lt_of_le_of_ne (scheduleValue_le_terminal q k) fun h => ?_
  exact absurd (Nat.sInf_le (show k ∈ {k | scheduleValue q k = terminalVariance q} from h))
    (not_le.mpr hk)

/-- One step of the schedule costs at most `8` operations. -/
theorem nextVarianceProg_cost_le (dimension terminal sigma2 : Num ℝ) :
    (nextVarianceProg dimension terminal sigma2).cost ≤ 8 := by
  simp only [nextVarianceProg, Counted.bind_cost, Counted.le_cost, Counted.lit_cost]
  split <;> simp

/-- The state of the schedule loop after `k` rounds: the variances of steps `0, …, k − 1`
recorded, the variance of step `k` current, and the count `k + 1`. -/
def ScheduleState (q : VolumeParams) (k : ℕ) (st : List (Num ℝ) × Num ℝ × Num ℕ) : Prop :=
  st.1.map Num.get = List.ofFn (fun i : Fin k => scheduleValue q i) ∧
    st.2.1.get = scheduleValue q k ∧ st.2.2.get = k + 1

/-- **The rounds of the schedule loop.**  From the state of round `k ≤ terminalPhaseSteps q`,
with enough rounds left, the loop ends in the state of round `terminalPhaseSteps q`, at
most `11` operations per round taken plus the stopping test. -/
theorem scheduleRounds (q : VolumeParams) {d T : Num ℝ} {one : Num ℕ} (hd : d.get = q.n)
    (hT : T.get = terminalVariance q) (hone : one.get = 1) :
    ∀ (l : List ℕ) (k : ℕ) (st : List (Num ℝ) × Num ℝ × Num ℕ), ScheduleState q k st →
      k ≤ terminalPhaseSteps q → terminalPhaseSteps q ≤ k + l.length →
      ScheduleState q (terminalPhaseSteps q)
          (Counted.value (Arlib.Computation.Charged.foldlWhile
            (fun b _ => scheduleRound d T one b) l st)) ∧
        Counted.cost (Arlib.Computation.Charged.foldlWhile
            (fun b _ => scheduleRound d T one b) l st) ≤
          11 * (terminalPhaseSteps q - k) + 1 := by
  intro l
  induction l with
  | nil =>
    intro k st hst hk hl
    simp only [List.length_nil, add_zero] at hl
    obtain rfl : k = terminalPhaseSteps q := le_antisymm hk hl
    rw [(Counted.foldlWhile_nil _ st).1, (Counted.foldlWhile_nil _ st).2]
    exact ⟨hst, by omega⟩
  | cons a l ih =>
    intro k st hst hk hl
    obtain ⟨h1, h2, h3⟩ := hst
    simp only [List.length_cons] at hl
    rcases lt_or_eq_of_le hk with hlt | rfl
    · -- below `C²n`: record the variance, step, and count
      have hsv : ¬ terminalVariance q ≤ scheduleValue q k :=
        not_le.mpr (scheduleValue_lt_terminal q hlt)
      have hround : (scheduleRound d T one st).value =
          some ((Counted.push st.1 st.2.1).value, (nextVarianceProg d T st.2.1).value,
            (Counted.add st.2.2 one).value) := by
        simp [scheduleRound, hT, h2, hsv]
      obtain ⟨hv, hc⟩ := Counted.foldlWhile_cons_some
        (f := fun b _ => scheduleRound d T one b) (a := a) (l := l) hround
      have hnext : (nextVarianceProg d T st.2.1).value.get = scheduleValue q (k + 1) := by
        rw [nextVarianceProg_value q hd hT, h2, scheduleValue_succ]
      obtain ⟨ih1, ih2⟩ := ih (k + 1)
        ((Counted.push st.1 st.2.1).value, (nextVarianceProg d T st.2.1).value,
          (Counted.add st.2.2 one).value)
        ⟨by rw [List.ofFn_succ_last]; simp [h1, h2], hnext, by simp [h3, hone]⟩
        (by omega) (by omega)
      have hcr : (scheduleRound d T one st).cost ≤ 11 := by
        have := nextVarianceProg_cost_le d T st.2.1
        simp only [scheduleRound, Counted.bind_cost, Counted.le_cost, Counted.le_value, hT, h2,
          hsv, decide_false, Bool.false_eq_true, ↓reduceIte, Counted.add_cost,
          Counted.push_cost, Counted.pure_cost]
        omega
      refine ⟨by rw [hv]; exact ih1, ?_⟩
      rw [hc]
      omega
    · -- at `C²n`: stop
      have hsv : terminalVariance q ≤ scheduleValue q (terminalPhaseSteps q) :=
        (scheduleValue_terminalPhaseSteps q).ge
      have hround : (scheduleRound d T one st).value = none := by
        simp [scheduleRound, hT, h2, hsv]
      obtain ⟨hv, hc⟩ := Counted.foldlWhile_cons_none
        (f := fun b _ => scheduleRound d T one b) (a := a) (l := l) hround
      refine ⟨by rw [hv]; exact ⟨h1, h2, h3⟩, ?_⟩
      rw [hc]
      simp [scheduleRound, hT, h2, hsv]

/-- **The schedule program** from `σ₀²`, with fuel at least `terminalPhaseSteps q`, holds
`coolingSchedule q` and `numPhases q`, at most `11` operations per step plus four. -/
theorem scheduleProg_spec (q : VolumeParams) {d T s : Num ℝ} {F : Num ℕ} (hd : d.get = q.n)
    (hT : T.get = terminalVariance q) (hs : s.get = initialVariance q)
    (hF : terminalPhaseSteps q ≤ F.get) :
    (scheduleProg d T F s).value.1.map Num.get = coolingSchedule q ∧
      (scheduleProg d T F s).value.2.get = numPhases q ∧
      (scheduleProg d T F s).cost ≤ 11 * terminalPhaseSteps q + 4 := by
  obtain ⟨⟨h1, h2, h3⟩, hc⟩ := scheduleRounds q hd hT (one := (Counted.lit (1 : ℕ)).value) rfl
    (List.range F.get) 0 ([], s, (Counted.lit (1 : ℕ)).value)
    ⟨by simp, by rw [hs]; simp [scheduleValue], by simp⟩ (Nat.zero_le _) (by simpa using hF)
  refine ⟨?_, ?_, ?_⟩
  · simp only [scheduleProg, Counted.bind_value, Counted.pure_value, Counted.iterateWhile_value,
      Counted.push_value, List.map_append, List.map_cons, List.map_nil, h1, h2, coolingSchedule]
    rw [List.ofFn_succ_last (n := terminalPhaseSteps q)]
    rfl
  · simp only [scheduleProg, Counted.bind_value, Counted.pure_value, Counted.iterateWhile_value,
      h3]
    rfl
  · simp only [scheduleProg, Counted.bind_cost, Counted.lit_cost, Counted.iterateWhile_cost,
      Counted.push_cost, Counted.pure_cost]
    omega

/-! ## The constants -/

/-- **The constants of a call are computed exactly.** -/
theorem runConstantsProg_value (q : VolumeParams) :
    (runConstantsProg q).value.Holds q := by
  constructor
  have hpos : 0 < 2 * Real.pi * initialVariance q := by
    have := initialVariance_pos q
    positivity
  have hZ : Real.exp (Real.log (2 * Real.pi * initialVariance q) * ((q.n : ℝ) / 2)) =
      initialGaussianIntegral q := by
    rw [initialGaussianIntegral, Real.rpow_eq_pow, Real.rpow_def_of_pos hpos]
  simp only [initialVariance] at hZ hpos
  have hsched := fun {d T s : Num ℝ} {F : Num ℕ} (hd : d.get = q.n)
      (hT : T.get = terminalVariance q) (hs : s.get = q.eps / (64 * (q.n : ℝ)))
      (hF : F.get = slowPhaseSteps q + fastPhaseSteps q) =>
    scheduleProg_spec q hd hT hs (by rw [hF]; exact terminalPhaseSteps_le_total q)
  simp only [terminalVariance, terminalScale, slowPhaseSteps, fastPhaseSteps] at hsched
  unfold RunConstants.view
  simp only [runConstantsProg, Counted.bind_value, Counted.pure_value, Counted.cast_value,
    Counted.lit_value, Counted.div_value, Counted.protectedLog_value, Counted.pow_value,
    Counted.mul_value, Counted.max_value, Counted.sqrt_value, Counted.log_value,
    Counted.exp_value, Counted.sub_value, Counted.ceil_value, Counted.add_value,
    Counted.mulLit_value, Counted.divLit_value, Counted.litDiv_value, Counted.litMax_value]
  -- rewriting the schedule in a separate pass keeps the kernel check cheap
  rw [(hsched (by simp) (by simp) (by simp) (by simp)).1,
    (hsched (by simp) (by simp) (by simp) (by simp)).2.1]
  unfold runConstants
  simp only [RunValues.mk.injEq, true_and]
  -- each field is its formula; the Gaussian integral is `(2πσ₀²)^{n/2}` written with `exp`
  repeat' apply And.intro
  all_goals first
    | rfl
    | exact hZ
    | simp [scaleFactor, one_div]

/-- **The constants of a phase are computed exactly.** -/
theorem phaseConstantsProg_value (q : VolumeParams) {G : RunConstants} (hG : G.Holds q)
    (sigma2 : Num ℝ) :
    (phaseConstantsProg G sigma2).value.view = phaseConstants q sigma2.get := by
  by_cases h : sigma2.get ≤ 1 <;>
  simp [phaseConstantsProg, walkRequirementProg, PhaseConstants.view, phaseConstants,
    phaseRadius, proposalRadius, walkSteps, strideFor, firstWalkRequirement,
    retryWalkRequirement, walkRequirement, maxProposals, proposalCapRequirement,
    phaseSampleCount, h, hG.dimension, hG.accuracyLog, hG.warm, hG.blockError,
    hG.queryBudget, hG.fixedRateSampleCount, hG.sampleCount]


/-! ## Costs -/

/-- How far the schedule program stays below its bound `11 · terminalPhaseSteps q + 4`. -/
noncomputable def scheduleSlack (q : VolumeParams) (d T s : Num ℝ) (F : Num ℕ) : ℕ :=
  11 * terminalPhaseSteps q + 4 - (scheduleProg d T F s).cost

theorem scheduleProg_cost_eq_slack (q : VolumeParams) {d T s : Num ℝ} {F : Num ℕ}
    (hd : d.get = q.n) (hT : T.get = terminalVariance q) (hs : s.get = initialVariance q)
    (hF : terminalPhaseSteps q ≤ F.get) :
    (scheduleProg d T F s).cost = 11 * terminalPhaseSteps q + 4 - scheduleSlack q d T s F := by
  have := (scheduleProg_spec q hd hT hs hF).2.2
  unfold scheduleSlack
  omega

/-- **The constants of a call cost `166` operations, plus the schedule loop**, at most
`11` per cooling step plus four. -/
theorem runConstantsProg_cost_le (q : VolumeParams) :
    (runConstantsProg q).cost ≤ 11 * terminalPhaseSteps q + 170 := by
  have hsc := fun {d T s : Num ℝ} {F : Num ℕ} (hd : d.get = q.n)
      (hT : T.get = terminalVariance q) (hs : s.get = q.eps / (64 * (q.n : ℝ)))
      (hF : F.get = slowPhaseSteps q + fastPhaseSteps q) =>
    scheduleProg_cost_eq_slack q hd hT hs (by rw [hF]; exact terminalPhaseSteps_le_total q)
  simp only [terminalVariance, terminalScale, slowPhaseSteps, fastPhaseSteps] at hsc
  simp only [runConstantsProg, Counted.bind_cost, Counted.cast_cost, Counted.lit_cost,
    Counted.div_cost, Counted.protectedLog_cost, Counted.pow_cost, Counted.mul_cost,
    Counted.max_cost, Counted.sqrt_cost, Counted.log_cost, Counted.exp_cost, Counted.sub_cost,
    Counted.ceil_cost, Counted.add_cost, Counted.mulLit_cost, Counted.divLit_cost,
    Counted.litDiv_cost, Counted.litMax_cost, Counted.pure_cost]
  rw [hsc (by simp) (by simp) (by simp) (by simp)]
  omega

/-- `walkRequirement` costs `23` operations. -/
theorem walkRequirementProg_cost (dimension proposal rootSigma M err : Num ℝ) :
    (walkRequirementProg dimension proposal rootSigma M err).cost = 23 := by
  simp [walkRequirementProg]

/-- **The constants of a phase cost `72` operations.** -/
theorem phaseConstantsProg_cost (G : RunConstants) (sigma2 : Num ℝ) :
    (phaseConstantsProg G sigma2).cost = 72 := by
  simp [phaseConstantsProg, walkRequirementProg_cost]

end ttc.ChargedCV18

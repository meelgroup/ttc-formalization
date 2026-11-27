/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Estimator
import ttc.Analysis.ThresholdCapBound
import ttc.Analysis.Tape.RuntimeBudget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledLogEnvelope

/-! # Accuracy dependence of the sealed operation budget

The population cap and the amplified CV18 query cap enter the component cost
additively. This file isolates the inverse-square factor in those two caps.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations ttc.Program ttc.RuntimeBudget
open ArlibCommunity.Algorithms.CV18

/-- Threshold numerator after factoring out the single `1 / ε²`. -/
def populationCapNumerator (p : ApproxParams) (m : ℕ) : ℝ :=
  3888 * Real.log (24 / p.delta) + 15 * (Real.log (6 / p.delta) + Real.log m)

theorem sealed_populationCap_le {d k : ℕ} {F : LRAFormula d k}
    (D : Decomposition F) (p : ApproxParams) (hm : 0 < D.componentCount) :
    (Nat.floor (paramsOf D p).thresh.get : ℝ) ≤
      populationCapNumerator p D.componentCount / p.epsilon ^ 2 := by
  obtain ⟨-, -, -, -, hTh, -, -⟩ := paramsProg_val D p hm
  change (paramsOf D p).thresh.get = p.Thresh D.componentCount at hTh
  rw [hTh]
  have he := p.epsilon_pos
  have he2 : 0 < p.epsilon ^ 2 := sq_pos_of_pos he
  have he1 : p.epsilon ^ 2 ≤ 1 := by nlinarith [p.epsilon_le_one, sq_nonneg (1 - p.epsilon)]
  have hd1 : 1 ≤ 6 / p.delta := (one_le_div p.delta_pos).2 (by linarith [p.delta_le_one])
  have hm1 : (1 : ℝ) ≤ D.componentCount := by exact_mod_cast hm
  have hlog : 0 ≤ 15 * (Real.log (6 / p.delta) + Real.log D.componentCount) := by
    have h₁ := Real.log_nonneg hd1
    have h₂ := Real.log_nonneg hm1
    positivity
  have hsecond : 15 * (Real.log (6 / p.delta) + Real.log D.componentCount) ≤
      15 * (Real.log (6 / p.delta) + Real.log D.componentCount) / p.epsilon ^ 2 := by
    apply (le_div_iff₀ he2).2
    exact (mul_le_mul_of_nonneg_left he1 hlog).trans_eq (mul_one _)
  have hfirst :
      27 * Real.log (24 / p.delta) / p.ε' ^ 2 =
        3888 * Real.log (24 / p.delta) / p.epsilon ^ 2 := by
    unfold ApproxParams.ε'
    field_simp
    ring
  calc
    _ ≤ p.Thresh D.componentCount := Nat.floor_le (p.threshold_pos _).le
    _ ≤ _ := p.threshold_le_explicit_parameter_envelope _ hm
    _ ≤ _ := add_le_add (le_of_eq hfirst) hsecond
    _ = _ := by rw [populationCapNumerator, add_div]

private theorem amplified_query_cap_le (q : VolumeParams) :
    ((confidenceRepetitions q * queryBudget q : ℕ) : ℝ) ≤
      585 * runCostConstant *
        (max 1 q.roundness * (q.n : ℝ) ^ 3 / q.eps ^ 2) *
        (14113440000 * volumeParamLog q ^ 10) := by
  have hLog := one_le_protectedLog (1 / q.p)
  have hRep : (confidenceRepetitions q : ℝ) ≤ 9 * protectedLog (1 / q.p) := by
    unfold confidenceRepetitions
    have hCeil := Nat.ceil_lt_add_one
      (show 0 ≤ 8 * protectedLog (1 / q.p) by positivity)
    linarith
  have hCost : 1 ≤ runCostConstant := by norm_num [runCostConstant]
  have hRate := runRate_one_le q
  have hQuery : (queryBudget q : ℝ) ≤ 65 * runCostConstant * runRate q := by
    unfold queryBudget budgetOfRate
    have hCeil := Nat.ceil_lt_add_one
      (show 0 ≤ 64 * runCostConstant * runRate q by positivity)
    have hProduct : 1 ≤ runCostConstant * runRate q := one_le_mul_of_one_le_of_one_le hCost hRate
    linarith
  have hPoly := figureOneScheduledLogEnvelope_le q
  have hMain : 0 ≤ 585 * runCostConstant *
      (max 1 q.roundness * (q.n : ℝ) ^ 3 / q.eps ^ 2) := by positivity
  calc
    _ = (confidenceRepetitions q : ℝ) * (queryBudget q : ℝ) := by push_cast; rfl
    _ ≤ (9 * protectedLog (1 / q.p)) * (65 * runCostConstant * runRate q) :=
      mul_le_mul hRep hQuery (Nat.cast_nonneg _) (by positivity)
    _ = 585 * runCostConstant * (max 1 q.roundness * (q.n : ℝ) ^ 3 / q.eps ^ 2) *
        figureOneScheduledLogEnvelope q := by
      unfold runRate baseRate figureOneScheduledLogEnvelope
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hPoly hMain

/-- All CV18 repetitions of the sealed program together have a query cap with one
inverse-square factor and a proved polylog envelope, not an assumed log loss. -/
theorem sealed_cv18AmplifiedQueryCap_le (q : VolumeParams)
    (eps roundness failure : Num ℝ) (he : eps.get = q.eps) (hr : roundness.get = q.roundness)
    (hf : failure.get = q.p) :
    let G := (runConstantsProg q.n eps roundness failure).val
    ((G.repetitions.get * G.queryBudget.get : ℕ) : ℝ) ≤
      585 * runCostConstant *
        (max 1 q.roundness * (q.n : ℝ) ^ 3 / q.eps ^ 2) *
        (14113440000 * volumeParamLog q ^ 10) := by
  intro G
  have hG := holds_runConstantsProg q eps roundness failure he hr hf
  have hRep : G.repetitions.get = confidenceRepetitions q := hG.repetitions
  have hQuery : G.queryBudget.get = queryBudget q := hG.queryBudget
  rw [hRep, hQuery]
  exact amplified_query_cap_le q

section Component

variable {d k : ℕ} {F : LRAFormula d k}

/-- The actual mathematical parameters of TTC's CV18 call at a component. -/
def sealedCV18Params (hd : 3 ≤ d) (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) : VolumeParams where
  n := d
  dim_ok := hd
  eps := p.epsilon / 24
  heps := ⟨by positivity [p.epsilon_pos], by linarith [p.epsilon_le_one]⟩
  p := p.delta / (8 * D.componentCount)
  hp := by
    have h : (1 : ℝ) ≤ D.componentCount := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
    exact ⟨by positivity [p.delta_pos], (div_lt_iff₀ (by positivity)).2
      (by linarith [p.delta_le_one])⟩
  roundness := (max 1 ((D.component i).BoundingRadius / (D.component i).inradius)) ^ 2 / d
  roundness_pos := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    exact div_pos (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))) hd0

theorem sealedCV18Params_match (hd : 3 ≤ d)
    (D : Decomposition F) (p : ApproxParams) (i : Fin D.componentCount) :
    let x := (cv18ParamsProg (paramsOf D p) (loaded (D.component i))).val
    let q := sealedCV18Params hd D p i
    x.1.get = q.eps ∧ x.2.2.get = q.roundness ∧ x.2.1.get = q.p := by
  intro x q
  obtain ⟨-, hdim, heps, hδ, -, -, -⟩ := paramsProg_val D p
    (Nat.zero_lt_of_lt i.isLt)
  change (paramsOf D p).dim.get = d at hdim
  change (paramsOf D p).epsPrime.get = p.ε' at heps
  change (paramsOf D p).deltaPrime.get = p.δ' D.componentCount at hδ
  obtain ⟨hx1, hx2, hx3⟩ := cv18Params_val (D.component i) (paramsOf D p)
  have he : x.1.get = q.eps := by
    rw [show x.1.get = _ from hx1, heps]
    change (p.epsilon / 12) / 2 = p.epsilon / 24
    ring
  have hf : x.2.1.get = q.p := by
    rw [show x.2.1.get = _ from hx2, hδ]
    change (p.delta / (4 * (D.componentCount : ℝ))) / 2 =
      p.delta / (8 * (D.componentCount : ℝ))
    ring
  have hr : x.2.2.get = q.roundness := by
    rw [show x.2.2.get = _ from hx3, hdim]
    rfl
  exact ⟨he, hr, hf⟩

/-- Numerator for the amplified query bound after replacing CV18's tolerance by
TTC's `ε / 24`. The only accuracy dependence left here is in `volumeParamLog`. -/
def cv18QueryNumerator (q : VolumeParams) : ℝ :=
  576 * (585 * runCostConstant) * (max 1 q.roundness * (q.n : ℝ) ^ 3) *
    (14113440000 * volumeParamLog q ^ 10)

theorem sealed_componentAmplifiedQueryCap_le (hd : 3 ≤ d)
    (D : Decomposition F) (p : ApproxParams) (i : Fin D.componentCount) :
    let x := (cv18ParamsProg (paramsOf D p) (loaded (D.component i))).val
    let G := (runConstantsProg d x.1 x.2.2 x.2.1).val
    ((G.repetitions.get * G.queryBudget.get : ℕ) : ℝ) ≤
      cv18QueryNumerator (sealedCV18Params hd D p i) / p.epsilon ^ 2 := by
  intro x G
  let q := sealedCV18Params hd D p i
  obtain ⟨he, hr, hf⟩ := sealedCV18Params_match hd D p i
  have h := sealed_cv18AmplifiedQueryCap_le q x.1 x.2.2 x.2.1 he hr hf
  refine h.trans_eq ?_
  unfold cv18QueryNumerator
  rw [show q.eps = p.epsilon / 24 from rfl]
  ring

/-- The part of a component budget independent of the population and query
caps, except for the parameters of the deterministic setup and the schedule. -/
def componentBaseOps (K : Params) (L : Loaded d) : ℕ :=
  let x := (cv18ParamsProg K L).val
  let c := runConstantsProg d x.1 x.2.2 x.2.1
  let G := c.val
  let r := G.repetitions.get
  opsTotal (cv18Offsets L).cost + opsTotal (cv18ParamsProg K L).cost +
    opsTotal c.cost + opsTotal (scaledOffsets L K.scale).cost +
    opsTotal (walkConstantsProg L K.scale K.epsPrime K.dim).cost +
    76 + r * (G.schedule.length * (2 * d + 83) + (7 * d + 87) + (4 * r + 5))

/-- Cost per unit of the population cap, including scans and walk attempts. -/
def componentPerCopyOps (K : Params) (L : Loaded d) : ℕ :=
  let W := (walkConstantsProg L K.scale K.epsPrime K.dim).val
  d + 2 * d * L.facets + 31 + 2 * sampleTryOps d L.facets W.steps.get

/-- Cost per unit of the amplified CV18 query cap, including facet arithmetic. -/
def componentPerQueryOps (L : Loaded d) : ℕ := 12 * d + 31 + 2 * d * L.facets

theorem componentOpsBudget_eq_add_caps (K : Params) (L : Loaded d) :
    let x := (cv18ParamsProg K L).val
    let G := (runConstantsProg d x.1 x.2.2 x.2.1).val
    componentOpsBudget K L = componentBaseOps K L +
      componentPerCopyOps K L * Nat.floor K.thresh.get +
      componentPerQueryOps L * (G.repetitions.get * G.queryBudget.get) := by
  dsimp only [componentOpsBudget, cv18TapeOpsBudget, cappedRunOps, tailOpsBudget,
    componentBaseOps, componentPerCopyOps, componentPerQueryOps]
  ring

/-- Both cap-driven terms in the actual component budget share a single
`1 / ε²`. This does not yet simplify the walk length or the setup remainder. -/
theorem sealed_componentOpsBudget_le_inverseSquare (hd : 3 ≤ d)
    (D : Decomposition F) (p : ApproxParams) (i : Fin D.componentCount) :
    let K := paramsOf D p
    let L := loaded (D.component i)
    (componentOpsBudget K L : ℝ) ≤ componentBaseOps K L +
      ((componentPerCopyOps K L : ℝ) * populationCapNumerator p D.componentCount +
        (componentPerQueryOps L : ℝ) * cv18QueryNumerator (sealedCV18Params hd D p i)) /
      p.epsilon ^ 2 := by
  intro K L
  rw [componentOpsBudget_eq_add_caps K L]
  push_cast
  have hpop := sealed_populationCap_le D p (Nat.zero_lt_of_lt i.isLt)
  have hcv := sealed_componentAmplifiedQueryCap_le hd D p i
  dsimp only at hcv
  push_cast at hcv
  have hp := mul_le_mul_of_nonneg_left hpop (Nat.cast_nonneg (α := ℝ) (componentPerCopyOps K L))
  have hc := mul_le_mul_of_nonneg_left hcv (Nat.cast_nonneg (α := ℝ) (componentPerQueryOps L))
  refine (add_le_add (add_le_add le_rfl hp) hc).trans_eq ?_
  ring

end Component

end ttc.Tape

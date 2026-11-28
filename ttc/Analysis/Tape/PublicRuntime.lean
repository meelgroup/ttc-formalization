/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.EpsilonCost
import ttc.Analysis.Tape.Runtime

/-! # Relating the implementation budget to an explicit input formula -/

set_option autoImplicit false

noncomputable section

namespace ttc

open scoped BigOperators

/-- A formula for the walk deadline, using only the geometry of the input. -/
def arithmeticWalkLength {d : ℕ} (P : PolytopeData d) (b : ℕ) (eps : ℝ) : ℕ :=
  let h := (10 : ℝ) ^ b
  let g := h * P.inradius
  let η := eps / 12
  let κ := Real.sqrt (2 * Real.log (4 / (η / 4))) +
    Real.sqrt (2 * Real.log P.presentation.facetCount)
  let R := (1 + κ / g) * (h * P.BoundingRadius)
  Nat.ceil (2 ^ 68 * (d : ℝ) ^ 3 * (R / g) ^ 2 * Real.log (2 * R))

/-- The population-cap numerator, before division by `ε²`. -/
def arithmeticPopulationNumerator (p : ApproxParams) (m : ℕ) : ℝ :=
  3888 * Real.log (24 / p.delta) + 15 * (Real.log (6 / p.delta) + Real.log m)

/-- Roundness of the normalized input to the volume estimator. -/
def arithmeticRoundness {d : ℕ} (P : PolytopeData d) : ℝ :=
  (max 1 (P.BoundingRadius / P.inradius)) ^ 2 / d

/-- A ceiling bound on the number of variances in the cooling schedule. -/
def arithmeticScheduleCap (d : ℕ) (p : ApproxParams) (roundness : ℝ) : ℕ :=
  let θ := p.epsilon / 24
  let T := max 1 (max (d : ℝ) (1024 * roundness * d * (max 1 (Real.log (8 / θ))) ^ 2))
  Nat.ceil (2 * (d : ℝ) * (6 + max 1 (Real.log (d / θ)))) + Nat.ceil (3 * T) + 1

/-- Number of independent cooling runs for one component. -/
def arithmeticCV18Repetitions (m : ℕ) (p : ApproxParams) : ℕ :=
  Nat.ceil (8 * max 1 (Real.log (1 / (p.delta / (8 * m)))))

/-- The amplified CV18 query-cap numerator, with its logarithmic losses explicit. -/
def arithmeticQueryNumerator (d m : ℕ) (p : ApproxParams) (roundness : ℝ) : ℝ :=
  let Λ := max 1 (Real.log ((d : ℝ) * max 1 roundness /
    ((p.epsilon / 24) * (p.delta / (8 * m)))))
  576 * (585 * (10 : ℝ) ^ 30) * (max 1 roundness * (d : ℝ) ^ 3) * (14113440000 * Λ ^ 10)

/-- Input-only cost bound for one normalized component. The capped population and
amplified query terms add, sharing a single inverse-square accuracy factor. -/
def arithmeticComponentBound {d : ℕ} (m b : ℕ) (p : ApproxParams) (P : PolytopeData d) : ℝ :=
  let r := P.presentation.facetCount
  let roundness := arithmeticRoundness P
  let S := arithmeticScheduleCap d p roundness
  let R := arithmeticCV18Repetitions m p
  let T := arithmeticWalkLength P b p.epsilon
  let perTry := 13 * d + 5 + 2 * d * r + T * (6 * d + 8 + r * (4 * d + 5))
  let base : ℕ := r * (2 * d + 2) + 20 + (200 + 12 * S) + r +
    (100 + d + r * (4 * d + 10)) + 76 +
    R * (S * (2 * d + 83) + (7 * d + 87) + (4 * R + 5))
  (base : ℝ) +
    (((d + 2 * d * r + 31 + 2 * perTry : ℕ) : ℝ) * arithmeticPopulationNumerator p m +
      ((12 * d + 31 + 2 * d * r : ℕ) : ℝ) * arithmeticQueryNumerator d m p roundness) /
      p.epsilon ^ 2

/-- Public expected arithmetic bound from the certified decomposition and
approximation parameters. No charged computation occurs on this side of the claim. -/
def ttcArithmeticBound {d k : ℕ} {F : LRAFormula d k} (D : Decomposition F)
    (p : ApproxParams) : ℝ :=
  if D.componentCount = 0 then 1 else
    let b := GetPrecision D (p.epsilon / 96)
    100 + 10 * D.componentCount + ∑ i : Fin D.componentCount,
      (((D.component i).presentation.facetCount * (d + 1) + d + 4 : ℕ) +
        arithmeticComponentBound D.componentCount b p (D.component i))

end ttc

namespace ttc.Tape

open Arlib.Computation (Num Charged Rate CostVec)
open ttc.Model.Operations ttc.Program ttc.RuntimeBudget
open ArlibCommunity.Algorithms.CV18
open scoped BigOperators ENNReal

variable {d k : ℕ} {F : LRAFormula d k}

private theorem opsTotal_foldlM_uniform {α β : Type} (l : List α)
    (f : β → α → Prog β) (B : ℕ) (h : ∀ s a, opsTotal (f s a).cost = B) (s : β) :
    opsTotal (l.foldlM f s).cost = l.length * B := by
  induction l generalizing s with
  | nil =>
      rw [List.foldlM_nil, List.length_nil, zero_mul]
      exact opsTotal_pure s
  | cons a l ih =>
      simp only [List.foldlM_cons, opsTotal_bind, h, ih, List.length_cons, Nat.succ_mul]
      exact Nat.add_comm ..

private theorem opsTotal_mapM_eq_sum {α β : Type} (l : List α) (f : α → Prog β) :
    opsTotal (l.mapM f).cost = (l.map fun x => opsTotal (f x).cost).sum := by
  induction l with
  | nil => exact opsTotal_pure ([] : List β)
  | cons a l ih =>
      simp only [List.mapM_cons, opsTotal_bind, List.map_cons, List.sum_cons, ih]
      rw [show ∀ as : List β, opsTotal ((pure ((f a).val :: as) : Prog (List β))).cost = 0
        from fun as => opsTotal_pure _]
      simp

private theorem opts_pow (x : Num ℝ) (n : ℕ) : opsTotal (A.pow x n).cost = n + 1 := by
  induction n with
  | zero => exact opsTotal_lit _
  | succ n ih => simp only [A.pow, opsTotal_bind, ih, opsTotal_mul]

private theorem opts_cast (x : Num ℕ) : opsTotal (A.cast x).cost = 1 := by
  simp [A.cast, opsTotal_one]

private theorem opts_log (x : Num ℝ) : opsTotal (A.log x).cost = 1 := by
  simp [A.log, opsTotal_one]

private theorem opts_ceil (x : Num ℝ) : opsTotal (A.ceil x).cost = 1 := by
  simp [A.ceil, opsTotal_one]

attribute [local simp] opts_pow opts_cast opts_log opts_ceil

private theorem opts_load (c : ComponentInput d) :
    opsTotal (load c).cost = c.facetCount * (d + 1) + d + 4 := by
  have hnorm : opsTotal (A.forEach fun j : Fin c.facetCount =>
      A.forEach fun i : Fin d => A.lit (c.normal j i)).cost = c.facetCount * d :=
    opsTotal_forEach_uniform _ _ _ fun _ => by
      simpa using opsTotal_forEach_uniform 1 d _ (fun _ => opsTotal_lit _)
  have hoff : opsTotal (A.forEach fun j : Fin c.facetCount => A.lit (c.offset j)).cost =
      c.facetCount := by
    simpa using opsTotal_forEach_uniform 1 c.facetCount _ (fun _ => opsTotal_lit _)
  have hcen : opsTotal (A.forEach fun i : Fin d => A.lit (c.incenter i)).cost = d := by
    simpa using opsTotal_forEach_uniform 1 d _ (fun _ => opsTotal_lit _)
  simp only [load, opsTotal_bind, opsTotal_lit, opts_cast, opsTotal_pure, hnorm, hoff, hcen]
  ring

private theorem opts_precision (q : Num ℝ) (Ls : List (Loaded d)) :
    opsTotal (getPrecision q Ls).cost = 2 * Ls.length + 6 := by
  have hf (one : Num ℝ) := opsTotal_foldlM_uniform Ls
    (fun acc L => do
      let ratio ← A.div q L.inradius
      A.max acc ratio) 2 (by intros; simp only [opsTotal_bind, opsTotal_div, opsTotal_max]) one
  simp only [getPrecision, opsTotal_bind, opsTotal_lit, hf, opts_log, opts_ceil, opsTotal_div]
  omega

private theorem opts_params (cs : List (ComponentInput d)) (Ls : List (Loaded d))
    (hLs : Ls.length = cs.length) (eps delta : ℝ) :
    opsTotal (paramsProg cs Ls eps delta).cost ≤ 10 * cs.length + 96 := by
  have hf (z o : Num ℕ) := opsTotal_foldlM_uniform cs
    (fun (acc : Num ℕ × Num ℕ) (c : ComponentInput d) => do
      let m' ← A.add acc.1 o
      let r ← A.lit c.facetCount
      let t' ← A.add acc.2 r
      A.pure (m', t')) 3
    (by intros; simp only [opsTotal_bind, opsTotal_add_num, opsTotal_lit, opsTotal_pure]) (z, z)
  simp only [paramsProg, opsTotal_bind, hf, opsTotal_lit, opts_cast, opts_precision, hLs,
    A.mulLit, A.divLit, A.litDiv, opts_log, opts_pow, opsTotal_div, opsTotal_mul,
    opsTotal_add_num, opsTotal_sub, opsTotal_max, opsTotal_pure, pow10, opsTotal_exp,
    latticeRadiusProg, opsTotal_sqrt]
  omega

private theorem opts_cv18Params (K : Params) (L : Loaded d) :
    opsTotal (cv18ParamsProg K L).cost ≤ 20 := by
  simp only [cv18ParamsProg, A.divLit, A.litMax, opsTotal_bind, opsTotal_lit,
    opsTotal_div, opsTotal_max, opts_pow, opsTotal_pure]
  decide

private theorem opts_scaledOffsets (L : Loaded d) (s : Num ℝ) :
    opsTotal (scaledOffsets L s).cost = L.facets := by
  simpa [scaledOffsets] using
    opsTotal_forEach_uniform 1 L.facets (fun i => A.mul s (L.offset i)) (fun _ => opsTotal_mul ..)

private theorem opts_cv18Offsets (hd : 0 < d) (L : Loaded d) :
    opsTotal (cv18Offsets L).cost ≤ L.facets * (2 * d + 2) := by
  unfold cv18Offsets
  apply opsTotal_forEach_le
  intro i
  simp only [opsTotal_bind, opsTotal_dot_pos _ hd, opsTotal_sub, opsTotal_div]
  omega

private theorem opts_walk (hd : 0 < d) (L : Loaded d) (s eta dim : Num ℝ) :
    opsTotal (walkConstantsProg L s eta dim).cost ≤ 100 + d + L.facets * (4 * d + 10) := by
  have hf (κ γ' : Num ℝ) (z' : NumPoint d) :
      opsTotal (A.forEach fun j : Fin L.facets => do
        let sb ← A.mul s (L.offset j)
        let aa ← A.normSq (L.normal j)
        let na ← A.sqrt aa
        let infl ← A.mul κ na
        let bj ← A.add sb infl
        let az ← A.dot d (L.normal j) z'
        let slack ← A.sub bj az
        A.div slack γ').cost = L.facets * (4 * d + 4) := by
    apply opsTotal_forEach_uniform
    intro j
    simp only [opsTotal_bind, opsTotal_dot_pos _ hd, opsTotal_normSq hd,
      opsTotal_mul, opsTotal_sqrt, opsTotal_add_num, opsTotal_sub, opsTotal_div]
    omega
  simp only [walkConstantsProg, A.mulLit, A.divLit, A.litDiv, opsTotal_bind, opsTotal_lit,
    opsTotal_div, opsTotal_mul, opsTotal_add_num, opts_log, opsTotal_sqrt, opsTotal_smul,
    opts_pow, opts_ceil, opsTotal_pure, hf]
  have hh := Nat.mul_le_mul_left L.facets (show 4 * d + 4 ≤ 4 * d + 10 by omega)
  omega

private theorem opsTotal_eq_steps {α : Type} (p : Prog α) :
    opsTotal p.cost = Charged.steps (Rate.unit Op) p := by
  simp [opsTotal, Charged.steps, CostVec.steps]

private theorem opts_scheduleRound (a t : Num ℝ) (one : Num ℕ)
    (s : List (Num ℝ) × Num ℝ × Num ℕ) : opsTotal (scheduleRound a t one s).cost ≤ 12 := by
  have h (v : Num ℝ) : opsTotal (nextVarianceProg a t v).cost ≤ 8 := by
    simp only [nextVarianceProg, opsTotal_bind, opsTotal_lit, opsTotal_le]
    split <;> simp only [A.litDiv, A.mulLit, opsTotal_bind, opsTotal_lit,
      opsTotal_div, opsTotal_mul, opsTotal_add_num, opsTotal_min] <;> decide
  simp only [scheduleRound, opsTotal_bind, opsTotal_le]
  split
  · simp only [opsTotal_pure]; decide
  · simp only [opsTotal_bind, opsTotal_add_num, opsTotal_push, opsTotal_pure]
    have := h s.2.1
    omega

private theorem opts_schedule (a t : Num ℝ) (fuel : Num ℕ) (s : Num ℝ) :
    opsTotal (scheduleProg a t fuel s).cost ≤ 3 + fuel.get * 12 := by
  have hi : ∀ (one : Num ℕ) (st : List (Num ℝ) × Num ℝ × Num ℕ),
      opsTotal (A.iterateWhile (scheduleRound a t one) fuel st).cost ≤ 1 + fuel.get * 12 := by
    intro one st
    rw [opsTotal_eq_steps]
    exact Num.steps_iterateWhile_le (Rate.unit Op)
      (fun _ z => (opsTotal_eq_steps _).symm ▸ opts_scheduleRound a t one z) fuel st
  simp only [scheduleProg, opsTotal_bind, opsTotal_lit, opsTotal_push, opsTotal_pure]
  have := hi (A.lit (1 : ℕ)).val ([], s, (A.lit (1 : ℕ)).val)
  omega

private theorem arithmeticScheduleCap_eq (hd : 3 ≤ d) (D : Decomposition F)
    (p : ApproxParams) (i : Fin D.componentCount) :
    arithmeticScheduleCap d p (arithmeticRoundness (D.component i)) =
      slowPhaseSteps (sealedCV18Params hd D p i) + fastPhaseSteps (sealedCV18Params hd D p i) + 1 :=
  rfl

open Lean Elab Tactic Meta in
set_option maxHeartbeats 400000 in
private theorem opts_runConstants (d : ℕ) (eps roundness failure : Num ℝ) :
    opsTotal (runConstantsProg d eps roundness failure).cost ≤
    let T := max 1 (max (d : ℝ)
      (1024 * roundness.get * d * (max 1 (Real.log (8 / eps.get))) ^ 2))
    200 + 12 * (Nat.ceil (2 * (d : ℝ) * (6 + max 1 (Real.log (d / eps.get)))) +
      Nat.ceil (3 * T) + 1) := by
  let n := (A.cast (A.lit d).val).val
  let l := (A.protectedLog (A.litDiv 8 eps).val).val
  let M := (A.mul (A.mul (A.mulLit 1024 roundness).val n).val (A.pow l 2).val).val
  let T := (A.litMax 1 (A.max n M).val).val
  let s := (A.div eps (A.mulLit 64 n).val).val
  let u := (A.protectedLog (A.div n eps).val).val
  let slow := (A.ceil (A.mul (A.mulLit 2 n).val (A.add (A.lit 6).val u).val).val).val
  let fast := (A.ceil (A.mulLit 3 T).val).val
  let fuel := (A.add slow fast).val
  have hF : fuel.get = Nat.ceil (2 * (d : ℝ) * (6 + max 1 (Real.log (d / eps.get)))) +
      Nat.ceil (3 * max 1 (max (d : ℝ)
        (1024 * roundness.get * d * (max 1 (Real.log (8 / eps.get))) ^ 2))) := by
    simp only [fuel, slow, fast, n, u, T, M, l, getA_add, A.ceil, Num.get_ceil, getA_mul,
      getA_mulLit, getA_lit, getA_cast, getA_div, getA_litDiv, A.protectedLog, A.litMax,
      Charged.val_bind, getA_max, getA_log, get_Apow]
  have hs := opts_schedule n T fuel s
  rw [hF] at hs
  dsimp only [n, T, M, l, s, u, slow, fast, fuel] at hs
  simp only [runConstantsProg, opsTotal_bind, opsTotal_lit, opts_cast, opts_log, opts_ceil, opts_pow,
    opsTotal_sub, opsTotal_add_num, opsTotal_mul, opsTotal_max, opsTotal_div, opsTotal_sqrt,
    opsTotal_exp, opsTotal_pure, A.mulLit, A.divLit, A.litDiv, A.litMax, A.protectedLog]
  -- The cooling loop is the only term whose charge still varies.
  simp only [A.mulLit, A.litDiv, A.litMax, A.protectedLog] at hs
  -- Abstract the one unevaluated tally before doing arithmetic. Do not ask
  -- the arithmetic tactic to normalize the definition of the cooling loop.
  run_tac withMainContext do
    let g ← getMainGoal
    let target ← g.getType
    let h ← getFVarId (mkIdent `hs)
    let ht ← h.getType
    let isTally := fun e : Expr => e.isAppOfArity ``opsTotal 1
    let some tally := target.find? isTally | throwError "expected one cooling tally"
    let some slowBound := ht.find? (·.isAppOf ``Nat.ceil) | throwError "expected a cooling ceiling"
    let some fastBound := ht.find? (fun e => e.isAppOfArity ``Nat.ceil slowBound.getAppNumArgs &&
        e != slowBound) | throwError "expected a second cooling ceiling"
    let cut := fun (e : Expr) (i : Nat) =>
      e.replace fun e =>
        if isTally e then some (.bvar i)
        else if e == slowBound then some (.bvar (i + 2))
        else if e == fastBound then some (.bvar (i + 1))
        else none
    let nat := mkConst ``Nat
    let quantified := mkForall `s .default nat (mkForall `f .default nat
      (mkForall `charge .default nat (mkForall `h .default (cut ht 0) (cut target 1))))
    let sub ← mkFreshExprSyntheticOpaqueMVar quantified
    g.assign (mkAppN sub #[slowBound, fastBound, tally, .fvar h])
    replaceMainGoal [sub.mvarId!]
  intro a b charge h
  clear hs hF
  clear fuel slow fast u s T M l n
  ring_nf at h ⊢
  omega

private theorem opts_componentBase (hd : 3 ≤ d) (D : Decomposition F)
    (p : ApproxParams) (i : Fin D.componentCount) :
    let P := D.component i
    let r := P.presentation.facetCount
    let S := arithmeticScheduleCap d p (arithmeticRoundness P)
    let R := arithmeticCV18Repetitions D.componentCount p
    componentBaseOps (paramsOf D p) (loaded P) ≤
      r * (2 * d + 2) + 20 + (200 + 12 * S) + r +
      (100 + d + r * (4 * d + 10)) + 76 +
      R * (S * (2 * d + 83) + (7 * d + 87) + (4 * R + 5)) := by
  intro P r S R
  let K := paramsOf D p
  let L := loaded P
  let x := (cv18ParamsProg K L).val
  let q := sealedCV18Params hd D p i
  let c := runConstantsProg d x.1 x.2.2 x.2.1
  let G := c.val
  have hmatch : x.1.get = q.eps ∧ x.2.2.get = q.roundness ∧ x.2.1.get = q.p :=
    sealedCV18Params_match hd D p i
  obtain ⟨he, hr, hf⟩ := hmatch
  have hG : (RunConstants.toC G).Holds q := holds_runConstantsProg q x.1 x.2.2 x.2.1 he hr hf
  have hRep : G.repetitions.get = R := hG.repetitions
  have hS := congrArg List.length hG.schedule
  simp only [RunConstants.toC, List.length_map, coolingSchedule, List.length_ofFn] at hS
  have hSchedule : G.schedule.length ≤ S := by
    rw [hS, show S = slowPhaseSteps q + fastPhaseSteps q + 1 from arithmeticScheduleCap_eq hd D p i]
    exact Nat.add_le_add_right (terminalPhaseSteps_le_total q) 1
  have he' : x.1.get = p.epsilon / 24 := he
  have hr' : x.2.2.get = arithmeticRoundness P := hr
  have hC : opsTotal c.cost ≤ 200 + 12 * S := by
    have h := opts_runConstants d x.1 x.2.2 x.2.1
    dsimp only at h
    rw [he', hr'] at h
    exact h
  have h1 := opts_cv18Offsets (d := d) (by omega) L
  have h2 := opts_cv18Params K L
  have h3 := opts_scaledOffsets L K.scale
  have h4 := opts_walk (d := d) (by omega) L K.scale K.epsPrime K.dim
  change opsTotal (cv18Offsets L).cost + opsTotal (cv18ParamsProg K L).cost +
      opsTotal c.cost + opsTotal (scaledOffsets L K.scale).cost +
      opsTotal (walkConstantsProg L K.scale K.epsPrime K.dim).cost + 76 +
      G.repetitions.get * (G.schedule.length * (2 * d + 83) + (7 * d + 87) +
        (4 * G.repetitions.get + 5)) ≤ _
  rw [hRep, h3]
  gcongr

private theorem opts_component (hd : 3 ≤ d) (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) :
    (componentOpsBudget (paramsOf D p) (loaded (D.component i)) : ℝ) ≤
      arithmeticComponentBound D.componentCount (GetPrecision D (p.epsilon / 96)) p
        (D.component i) := by
  let K := paramsOf D p
  let P := D.component i
  let L := loaded P
  obtain ⟨-, hdim, he, -, -, hs, -⟩ := paramsProg_val D p (Nat.zero_lt_of_lt i.isLt)
  change K.dim.get = d at hdim
  change K.epsPrime.get = p.ε' at he
  change K.scale.get = decimalScale (GetPrecision D (p.epsilon / 96)) at hs
  have hw := walkC_steps P (GetPrecision D (p.epsilon / 96)) p.ε' K.scale K.epsPrime K.dim hs he hdim
  have hw' : (walkConstantsProg L K.scale K.epsPrime K.dim).val.steps.get =
      arithmeticWalkLength P (GetPrecision D (p.epsilon / 96)) p.epsilon := hw
  have hbase := opts_componentBase hd D p i
  dsimp only at hbase
  have h := sealed_componentOpsBudget_le_inverseSquare hd D p i
  dsimp only at h
  refine h.trans ?_
  change (componentBaseOps K L : ℝ) +
      ((componentPerCopyOps K L : ℝ) * populationCapNumerator p D.componentCount +
        (componentPerQueryOps L : ℝ) * cv18QueryNumerator (sealedCV18Params hd D p i)) /
        p.epsilon ^ 2 ≤ _
  unfold componentPerCopyOps
  dsimp only
  rw [hw']
  apply add_le_add
  · exact_mod_cast hbase
  · exact le_rfl

/-- The measured implementation budget is bounded by the input-only formula. -/
theorem estimatorOpsBudget_le_arithmeticBound (hd : 3 ≤ d) (D : Decomposition F)
    (p : ApproxParams) :
    (estimatorOpsBudget (SealedRun.componentsOf D) p.epsilon p.delta : ℝ) ≤
      ttcArithmeticBound D p := by
  let cs := SealedRun.componentsOf D
  have hlen : cs.length = D.componentCount := List.length_ofFn
  by_cases hm : D.componentCount = 0
  · have hnil : cs = [] := List.length_eq_zero_iff.mp (hlen.trans hm)
    simp [ttcArithmeticBound, hm, ← show cs = SealedRun.componentsOf D from rfl, hnil, estimatorOpsBudget]
  have hcons : cs ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlen
    exact hm hlen.symm
  let c := cs.mapM load
  let M := paramsProg cs c.val p.epsilon p.delta
  have hK : M.val = paramsOf D p := by simp only [M, c, paramsOf, val_mapM, cs]
  have hsize : c.val.length = cs.length := by simp [c, val_mapM]
  have h0 : estimatorOpsBudget cs p.epsilon p.delta = opsTotal c.cost + opsTotal M.cost + 4 +
      (c.val.map (componentOpsBudget M.val)).sum := by
    cases h : cs with
    | nil => exact (hcons h).elim
    | cons z zs => simp only [c, M, h, estimatorOpsBudget]
  have hload : opsTotal c.cost = ∑ i : Fin D.componentCount,
      ((D.component i).presentation.facetCount * (d + 1) + d + 4) := by
    rw [show c = cs.mapM load from rfl, opsTotal_mapM_eq_sum]
    simp only [opts_load, cs, SealedRun.componentsOf, List.map_ofFn, Function.comp_def,
      SealedRun.componentInput, List.sum_ofFn]
  have hval : c.val = List.ofFn (fun i : Fin D.componentCount => loaded (D.component i)) := by
    simp only [c, cs, val_mapM, SealedRun.componentsOf, List.map_ofFn, Function.comp_def,
      val_load_componentInput]
  have hparams : opsTotal M.cost ≤ 10 * D.componentCount + 96 :=
    (opts_params cs c.val hsize _ _).trans_eq (by rw [hlen])
  change (estimatorOpsBudget cs p.epsilon p.delta : ℝ) ≤ _
  rw [h0, hload, hK, hval, List.map_ofFn, List.sum_ofFn, ttcArithmeticBound, ite_eq_right hm]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_ofNat, Function.comp_apply, Nat.cast_mul, Nat.cast_one]
  conv_rhs => rw [Finset.sum_add_distrib]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin D.componentCount))) =>
    opts_component hd D p i)
  have hP : (opsTotal M.cost : ℝ) ≤ 10 * D.componentCount + 96 := by exact_mod_cast hparams
  linarith only [hsum, hP]

theorem sealed_expectedOperations_le_arithmeticBound (hn : 3 ≤ d) (F : LRAFormula d k)
    (hb : Bornology.IsBounded (solutionSet F)) (p : ApproxParams)
    (prep : TTCPreprocessor d k) :
    SealedRun.expectedOperations F hb p prep ≤ ENNReal.ofReal (ttcArithmeticBound (prep.run F hb) p) := by
  refine (sealed_expectedOperations_le hn F hb p prep).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (estimatorOpsBudget_le_arithmeticBound (by omega) (prep.run F hb) p)

end ttc.Tape

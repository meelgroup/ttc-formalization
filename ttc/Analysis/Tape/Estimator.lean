/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Params
import ttc.Analysis.CV18Admissible

/-!
# The whole run, with fuel

On a nonempty decomposition the sealed program loads the components, computes the
parameters, runs the loop and outputs `|X| / (p · 10^{bn})`.  With `fuel` rounds for its
unbounded loops its output law is the old loop's with the same fuel, mapped by the old
output `Est` (`estimator_law`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc (TTCState)
open ArlibCommunity.Algorithms.CV18 (measurable_some)

variable {d : ℕ}

theorem isProbabilityMeasure_vlaw {α : Type} [MeasurableSpace α] (p : Tree d α) (b : ℕ)
    (hm : Measurable fun t => outcome (exec p b t)) : IsProbabilityMeasure (vlaw p b) := by
  rw [vlaw, ← tapeLaw_map_exec p b hm]
  have := Measure.isProbabilityMeasure_map (μ := ttc.SealedRun.tapeLaw d) hm.aemeasurable
  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

variable {k : ℕ} {F : ttc.LRAFormula d k}

/-- The run's parameters on a decomposition. -/
def paramsOf (D : ttc.Decomposition F) (p : ttc.ApproxParams) : Params :=
  (paramsProg (ttc.SealedRun.componentsOf D)
    ((ttc.SealedRun.componentsOf D).map fun c => (load c).val) p.epsilon p.delta).val

/-- The sealed sampler's law on a component, with `fuel` rounds. -/
def samplerLaw (K : Params) (fuel b' : ℕ) (P : ttc.PolytopeData d) : Measure (Option (Fin d → ℤ)) :=
  (vlaw (sampleUntilAcceptedT (loaded P) (walkConstantsProg (loaded P) K.scale K.epsPrime K.dim).val
    (scaledOffsets (loaded P) K.scale).val K.dimN fuel) b').map (Option.map getZ)

theorem isProbabilityMeasure_samplerLaw (K : Params) (fuel b' : ℕ) (P : ttc.PolytopeData d) :
    IsProbabilityMeasure (samplerLaw K fuel b' P) := by
  have := isProbabilityMeasure_vlaw _ b'
    ((mf_sampleUntilAccepted (Q := Unit) (loaded P) (walkConstantsProg (loaded P) K.scale
      K.epsPrime K.dim).val (scaledOffsets (loaded P) K.scale).val K.dimN fuel).outcome () b')
  exact Measure.isProbabilityMeasure_map (measurable_optionMap measurable_getZ).aemeasurable

/-- The output `|X| / (p · 10^{bn})`, read off a view. -/
def estView (b : ℕ) (w : ℝ × ℕ) : NNReal :=
  Real.toNNReal ((Multiset.card (decMS (d := d) w.2) : ℝ) / (w.1 * 10 ^ (b * d)))

theorem est_eq_estView (b : ℕ) (y : TTCState d) : ttc.Est b y = estView (d := d) b (stVO y) := by
  simp only [estView, stVO, decMS_encMS, Multiset.card_map, ttc.Est]
  rw [show (Multiset.card y.X.val : ℝ) = ((y.X.card : NNReal) : ℝ) by rw [NNReal.coe_natCast]; rfl]
  rw [show ((10 : ℝ) ^ (b * d)) = (((10 : NNReal) ^ (b * d) : NNReal) : ℝ) by push_cast; rfl,
    ← NNReal.coe_mul, ← NNReal.coe_div, Real.toNNReal_coe]

theorem vlaw_computeBind {δ β : Type} [MeasurableSpace β] (c : Prog δ) (f : δ → Tree d β)
    (b : ℕ) : vlaw ((compute c).bind f) b = vlaw (f c.val) b :=
  vlaw_step c f b

theorem estimatorT_cons (fuel : ℕ) (cs : List (ttc.ComponentInput d)) (hcs : cs ≠ [])
    (eps delta : ℝ) :
    estimatorT (cv18T d) fuel cs eps delta =
      (compute (cs.mapM load)).bind fun Ls =>
      (compute (paramsProg cs Ls eps delta)).bind fun K =>
      (compute (A.lit (0 : ℕ))).bind fun zero =>
      (Ls.foldlM (fun s L => stepT (cv18T d) fuel K L s) (⟨K.thresh, [], zero⟩ : State d)).bind
        fun final => compute (do
          let size ← A.cast final.size
          let den ← A.mul final.p K.scaleN
          A.div size den) := by
  cases cs with
  | nil => exact absurd rfl hcs
  | cons c cs => rfl

/-- The output's arithmetic. -/
noncomputable def outProg (K : Params) (final : State d) : Prog (Num ℝ) := do
  let size ← A.cast final.size
  let den ← A.mul final.p K.scaleN
  A.div size den

theorem get_outProg (K : Params) (final : State d) :
    (outProg K final).val.get = final.size.get / (final.p.get * K.scaleN.get) := by
  simp [outProg, Charged.val_bind, A.cast, A.mul, A.div, Num.get_div, Num.get_mul, Num.get_cast]

/-- **The sealed program with fuel has the old loop's law with the same fuel**, mapped by the
old output `Est`. -/
theorem estimator_law (hn : 3 ≤ d) (D : ttc.Decomposition F) (p : ttc.ApproxParams)
    (hm : 0 < D.componentCount) (fuel b' : ℕ) :
    (vlaw (estimatorT (cv18T d) fuel (ttc.SealedRun.componentsOf D) p.epsilon p.delta) b').map
        (Option.map fun x => Real.toNNReal x.get) =
      (oldFoldF hn p.ε' (p.δ' D.componentCount) (p.Thresh D.componentCount) fuel
          (ttc.GetPrecision D p.precisionEta) (samplerLaw (paramsOf D p) fuel b')
          (List.ofFn D.component) (TTCState.initial d (p.Thresh D.componentCount))).map
        (Option.map (ttc.Est (ttc.GetPrecision D p.precisionEta))) := by
  classical
  set cs := ttc.SealedRun.componentsOf D with hcsdef
  set K := paramsOf D p with hK
  set bP := ttc.GetPrecision D p.precisionEta
  set m := D.componentCount
  have hcs : cs ≠ [] := by
    simp only [cs, ttc.SealedRun.componentsOf, ne_eq, List.ofFn_eq_nil_iff]
    omega
  obtain ⟨hdimN, hdim, he, hdl, hth, hs, hsN⟩ : K.dimN.get = d ∧ K.dim.get = d ∧
      K.epsPrime.get = p.ε' ∧ K.deltaPrime.get = p.δ' m ∧ K.thresh.get = p.Thresh m ∧
      K.scale.get = ttc.decimalScale bP ∧ K.scaleN.get = 10 ^ (bP * d) :=
    paramsProg_val D p hm
  have hLs : cs.map (fun c => (load c).val) = (List.ofFn D.component).map loaded := by
    simp [cs, ttc.SealedRun.componentsOf, List.map_ofFn, Function.comp_def,
      val_load_componentInput]
  have hvN : Measurable (stVN (d := d)) := (stCorr (d := d) 0).measurable_vN
  have hvO : Measurable (stVO (d := d)) := (stCorr (d := d) 0).measurable_vO
  rw [estimatorT_cons fuel cs hcs, vlaw_computeBind, vlaw_computeBind, vlaw_computeBind,
    val_mapM]
  change (vlaw ((((cs.map fun c => (load c).val)).foldlM (fun s L => stepT (cv18T d) fuel K L s)
    (⟨K.thresh, [], (A.lit (0 : ℕ)).val⟩ : State d)).bind fun final =>
      compute (outProg K final)) b').map _ = _
  rw [hLs]
  set x0 : State d := ⟨K.thresh, [], (A.lit (0 : ℕ)).val⟩
  set fold := ((List.ofFn D.component).map loaded).foldlM
    (fun s L => stepT (cv18T d) fuel K L s) x0
  have hmF : Measurable fun τ => outcome (exec fold b' τ) :=
    ((MeasFam.foldlM_fixed (A := Unit) (g := fun _ s L => stepT (cv18T d) fuel K L s)
      (fun L => mf_step fuel K L measurable_snd) ((List.ofFn D.component).map loaded)).outcome
        ((), x0) b')
  have hMP : MP fun final : State d => outProg K final := by
    unfold outProg
    exact MP.bind' (mp_cast (State.measurable_size)) (MP.bind' (mp_mul
      (State.measurable_p.comp measurable_fst) measurable_const) (mp_div (by fun_prop)
        measurable_snd))
  have hmO : MeasFam fun final : State d => compute (n := d) (outProg K final) :=
    MeasFam.computeEnd hMP
  rw [vlaw_bind_capFirst hmO (fun _ => trivial) fold b' hmF b']
  have hk : (fun o : Option (State d) => o.elim (Measure.dirac none) fun a =>
      vlaw (compute (n := d) (outProg K a)) b') =
      fun o => Measure.dirac (Option.map (fun a => (outProg K a).val) o) := by
    funext o
    rcases o with _ | a
    · rfl
    · simp [vlaw_compute]
  rw [hk, Measure.bind_dirac_eq_map _ (measurable_optionMap hMP.1),
    Measure.map_map (g := Option.map fun x : Num ℝ => Real.toNNReal x.get)
      (f := Option.map fun a => (outProg K a).val)
      (measurable_optionMap (measurable_real_toNNReal.comp Num.measurable_get))
      (measurable_optionMap hMP.1)]
  -- the output reads the view
  have hx0 : 0 ≤ x0.p.get := by
    show 0 ≤ K.thresh.get
    rw [hth]
    exact (p.threshold_pos _).le
  have hpost : Post fold fun s => 0 ≤ s.p.get ∧ s.size.get = s.X.length :=
    post_foldlM (I := fun s : State d => 0 ≤ s.p.get ∧ s.size.get = s.X.length)
      (fun s L hs => post_stepT fuel K L s hs.1) _ x0 ⟨hx0, by simp [x0, A.lit]⟩
  have hEV : Measurable (estView (d := d) bP) := by
    unfold estView
    exact measurable_real_toNNReal.comp (((measurable_of_countable
      (fun n : ℕ => (Multiset.card (decMS (d := d) n) : ℝ))).comp measurable_snd).div
        (measurable_fst.mul_const _))
  have hae : ((Option.map fun x : Num ℝ => Real.toNNReal x.get) ∘
      Option.map fun a => (outProg K a).val)
      =ᵐ[vlaw fold b'] Option.map (estView (d := d) bP) ∘ Option.map stVN := by
    filter_upwards [ae_vlaw_post hpost measurableSet_stateOk b' hmF] with o ho
    rcases o with _ | a
    · rfl
    · obtain ⟨_, hsz⟩ := ho a rfl
      simp only [Option.map_some, Function.comp_apply, Option.some.injEq]
      rw [get_outProg, hsN, hsz]
      simp only [estView, stVN, decMS_encMS, Multiset.coe_card, List.length_map]
  rw [Measure.map_congr hae, ← Measure.map_map (measurable_optionMap hEV) (measurable_optionMap hvN),
    fold_piece hn p.ε' (p.δ' m) (p.Thresh m) fuel bP (samplerLaw K fuel b') K b'
      (ttc.CommunityCV18.admissibleTTCRequest D p ⟨0, hm⟩) he hdl hth (p.threshold_pos m) hdim hdimN hs hsN
      (fun P => isProbabilityMeasure_samplerLaw K fuel b' P) (List.ofFn D.component)
      (fun P _ => rfl) x0 (TTCState.initial d (p.Thresh m)) ?_,
    Measure.map_map (measurable_optionMap hEV) (measurable_optionMap hvO)]
  · congr 1
    funext o
    rcases o with _ | y
    · rfl
    · simp only [Option.map_some, Function.comp_apply, est_eq_estView]
  · refine ⟨hx0, ⟨?_, fun c hc => by simp [TTCState.initial] at hc⟩, ?_⟩
    · simp [ttc.TTCState.LabelsFresh, TTCState.initial]
    · show (K.thresh.get, _) = (_, _)
      simp only [hth, TTCState.initial, Real.coe_toNNReal _ (p.threshold_pos m).le,
        Finset.empty_val, Multiset.map_zero]
      rfl

end ttc.Tape

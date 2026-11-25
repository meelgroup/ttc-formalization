/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.SampleLaw

/-!
# Attempts until one is accepted, with fuel

`sampleUntilAcceptedT … fuel` makes at most `fuel` attempts and stops the run if none is
accepted.  When one attempt is accepted with probability `1 − c`, its result has the law
(`retryLaw_eq'`)

  `(1 − c^fuel) · (the accepted attempt's law) + c^fuel · (stop)`,

so as the fuel grows it becomes the old model's "retry until accepted" law, the proposal law
conditioned on acceptance (`vlaw_sampleUntilAcceptedT`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ArlibCommunity.Algorithms.CV18 (measurable_some optionToSum measurable_optionToSum)
open ArlibCommunity.Foundations.MarkovChainTheory (iterate)

/-! ## Optional values -/

section Option

variable {β : Type} [MeasurableSpace β]

theorem measurableSet_none : MeasurableSet ({none} : Set (Option β)) := by
  have : ({none} : Set (Option β)) = optionToSum ⁻¹' Set.range Sum.inl := by
    ext o; cases o <;> simp [optionToSum]
  rw [this]
  exact measurable_optionToSum measurableSet_range_inl

theorem measurableSet_range_some : MeasurableSet (Set.range (some : β → Option β)) := by
  have : Set.range (some : β → Option β) = optionToSum ⁻¹' Set.range Sum.inr := by
    ext o; cases o <;> simp [optionToSum]
  rw [this]
  exact measurable_optionToSum measurableSet_range_inr

theorem measurable_optionElimKernel {γ : Type} [MeasurableSpace γ] (m : Measure γ)
    {f : β → Measure γ} (hf : Measurable f) : Measurable fun o : Option β => o.elim m f := by
  have : (fun o : Option β => o.elim m f) = Sum.elim (fun _ : Unit => m) f ∘ optionToSum := by
    funext o; cases o <;> rfl
  rw [this]
  exact (Measurable.sumElim measurable_const hf).comp measurable_optionToSum

end Option

/-! ## The retry law -/

section Retry

variable {β : Type} [MeasurableSpace β]

/-- **At most `fuel` attempts with law `ν`** (`none` = rejected), stopping (`none`) if all
are rejected. -/
def retryLaw (ν : Measure (Option β)) : ℕ → Measure (Option β)
  | 0 => Measure.dirac none
  | f + 1 => ν.bind fun r => r.elim (retryLaw ν f) fun w => Measure.dirac (some w)

/-- **The retry law, in closed form**: with `c` the rejection probability, a stop with
probability `c^fuel`, and otherwise an accepted attempt. -/
theorem retryLaw_eq (ν : Measure (Option β)) :
    ∀ f : ℕ, retryLaw ν f = (∑ j ∈ Finset.range f, ν {none} ^ j) • ν.restrict (Set.range some) +
      ν {none} ^ f • Measure.dirac none
  | 0 => by simp [retryLaw]
  | f + 1 => by
      ext S hS
      have hK : Measurable fun r : Option β =>
          r.elim (retryLaw ν f) fun w => Measure.dirac (some w) :=
        measurable_optionElimKernel _ (Measure.measurable_dirac.comp measurable_some)
      have hpt : ∀ r : Option β, (r.elim (retryLaw ν f) fun w => Measure.dirac (some w)) S =
          ({none} : Set (Option β)).indicator (fun _ => retryLaw ν f S) r +
            (Set.range some ∩ S).indicator 1 r := by
        intro r
        rcases r with _ | w
        · simp
        · by_cases hw : some w ∈ S
          · simp [Measure.dirac_apply' _ hS, hw]
          · simp [Measure.dirac_apply' _ hS, hw]
      rw [retryLaw, Measure.bind_apply hS hK.aemeasurable]
      simp_rw [hpt]
      rw [lintegral_add_left (measurable_const.indicator measurableSet_none),
        lintegral_indicator_const measurableSet_none,
        lintegral_indicator_one (measurableSet_range_some.inter hS), retryLaw_eq ν f]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply hS, Finset.sum_range_succ', pow_zero, pow_succ]
      rw [Set.inter_comm, ← Finset.sum_mul]
      ring

theorem retryLaw_none (ν : Measure (Option β)) :
    ν.restrict (Set.range some) {none} = 0 := by
  rw [Measure.restrict_apply measurableSet_none]
  convert measure_empty (μ := ν)
  ext o; cases o <;> simp

end Retry

/-! ## The sampler -/

variable {d : ℕ}

theorem free_sampleTryT (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) : Free (sampleTryT L W scaled dimN) := by
  rw [sampleTryT_eq]
  exact Free.bind (free_startT dimN) fun y₀ =>
    Free.bind (free_hitAndRunWalkT _ _ _ _ _) fun y => free_finishT L W scaled y

/-- The rounded proposal law: walk from the start law, map by the chart, round. -/
def proposalLaw [NeZero d] (L : Loaded d) (W : WalkConstants d L.facets) :
    Measure (Fin d → ℤ) :=
  (iterate (walkKernel L W) (ballStartLaw d) W.steps.get).bind fun z =>
    roundPointLaw (toPt (chartProg W (ofPt z)).val)

/-- One attempt's verdict, on the rounded proposal: `some w` if accepted. -/
def acceptOpt (L : Loaded d) (scaled : Fin L.facets → Num ℝ) (w : Fin d → ℤ) :
    Option (Fin d → ℤ) :=
  if accepts L scaled w then some w else none

theorem verdict_eq (L : Loaded d) (scaled : Fin L.facets → Num ℝ) :
    verdict L scaled = some ∘ acceptOpt L scaled := rfl

/-- The law of one attempt's verdict. -/
def attemptLaw [NeZero d] (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) : Measure (Option (Fin d → ℤ)) :=
  (proposalLaw L W).map (acceptOpt L scaled)

/-- The rounding law at a point, by its formula. -/
theorem roundPointLaw_eq_map (x : EuclideanSpace ℝ (Fin d)) :
    roundPointLaw x = (Measure.pi fun _ : Fin d => uniformUnit).map
      fun v : Fin d → ℝ => fun i : Fin d => ⌊x i⌋ + if v i < x i - ⌊x i⌋ then (1 : ℤ) else 0 := by
  rw [roundPointLaw]
  congr 1
  funext v
  rw [RoundPoint.roundPoint_value]

/-- **The rounding law depends measurably on the point.** -/
theorem measurable_roundPointLaw : Measurable (roundPointLaw (n := d)) := by
  let R : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) → Fin d → ℤ := fun q i =>
    ⌊q.1 i⌋ + if q.2 i < q.1 i - ⌊q.1 i⌋ then (1 : ℤ) else 0
  have hR : Measurable R := by
    refine measurable_pi_iff.mpr fun i => ?_
    have h1 : Measurable fun q : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) => q.1 i :=
      (EuclideanSpace.proj i).continuous.measurable.comp measurable_fst
    have h2 : Measurable fun q : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) => q.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    have hf : Measurable fun q : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) => ⌊q.1 i⌋ :=
      Int.measurable_floor.comp h1
    have h3 : Measurable fun q : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) => ((⌊q.1 i⌋ : ℤ) : ℝ) :=
      (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp hf
    have hc : MeasurableSet {q : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) |
        q.2 i < q.1 i - ⌊q.1 i⌋} := measurableSet_lt h2 (h1.sub h3)
    have hite : Measurable fun q : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) =>
        if q.2 i < q.1 i - ⌊q.1 i⌋ then (1 : ℤ) else 0 :=
      Measurable.ite hc measurable_const measurable_const
    exact (measurable_of_countable (fun p : ℤ × ℤ => p.1 + p.2)).comp (hf.prodMk hite)
  have heq : roundPointLaw (n := d) = fun x =>
      (Measure.pi fun _ : Fin d => uniformUnit).map fun v => R (x, v) :=
    funext fun x => roundPointLaw_eq_map x
  rw [heq]
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have e : ∀ x, ((Measure.pi fun _ : Fin d => uniformUnit).map fun v => R (x, v)) S =
      (Measure.pi fun _ : Fin d => uniformUnit) (Prod.mk x ⁻¹' (R ⁻¹' S)) := fun x =>
    Measure.map_apply (hR.comp (measurable_const.prodMk measurable_id)) hS
  simp only [e]
  exact measurable_measure_prodMk_left (hR hS)

/-- The chart's point, as a function of the walk's end point. -/
theorem measurable_chartPt {r : ℕ} (W : WalkConstants d r) :
    Measurable fun z : EuclideanSpace ℝ (Fin d) => toPt (chartProg W (ofPt z)).val :=
  measurable_toPt.comp (mp_chart W measurable_ofPt).1

/-- One attempt, viewed: its verdict's law. -/
theorem vlaw_sampleTryT' [NeZero d] (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) (hdim : dimN.get = d)
    (hK : Bornology.IsBounded (walkBody L W))
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ walkBody L W) (b : ℕ) :
    (vlaw (sampleTryT L W scaled dimN) b).map attemptView = (attemptLaw L W scaled).map some := by
  have hRP : Measurable fun z => roundPointLaw (toPt (chartProg W (ofPt z)).val) :=
    measurable_roundPointLaw.comp (measurable_chartPt W)
  rw [vlaw_sampleTryT L W scaled dimN hdim hK hball b, attemptLaw, proposalLaw,
    Measure.map_map measurable_some (measurable_of_countable _),
    Measure.map_bind hRP.aemeasurable (measurable_of_countable _).aemeasurable]
  congr 1
  funext z
  rw [finishLaw_eq, verdict_eq]


theorem mf_retryCont (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) (f : ℕ) :
    MeasFam fun r : Option (Fin d → Num ℤ) =>
      r.elim (sampleUntilAcceptedT L W scaled dimN f) Tree.pure :=
  MeasFam.optionElim (o := id) measurable_id (mf_sampleUntilAccepted L W scaled dimN f)
    (MeasFam.pure measurable_snd)

/-- **At most `fuel` attempts**: the sampler's result has the retry law of one attempt's
verdict. -/
theorem vlaw_sampleUntilAcceptedT [NeZero d] (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) (hdim : dimN.get = d)
    (hK : Bornology.IsBounded (walkBody L W))
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ walkBody L W) (b : ℕ) :
    ∀ fuel : ℕ, (vlaw (sampleUntilAcceptedT L W scaled dimN fuel) b).map (Option.map getZ) =
      retryLaw (attemptLaw L W scaled) fuel
  | 0 => by
      show (vlaw Tree.fail b).map _ = _
      rw [vlaw_fail, Measure.map_dirac' (measurable_optionMap measurable_getZ)]
      rfl
  | f + 1 => by
      have hm : Measurable fun t => outcome (exec (sampleTryT L W scaled dimN) b t) :=
        (mf_sampleTry (Q := Unit) L W scaled dimN).outcome () b
      have hk := mf_retryCont L W scaled dimN f
      have hkv := hk.measurable_vlaw b
      -- one attempt's law, held
      have hT : vlaw (sampleTryT L W scaled dimN) b =
          (attemptLaw L W scaled).map fun r => some (Option.map sealZ r) := by
        have h := congrArg (Measure.map (Option.map (Option.map sealZ)))
          (vlaw_sampleTryT' L W scaled dimN hdim hK hball b)
        rw [attemptView, Measure.map_map (measurable_optionMap (measurable_optionMap measurable_sealZ))
            (measurable_optionMap (measurable_optionMap measurable_getZ)),
          Measure.map_map (measurable_optionMap (measurable_optionMap measurable_sealZ))
            measurable_some] at h
        have hid : Option.map (Option.map sealZ) ∘ Option.map (Option.map (getZ (k := d))) = id := by
          funext o; rcases o with _ | _ | z <;> simp
        rw [hid, Measure.map_id] at h
        rw [h]
        rfl
      show (vlaw ((sampleTryT L W scaled dimN).bind fun r =>
        r.elim (sampleUntilAcceptedT L W scaled dimN f) Tree.pure) b).map _ = _
      rw [vlaw_bind hk (free_sampleTryT L W scaled dimN) b hm, hT,
        Measure.bind_map (f := fun r => some (Option.map sealZ r))
          (measurable_some.comp (measurable_optionMap measurable_sealZ)).aemeasurable
          (measurable_optionKernel hkv).aemeasurable]
      simp only [Option.elim_some]
      rw [Measure.map_bind (show Measurable fun r : Option (Fin d → ℤ) =>
          vlaw ((Option.map sealZ r).elim (sampleUntilAcceptedT L W scaled dimN f) Tree.pure) b from
          hkv.comp (measurable_optionMap measurable_sealZ)).aemeasurable
          (measurable_optionMap measurable_getZ).aemeasurable, retryLaw]
      congr 1
      funext r
      rcases r with _ | w
      · exact vlaw_sampleUntilAcceptedT L W scaled dimN hdim hK hball b f
      · show (vlaw (Tree.pure (sealZ w)) b).map _ = _
        rw [vlaw_pure, Measure.map_dirac' (measurable_optionMap measurable_getZ)]
        simp

/-- The accepted part of one attempt's verdict is the proposal law on the accepted points. -/
theorem attemptLaw_restrict_some [NeZero d] (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) :
    (attemptLaw L W scaled).restrict (Set.range some) =
      ((proposalLaw L W).restrict {w | accepts L scaled w}).map some := by
  ext S hS
  rw [Measure.restrict_apply hS, attemptLaw, Measure.map_apply (measurable_of_countable _)
    (hS.inter measurableSet_range_some), Measure.map_apply measurable_some hS,
    Measure.restrict_apply ((Set.to_countable _).measurableSet)]
  congr 1
  ext w
  simp only [acceptOpt, Set.mem_preimage, Set.mem_inter_iff, Set.mem_range, Set.mem_ofPred_eq]
  split_ifs with h <;> simp [h]

/-- One attempt is rejected with the proposal law's probability of a rejected point. -/
theorem attemptLaw_none [NeZero d] (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) :
    attemptLaw L W scaled {none} = proposalLaw L W {w | accepts L scaled w = false} := by
  rw [attemptLaw, Measure.map_apply (measurable_of_countable _) measurableSet_none]
  congr 1
  ext w
  simp only [acceptOpt, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  split_ifs with h <;> simp [h]

/-- **The sampler with fuel, in closed form**: with `c` the probability that a proposal is
rejected, it stops with probability `c^fuel` and otherwise returns a proposal conditioned on
acceptance — the old model's retry-until-accepted law (`acceptedRoundedLatticeLaw`). -/
theorem vlaw_sampleUntilAcceptedT_eq [NeZero d] (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) (hdim : dimN.get = d)
    (hK : Bornology.IsBounded (walkBody L W))
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ walkBody L W) (b fuel : ℕ) :
    (vlaw (sampleUntilAcceptedT L W scaled dimN fuel) b).map (Option.map getZ) =
      (∑ j ∈ Finset.range fuel, proposalLaw L W {w | accepts L scaled w = false} ^ j) •
          ((proposalLaw L W).restrict {w | accepts L scaled w}).map some +
        proposalLaw L W {w | accepts L scaled w = false} ^ fuel • Measure.dirac none := by
  rw [vlaw_sampleUntilAcceptedT L W scaled dimN hdim hK hball b fuel, retryLaw_eq,
    attemptLaw_restrict_some, attemptLaw_none]

/-- The restriction to the accepted points is the conditioned law, scaled by the acceptance
probability. -/
theorem restrict_eq_smul_condOn {X : Type} [MeasurableSpace X] (μ : Measure X) (S : Set X)
    (h0 : μ S ≠ 0) (htop : μ S ≠ ⊤) :
    μ.restrict S = μ S • ArlibCommunity.Foundations.Convex.condOn μ S := by
  rw [ArlibCommunity.Foundations.Convex.condOn, smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]

end ttc.Tape

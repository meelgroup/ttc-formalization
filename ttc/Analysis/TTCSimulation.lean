import ttc.Analysis.SampleAppendTape
import ttc.Analysis.GivenVolumeFold
import ttc.Analysis.RunMarginal
import ttc.Analysis.OracleNormalization

/-!
# Algorithm `ttc` is the reference run with its rate multiplied by `Thresh`

Algorithm `ttc` starts from `p = Thresh` and scales volumes by `10^{bn}`; the reference
run (`ReferenceProgram.lean`) starts from `p = 1` and scales volumes by
`Thresh · 10^{bn}`. Every product `t · p`, hence every Poisson mean, guard and number
of halvings, agrees, and the algorithm's state is the reference state with `p`
multiplied by `Thresh`. Consequently the two runs have the same output law and the
same charged output law.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace ttc

/-! ## The rate rescaling -/

/-- Multiply the rate of a state by `c`. -/
def TTCState.scaleRate {n : Nat} (c : NNReal) (s : TTCState n) : TTCState n :=
  { s with p := c * s.p }

/-- Divide the rate of a state by `c`. -/
def TTCState.unscaleRate {n : Nat} (c : NNReal) (s : TTCState n) : TTCState n :=
  { s with p := s.p / c }

theorem TTCState.scaleRate_unscaleRate {n : Nat} {c : NNReal} (hc : c ≠ 0)
    (s : TTCState n) : (s.unscaleRate c).scaleRate c = s := by
  cases s
  simp [TTCState.scaleRate, TTCState.unscaleRate, mul_div_cancel₀ _ hc]

private theorem measurable_state_coords {n : Nat} :
    Measurable (fun s : TTCState n => (s.p, s.X, s.nextLabel)) :=
  comap_measurable _

@[fun_prop]
theorem measurable_scaleRate {n : Nat} (c : NNReal) :
    Measurable (TTCState.scaleRate (n := n) c) := by
  have hrate : Measurable (fun s : TTCState n => s.p) :=
    measurable_fst.comp measurable_state_coords
  have hsamples : Measurable (fun s : TTCState n => s.X) :=
    (measurable_fst.comp measurable_snd).comp measurable_state_coords
  have hnext : Measurable (fun s : TTCState n => s.nextLabel) :=
    (measurable_snd.comp measurable_snd).comp measurable_state_coords
  rw [measurable_comap_iff]
  change Measurable (fun s : TTCState n => (c * s.p, s.X, s.nextLabel))
  exact (measurable_const.mul hrate).prodMk (hsamples.prodMk hnext)

theorem measurable_unscaleRate {n : Nat} (c : NNReal) :
    Measurable (TTCState.unscaleRate (n := n) c) := by
  have hrate : Measurable (fun s : TTCState n => s.p) :=
    measurable_fst.comp measurable_state_coords
  have hsamples : Measurable (fun s : TTCState n => s.X) :=
    (measurable_fst.comp measurable_snd).comp measurable_state_coords
  have hnext : Measurable (fun s : TTCState n => s.nextLabel) :=
    (measurable_snd.comp measurable_snd).comp measurable_state_coords
  rw [measurable_comap_iff]
  change Measurable (fun s : TTCState n => (s.p / c, s.X, s.nextLabel))
  exact (hrate.div_const c).prodMk (hsamples.prodMk hnext)

/-- Rescale the state coordinate of a pair. -/
def scaleRateFst {n : Nat} {β : Type*} (c : NNReal) (z : TTCState n × β) :
    TTCState n × β :=
  (z.1.scaleRate c, z.2)

@[fun_prop]
theorem measurable_scaleRateFst {n : Nat} {β : Type*} [MeasurableSpace β]
    (c : NNReal) : Measurable (scaleRateFst (n := n) (β := β) c) :=
  ((measurable_scaleRate c).comp measurable_fst).prodMk measurable_snd

/-! ## Pointwise agreement of the two parametrisations -/

/-- The paper's `k = ⌈log₂ (x / Thresh)⌉` (or `0`) is the first `r` with
`x / 2^r ≤ Thresh`. -/
theorem rateHalvings_eq_sInf (x : NNReal) {Thresh : Real} (hThresh : 0 < Thresh) :
    (if Thresh ≤ (x : Real) then Nat.ceil (Real.logb 2 ((x : Real) / Thresh)) else 0) =
      sInf {rounds : Nat | ((x / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ Thresh} := by
  have hmem (r : Nat) :
      r ∈ {rounds : Nat | ((x / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ Thresh} ↔
        (x : Real) / Thresh ≤ (2 : Real) ^ r := by
    simp only [Set.mem_setOf_eq, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
    rw [div_le_iff₀ (by positivity), div_le_iff₀ hThresh, mul_comm]
  split_ifs with hle
  · have hpos : 0 < (x : Real) / Thresh := div_pos (by linarith) hThresh
    have hiff (r : Nat) :
        r ∈ {rounds : Nat | ((x / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ Thresh} ↔
          Nat.ceil (Real.logb 2 ((x : Real) / Thresh)) ≤ r := by
      rw [hmem, Nat.ceil_le, Real.logb_le_iff_le_rpow (by norm_num) hpos,
        Real.rpow_natCast]
    have hset : {rounds : Nat | ((x / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ Thresh} =
        Set.Ici (Nat.ceil (Real.logb 2 ((x : Real) / Thresh))) := by
      ext r
      exact hiff r
    rw [hset, csInf_Ici]
  · have hzero : (0 : Nat) ∈
        {rounds : Nat | ((x / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ Thresh} := by
      rw [hmem, pow_zero, div_le_one hThresh]
      linarith
    exact (Nat.sInf_eq_zero.mpr (Or.inl hzero)).symm

/-- The algorithm's scaled volume times its rate is the reference product. -/
theorem t_mul_scaleRate (b n : Nat) (Thresh : Real) (v q : NNReal) :
    ttcPseudocode.t b n v * (Real.toNNReal Thresh * q) =
      ttcReference.t b n Thresh v * q := by
  unfold ttcPseudocode.t ttcReference.t
  ring

theorem rateHalvings_scaleRate {n : Nat} (b : Nat) {Thresh : Real} (hThresh : 0 < Thresh)
    (s : TTCState n) (v : NNReal) :
    ttcPseudocode.rateHalvings (s.scaleRate (Real.toNNReal Thresh))
        (ttcPseudocode.t b n v) Thresh =
      ttcReference.firstLoopExit s (ttcReference.t b n Thresh v) Thresh := by
  unfold ttcPseudocode.rateHalvings ttcReference.firstLoopExit
  have hprod : ttcPseudocode.t b n v * (s.scaleRate (Real.toNNReal Thresh)).p =
      ttcReference.t b n Thresh v * s.p :=
    t_mul_scaleRate b n Thresh v s.p
  rw [hprod]
  have h := rateHalvings_eq_sInf (ttcReference.t b n Thresh v * s.p) hThresh
  simpa only [mul_div_assoc] using h

theorem rateCheckResult_scaleRate {n : Nat} (b : Nat) {Thresh : Real}
    (hThresh : 0 < Thresh) (s : TTCState n) (v : NNReal) (coins : Nat × Nat → Bool) :
    ttcPseudocode.rateCheckResult (s.scaleRate (Real.toNNReal Thresh))
        (ttcPseudocode.t b n v) Thresh coins =
      (ttcReference.firstLoopResult s (ttcReference.t b n Thresh v) Thresh coins).scaleRate
        (Real.toNNReal Thresh) := by
  unfold ttcPseudocode.rateCheckResult ttcReference.firstLoopResult
  rw [rateHalvings_scaleRate b hThresh s v]
  simp only [TTCState.scaleRate, mul_div_assoc]

theorem rateCheckCost_scaleRate {n : Nat} (b : Nat) {Thresh : Real}
    (hThresh : 0 < Thresh) (s : TTCState n) (v : NNReal) :
    ttcPseudocode.rateCheckCost (s.scaleRate (Real.toNNReal Thresh))
        (ttcPseudocode.t b n v) Thresh =
      ttcReference.firstLoopCost s (ttcReference.t b n Thresh v) Thresh := by
  unfold ttcPseudocode.rateCheckCost ttcReference.firstLoopCost
  rw [rateHalvings_scaleRate b hThresh s v]
  rfl

theorem removeComponent_scaleRate {n : Nat} (c : NNReal) (s : TTCState n)
    (P : PolytopeData n) :
    (s.scaleRate c).removeComponent P = (s.removeComponent P).scaleRate c := rfl

theorem addBatch_scaleRate {n count : Nat} (c : NNReal) (s : TTCState n)
    (points : Fin count → LatticePoint n) :
    (s.scaleRate c).addBatch points = (s.addBatch points).scaleRate c := rfl

theorem secondLoopResult_scaleRate {n : Nat} (c : NNReal) (s : TTCState n) (N : Nat)
    (Thresh : Real) (coins : Nat × Nat → Bool) :
    ttcPseudocode.secondLoopResult (s.scaleRate c) N Thresh coins =
      scaleRateFst c (ttcPseudocode.secondLoopResult s N Thresh coins) := by
  simp only [ttcPseudocode.secondLoopResult, scaleRateFst, TTCState.scaleRate, mul_div_assoc]
  rfl

theorem secondLoopCost_scaleRate {n : Nat} (c : NNReal) (s : TTCState n) (N : Nat)
    (Thresh : Real) (coins : Nat × Nat → Bool) :
    ttcPseudocode.secondLoopCost (s.scaleRate c) N Thresh coins =
      ttcPseudocode.secondLoopCost s N Thresh coins := rfl

theorem initial_eq_scaleRate (n : Nat) (Thresh : Real) :
    TTCState.initial n Thresh = (TTCState.unitInitial n).scaleRate (Real.toNNReal Thresh) := by
  simp [TTCState.initial, TTCState.unitInitial, TTCState.scaleRate]

theorem Est_scaleRate {n : Nat} (b : Nat) (Thresh : Real) (s : TTCState n) :
    Est b (s.scaleRate (Real.toNNReal Thresh)) = EstReference b Thresh s := by
  unfold Est EstReference TTCState.scaleRate
  congr 1
  ring

/-! ## The uncharged run -/

section Uncharged

variable {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
  (P : PolytopeData n) (b : Nat) (eta Thresh : Real)

/-- Sampling and appending (line `line:sample`), common to both parametrisations. -/
def simSampleAppend (z : TTCState n × Nat) : Measure (TTCState n) :=
  ((ttcSubroutines hn prep).GenerateSamples P z.2 b eta).map
    fun batch => z.1.addBatch batch

/-- The halving loop followed by sampling, common to both parametrisations. -/
def simCountTail (s : TTCState n) (N : Nat) : Measure (TTCState n) :=
  (ttcPseudocode.secondLoop s N Thresh).bind (simSampleAppend hn prep P b eta)

/-- The Poisson draw and everything after it, at scaled volume `t`. -/
def simPoissonTail (t : NNReal) (s : TTCState n) : Measure (TTCState n) :=
  (Poisson (t * s.p)).bind (simCountTail hn prep P b eta Thresh s)

theorem measurable_simSampleAppend (delta : Real) :
    Measurable (simSampleAppend hn prep P b eta) :=
  measurable_community_sampleAppend_kernel hn prep P b eta delta

theorem simSampleAppend_scaleRate (c : NNReal) (z : TTCState n × Nat) :
    simSampleAppend hn prep P b eta (scaleRateFst c z) =
      (simSampleAppend hn prep P b eta z).map (TTCState.scaleRate c) := by
  have hadd : Measurable (fun batch : SampleBatch n z.2 => z.1.addBatch batch) :=
    measurable_addBatch.comp (measurable_const.prodMk measurable_id)
  unfold simSampleAppend
  rw [Measure.map_map (measurable_scaleRate c) hadd]
  rfl

theorem simCountTail_scaleRate (delta : Real) (c : NNReal) (s : TTCState n) (N : Nat) :
    simCountTail hn prep P b eta Thresh (s.scaleRate c) N =
      (simCountTail hn prep P b eta Thresh s N).map (TTCState.scaleRate c) := by
  have hL3 := measurable_simSampleAppend hn prep P b eta delta
  have hloop : ttcPseudocode.secondLoop (s.scaleRate c) N Thresh =
      (ttcPseudocode.secondLoop s N Thresh).map (scaleRateFst c) := by
    unfold ttcPseudocode.secondLoop
    rw [Measure.map_map (measurable_scaleRateFst c) (measurable_thinningResult s N Thresh)]
    congr 1
    funext coins
    exact secondLoopResult_scaleRate c s N Thresh coins
  unfold simCountTail
  rw [hloop, Measure.bind_map (measurable_scaleRateFst c).aemeasurable hL3.aemeasurable]
  simp_rw [simSampleAppend_scaleRate hn prep P b eta c]
  exact (map_bind_measure _ _ _ hL3.aemeasurable (measurable_scaleRate c)).symm

theorem simPoissonTail_scaleRate (delta : Real) (c : NNReal) (t t' : NNReal) (s : TTCState n)
    (hrate : t' * (c * s.p) = t * s.p) :
    simPoissonTail hn prep P b eta Thresh t' (s.scaleRate c) =
      (simPoissonTail hn prep P b eta Thresh t s).map (TTCState.scaleRate c) := by
  unfold simPoissonTail
  change (Poisson (t' * (c * s.p))).bind _ = _
  rw [hrate]
  have htail : simCountTail hn prep P b eta Thresh (s.scaleRate c) =
      fun N => (simCountTail hn prep P b eta Thresh s N).map (TTCState.scaleRate c) :=
    funext (simCountTail_scaleRate hn prep P b eta Thresh delta c s)
  rw [htail]
  exact (map_bind_measure _ _ _ Measurable.of_discrete.aemeasurable
    (measurable_scaleRate c)).symm

theorem measurable_simPoissonTail (delta : Real) (t : NNReal) :
    Measurable (simPoissonTail hn prep P b eta Thresh t) := by
  have hc := (community_poisson_count_sample_append_kernel_measurable hn prep 1 P b
    eta delta Thresh).comp
    (measurable_id.prodMk measurable_const : Measurable fun s : TTCState n => (s, t))
  have hm := (Measure.measurable_map _ measurable_fst).comp hc
  convert hm using 1
  funext s
  exact (community_poisson_count_sample_append_fst hn prep 1 P b eta delta Thresh s t).symm

/-- The component iteration after `ComputeVolume`, in the algorithm's parametrisation. -/
def simGivenVolume (outcome : VolumeOutcome) (state : TTCState n) : Measure (TTCState n) :=
  let t := ttcPseudocode.t b n outcome.2
  (ttcPseudocode.rateCheck (state.removeComponent P) t Thresh).bind
    (simPoissonTail hn prep P b eta Thresh t)

theorem simGivenVolume_scaleRate (delta : Real) (hThresh : 0 < Thresh) (outcome : VolumeOutcome)
    (s : TTCState n) :
    simGivenVolume hn prep P b eta Thresh outcome (s.scaleRate (Real.toNNReal Thresh)) =
      (communityComponentGivenVolume hn prep P b eta delta Thresh outcome s).map
        (TTCState.scaleRate (Real.toNNReal Thresh)) := by
  set c := Real.toNNReal Thresh with hc
  have hc0 : c ≠ 0 := (Real.toNNReal_pos.mpr hThresh).ne'
  set t := ttcPseudocode.t b n outcome.2
  set tr := ttcReference.t b n Thresh outcome.2
  let K := s.removeComponent P
  have hcheck : ttcPseudocode.rateCheck (K.scaleRate c) t Thresh =
      (ttcReference.firstLoop K tr Thresh).map (TTCState.scaleRate c) := by
    unfold ttcPseudocode.rateCheck ttcReference.firstLoop
    rw [Measure.map_map (measurable_scaleRate c) (measurable_rateThinningResult K tr Thresh)]
    congr 1
    funext coins
    exact rateCheckResult_scaleRate b hThresh K outcome.2 coins
  have hnewEq : simPoissonTail hn prep P b eta Thresh t =
      fun x => (simPoissonTail hn prep P b eta Thresh tr (x.unscaleRate c)).map
        (TTCState.scaleRate c) := by
    funext x
    conv_lhs => rw [← TTCState.scaleRate_unscaleRate hc0 x]
    exact simPoissonTail_scaleRate hn prep P b eta Thresh delta c tr t _
      (t_mul_scaleRate b n Thresh outcome.2 _)
  have hnew : Measurable (simPoissonTail hn prep P b eta Thresh t) := by
    rw [hnewEq]
    exact (Measure.measurable_map _ (measurable_scaleRate c)).comp
      ((measurable_simPoissonTail hn prep P b eta Thresh delta tr).comp
        (measurable_unscaleRate c))
  have href := measurable_simPoissonTail hn prep P b eta Thresh delta tr
  change (ttcPseudocode.rateCheck (K.scaleRate c) t Thresh).bind
      (simPoissonTail hn prep P b eta Thresh t) =
    ((ttcReference.firstLoop K tr Thresh).bind
      (simPoissonTail hn prep P b eta Thresh tr)).map (TTCState.scaleRate c)
  rw [hcheck, Measure.bind_map (measurable_scaleRate c).aemeasurable hnew.aemeasurable,
    map_bind_measure _ _ _ href.aemeasurable (measurable_scaleRate c)]
  congr 1
  funext f
  exact simPoissonTail_scaleRate hn prep P b eta Thresh delta c tr t f
    (t_mul_scaleRate b n Thresh outcome.2 f.p)

theorem step_eq_simGivenVolume (delta : Real) (x : TTCState n) :
    ttcPseudocode.step (ttcSubroutines hn prep) b eta delta Thresh P x =
      ((ttcSubroutines hn prep).ComputeVolume P eta delta).bind
        (fun outcome => simGivenVolume hn prep P b eta Thresh outcome x) := rfl

theorem refStep_eq_givenVolume (delta : Real) (s : TTCState n) :
    ttcReference.step (ttcSubroutines hn prep) b eta delta Thresh P s =
      ((ttcSubroutines hn prep).ComputeVolume P eta delta).bind
        (fun outcome => communityComponentGivenVolume hn prep P b eta delta Thresh
          outcome s) := rfl

theorem step_scaleRate (delta : Real) (hThresh : 0 < Thresh) (s : TTCState n) :
    ttcPseudocode.step (ttcSubroutines hn prep) b eta delta Thresh P
        (s.scaleRate (Real.toNNReal Thresh)) =
      (ttcReference.step (ttcSubroutines hn prep) b eta delta Thresh P s).map
        (TTCState.scaleRate (Real.toNNReal Thresh)) := by
  have hjoint := measurable_communityComponentGivenVolume hn prep P b eta delta Thresh
    hThresh
  have hpair : Measurable (fun outcome : VolumeOutcome => (s, outcome)) :=
    measurable_const.prodMk measurable_id
  have hGV := hjoint.comp hpair
  rw [Function.comp_def] at hGV
  rw [step_eq_simGivenVolume, refStep_eq_givenVolume,
    map_bind_measure _ _ _ hGV.aemeasurable (measurable_scaleRate _)]
  congr 1
  funext outcome
  exact simGivenVolume_scaleRate hn prep P b eta Thresh delta hThresh outcome s

end Uncharged

theorem loop_scaleRate {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta Thresh : Real) (hThresh : 0 < Thresh)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((ttcSubroutines hn prep).ComputeVolume P eta delta))
    (s : TTCState n) :
    ttcPseudocode.loop (ttcSubroutines hn prep) b eta delta Thresh components
        (s.scaleRate (Real.toNNReal Thresh)) =
      (ttcReference.loop (ttcSubroutines hn prep) b eta delta Thresh components s).map
        (TTCState.scaleRate (Real.toNNReal Thresh)) := by
  set c := Real.toNNReal Thresh
  have hc0 : c ≠ 0 := (Real.toNNReal_pos.mpr hThresh).ne'
  induction components generalizing s with
  | nil =>
      exact (Measure.map_dirac' (measurable_scaleRate c) s).symm
  | cons P rest ih =>
      have hrest : ∀ Q ∈ rest, IsProbabilityMeasure
          ((ttcSubroutines hn prep).ComputeVolume Q eta delta) :=
        fun Q hQ => hvolume Q (List.mem_cons_of_mem P hQ)
      have href := measurable_communityProcessComponents hn prep b eta delta Thresh
        hThresh rest hrest
      have hnewEq : ttcPseudocode.loop (ttcSubroutines hn prep) b eta delta Thresh rest =
          fun x => (ttcReference.loop (ttcSubroutines hn prep) b eta delta Thresh rest
            (x.unscaleRate c)).map (TTCState.scaleRate c) := by
        funext x
        conv_lhs => rw [← TTCState.scaleRate_unscaleRate hc0 x]
        exact ih hrest _
      have hnew : Measurable
          (ttcPseudocode.loop (ttcSubroutines hn prep) b eta delta Thresh rest) := by
        rw [hnewEq]
        exact (Measure.measurable_map _ (measurable_scaleRate c)).comp
          (href.comp (measurable_unscaleRate c))
      change (ttcPseudocode.step (ttcSubroutines hn prep) b eta delta Thresh P
          (s.scaleRate c)).bind
          (ttcPseudocode.loop (ttcSubroutines hn prep) b eta delta Thresh rest) =
        ((ttcReference.step (ttcSubroutines hn prep) b eta delta Thresh P s).bind
          (ttcReference.loop (ttcSubroutines hn prep) b eta delta Thresh rest)).map
            (TTCState.scaleRate c)
      rw [step_scaleRate hn prep P b eta Thresh delta hThresh s,
        Measure.bind_map (measurable_scaleRate c).aemeasurable hnew.aemeasurable,
        map_bind_measure _ _ _ href.aemeasurable (measurable_scaleRate c)]
      congr 1
      funext x
      exact ih hrest x

theorem measurable_Est {n : Nat} (b : Nat) : Measurable (Est (n := n) b) := by
  have hrate : Measurable (fun s : TTCState n => s.p) :=
    measurable_fst.comp measurable_state_coords
  have hsamples : Measurable (fun s : TTCState n => s.X) :=
    (measurable_fst.comp measurable_snd).comp measurable_state_coords
  have hcount : Measurable (fun s : TTCState n => (s.X.card : NNReal)) :=
    (measurable_of_countable (fun copies : Finset (SampleCopy n) =>
      (copies.card : NNReal))).comp hsamples
  unfold Est
  exact hcount.div (hrate.mul_const _)

/-- **Algorithm `ttc` has the reference output law.** -/
theorem ttc_eq_ttcRef {n k : Nat} (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams)
    (prep : TTCPreprocessor n k) :
    ttc hn F hbounded p prep = ttcRef hn F hbounded p prep := by
  unfold ttc ttcRef ttcPseudocode ttcReference
  dsimp only
  split_ifs with hm
  · rfl
  · set D := (ttcSubroutines hn prep).preprocessing.run F hbounded
    set Thresh := p.Thresh D.componentCount
    have hThresh : 0 < Thresh := p.threshold_pos D.componentCount
    have hvolume : ∀ P ∈ List.ofFn D.component, IsProbabilityMeasure
        ((ttcSubroutines hn prep).ComputeVolume P p.ε' (p.δ' D.componentCount)) := by
      intro P hP
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
      exact community_volume_isProbabilityMeasure hn D p prep i
    rw [initial_eq_scaleRate, loop_scaleRate hn prep _ _ _ Thresh hThresh _ hvolume,
      Measure.map_map (measurable_Est _) (measurable_scaleRate _)]
    congr 1
    funext s
    exact Est_scaleRate _ Thresh s

/-! ## The charged run -/

private theorem measurable_costedCont {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (next : α → Measure (β × Nat)) (hnext : Measurable next) :
    Measurable (fun result : α × Nat =>
      (next result.1).map fun future => (future.1, result.2 + future.2)) := by
  apply measurable_from_prod_countable_left
  intro cost
  exact (Measure.measurable_map
    (fun future : β × Nat => (future.1, cost + future.2)) (by fun_prop)).comp hnext

/-- A map of the state coordinate commutes with charged composition. -/
theorem costedBind_map_state {α X Y : Type*}
    [MeasurableSpace α] [MeasurableSpace X] [MeasurableSpace Y]
    (first : Measure (α × Nat)) (next : α → Measure (X × Nat)) (hnext : Measurable next)
    (e : X → Y) (he : Measurable e) :
    costedBind first (fun a => (next a).map (fun z => (e z.1, z.2))) =
      (costedBind first next).map (fun z => (e z.1, z.2)) := by
  unfold costedBind
  rw [map_bind_measure _ _ _ (measurable_costedCont next hnext).aemeasurable
    (by fun_prop)]
  congr 1
  funext r
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Charged composition after a map of the first state coordinate. -/
theorem costedBind_map_source {A A' Y : Type*}
    [MeasurableSpace A] [MeasurableSpace A'] [MeasurableSpace Y]
    (first : Measure (A × Nat)) (f : A → A') (hf : Measurable f)
    (next : A' → Measure (Y × Nat)) (hnext : Measurable next) :
    costedBind (first.map (fun z => (f z.1, z.2))) next =
      costedBind first (fun a => next (f a)) := by
  unfold costedBind
  rw [Measure.bind_map (by fun_prop : Measurable fun z : A × Nat => (f z.1, z.2)).aemeasurable
    (measurable_costedCont next hnext).aemeasurable]

theorem costedBind_map_source_scaleRate {n : Nat} {Y : Type*} [MeasurableSpace Y]
    (first : Measure (TTCState n × Nat)) (c : NNReal)
    (next : TTCState n → Measure (Y × Nat)) (hnext : Measurable next) :
    costedBind (first.map (scaleRateFst c)) next =
      costedBind first (fun a => next (a.scaleRate c)) :=
  costedBind_map_source first _ (measurable_scaleRate c) next hnext

theorem costedBind_map_state_scaleRate {n : Nat} {α : Type*} [MeasurableSpace α]
    (first : Measure (α × Nat)) (next : α → Measure (TTCState n × Nat))
    (hnext : Measurable next) (c : NNReal) :
    costedBind first (fun a => (next a).map (scaleRateFst c)) =
      (costedBind first next).map (scaleRateFst c) :=
  costedBind_map_state first next hnext _ (measurable_scaleRate c)

theorem costedCharge_dirac_scaleRate {n : Nat} (c : NNReal) (x : TTCState n) (k : Nat) :
    costedCharge (Measure.dirac (x.scaleRate c)) k =
      (costedCharge (Measure.dirac x) k).map (scaleRateFst c) := by
  unfold costedCharge
  rw [Measure.map_dirac' (by fun_prop), Measure.map_dirac' (by fun_prop),
    Measure.map_dirac' (measurable_scaleRateFst c)]
  rfl

section Charged

variable {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k) (factor : Nat)
  (P : PolytopeData n) (b : Nat) (eta Thresh : Real)

/-- Charged sampling and appending, common to both parametrisations. -/
def simCostedSampleAppend (z : TTCState n × Nat) : Measure (TTCState n × Nat) :=
  costedBind
    ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost P z.2 b eta)
    (fun batch => costedCharge (Measure.dirac (z.1.addBatch batch))
      (z.2 * TTCRuntime.appendCopyOperations))

/-- The charged halving loop followed by sampling. -/
def simCostedCountTail (s : TTCState n) (N : Nat) : Measure (TTCState n × Nat) :=
  costedBind (ttcPseudocode.secondLoopWithCost s N Thresh)
    (simCostedSampleAppend hn prep factor P b eta)

/-- The charged Poisson draw and everything after it, at scaled volume `t`. -/
def simCostedPoissonTail (t : NNReal) (s : TTCState n) : Measure (TTCState n × Nat) :=
  costedBind (costedCharge (Poisson (t * s.p)) TTCRuntime.poissonDrawOperations)
    (simCostedCountTail hn prep factor P b eta Thresh s)

theorem measurable_simCostedSampleAppend (delta : Real) :
    Measurable (simCostedSampleAppend hn prep factor P b eta) :=
  community_sample_append_kernel_measurable hn prep factor P b eta delta

theorem simCostedSampleAppend_scaleRate (c : NNReal) (z : TTCState n × Nat) :
    simCostedSampleAppend hn prep factor P b eta (scaleRateFst c z) =
      (simCostedSampleAppend hn prep factor P b eta z).map (scaleRateFst c) := by
  unfold simCostedSampleAppend
  have hnext : Measurable (fun batch : SampleBatch n z.2 =>
      costedCharge (Measure.dirac (z.1.addBatch batch))
        (z.2 * TTCRuntime.appendCopyOperations)) := measurable_of_countable _
  have h := costedBind_map_state_scaleRate
    ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost P z.2 b eta)
    _ hnext c
  refine Eq.trans ?_ h
  congr 1
  funext batch
  exact costedCharge_dirac_scaleRate c (z.1.addBatch batch) _

theorem simCostedCountTail_scaleRate (delta : Real) (c : NNReal) (s : TTCState n)
    (N : Nat) :
    simCostedCountTail hn prep factor P b eta Thresh (s.scaleRate c) N =
      (simCostedCountTail hn prep factor P b eta Thresh s N).map (scaleRateFst c) := by
  have hL3 := measurable_simCostedSampleAppend hn prep factor P b eta delta
  have hcost : Measurable (fun coins : Nat × Nat → Bool =>
      ttcPseudocode.secondLoopCost s N Thresh coins) := by
    unfold ttcPseudocode.secondLoopCost
    exact (measurable_of_countable
      (fun rounds : Nat => rounds *
        TTCRuntime.countThinningRoundOperations s.X.card)).comp
          (measurable_firstExitRound s N Thresh)
  have hpair : Measurable (fun coins : Nat × Nat → Bool =>
      (ttcPseudocode.secondLoopResult s N Thresh coins,
        ttcPseudocode.secondLoopCost s N Thresh coins)) :=
    (measurable_thinningResult s N Thresh).prodMk hcost
  have hloop : ttcPseudocode.secondLoopWithCost (s.scaleRate c) N Thresh =
      (ttcPseudocode.secondLoopWithCost s N Thresh).map
        (fun z => (scaleRateFst c z.1, z.2)) := by
    have hm : Measurable (fun z : (TTCState n × Nat) × Nat => (scaleRateFst c z.1, z.2)) :=
      ((measurable_scaleRateFst c).comp measurable_fst).prodMk measurable_snd
    unfold ttcPseudocode.secondLoopWithCost
    rw [Measure.map_map hm hpair]
    congr 1
    funext coins
    exact Prod.ext (secondLoopResult_scaleRate c s N Thresh coins)
      (secondLoopCost_scaleRate c s N Thresh coins)
  unfold simCostedCountTail
  rw [hloop, costedBind_map_source _ _ (measurable_scaleRateFst c) _ hL3]
  have hfun : (fun a => simCostedSampleAppend hn prep factor P b eta (scaleRateFst c a)) =
      fun a => (simCostedSampleAppend hn prep factor P b eta a).map (scaleRateFst c) :=
    funext (simCostedSampleAppend_scaleRate hn prep factor P b eta c)
  rw [hfun]
  exact costedBind_map_state_scaleRate _ _ hL3 c

theorem simCostedPoissonTail_scaleRate (delta : Real) (c : NNReal) (t t' : NNReal)
    (s : TTCState n) (hrate : t' * (c * s.p) = t * s.p) :
    simCostedPoissonTail hn prep factor P b eta Thresh t' (s.scaleRate c) =
      (simCostedPoissonTail hn prep factor P b eta Thresh t s).map (scaleRateFst c) := by
  unfold simCostedPoissonTail
  change costedBind (costedCharge (Poisson (t' * (c * s.p))) _) _ = _
  rw [hrate]
  have htail : simCostedCountTail hn prep factor P b eta Thresh (s.scaleRate c) =
      fun N => (simCostedCountTail hn prep factor P b eta Thresh s N).map
        (scaleRateFst c) :=
    funext (simCostedCountTail_scaleRate hn prep factor P b eta Thresh delta c s)
  rw [htail]
  exact costedBind_map_state_scaleRate _ _ Measurable.of_discrete c

theorem measurable_simCostedPoissonTail (delta : Real) (t : NNReal) :
    Measurable (simCostedPoissonTail hn prep factor P b eta Thresh t) := by
  have hc := (community_poisson_count_sample_append_kernel_measurable hn prep factor P b
    eta delta Thresh).comp
    (measurable_id.prodMk measurable_const : Measurable fun s : TTCState n => (s, t))
  exact hc

/-- The charged rate check and everything after it, in the algorithm's parametrisation. -/
def simCostedRateTail (t : NNReal) (s : TTCState n) : Measure (TTCState n × Nat) :=
  costedBind (ttcPseudocode.rateCheckWithCost s t Thresh)
    (simCostedPoissonTail hn prep factor P b eta Thresh t)

/-- The charged reference rate check and everything after it. -/
def simCostedRefRateTail (t : NNReal) (s : TTCState n) : Measure (TTCState n × Nat) :=
  costedBind (ttcReference.firstLoopWithCost s t Thresh)
    (simCostedPoissonTail hn prep factor P b eta Thresh t)

theorem measurable_simCostedRefRateTail (delta : Real) (hThresh : 0 < Thresh)
    (t : NNReal) :
    Measurable (simCostedRefRateTail hn prep factor P b eta Thresh t) := by
  have hc := (community_costed_rate_tail_measurable hn prep factor P b
    eta delta Thresh hThresh).comp
    (measurable_id.prodMk measurable_const : Measurable fun s : TTCState n => (s, t))
  exact hc

theorem simCostedRateTail_scaleRate (delta : Real) (hThresh : 0 < Thresh)
    (v : NNReal) (s : TTCState n) :
    simCostedRateTail hn prep factor P b eta Thresh (ttcPseudocode.t b n v)
        (s.scaleRate (Real.toNNReal Thresh)) =
      (simCostedRefRateTail hn prep factor P b eta Thresh (ttcReference.t b n Thresh v) s).map
        (scaleRateFst (Real.toNNReal Thresh)) := by
  set c := Real.toNNReal Thresh with hc
  have hc0 : c ≠ 0 := (Real.toNNReal_pos.mpr hThresh).ne'
  set t := ttcPseudocode.t b n v
  set tr := ttcReference.t b n Thresh v
  have hres : Measurable (fun coins : Nat × Nat → Bool =>
      (ttcReference.firstLoopResult s tr Thresh coins,
        ttcReference.firstLoopCost s tr Thresh)) :=
    (measurable_rateThinningResult s tr Thresh).prodMk measurable_const
  have hcheck : ttcPseudocode.rateCheckWithCost (s.scaleRate c) t Thresh =
      (ttcReference.firstLoopWithCost s tr Thresh).map
        (fun z => (z.1.scaleRate c, z.2)) := by
    unfold ttcPseudocode.rateCheckWithCost ttcReference.firstLoopWithCost
    rw [Measure.map_map (by fun_prop) hres]
    congr 1
    funext coins
    exact Prod.ext (rateCheckResult_scaleRate b hThresh s v coins)
      (rateCheckCost_scaleRate b hThresh s v)
  have hnewEq : simCostedPoissonTail hn prep factor P b eta Thresh t =
      fun x => (simCostedPoissonTail hn prep factor P b eta Thresh tr
        (x.unscaleRate c)).map (scaleRateFst c) := by
    funext x
    conv_lhs => rw [← TTCState.scaleRate_unscaleRate hc0 x]
    exact simCostedPoissonTail_scaleRate hn prep factor P b eta Thresh delta c tr t _
      (t_mul_scaleRate b n Thresh v _)
  have href := measurable_simCostedPoissonTail hn prep factor P b eta Thresh delta tr
  have hnew : Measurable (simCostedPoissonTail hn prep factor P b eta Thresh t) := by
    rw [hnewEq]
    exact (Measure.measurable_map _ (measurable_scaleRateFst c)).comp
      (href.comp (measurable_unscaleRate c))
  unfold simCostedRateTail simCostedRefRateTail
  rw [hcheck]
  change costedBind (Measure.map (scaleRateFst c) _) _ = _
  rw [costedBind_map_source_scaleRate _ c _ hnew]
  have hfun : (fun a => simCostedPoissonTail hn prep factor P b eta Thresh t
      (a.scaleRate c)) =
      fun a => (simCostedPoissonTail hn prep factor P b eta Thresh tr a).map
        (scaleRateFst c) :=
    funext fun a => simCostedPoissonTail_scaleRate hn prep factor P b eta Thresh delta c
      tr t a (t_mul_scaleRate b n Thresh v a.p)
  rw [hfun]
  exact costedBind_map_state_scaleRate _ _ href c

/-- The charged component iteration after `ComputeVolume`, in the algorithm's
parametrisation. -/
def simCostedGivenVolume (outcome : VolumeOutcome) (state : TTCState n) :
    Measure (TTCState n × Nat) :=
  let deleted := state.removeComponent P
  costedBind
    (costedCharge (Measure.dirac deleted)
      (TTCRuntime.deletionPassOperations n P.presentation.facetCount state.X.card
        (state.X.card - deleted.X.card)))
    (simCostedRateTail hn prep factor P b eta Thresh (ttcPseudocode.t b n outcome.2))

theorem simCostedGivenVolume_scaleRate (delta : Real) (hThresh : 0 < Thresh)
    (outcome : VolumeOutcome) (s : TTCState n) :
    simCostedGivenVolume hn prep factor P b eta Thresh outcome
        (s.scaleRate (Real.toNNReal Thresh)) =
      (communityCostedComponentTail hn prep factor P b eta delta Thresh s outcome).map
        (scaleRateFst (Real.toNNReal Thresh)) := by
  set c := Real.toNNReal Thresh with hc
  have hc0 : c ≠ 0 := (Real.toNNReal_pos.mpr hThresh).ne'
  set t := ttcPseudocode.t b n outcome.2
  set tr := ttcReference.t b n Thresh outcome.2
  have href := measurable_simCostedRefRateTail hn prep factor P b eta Thresh delta
    hThresh tr
  have hnewEq : simCostedRateTail hn prep factor P b eta Thresh t =
      fun x => (simCostedRefRateTail hn prep factor P b eta Thresh tr
        (x.unscaleRate c)).map (scaleRateFst c) := by
    funext x
    conv_lhs => rw [← TTCState.scaleRate_unscaleRate hc0 x]
    exact simCostedRateTail_scaleRate hn prep factor P b eta Thresh delta hThresh
      outcome.2 _
  have hnew : Measurable (simCostedRateTail hn prep factor P b eta Thresh t) := by
    rw [hnewEq]
    exact (Measure.measurable_map _ (measurable_scaleRateFst c)).comp
      (href.comp (measurable_unscaleRate c))
  let K := s.removeComponent P
  let dc := TTCRuntime.deletionPassOperations n P.presentation.facetCount s.X.card
    (s.X.card - K.X.card)
  change costedBind (costedCharge (Measure.dirac (K.scaleRate c)) dc)
      (simCostedRateTail hn prep factor P b eta Thresh t) =
    (costedBind (costedCharge (Measure.dirac K) dc)
      (simCostedRefRateTail hn prep factor P b eta Thresh tr)).map (scaleRateFst c)
  rw [costedCharge_dirac_scaleRate, costedBind_map_source_scaleRate _ c _ hnew]
  have hfun : (fun a => simCostedRateTail hn prep factor P b eta Thresh t
      (a.scaleRate c)) =
      fun a => (simCostedRefRateTail hn prep factor P b eta Thresh tr a).map
        (scaleRateFst c) :=
    funext fun a => simCostedRateTail_scaleRate hn prep factor P b eta Thresh delta
      hThresh outcome.2 a
  rw [hfun]
  exact costedBind_map_state_scaleRate _ _ href c

theorem stepWithCost_eq_sim (delta : Real) (x : TTCState n) :
    ttcPseudocode.stepWithCost (ttcCostedSubroutines hn prep factor) b eta delta Thresh P x =
      costedBind ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost P eta delta)
        (fun outcome => simCostedGivenVolume hn prep factor P b eta Thresh outcome x) := rfl

theorem refStepWithCost_eq_tail (delta : Real) (s : TTCState n) :
    ttcReference.stepWithCost (ttcCostedSubroutines hn prep factor) b eta delta Thresh P s =
      costedBind ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost P eta delta)
        (communityCostedComponentTail hn prep factor P b eta delta Thresh s) := rfl

theorem stepWithCost_scaleRate (delta : Real) (hThresh : 0 < Thresh) (s : TTCState n) :
    ttcPseudocode.stepWithCost (ttcCostedSubroutines hn prep factor) b eta delta Thresh P
        (s.scaleRate (Real.toNNReal Thresh)) =
      (ttcReference.stepWithCost (ttcCostedSubroutines hn prep factor) b eta delta Thresh
        P s).map (scaleRateFst (Real.toNNReal Thresh)) := by
  have htail := community_component_tail_measurable hn prep factor P b eta delta Thresh
    hThresh s
  rw [stepWithCost_eq_sim, refStepWithCost_eq_tail]
  have hfun : (fun outcome => simCostedGivenVolume hn prep factor P b eta Thresh outcome
      (s.scaleRate (Real.toNNReal Thresh))) =
      fun outcome => (communityCostedComponentTail hn prep factor P b eta delta Thresh
        s outcome).map (scaleRateFst (Real.toNNReal Thresh)) :=
    funext fun outcome => simCostedGivenVolume_scaleRate hn prep factor P b eta Thresh
      delta hThresh outcome s
  rw [hfun]
  exact costedBind_map_state_scaleRate _ _ htail _

end Charged

theorem loopWithCost_scaleRate {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta Thresh : Real) (hThresh : 0 < Thresh)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components,
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta) Set.univ ≤ 1)
    (s : TTCState n) :
    ttcPseudocode.loopWithCost (ttcCostedSubroutines hn prep factor) b eta delta Thresh
        components (s.scaleRate (Real.toNNReal Thresh)) =
      (ttcReference.loopWithCost (ttcCostedSubroutines hn prep factor) b eta delta Thresh
        components s).map (scaleRateFst (Real.toNNReal Thresh)) := by
  set c := Real.toNNReal Thresh
  have hc0 : c ≠ 0 := (Real.toNNReal_pos.mpr hThresh).ne'
  induction components generalizing s with
  | nil =>
      change Measure.dirac ((s.scaleRate c), 0) = (Measure.dirac (s, 0)).map _
      rw [Measure.map_dirac' (measurable_scaleRateFst c)]
      rfl
  | cons P rest ih =>
      have hrest : ∀ Q ∈ rest,
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            Q eta delta) Set.univ ≤ 1 :=
        fun Q hQ => hvolume Q (List.mem_cons_of_mem P hQ)
      have href := community_components_kernel_measurable hn prep factor b eta delta
        Thresh hThresh rest hrest
      have hnewEq : ttcPseudocode.loopWithCost (ttcCostedSubroutines hn prep factor) b eta
          delta Thresh rest =
          fun x => (ttcReference.loopWithCost (ttcCostedSubroutines hn prep factor) b eta
            delta Thresh rest (x.unscaleRate c)).map (scaleRateFst c) := by
        funext x
        conv_lhs => rw [← TTCState.scaleRate_unscaleRate hc0 x]
        exact ih hrest _
      have hnew : Measurable (ttcPseudocode.loopWithCost
          (ttcCostedSubroutines hn prep factor) b eta delta Thresh rest) := by
        rw [hnewEq]
        exact (Measure.measurable_map _ (measurable_scaleRateFst c)).comp
          (href.comp (measurable_unscaleRate c))
      change costedBind (ttcPseudocode.stepWithCost (ttcCostedSubroutines hn prep factor)
          b eta delta Thresh P (s.scaleRate c))
          (ttcPseudocode.loopWithCost (ttcCostedSubroutines hn prep factor) b eta delta
            Thresh rest) =
        (costedBind (ttcReference.stepWithCost (ttcCostedSubroutines hn prep factor)
          b eta delta Thresh P s)
          (ttcReference.loopWithCost (ttcCostedSubroutines hn prep factor) b eta delta
            Thresh rest)).map (scaleRateFst c)
      rw [stepWithCost_scaleRate hn prep factor P b eta Thresh delta hThresh s,
        costedBind_map_source_scaleRate _ c _ hnew]
      have hfun : (fun a => ttcPseudocode.loopWithCost (ttcCostedSubroutines hn prep factor)
          b eta delta Thresh rest (a.scaleRate c)) =
          fun a => (ttcReference.loopWithCost (ttcCostedSubroutines hn prep factor) b eta
            delta Thresh rest a).map (scaleRateFst c) :=
        funext fun a => ih hrest a
      rw [hfun]
      exact costedBind_map_state_scaleRate _ _ href c

/-- **The charged algorithm `ttcWithCost` has the reference charged law.** -/
theorem ttcWithCost_eq_ttcRefWithCost {n k : Nat} (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams)
    (prep : TTCPreprocessor n k) (preprocessingOperations factor : Nat) :
    ttcWithCost hn F hbounded p prep preprocessingOperations factor =
      ttcRefWithCost hn F hbounded p prep preprocessingOperations factor := by
  unfold ttcWithCost ttcRefWithCost ttcPseudocodeWithCost ttcReferenceWithCost
  dsimp only
  split_ifs with hm
  · rfl
  · set D := (ttcCostedSubroutines hn prep factor).base.preprocessing.run F hbounded
    set Thresh := p.Thresh D.componentCount
    have hThresh : 0 < Thresh := p.threshold_pos D.componentCount
    have hvolume : ∀ P ∈ List.ofFn D.component,
        ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
          P p.ε' (p.δ' D.componentCount)) Set.univ ≤ 1 := by
      intro P hP
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
      have := community_costed_volume_isProbabilityMeasure hn D p prep factor i
      exact prob_le_one
    have hout : Measurable (fun result : TTCState n × Nat =>
        (Est (n := n) ((ttcCostedSubroutines hn prep factor).base.choosePrecision D p)
          result.1, preprocessingOperations + result.2)) :=
      ((measurable_Est _).comp measurable_fst).prodMk (by fun_prop)
    rw [initial_eq_scaleRate,
      loopWithCost_scaleRate hn prep factor _ _ _ Thresh hThresh _ hvolume,
      Measure.map_map hout (measurable_scaleRateFst _)]
    congr 1
    funext result
    simp only [Function.comp_apply, scaleRateFst, Est_scaleRate]

end ttc

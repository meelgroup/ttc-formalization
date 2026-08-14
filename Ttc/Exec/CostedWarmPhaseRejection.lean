/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.RawGaussianLazyStoppedExecution
import Ttc.Volume.CVFreshRestartKernel
import Mathlib.Probability.Independence.Integration

/-!
# Costed iid rejection for warm Gaussian phases

This is the operational outer-loop layer.  A round carries an actual `ENNReal` cost and a
candidate.  Independent copies are drawn until acceptance; the stopped cost is the sum of
the costs of precisely the rounds that were executed, and is `∞` on a nonterminating path.
-/

namespace Ttc.CostedWarmPhaseRejection

open MeasureTheory ProbabilityTheory Function Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.SpeedyRejection Ttc.RawGaussianLazyStoppedExecution
open scoped ENNReal Classical Pointwise

section Generic

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

def liftedAccept (A : Set E) : Set (ENNReal × E) := Prod.snd ⁻¹' A

theorem measurableSet_liftedAccept {A : Set E} (hA : MeasurableSet A) :
    MeasurableSet (liftedAccept (E := E) A) := hA.preimage measurable_snd

/-- Total cost of all iid rounds through and including the first accepted round. -/
noncomputable def stoppedQueryCost (A : Set E)
    (omega : RoundSpace (ENNReal × E)) : ENNReal :=
  ∑' j : Nat, (survives (liftedAccept A) j).indicator
    (fun omega => (omega j).1) omega

theorem measurable_stoppedQueryCost {A : Set E} (hA : MeasurableSet A) :
    Measurable (stoppedQueryCost (E := E) A) := by
  unfold stoppedQueryCost
  apply Measurable.tsum
  intro j
  exact (measurable_fst.comp (measurable_pi_apply j)).indicator
    (measurableSet_survives (measurableSet_liftedAccept hA) j)

/-- Cost and candidate returned by the iid stopped experiment. -/
noncomputable def stoppedCostedOutput (A : Set E)
    (omega : RoundSpace (ENNReal × E)) : ENNReal × E :=
  (stoppedQueryCost A omega,
    (Ttc.CV.firstAcceptedDraw (liftedAccept A) omega).2)

theorem measurable_stoppedCostedOutput {A : Set E} (hA : MeasurableSet A) :
    Measurable (stoppedCostedOutput (E := E) A) :=
  (measurable_stoppedQueryCost hA).prodMk
    (measurable_snd.comp
      (Ttc.CV.measurable_firstAcceptedDraw (measurableSet_liftedAccept hA)))

/-- Law of the costed first-accepted candidate. -/
noncomputable def costedRejectionLaw (nu : Measure (ENNReal × E)) (A : Set E) :
    Measure (ENNReal × E) :=
  Measure.map (stoppedCostedOutput A) (roundsMeasure nu)

theorem isProbabilityMeasure_costedRejectionLaw
    (nu : Measure (ENNReal × E)) [IsProbabilityMeasure nu]
    {A : Set E} (hA : MeasurableSet A) :
    IsProbabilityMeasure (costedRejectionLaw nu A) := by
  constructor
  rw [costedRejectionLaw, Measure.map_apply
    (measurable_stoppedCostedOutput hA) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

/-- Conditioning on a preimage commutes with mapping. -/
theorem map_condOn_preimage (nu : Measure (ENNReal × E))
    {A : Set E} (hA : MeasurableSet A) :
    Measure.map Prod.snd (Arlib.condOn nu (liftedAccept A)) =
      Arlib.condOn (Measure.map Prod.snd nu) A := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_snd hS,
    Arlib.condOn_apply _ (measurableSet_liftedAccept hA) (hS.preimage measurable_snd),
    Arlib.condOn_apply _ hA hS,
    Measure.map_apply measurable_snd hA,
    Measure.map_apply measurable_snd (hS.inter hA)]
  congr 1

/-- Forgetting cost gives ordinary conditioning of the candidate marginal. -/
theorem map_snd_costedRejectionLaw
    (nu : Measure (ENNReal × E)) [IsProbabilityMeasure nu]
    {A : Set E} (hA : MeasurableSet A) (hpos : 0 < nu (liftedAccept A)) :
    Measure.map Prod.snd (costedRejectionLaw nu A) =
      Arlib.condOn (Measure.map Prod.snd nu) A := by
  rw [costedRejectionLaw,
    Measure.map_map measurable_snd (measurable_stoppedCostedOutput hA)]
  have hcomp : Prod.snd ∘ stoppedCostedOutput (E := E) A =
      Prod.snd ∘ Ttc.CV.firstAcceptedDraw (liftedAccept A) := rfl
  rw [hcomp, ← Measure.map_map measurable_snd
      (Ttc.CV.measurable_firstAcceptedDraw (measurableSet_liftedAccept hA)),
    Ttc.CV.map_firstAcceptedDraw_eq_condOn nu
      (measurableSet_liftedAccept hA) hpos,
    map_condOn_preimage nu hA]

/-- Rejection indicator of one candidate. -/
noncomputable def rejectWeight (A : Set E) (z : ENNReal × E) : ENNReal :=
  Aᶜ.indicator (fun _ => 1) z.2

theorem measurable_rejectWeight {A : Set E} (hA : MeasurableSet A) :
    Measurable (rejectWeight (E := E) A) :=
  (measurable_const.indicator hA.compl).comp measurable_snd

theorem prod_rejectWeight_eq_survivalIndicator (A : Set E) (j : Nat)
    (omega : RoundSpace (ENNReal × E)) :
    ∏ i ∈ Finset.range j, rejectWeight A (omega i) =
      (survives (liftedAccept A) j).indicator (fun _ => 1) omega := by
  by_cases h : omega ∈ survives (liftedAccept A) j
  · rw [Set.indicator_of_mem h]
    apply Finset.prod_eq_one
    intro i hi
    rw [rejectWeight, Set.indicator_of_mem]
    simpa [survives, liftedAccept] using h i (Finset.mem_range.1 hi)
  · rw [Set.indicator_of_notMem h]
    simp only [survives, liftedAccept, Set.mem_setOf_eq, not_forall] at h
    obtain ⟨i, hi, hmem⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_range.2 hi)
    rw [rejectWeight, Set.indicator_of_notMem]
    simpa using hmem

theorem lintegral_stoppedQueryCost
    (nu : Measure (ENNReal × E)) [IsProbabilityMeasure nu]
    {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ omega, stoppedQueryCost A omega ∂(roundsMeasure nu) =
      (nu (liftedAccept A))⁻¹ * ∫⁻ z, z.1 ∂nu := by
  unfold stoppedQueryCost
  have hton := lintegral_tsum (μ := roundsMeasure nu)
    (f := fun j omega => (survives (liftedAccept A) j).indicator
      (fun omega => (omega j).1) omega) (fun j =>
      ((measurable_fst.comp (measurable_pi_apply j)).indicator
        (measurableSet_survives (measurableSet_liftedAccept hA) j)).aemeasurable)
  rw [hton]
  have hterm : ∀ j : Nat,
      ∫⁻ omega, (survives (liftedAccept A) j).indicator
          (fun omega => (omega j).1) omega ∂(roundsMeasure nu) =
        nu (liftedAccept A)ᶜ ^ j * ∫⁻ z, z.1 ∂nu := by
    intro j
    let X : Nat → RoundSpace (ENNReal × E) → ENNReal := fun i omega =>
      if i = j then (omega i).1 else rejectWeight A (omega i)
    have hXmeas : ∀ i, Measurable (X i) := by
      intro i
      dsimp [X]
      split_ifs
      · exact measurable_fst.comp (measurable_pi_apply i)
      · exact (measurable_rejectWeight hA).comp (measurable_pi_apply i)
    have hXi : ∀ i ∈ Finset.range j, X i =
        fun omega => rejectWeight A (omega i) := by
      intro i hi
      funext omega
      simp [X, ne_of_lt (Finset.mem_range.1 hi)]
    have hXj : X j = fun omega => (omega j).1 := by simp [X]
    have hind : iIndepFun X (roundsMeasure nu) := by
      have hd := iIndepFun_draw nu
      let g : Nat → (ENNReal × E) → ENNReal := fun i z =>
        if i = j then z.1 else rejectWeight A z
      have hg : ∀ i, Measurable (g i) := by
        intro i
        dsimp [g]
        split_ifs
        · exact measurable_fst
        · exact measurable_rejectWeight hA
      have hc := hd.comp g hg
      convert hc using 1 <;> rfl
    let P : RoundSpace (ENNReal × E) → ENNReal :=
      fun omega => ∏ i ∈ Finset.range j, X i omega
    have hPeq : P = (∏ i ∈ Finset.range j, X i) := by
      funext omega
      simp only [P, Finset.prod_apply]
    have hprod : P =
        (survives (liftedAccept A) j).indicator (fun _ => 1) := by
      funext omega
      dsimp only [P]
      rw [Finset.prod_congr rfl fun i hi => congrFun (hXi i hi) omega]
      exact prod_rejectWeight_eq_survivalIndicator A j omega
    have hfun : (survives (liftedAccept A) j).indicator
          (fun omega => (omega j).1) =
        P * X j := by
      funext omega
      rw [hprod, hXj]
      by_cases hs : omega ∈ survives (liftedAccept A) j <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs]
    have hprodMeas : Measurable P := by
      dsimp only [P]
      exact Finset.measurable_prod (Finset.range j) fun i _ => hXmeas i
    have hindP : IndepFun P (X j) (roundsMeasure nu) := by
      rw [hPeq]
      exact hind.indepFun_prod_range_succ hXmeas j
    rw [hfun,
      ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
        (μ := roundsMeasure nu) (f := P) (g := X j)
        hprodMeas (hXmeas j)
        hindP,
      hprod, show (fun _ : RoundSpace (ENNReal × E) => (1 : ENNReal)) = 1 from rfl,
      lintegral_indicator_one
        (measurableSet_survives (measurableSet_liftedAccept hA) j),
      roundsMeasure_survives nu (measurableSet_liftedAccept hA) j,
      hXj]
    exact congrArg (fun m => nu (liftedAccept A)ᶜ ^ j * m)
      ((measurePreserving_draw nu j).lintegral_comp measurable_fst)
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    prob_compl_eq_one_sub (measurableSet_liftedAccept hA),
    ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

theorem lintegral_fst_costedRejectionLaw
    (nu : Measure (ENNReal × E)) [IsProbabilityMeasure nu]
    {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ z, z.1 ∂(costedRejectionLaw nu A) =
      (nu (liftedAccept A))⁻¹ * ∫⁻ z, z.1 ∂nu := by
  rw [costedRejectionLaw, lintegral_map measurable_fst
    (measurable_stoppedCostedOutput hA)]
  exact lintegral_stoppedQueryCost nu hA

end Generic

section WarmPhase

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

theorem shrinkFactor_ne_zero (n : Nat) :
    (1 - 1 / (2 * (n : Real))) ≠ 0 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : (1 : Real) ≤ (Nat.succ n : Real) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hpos : (0 : Real) < (Nat.succ n : Real) := by positivity
      have hhalf : 1 / (2 * (Nat.succ n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith

/-- The endpoint of the recorded-query lazy speedy execution, retaining its total query
count.  This is the costed law from which the first restart stage draws iid copies. -/
noncomputable def walkEndpointCostLaw
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu0 : Measure (State n)) (t : Nat) : Measure (ENNReal × State n) :=
  Measure.map (fun omega =>
      (actualMembershipQueryCount t omega, (omega t).2))
    (lazyRawStoppedExecution K hK delta s hdelta mu0)

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat) :
    IsProbabilityMeasure (walkEndpointCostLaw K hK delta s hdelta mu0 t) := by
  unfold walkEndpointCostLaw
  have hout : Measurable (fun omega : Nat → ENNReal × State n =>
      (actualMembershipQueryCount t omega, (omega t).2)) :=
    (measurable_actualMembershipQueryCount t).prodMk
      (measurable_snd.comp (measurable_pi_apply t))
  constructor
  rw [Measure.map_apply hout MeasurableSet.univ, Set.preimage_univ,
    measure_univ]

theorem map_snd_walkEndpointCostLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat) :
    Measure.map Prod.snd (walkEndpointCostLaw K hK delta s hdelta mu0 t) =
      iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t := by
  have hout : Measurable (fun omega : Nat → ENNReal × State n =>
      (actualMembershipQueryCount t omega, (omega t).2)) :=
    (measurable_actualMembershipQueryCount t).prodMk
      (measurable_snd.comp (measurable_pi_apply t))
  rw [walkEndpointCostLaw, Measure.map_map measurable_snd hout]
  change Measure.map (fun omega => (omega t).2)
      (lazyRawStoppedExecution K hK delta s hdelta mu0) = _
  exact map_lazyRawStoppedExecution_output hK delta s hdelta mu0 t

theorem lintegral_fst_walkEndpointCostLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat) :
    ∫⁻ z, z.1 ∂(walkEndpointCostLaw K hK delta s hdelta mu0 t) =
      ∫⁻ omega, actualMembershipQueryCount t omega
        ∂(lazyRawStoppedExecution K hK delta s hdelta mu0) := by
  have hout : Measurable (fun omega : Nat → ENNReal × State n =>
      (actualMembershipQueryCount t omega, (omega t).2)) :=
    (measurable_actualMembershipQueryCount t).prodMk
      (measurable_snd.comp (measurable_pi_apply t))
  rw [walkEndpointCostLaw, lintegral_map measurable_fst hout]

/-- First source restart: rerun the whole costed walk until its endpoint lies in the
shrunken body, then rescale, retaining the sum of all recorded query counts. -/
noncomputable def phasePointCostLaw
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu0 : Measure (State n)) (t : Nat) : Measure (ENNReal × State n) :=
  let c : Real := 1 - 1 / (2 * (n : Real))
  Measure.map (fun z : ENNReal × State n => (z.1, c⁻¹ • z.2))
    (costedRejectionLaw
      (walkEndpointCostLaw K hK delta s hdelta mu0 t) (c • K))

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat) :
    IsProbabilityMeasure (phasePointCostLaw K hK delta s hdelta mu0 t) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hcK : MeasurableSet (c • K) :=
    measurableSet_smul_set hK (shrinkFactor_ne_zero n)
  letI : IsProbabilityMeasure
      (costedRejectionLaw (walkEndpointCostLaw K hK delta s hdelta mu0 t) (c • K)) :=
    isProbabilityMeasure_costedRejectionLaw _ hcK
  unfold phasePointCostLaw
  constructor
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

theorem map_snd_phasePointCostLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat)
    (hshrink : 0 < (iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
      ((1 - 1 / (2 * (n : Real))) • K)) :
    Measure.map Prod.snd (phasePointCostLaw K hK delta s hdelta mu0 t) =
      phasePointProposal K delta s mu0 t := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hcK : MeasurableSet (c • K) :=
    measurableSet_smul_set hK (shrinkFactor_ne_zero n)
  rw [phasePointCostLaw, Measure.map_map measurable_snd (by fun_prop)]
  change Measure.map (fun z : ENNReal × State n => c⁻¹ • z.2)
      (costedRejectionLaw (walkEndpointCostLaw K hK delta s hdelta mu0 t) (c • K)) = _
  rw [show (fun z : ENNReal × State n => c⁻¹ • z.2) =
      (fun x : State n => c⁻¹ • x) ∘ Prod.snd from rfl,
    ← Measure.map_map (by fun_prop) measurable_snd,
    map_snd_costedRejectionLaw _ hcK]
  · rw [map_snd_walkEndpointCostLaw hK delta s hdelta mu0 t]
    rfl
  · rw [show liftedAccept (E := State n) (c • K) = Prod.snd ⁻¹' (c • K) from rfl,
      ← Measure.map_apply measurable_snd hcK,
      map_snd_walkEndpointCostLaw hK delta s hdelta mu0 t]
    exact hshrink

theorem lintegral_fst_phasePointCostLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat) :
    ∫⁻ z, z.1 ∂(phasePointCostLaw K hK delta s hdelta mu0 t) =
      ((iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
        ((1 - 1 / (2 * (n : Real))) • K))⁻¹ *
        ∫⁻ omega, actualMembershipQueryCount t omega
          ∂(lazyRawStoppedExecution K hK delta s hdelta mu0) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hcK : MeasurableSet (c • K) :=
    measurableSet_smul_set hK (shrinkFactor_ne_zero n)
  rw [phasePointCostLaw, lintegral_map measurable_fst (by fun_prop),
    lintegral_fst_costedRejectionLaw _ hcK,
    show (walkEndpointCostLaw K hK delta s hdelta mu0 t)
        (liftedAccept (c • K)) =
      (iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t) (c • K) by
        rw [show liftedAccept (E := State n) (c • K) = Prod.snd ⁻¹' (c • K) from rfl,
          ← Measure.map_apply measurable_snd hcK,
          map_snd_walkEndpointCostLaw hK delta s hdelta mu0 t],
    lintegral_fst_walkEndpointCostLaw hK delta s hdelta mu0 t]

/-- Add the independent uniform coin used by the final speedy acceptance test to a
costed point law.  The coin costs no membership query. -/
noncomputable def costedSpeedyRoundLaw
    (rho : Measure (ENNReal × State n)) : Measure (ENNReal × (State n × Real)) :=
  Measure.map (fun p : (ENNReal × State n) × Real =>
      (p.1.1, (p.1.2, p.2))) (rho.prod unitCoin)

instance (rho : Measure (ENNReal × State n)) [IsProbabilityMeasure rho] :
    IsProbabilityMeasure (costedSpeedyRoundLaw rho) := by
  unfold costedSpeedyRoundLaw
  constructor
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

theorem map_snd_costedSpeedyRoundLaw
    (rho : Measure (ENNReal × State n)) [IsProbabilityMeasure rho] :
    Measure.map Prod.snd (costedSpeedyRoundLaw rho) =
      proposal (Measure.map Prod.snd rho) := by
  unfold costedSpeedyRoundLaw proposal
  rw [Measure.map_map measurable_snd (by fun_prop)]
  change Measure.map (fun p : (ENNReal × State n) × Real => (p.1.2, p.2))
      (rho.prod unitCoin) = _
  rw [show (fun p : (ENNReal × State n) × Real => (p.1.2, p.2)) =
      Prod.map Prod.snd id from rfl]
  simpa using
    (Measure.map_prod_map rho unitCoin measurable_snd measurable_id).symm

theorem lintegral_fst_costedSpeedyRoundLaw
    (rho : Measure (ENNReal × State n)) [IsProbabilityMeasure rho] :
    ∫⁻ z, z.1 ∂(costedSpeedyRoundLaw rho) = ∫⁻ z, z.1 ∂rho := by
  unfold costedSpeedyRoundLaw
  rw [lintegral_map measurable_fst (by fun_prop), lintegral_prod]
  · simp
  · fun_prop

/-- Both operational restart stages, with the final output retaining the sum of the
membership-query costs of every fully rerun inner experiment. -/
noncomputable def warmPhaseCostLaw
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu0 : Measure (State n)) (t : Nat) : Measure (ENNReal × State n) :=
  let c : Real := 1 - 1 / (2 * (n : Real))
  Measure.map (fun z : ENNReal × (State n × Real) => (z.1, z.2.1))
    (costedRejectionLaw
      (costedSpeedyRoundLaw
        (phasePointCostLaw K hK delta s hdelta mu0 t))
      (acceptRegion c s))

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat) :
    IsProbabilityMeasure (warmPhaseCostLaw K hK delta s hdelta mu0 t) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hA : MeasurableSet (acceptRegion (n := n) c s) := measurableSet_acceptRegion c s
  letI : IsProbabilityMeasure
      (costedRejectionLaw
        (costedSpeedyRoundLaw
          (phasePointCostLaw K hK delta s hdelta mu0 t))
        (acceptRegion c s)) :=
    isProbabilityMeasure_costedRejectionLaw _ hA
  unfold warmPhaseCostLaw
  constructor
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

/-- The costed two-restart implementation has exactly the source-level phase law as its
state marginal.  In particular, independent copies of this measure are the independently
restarted coordinates required by the packed hybrid sampler. -/
theorem map_snd_warmPhaseCostLaw_eq_phaseLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) {s : Real}
    (hdelta : 0 < delta) (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat)
    (hshrink : 0 < (iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
      ((1 - 1 / (2 * (n : Real))) • K))
    (hs : 0 < s) (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (hmass : ((phasePointProposal K delta s mu0 t).withDensity (fun x =>
      ENNReal.ofReal (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s x)))
        Set.univ ≠ 0) :
    Measure.map Prod.snd
        (warmPhaseCostLaw K hK delta s hdelta mu0 t) =
      Ttc.CVSampler.phaseLaw K delta s mu0 t := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let rho := phasePointCostLaw K hK delta s hdelta mu0 t
  have hrho : Measure.map Prod.snd rho = phasePointProposal K delta s mu0 t :=
    map_snd_phasePointCostLaw hK delta s hdelta mu0 t hshrink
  letI : IsProbabilityMeasure (phasePointProposal K delta s mu0 t) := by
    constructor
    rw [← hrho, Measure.map_apply measurable_snd MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  have hround : Measure.map Prod.snd (costedSpeedyRoundLaw rho) =
      proposal (phasePointProposal K delta s mu0 t) := by
    rw [map_snd_costedSpeedyRoundLaw, hrho]
  have hpos : 0 < (costedSpeedyRoundLaw rho)
      (liftedAccept (acceptRegion (n := n) c s)) := by
    rw [show liftedAccept (E := State n × Real) (acceptRegion c s) =
        Prod.snd ⁻¹' (acceptRegion c s) from rfl,
      ← Measure.map_apply measurable_snd (measurableSet_acceptRegion c s), hround,
      proposal_acceptRegion (phasePointProposal K delta s mu0 t) hs hc2]
    exact pos_iff_ne_zero.2 hmass
  rw [warmPhaseCostLaw, Measure.map_map measurable_snd (by fun_prop)]
  change Measure.map (Prod.fst ∘ Prod.snd)
      (costedRejectionLaw (costedSpeedyRoundLaw rho) (acceptRegion c s)) = _
  rw [← Measure.map_map measurable_fst measurable_snd,
    map_snd_costedRejectionLaw _ (measurableSet_acceptRegion c s) hpos,
    hround, map_fst_condOn_proposal (phasePointProposal K delta s mu0 t) hs hc2]
  rfl

/-- Exact expected actual-query accounting for both restart loops. -/
theorem lintegral_fst_warmPhaseCostLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) {s : Real}
    (hdelta : 0 < delta) (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat)
    (hshrink : 0 < (iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
      ((1 - 1 / (2 * (n : Real))) • K))
    (hs : 0 < s) (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    ∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK delta s hdelta mu0 t) =
      ((phasePointProposal K delta s mu0 t).withDensity
          (fun x => ENNReal.ofReal
            (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s x)) Set.univ)⁻¹ *
      ((iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
        ((1 - 1 / (2 * (n : Real))) • K))⁻¹ *
      ∫⁻ omega, actualMembershipQueryCount t omega
        ∂(lazyRawStoppedExecution K hK delta s hdelta mu0) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let rho := phasePointCostLaw K hK delta s hdelta mu0 t
  have hrho : Measure.map Prod.snd rho = phasePointProposal K delta s mu0 t :=
    map_snd_phasePointCostLaw hK delta s hdelta mu0 t hshrink
  letI : IsProbabilityMeasure (phasePointProposal K delta s mu0 t) := by
    constructor
    rw [← hrho, Measure.map_apply measurable_snd MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  have hround : Measure.map Prod.snd (costedSpeedyRoundLaw rho) =
      proposal (phasePointProposal K delta s mu0 t) := by
    rw [map_snd_costedSpeedyRoundLaw, hrho]
  rw [warmPhaseCostLaw, lintegral_map measurable_fst (by fun_prop),
    lintegral_fst_costedRejectionLaw _ (measurableSet_acceptRegion c s),
    show (costedSpeedyRoundLaw rho)
        (liftedAccept (acceptRegion (n := n) c s)) =
      ((phasePointProposal K delta s mu0 t).withDensity fun x =>
        ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ by
        rw [show liftedAccept (E := State n × Real) (acceptRegion c s) =
            Prod.snd ⁻¹' (acceptRegion c s) from rfl,
          ← Measure.map_apply measurable_snd (measurableSet_acceptRegion c s), hround,
          proposal_acceptRegion (phasePointProposal K delta s mu0 t) hs hc2],
    lintegral_fst_costedSpeedyRoundLaw rho,
    lintegral_fst_phasePointCostLaw hK delta s hdelta mu0 t]
  simp only [c, mul_assoc]

/-- With the standard half-mass shrink event and quarter-mass speedy event, the two nested
restart loops multiply the expected recorded membership-query count by at most eight. -/
theorem lintegral_fst_warmPhaseCostLaw_le_eight
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) {s : Real}
    (hdelta : 0 < delta) (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (t : Nat)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
        ((1 - 1 / (2 * (n : Real))) • K))
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤
      ((phasePointProposal K delta s mu0 t).withDensity
        (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s x))) Set.univ)
    (hs : 0 < s) (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    ∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK delta s hdelta mu0 t) ≤
      8 * ∫⁻ omega, actualMembershipQueryCount t omega
        ∂(lazyRawStoppedExecution K hK delta s hdelta mu0) := by
  have hhalfPos : 0 < (iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
      ((1 - 1 / (2 * (n : Real))) • K) :=
    lt_of_lt_of_le (by norm_num) hhalf
  rw [lintegral_fst_warmPhaseCostLaw hK delta hdelta mu0 t hhalfPos hs hc2]
  have hiHalf : ((iterate (lazy (speedyMetropolisGaussian K delta s)) mu0 t)
      ((1 - 1 / (2 * (n : Real))) • K))⁻¹ ≤ 2 := by
    calc
      _ ≤ (ENNReal.ofReal (1 / 2 : Real))⁻¹ := ENNReal.inv_le_inv.mpr hhalf
      _ = 2 := by
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 1 / 2)]
        norm_num
  have hiQuarter : (((phasePointProposal K delta s mu0 t).withDensity
      (fun x => ENNReal.ofReal
        (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s x))) Set.univ)⁻¹ ≤ 4 := by
    calc
      _ ≤ (ENNReal.ofReal (1 / 4 : Real))⁻¹ := ENNReal.inv_le_inv.mpr hquarter
      _ = 4 := by
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 1 / 4)]
        norm_num
  calc
    _ ≤ 4 * 2 * ∫⁻ omega, actualMembershipQueryCount t omega
          ∂(lazyRawStoppedExecution K hK delta s hdelta mu0) := by gcongr
    _ = 8 * ∫⁻ omega, actualMembershipQueryCount t omega
          ∂(lazyRawStoppedExecution K hK delta s hdelta mu0) := by norm_num

/-- Adjustable-radius operational capstone.  Every cost is a retained raw membership
query.  The factor eight is exactly the two independent restart factors (`2 · 4`); the
remaining `10/6` is the proved adjustable-radius lazy-walk query bound. -/
theorem six_mul_lintegral_warmPhaseCostLaw_le_eighty_mul_adjustable
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : Metric.ball (0 : State n) 1 ⊆ K)
    {q delta sigma R : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {M : ENNReal} {mu0 : Measure (State n)} [IsProbabilityMeasure mu0]
    (hwarm : IsWarm M mu0 (ellGaussianProb K delta (sigma ^ 2))) (t : Nat)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤
      (iterate (lazy (speedyMetropolisGaussian K delta (sigma ^ 2))) mu0 t)
        ((1 - 1 / (2 * (n : Real))) • K))
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤
      ((phasePointProposal K delta (sigma ^ 2) mu0 t).withDensity
        (fun x => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (sigma ^ 2) x))) Set.univ)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    6 * (∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK delta (sigma ^ 2) hdelta mu0 t)) ≤
      80 * ((t : ENNReal) * M) := by
  have h8 := lintegral_fst_warmPhaseCostLaw_le_eight hK delta hdelta mu0 t
    hhalf hquarter (sq_pos_of_pos hsigma) hc2
  have hraw := six_mul_expected_actualMembershipQueryCount_le_ten_mul_adjustable
    hn hK hKc hball hq hdelta hsigma hdeltan hdeltaq hR hRsigma hKR hwarm t
  calc
    6 * (∫⁻ z, z.1 ∂(warmPhaseCostLaw K hK delta (sigma ^ 2) hdelta mu0 t)) ≤
        6 * (8 * ∫⁻ omega, actualMembershipQueryCount t omega
          ∂(lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu0)) :=
      mul_le_mul_left' h8 6
    _ = 8 * (6 * ∫⁻ omega, actualMembershipQueryCount t omega
          ∂(lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu0)) := by
      ac_rfl
    _ ≤ 8 * (10 * ((t : ENNReal) * M)) := mul_le_mul_left' hraw 8
    _ = 80 * ((t : ENNReal) * M) := by
      rw [← mul_assoc]
      norm_num

end WarmPhase

end Ttc.CostedWarmPhaseRejection

#print axioms Ttc.CostedWarmPhaseRejection.lintegral_stoppedQueryCost
#print axioms Ttc.CostedWarmPhaseRejection.map_snd_warmPhaseCostLaw_eq_phaseLaw
#print axioms Ttc.CostedWarmPhaseRejection.lintegral_fst_warmPhaseCostLaw
#print axioms Ttc.CostedWarmPhaseRejection.six_mul_lintegral_warmPhaseCostLaw_le_eighty_mul_adjustable

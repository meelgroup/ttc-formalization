/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.ContinuingRejectionSignificant
import Arlib.Probability.InhomogeneousMarkov

/-!
# A finite history-dependent continuing-retry kernel

Unlike the existing iid rejection kernel, this transition updates the current point after
every rejection.  Its state stores the current point, an absorbing acceptance flag and
output, and the accumulated query cost.
-/

namespace Ttc.FiniteContinuingRetry

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical

variable {E C F : Type*} [MeasurableSpace E] [MeasurableSpace C] [MeasurableSpace F]

/-- `(current point, accepted?, output, accumulated cost)`.  Before acceptance the output
field contains the caller-supplied fallback value. -/
abbrev RetryState (E F : Type*) := E × Bool × F × ENNReal

def current (s : RetryState E F) : E := s.1
def accepted (s : RetryState E F) : Bool := s.2.1
def output (s : RetryState E F) : F := s.2.2.1
def accumulatedCost (s : RetryState E F) : ENNReal := s.2.2.2

theorem measurable_current : Measurable (current : RetryState E F → E) := by
  exact measurable_fst
theorem measurable_accepted : Measurable (accepted : RetryState E F → Bool) := by
  exact measurable_fst.comp measurable_snd
theorem measurable_output : Measurable (output : RetryState E F → F) := by
  exact measurable_fst.comp (measurable_snd.comp measurable_snd)
theorem measurable_accumulatedCost :
    Measurable (accumulatedCost : RetryState E F → ENNReal) := by
  exact measurable_snd.comp (measurable_snd.comp measurable_snd)

def acceptedStates : Set (RetryState E F) := {s | accepted s = true}

theorem measurableSet_acceptedStates : MeasurableSet (acceptedStates : Set (RetryState E F)) := by
  exact (measurableSet_singleton true).preimage measurable_accepted

def runningStates : Set (RetryState E F) := acceptedStatesᶜ

theorem measurableSet_runningStates : MeasurableSet (runningStates : Set (RetryState E F)) :=
  measurableSet_acceptedStates.compl

/-- Update by one candidate.  Acceptance records `out c`; rejection keeps the old output
fallback and moves the current point to `next c`. -/
noncomputable def advance (A : Set C) (next : C → E) (out : C → F)
    (roundCost : C → ENNReal) (s : RetryState E F) (c : C) : RetryState E F :=
  if c ∈ A then
    (next c, true, out c, accumulatedCost s + roundCost c)
  else
    (next c, false, output s, accumulatedCost s + roundCost c)

theorem measurable_advance {A : Set C} (hA : MeasurableSet A)
    {next : C → E} (hnext : Measurable next)
    {out : C → F} (hout : Measurable out)
    {roundCost : C → ENNReal} (hcost : Measurable roundCost) :
    Measurable (fun p : RetryState E F × C ↦
      advance A next out roundCost p.1 p.2) := by
  apply Measurable.piecewise (s := Prod.snd ⁻¹' A)
  · exact hA.preimage measurable_snd
  · simp only [accumulatedCost]
    fun_prop
  · simp only [output, accumulatedCost]
    fun_prop

/-- Active transition, retaining the old state beside the new candidate so the update can
depend on accumulated cost and fallback output. -/
noncomputable def activeRetryKernel
    (candidate : Kernel E C) [IsMarkovKernel candidate]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost) :
    Kernel (RetryState E F) (RetryState E F) :=
  Kernel.map
    (Kernel.compProd (Kernel.id : Kernel (RetryState E F) (RetryState E F))
      (Kernel.prodMkLeft (RetryState E F)
        (Kernel.comap candidate (current : RetryState E F → E) measurable_current)))
    (fun p ↦ advance A next out roundCost p.1 p.2)

instance activeRetryKernel.isMarkovKernel
    (candidate : Kernel E C) [IsMarkovKernel candidate]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost) :
    IsMarkovKernel (activeRetryKernel candidate A hA next hnext out hout roundCost hcost) := by
  unfold activeRetryKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_advance (E := E) (F := F) hA hnext hout hcost)

/-- One retry at time `j`.  Accepted states are absorbing. -/
noncomputable def retryStep
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (j : Nat) : Kernel (RetryState E F) (RetryState E F) :=
  Kernel.piecewise measurableSet_acceptedStates
    (Kernel.deterministic id measurable_id)
    (activeRetryKernel (candidate j) A hA next hnext out hout roundCost hcost)

instance retryStep.isMarkovKernel
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost) (j : Nat) :
    IsMarkovKernel (retryStep candidate A hA next hnext out hout roundCost hcost j) := by
  unfold retryStep
  infer_instance

/-- The active transition is simply the candidate law mapped by the state update. -/
theorem activeRetryKernel_apply
    (candidate : Kernel E C) [IsMarkovKernel candidate]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (s : RetryState E F) :
    activeRetryKernel candidate A hA next hnext out hout roundCost hcost s =
      (candidate (current s)).map (advance A next out roundCost s) := by
  let joint : Kernel (RetryState E F) (RetryState E F × C) :=
    Kernel.compProd (Kernel.id : Kernel (RetryState E F) (RetryState E F))
      (Kernel.prodMkLeft (RetryState E F)
        (Kernel.comap candidate (current : RetryState E F → E) measurable_current))
  have hjoint : joint s =
      (candidate (current s)).map (fun c ↦ (s, c)) := by
    ext D hD
    dsimp only [joint]
    rw [Kernel.compProd_apply hD, Kernel.id_apply, lintegral_dirac']
    · rw [Kernel.prodMkLeft_apply, Kernel.comap_apply,
        Measure.map_apply (by fun_prop) hD]
    · exact Kernel.measurable_kernel_prodMk_left' hD s
  have hall : Measurable (fun p : RetryState E F × C ↦
      advance A next out roundCost p.1 p.2) :=
    measurable_advance (E := E) (F := F) hA hnext hout hcost
  have hadv : Measurable (advance A next out roundCost s) :=
    hall.comp
      (measurable_const.prodMk measurable_id)
  rw [activeRetryKernel, show
    Kernel.compProd (Kernel.id : Kernel (RetryState E F) (RetryState E F))
      (Kernel.prodMkLeft (RetryState E F)
        (Kernel.comap candidate current measurable_current)) = joint from rfl,
    Kernel.map_apply _ hall, hjoint, Measure.map_map hall (by fun_prop)]
  congr 1

/-- Accepted states are absorbing; running states execute the time-indexed candidate. -/
theorem retryStep_apply
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (j : Nat) (s : RetryState E F) :
    retryStep candidate A hA next hnext out hout roundCost hcost j s =
      if accepted s = true then Measure.dirac s
      else (candidate j (current s)).map (advance A next out roundCost s) := by
  rw [retryStep, Kernel.piecewise_apply]
  by_cases hs : s ∈ (acceptedStates : Set (RetryState E F))
  · rw [if_pos hs, Kernel.deterministic_apply measurable_id,
      if_pos (by simpa [acceptedStates] using hs)]
    rfl
  · rw [if_neg hs, if_neg (by simpa [acceptedStates] using hs)]
    exact activeRetryKernel_apply (candidate j) A hA next hnext out hout roundCost hcost s

def acceptedOutputEvent (T : Set F) : Set (RetryState E F) :=
  {s | accepted s = true ∧ output s ∈ T}

theorem measurableSet_acceptedOutputEvent {T : Set F} (hT : MeasurableSet T) :
    MeasurableSet (acceptedOutputEvent (E := E) T) :=
  (measurableSet_acceptedStates.inter (hT.preimage measurable_output))

/-- Exact accepted-output recursion for one retry. -/
theorem retryStep_acceptedOutputEvent
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (j : Nat) (s : RetryState E F) {T : Set F} (hT : MeasurableSet T) :
    retryStep candidate A hA next hnext out hout roundCost hcost j s
        (acceptedOutputEvent T) =
      if accepted s = true then (acceptedOutputEvent T).indicator 1 s
      else candidate j (current s) (A ∩ out ⁻¹' T) := by
  rw [retryStep_apply]
  split_ifs with hs
  · rw [Measure.dirac_apply' _ (measurableSet_acceptedOutputEvent hT)]
  · have hadv : Measurable (advance A next out roundCost s) :=
      (measurable_advance (E := E) (F := F) hA hnext hout hcost).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hadv (measurableSet_acceptedOutputEvent hT)]
    congr 1
    ext c
    by_cases hc : c ∈ A <;>
      simp [hc, acceptedOutputEvent, advance, accepted, output]

/-- Exact survival recursion for one state: an absorbed state never survives, while an
active state survives precisely when the new candidate is rejected. -/
theorem retryStep_runningStates
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (j : Nat) (s : RetryState E F) :
    retryStep candidate A hA next hnext out hout roundCost hcost j s runningStates =
      if accepted s = true then 0 else candidate j (current s) Aᶜ := by
  rw [retryStep_apply]
  split_ifs with hs
  · rw [Measure.dirac_apply' _ measurableSet_runningStates]
    simp [runningStates, acceptedStates, hs]
  · have hadv : Measurable (advance A next out roundCost s) :=
      (measurable_advance (E := E) (F := F) hA hnext hout hcost).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hadv measurableSet_runningStates]
    congr 1
    ext c
    by_cases hc : c ∈ A <;>
      simp [hc, runningStates, acceptedStates, advance, accepted]

/-- One active retry adds at most the supplied deterministic per-round cost bound; an
already accepted state adds zero. -/
theorem retryStep_cost_le_one
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (B : ENNReal) (hB : ∀ c, roundCost c ≤ B)
    (j : Nat) (s : RetryState E F) :
    retryStep candidate A hA next hnext out hout roundCost hcost j s
        {s' | accumulatedCost s' ≤ accumulatedCost s + B} = 1 := by
  rw [retryStep_apply]
  split_ifs with hs
  · rw [Measure.dirac_apply']
    · simp
    · exact measurableSet_le measurable_accumulatedCost measurable_const
  · have hadv : Measurable (advance A next out roundCost s) :=
      (measurable_advance (E := E) (F := F) hA hnext hout hcost).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hadv
      (measurableSet_le measurable_accumulatedCost measurable_const)]
    have hall : (advance A next out roundCost s) ⁻¹'
        {s' | accumulatedCost s' ≤ accumulatedCost s + B} = Set.univ := by
      ext c
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      simp only [advance, accumulatedCost]
      split_ifs <;> exact add_le_add_right (hB c) _
    rw [hall, measure_univ]

/-- A finite execution performs exactly one candidate transition at each index below `L`;
accepted states merely take the absorbing transition. -/
def retryCount (L : Nat) : Nat := L

@[simp] theorem retryCount_zero : retryCount 0 = 0 := rfl
@[simp] theorem retryCount_succ (L : Nat) : retryCount (L + 1) = retryCount L + 1 := rfl

/-- Deterministic accumulated-cost bound along any realized finite retry path satisfying
the one-step cost support property. -/
theorem accumulatedCost_le_initial_add_mul
    (z : Nat → RetryState E F) (B : ENNReal) :
    ∀ L, (∀ j, j < L →
      accumulatedCost (z (j + 1)) ≤ accumulatedCost (z j) + B) →
      accumulatedCost (z L) ≤ accumulatedCost (z 0) + (L : ENNReal) * B := by
  intro L hstep
  induction L with
  | zero => simp
  | succ L ih =>
      calc
        accumulatedCost (z (L + 1)) ≤ accumulatedCost (z L) + B :=
          hstep L (by omega)
        _ ≤ (accumulatedCost (z 0) + (L : ENNReal) * B) + B :=
          add_le_add (ih (fun j hj ↦ hstep j (by omega))) le_rfl
        _ = accumulatedCost (z 0) + ((L + 1 : Nat) : ENNReal) * B := by
          push_cast
          ring

/-- Conditional-history restart/factorization for a retry transition.  This is the exact
seam consumed by the significant-survival warm theorem. -/
theorem retryStep_conditionalHistory_factorization
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    {H : Type*} [MeasurableSpace H] {rho : Measure H} [IsProbabilityMeasure rho]
    {last : H → RetryState E F} (hlast : Measurable last)
    (j : Nat) {S : Set H} {T : Set (RetryState E F)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hhalf : 1 / 2 ≤ rho.real S) :
    (rho ⊗ₘ Kernel.comap
      (retryStep candidate A hA next hnext out hout roundCost hcost j) last hlast).real
        (Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T) =
      rho.real S *
        (sampleFromKernel
          (retryStep candidate A hA next hnext out hout roundCost hcost j)
          ((condOn rho S).map last)).real T :=
  compProd_comap_rectangle_eq_conditional_restart
    (retryStep candidate A hA next hnext out hout roundCost hcost j)
    hlast hS hT hhalf

/-! ## Finite-law decomposition interface -/

/-- Exact finite decomposition exported to the significant-survival mixture analysis.

For the concrete retry kernel, `w i` is the first-acceptance mass at retry `i`, `proposal i`
is the candidate law conditional on survival to `i`, and `s L` is the unresolved survival
mass.  `output_eq` says that no retry factor is tensorized: accepted laws are combined with
their actual first-hit weights and the remaining mass is charged once to the fallback. -/
structure FiniteRetryDecomposition
    (L : Nat) (outputLaw : Measure E) (A : Set E) (fallback : E)
    (eta r : ENNReal) where
  w : Fin L → ENNReal
  proposal : Fin L → Measure E
  proposal_probability : ∀ i, IsProbabilityMeasure (proposal i)
  s : Nat → ENNReal
  output_eq : outputLaw =
    Ttc.ContinuingRejectionSignificant.acceptedMixture L w
      (fun i ↦ condOn (proposal i) A) (s L) fallback
  mass : (∑ i, w i) + s L = 1
  survival_zero : s 0 ≤ 1
  survival_mono : ∀ j, s (j + 1) ≤ s j
  survival_contract : ∀ j, eta ≤ s j → s (j + 1) ≤ r * s j

attribute [instance] FiniteRetryDecomposition.proposal_probability

/-- The concrete output-law decomposition plugs directly into the independently proved
significant-survival capstone. -/
theorem FiniteRetryDecomposition.tvLe_output_quarter
    {L : Nat} {outputLaw : Measure E} {A : Set E} {fallback : E}
    {eta r zeta : ENNReal}
    (hdec : FiniteRetryDecomposition L outputLaw A fallback eta r)
    (tau : Measure E) [IsProbabilityMeasure tau]
    (hA : MeasurableSet A)
    (hproposal : ∀ i, TVLe (hdec.proposal i) tau zeta)
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤ tau A)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 8 : Real))
    (hr : r ≤ 1) :
    TVLe outputLaw (condOn tau A) (16 * zeta + (eta + r ^ L)) := by
  rw [hdec.output_eq]
  exact Ttc.ContinuingRejectionSignificant.tvLe_continuingAcceptedMixture_quarter_of_survival
      L hdec.w hdec.proposal tau hA hdec.s eta r zeta fallback hdec.mass
      hproposal hquarter hzeta hdec.survival_zero hr hdec.survival_mono
      hdec.survival_contract

#print axioms retryStep_apply
#print axioms retryStep_acceptedOutputEvent
#print axioms retryStep_runningStates
#print axioms retryStep_cost_le_one
#print axioms accumulatedCost_le_initial_add_mul
#print axioms retryStep_conditionalHistory_factorization
#print axioms FiniteRetryDecomposition.tvLe_output_quarter

end Ttc.FiniteContinuingRetry

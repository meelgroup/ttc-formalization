import Ttc.Exec.CVHistoryCostedKernel
import Ttc.Exec.CVRetainedHistoryReferenceInduction
import Ttc.Exec.CVIdealAveragePathTelescope
import Ttc.Exec.CVIndependentStreamDependence

/-!
# Retained terminal histories have the ordinary finite-path law
-/

namespace Ttc.CVRetainedHistoryPathLaw

open MeasureTheory ProbabilityTheory Finset Preorder
open Arlib Arlib.Probability
open Ttc.CVHistoryCostedKernel
open Ttc.CVRetainedHistoryReferenceInduction
open Ttc.CVIdealAveragePathTelescope
open Ttc.CVIndependentStreamDependence
open scoped ENNReal Classical

variable {X : Type*} [MeasurableSpace X]

def initialHistoryState (x : X) : HistoryState X := ((0, fun _ ↦ x), x)

theorem measurable_initialHistoryState :
    Measurable (initialHistoryState : X → HistoryState X) := by
  unfold initialHistoryState
  fun_prop

noncomputable def initialHistoryLaw (mu : Measure X) : Measure (HistoryState X) :=
  Measure.map initialHistoryState mu

instance initialHistoryLaw.instIsProbabilityMeasure
    (mu : Measure X) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (initialHistoryLaw mu) :=
  Measure.isProbabilityMeasure_map measurable_initialHistoryState.aemeasurable

/-- The stored prefix together with the live current state. -/
def storedPrefixCurrent (t : Nat) (z : HistoryState X) :
    (Iic t → X) × X :=
  (fun j ↦ z.1.2 j.1, z.2)

theorem measurable_storedPrefixCurrent (t : Nat) :
    Measurable (storedPrefixCurrent (X := X) t) := by
  unfold storedPrefixCurrent
  fun_prop

/-- The corresponding prefix/current readout of an ordinary path. -/
def pathPrefixCurrent (t : Nat) (omega : Nat → X) : (Iic t → X) × X :=
  (frestrictLe t omega, omega t)

theorem measurable_pathPrefixCurrent (t : Nat) :
    Measurable (pathPrefixCurrent (X := X) t) := by
  unfold pathPrefixCurrent
  fun_prop

/-- Advance a prefix/current pair by one sampled state. -/
def advancePrefixCurrent (i : Nat) (z : ((Iic i → X) × X) × X) :
    (Iic (i + 1) → X) × X :=
  (extendIic i (z.1.1, z.2), z.2)

theorem measurable_advancePrefixCurrent (i : Nat) :
    Measurable (advancePrefixCurrent (X := X) i) := by
  unfold advancePrefixCurrent
  exact ((measurable_extendIic i).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk measurable_snd

def advanceHistoryNext (i : Nat) (z : (Iic i → X) × X) :
    (Iic (i + 1) → X) × X := (extendIic i z, z.2)

theorem measurable_advanceHistoryNext (i : Nat) :
    Measurable (advanceHistoryNext (X := X) i) :=
  (measurable_extendIic i).prodMk measurable_snd

theorem advancePrefixCurrent_path (i : Nat) (omega : Nat → X) :
    advancePrefixCurrent i (pathPrefixCurrent i omega, omega (i + 1)) =
      pathPrefixCurrent (i + 1) omega := by
  unfold advancePrefixCurrent pathPrefixCurrent
  rw [extendIic_history_next]

theorem storedPrefixCurrent_appendPhase (i : Nat)
    (z : HistoryState X) (y : ENNReal × X) :
    storedPrefixCurrent (i + 1) (appendPhase i (z.1, y)) =
      advancePrefixCurrent i (storedPrefixCurrent i z, y.2) := by
  apply Prod.ext
  · funext j
    by_cases hj : j.1 ≤ i
    · have hne : j.1 ≠ i + 1 := by omega
      simp [storedPrefixCurrent, appendPhase, advancePrefixCurrent, extendIic, hj,
        Function.update, hne]
    · have hle : j.1 ≤ i + 1 := mem_Iic.1 j.2
      have heq : j.1 = i + 1 := by omega
      simp [storedPrefixCurrent, appendPhase, advancePrefixCurrent, extendIic, hj,
        Function.update, heq]
  · rfl

/-- One history-appending phase, observed only through its new prefix and current
state, is the ordinary state transition applied to the old prefix/current pair. -/
theorem map_storedPrefixCurrent_historyCostedKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q]
    (P : Kernel X X) [IsMarkovKernel P]
    (hforget : ∀ x, Measure.map Prod.snd (Q x) = P x)
    (i : Nat) (z : HistoryState X) :
    Measure.map (storedPrefixCurrent (X := X) (i + 1))
        (historyCostedKernel Q i z) =
      Measure.map (fun x : X ↦ advancePrefixCurrent i
        (storedPrefixCurrent i z, x)) (P z.2) := by
  unfold historyCostedKernel
  rw [Kernel.map_apply _ (measurable_appendPhase i),
    Measure.map_map (measurable_storedPrefixCurrent (i + 1))
      (measurable_appendPhase i)]
  rw [Kernel.prod_apply]
  rw [Kernel.deterministic_apply measurable_fst, Kernel.comap_apply]
  have hf : Measurable (storedPrefixCurrent (X := X) (i + 1) ∘ appendPhase i) :=
    (measurable_storedPrefixCurrent (i + 1)).comp (measurable_appendPhase i)
  have hg : Measurable (fun x : X ↦ advancePrefixCurrent i
      (storedPrefixCurrent i z, x)) :=
    (measurable_advancePrefixCurrent i).comp (measurable_const.prodMk measurable_id)
  ext A hA
  rw [Measure.map_apply hf hA, Measure.map_apply hg hA]
  rw [Measure.prod_apply_symm]
  · let E : Set (ENNReal × X) :=
      (fun y ↦ advancePrefixCurrent i (storedPrefixCurrent i z, y.2)) ⁻¹' A
    have hE : MeasurableSet E := hA.preimage (hg.comp measurable_snd)
    rw [← hforget z.2, Measure.map_apply measurable_snd (hA.preimage hg)]
    have heval : ∀ y : ENNReal × X,
        (Measure.dirac z.1)
            ((fun x ↦ (x, y)) ⁻¹'
              (storedPrefixCurrent (i + 1) ∘ appendPhase i) ⁻¹' A) =
          E.indicator 1 y := by
      intro y
      have hsec : MeasurableSet
          ((fun x : HistoryPayload X ↦ (x, y)) ⁻¹'
            (storedPrefixCurrent (i + 1) ∘ appendPhase i) ⁻¹' A) :=
        (hA.preimage hf).preimage (measurable_id.prodMk measurable_const)
      rw [Measure.dirac_apply' _ hsec]
      by_cases hy : y ∈ E
      · simp only [Set.indicator_of_mem hy, Pi.one_apply]
        apply Set.indicator_of_mem
        change storedPrefixCurrent (i + 1) (appendPhase i (z.1, y)) ∈ A
        rw [storedPrefixCurrent_appendPhase]
        exact hy
      · simp only [Set.indicator_of_notMem hy, Pi.one_apply]
        apply Set.indicator_of_notMem
        change storedPrefixCurrent (i + 1) (appendPhase i (z.1, y)) ∉ A
        rw [storedPrefixCurrent_appendPhase]
        exact hy
    rw [lintegral_congr heval, lintegral_indicator_one hE]
    rfl
  · exact hA.preimage hf

/-- Map a bind when the output map intertwines the kernels pointwise. -/
theorem map_bind_of_pointwise
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (mu : Measure A) [SFinite mu]
    (Q : Kernel A B) [IsSFiniteKernel Q]
    (R : Kernel C D) [IsSFiniteKernel R]
    (f : A → C) (g : B → D) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ x, Measure.map g (Q x) = R (f x)) :
    Measure.map g (mu.bind Q) = (Measure.map f mu).bind R := by
  ext S hS
  rw [Measure.map_apply hg hS,
    Measure.bind_apply (hS.preimage hg) (Kernel.aemeasurable Q),
    Measure.bind_apply hS (Kernel.aemeasurable R),
    lintegral_map (Kernel.measurable_coe R hS) hf]
  apply lintegral_congr
  intro x
  rw [← Measure.map_apply hg hS, h x]

/-- Markov kernel on finite prefix/current pairs. -/
noncomputable def prefixCurrentStep (P : Kernel X X) (i : Nat) :
    Kernel ((Iic i → X) × X) ((Iic (i + 1) → X) × X) :=
  Kernel.map
    ((Kernel.deterministic id measurable_id) ×ₖ
      (Kernel.comap P Prod.snd measurable_snd))
    (advancePrefixCurrent i)

instance prefixCurrentStep.instIsMarkovKernel
    (P : Kernel X X) [IsMarkovKernel P] (i : Nat) :
    IsMarkovKernel (prefixCurrentStep P i) := by
  unfold prefixCurrentStep
  exact Kernel.IsMarkovKernel.map _ (measurable_advancePrefixCurrent i)

theorem prefixCurrentStep_apply (P : Kernel X X) [IsMarkovKernel P]
    (i : Nat) (z : (Iic i → X) × X) :
    prefixCurrentStep P i z =
      Measure.map (fun x ↦ advancePrefixCurrent i (z, x)) (P z.2) := by
  unfold prefixCurrentStep
  rw [Kernel.map_apply _ (measurable_advancePrefixCurrent i), Kernel.prod_apply,
    Kernel.deterministic_apply measurable_id, Kernel.comap_apply]
  rw [Measure.dirac_prod]
  rw [Measure.map_map (measurable_advancePrefixCurrent i) (by fun_prop)]
  rfl

theorem map_pathPrefixCurrent_succ
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure X) [IsProbabilityMeasure mu] (i : Nat) :
    Measure.map (pathPrefixCurrent (X := X) (i + 1))
        (inhomogeneousPathMeasure P mu) =
      (Measure.map (pathPrefixCurrent i) (inhomogeneousPathMeasure P mu)).bind
        (prefixCurrentStep (P i) i) := by
  let pathLaw := inhomogeneousPathMeasure P mu
  let pairNext : (Nat → X) → (Iic i → X) × X :=
    fun omega ↦ (frestrictLe i omega, omega (i + 1))
  have hjoint := map_history_next_inhomogeneousPathMeasure P mu i
  have hadv : advanceHistoryNext i ∘ pairNext = pathPrefixCurrent (i + 1) := by
    funext omega
    apply Prod.ext
    · exact extendIic_history_next i omega
    · rfl
  calc
    Measure.map (pathPrefixCurrent (i + 1)) pathLaw =
        Measure.map (advanceHistoryNext i)
          (Measure.map pairNext pathLaw) := by
      rw [Measure.map_map (measurable_advanceHistoryNext i) (by fun_prop), hadv]
    _ = Measure.map (advanceHistoryNext i)
          ((Measure.map (frestrictLe i) pathLaw) ⊗ₘ
            inhomogeneousHistoryKernel P i) := by rw [hjoint]
    _ = (Measure.map (pathPrefixCurrent i) pathLaw).bind
          (prefixCurrentStep (P i) i) := by
      ext S hS
      rw [Measure.map_apply (measurable_advanceHistoryNext i) hS,
        Measure.compProd_apply
          (hS.preimage (measurable_advanceHistoryNext i)),
        Measure.bind_apply hS (Kernel.aemeasurable _)]
      rw [lintegral_map (Kernel.measurable_coe (prefixCurrentStep (P i) i) hS)
        (measurable_pathPrefixCurrent i)]
      have hmeasF : Measurable (fun h : Iic i → X ↦
          (inhomogeneousHistoryKernel P i h)
            (Prod.mk h ⁻¹' advanceHistoryNext i ⁻¹' S)) := by
        have hh := Kernel.measurable_coe
          (Kernel.id ×ₖ inhomogeneousHistoryKernel P i)
          (hS.preimage (measurable_advanceHistoryNext i))
        convert hh using 1
        funext h
        rw [Kernel.id_prod_apply' _ _
          (hS.preimage (measurable_advanceHistoryNext i))]
      rw [lintegral_map hmeasF (measurable_frestrictLe i)]
      apply lintegral_congr
      intro omega
      rw [prefixCurrentStep_apply]
      unfold inhomogeneousHistoryKernel pathPrefixCurrent
      rw [Kernel.comap_apply]
      let f : X → (Iic (i + 1) → X) × X := fun x ↦
        advancePrefixCurrent i ((frestrictLe i omega, omega i), x)
      have hf : Measurable f :=
        (measurable_advancePrefixCurrent i).comp
          (measurable_const.prodMk measurable_id)
      rw [Measure.map_apply hf hS]
      simp only [Preorder.frestrictLe_apply]
      change (P i (omega i))
          ((fun x ↦ advanceHistoryNext i (frestrictLe i omega, x)) ⁻¹' S) =
        (P i (omega i)) (f ⁻¹' S)
      congr 2

/-- The retained terminal state carries exactly the ordinary finite Markov prefix. -/
theorem map_storedPrefixCurrent_retainedPathLaw
    (Q : Nat → Kernel X (ENNReal × X)) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) (t : Nat) :
    Measure.map (storedPrefixCurrent (X := X) t)
        (retainedPathLaw (fun i ↦ historyCostedKernel (Q i) i)
          (initialHistoryLaw mu) t) =
      Measure.map (pathPrefixCurrent t) (inhomogeneousPathMeasure P mu) := by
  induction t with
  | zero =>
      unfold retainedPathLaw initialHistoryLaw
      rw [Measure.map_map (measurable_storedPrefixCurrent 0)
        measurable_initialHistoryState]
      have hzero := Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_zero P mu
      have hfun : storedPrefixCurrent (X := X) 0 ∘ initialHistoryState =
          (fun x : X ↦ (fun _ : Iic 0 ↦ x, x)) := by
        funext x
        rfl
      rw [hfun]
      have hpathfun : pathPrefixCurrent (X := X) 0 =
          (fun x : X ↦ (fun _ : Iic 0 ↦ x, x)) ∘
            (fun omega : Nat → X ↦ omega 0) := by
        funext omega
        apply Prod.ext
        · funext j
          have hj : j.1 = 0 := Nat.eq_zero_of_le_zero (mem_Iic.1 j.2)
          simp [pathPrefixCurrent, frestrictLe, hj]
        · rfl
      rw [hpathfun]
      calc
        Measure.map (fun x : X ↦ (fun _ : Iic 0 ↦ x, x)) mu =
            Measure.map (fun x : X ↦ (fun _ : Iic 0 ↦ x, x))
              (Measure.map (fun omega : Nat → X ↦ omega 0)
                (inhomogeneousPathMeasure P mu)) := by rw [hzero]
        _ = _ := by
          exact Measure.map_map (by fun_prop) (measurable_pi_apply 0)
  | succ i ih =>
      letI : IsProbabilityMeasure
          (retainedPathLaw (fun i ↦ historyCostedKernel (Q i) i)
            (initialHistoryLaw mu) i) := inferInstance
      rw [retainedPathLaw]
      rw [map_bind_of_pointwise
        (retainedPathLaw (fun i ↦ historyCostedKernel (Q i) i)
          (initialHistoryLaw mu) i)
        (historyCostedKernel (Q i) i) (prefixCurrentStep (P i) i)
        (storedPrefixCurrent i) (storedPrefixCurrent (i + 1))
        (measurable_storedPrefixCurrent i) (measurable_storedPrefixCurrent (i + 1))]
      · rw [ih, ← map_pathPrefixCurrent_succ P mu i]
      · intro z
        rw [prefixCurrentStep_apply]
        exact map_storedPrefixCurrent_historyCostedKernel (Q i) (P i)
          (hforget i) i z

/-- Product of independently restarted retained-history executions. -/
noncomputable def independentRetainedPathLaw
    (k : Nat) (Q : Nat → Kernel X (ENNReal × X))
    [∀ i, IsMarkovKernel (Q i)] (mu : Measure X) (t : Nat) :
    Measure (Fin k → HistoryState X) :=
  Measure.pi (fun _ : Fin k ↦
    retainedPathLaw (fun i ↦ historyCostedKernel (Q i) i)
      (initialHistoryLaw mu) t)

instance independentRetainedPathLaw.instIsProbabilityMeasure
    (k : Nat) (Q : Nat → Kernel X (ENNReal × X))
    [∀ i, IsMarkovKernel (Q i)] (mu : Measure X)
    [IsProbabilityMeasure mu] (t : Nat) :
    IsProbabilityMeasure (independentRetainedPathLaw k Q mu t) := by
  unfold independentRetainedPathLaw
  infer_instance

/-- Read the retained prefix/current pair from every independent execution. -/
def independentStoredPrefixCurrent {k : Nat} (t : Nat)
    (z : Fin k → HistoryState X) : Fin k → ((Iic t → X) × X) :=
  fun l ↦ storedPrefixCurrent t (z l)

theorem measurable_independentStoredPrefixCurrent {k : Nat} (t : Nat) :
    Measurable (independentStoredPrefixCurrent (X := X) (k := k) t) := by
  unfold independentStoredPrefixCurrent
  apply measurable_pi_lambda
  intro l
  exact (measurable_storedPrefixCurrent t).comp (measurable_pi_apply l)

/-- Read the corresponding prefix/current pair from every ordinary path. -/
def independentPathPrefixCurrent {k : Nat} (t : Nat)
    (omega : Fin k → Nat → X) : Fin k → ((Iic t → X) × X) :=
  fun l ↦ pathPrefixCurrent t (omega l)

theorem measurable_independentPathPrefixCurrent {k : Nat} (t : Nat) :
    Measurable (independentPathPrefixCurrent (X := X) (k := k) t) := by
  unfold independentPathPrefixCurrent
  apply measurable_pi_lambda
  intro l
  exact (measurable_pathPrefixCurrent t).comp (measurable_pi_apply l)

/-- The product of retained terminal histories has exactly the finite-prefix product
law obtained from the ordinary independent complete-path law.  This is the
representation bridge needed to reuse the existing independent-stream CV accuracy
theorems without a new probabilistic assumption. -/
theorem map_independentStoredPrefixCurrent_independentRetainedPathLaw
    (k : Nat)
    (Q : Nat → Kernel X (ENNReal × X)) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) (t : Nat) :
    Measure.map (independentStoredPrefixCurrent (X := X) (k := k) t)
        (independentRetainedPathLaw k Q mu t) =
      Measure.map (independentPathPrefixCurrent (X := X) (k := k) t)
        (independentPathLaw k P mu) := by
  let scalarActual :=
    retainedPathLaw (fun i ↦ historyCostedKernel (Q i) i)
      (initialHistoryLaw mu) t
  let scalarIdeal := inhomogeneousPathMeasure P mu
  letI : IsProbabilityMeasure scalarActual := inferInstance
  letI : IsProbabilityMeasure scalarIdeal := inferInstance
  letI : ∀ _l : Fin k, SigmaFinite
      (Measure.map (storedPrefixCurrent (X := X) t) scalarActual) :=
    fun _l ↦ by infer_instance
  letI : ∀ _l : Fin k, SigmaFinite
      (Measure.map (pathPrefixCurrent (X := X) t) scalarIdeal) :=
    fun _l ↦ by infer_instance
  unfold independentStoredPrefixCurrent independentPathPrefixCurrent
  unfold independentRetainedPathLaw independentPathLaw
  unfold Ttc.CVIndependentStreamMoments.independentStreamLaw
  rw [Measure.pi_map_pi (fun _l ↦
    (measurable_storedPrefixCurrent (X := X) t).aemeasurable)]
  rw [Measure.pi_map_pi (fun _l ↦
    (measurable_pathPrefixCurrent (X := X) t).aemeasurable)]
  congr 1
  funext l
  exact map_storedPrefixCurrent_retainedPathLaw Q P mu hforget t

/-- Any measurable good event depending on the terminal prefixes/current states has
the same probability under retained executions as under the ordinary independent
complete-path model. -/
theorem independentRetainedPathLaw_real_preimage_eq
    (k : Nat)
    (Q : Nat → Kernel X (ENNReal × X)) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) (t : Nat)
    (G : Set (Fin k → ((Iic t → X) × X))) (hG : MeasurableSet G) :
    (independentRetainedPathLaw k Q mu t).real
        (independentStoredPrefixCurrent t ⁻¹' G) =
      (independentPathLaw k P mu).real
        (independentPathPrefixCurrent t ⁻¹' G) := by
  have hlaw := map_independentStoredPrefixCurrent_independentRetainedPathLaw
    k Q P mu hforget t
  rw [Measure.real, ← Measure.map_apply
      (measurable_independentStoredPrefixCurrent (X := X) (k := k) t) hG,
    hlaw, Measure.map_apply
      (measurable_independentPathPrefixCurrent (X := X) (k := k) t) hG,
    Measure.real]

#print axioms map_storedPrefixCurrent_historyCostedKernel
#print axioms map_storedPrefixCurrent_retainedPathLaw
#print axioms map_independentStoredPrefixCurrent_independentRetainedPathLaw

end Ttc.CVRetainedHistoryPathLaw

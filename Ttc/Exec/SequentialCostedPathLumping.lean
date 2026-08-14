import Ttc.Exec.CostedStatefulSpeedyPhases

/-! Full-path projection of inhomogeneous Markov executions. -/

namespace Ttc.SequentialCostedPathLumping

open MeasureTheory ProbabilityTheory Preorder Finset
open Arlib.Probability
open scoped ENNReal Classical

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

def pathMap (f : A → B) (omega : Nat → A) : Nat → B := fun i => f (omega i)

theorem measurable_pathMap {f : A → B} (hf : Measurable f) : Measurable (pathMap f) := by
  exact measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)

def historyMap (f : A → B) (i : Nat) (h : (_j : Iic i) → A) : (_j : Iic i) → B :=
  fun j => f (h j)

theorem measurable_historyMap {f : A → B} (hf : Measurable f) (i : Nat) :
    Measurable (historyMap f i) := by
  exact measurable_pi_lambda _ fun j => hf.comp (measurable_pi_apply j)

def extendHistory (i : Nat) (p : ((j : Iic i) → B) × B) : (j : Iic (i + 1)) → B :=
  fun j => if h : j.1 ≤ i then p.1 ⟨j.1, mem_Iic.2 h⟩ else p.2

theorem measurable_extendHistory (i : Nat) : Measurable (extendHistory (B := B) i) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : j.1 ≤ i
  · simp only [extendHistory, dif_pos h]
    exact (measurable_pi_apply (⟨j.1, mem_Iic.2 h⟩ : Iic i)).comp measurable_fst
  · simpa [extendHistory, h] using measurable_snd

omit [MeasurableSpace B] in
theorem extendHistory_history_next (i : Nat) (omega : Nat → B) :
    extendHistory i (frestrictLe i omega, omega (i + 1)) = frestrictLe (i + 1) omega := by
  ext j
  by_cases h : j.1 ≤ i
  · simp [extendHistory, h, frestrictLe_apply]
  · have hj : j.1 = i + 1 := by
      apply Nat.le_antisymm (mem_Iic.1 j.2)
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
    simp [extendHistory, frestrictLe_apply, hj]

/-- A joint Markov law commutes with maps of its old and new coordinates. -/
theorem map_compProd_prodMap_of_pointwise
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (mu : Measure A) [SFinite mu] (kap : Kernel A C) [IsSFiniteKernel kap]
    (eta : Kernel B D) [IsSFiniteKernel eta]
    {f : A → B} {g : C → D} (hf : Measurable f) (hg : Measurable g)
    (hkap : ∀ x, Measure.map g (kap x) = eta (f x)) :
    Measure.map (Prod.map f g) (mu ⊗ₘ kap) = (Measure.map f mu) ⊗ₘ eta := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap hg) hs]
  rw [Measure.compProd_apply (hs.preimage (hf.prodMap hg))]
  rw [Measure.compProd_apply hs]
  have hm : Measurable (fun b => eta b (Prod.mk b ⁻¹' s)) := by
    simpa only [Kernel.id_prod_apply' eta _ hs] using
      (Kernel.measurable_coe (Kernel.id ×ₖ eta) hs)
  rw [lintegral_map hm hf]
  apply lintegral_congr
  intro x
  rw [← hkap x]
  have hsx : MeasurableSet (Prod.mk (f x) ⁻¹' s) :=
    hs.preimage (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hg hsx]
  rfl

/-- Every finite initial history of an inhomogeneous path commutes with a Markov
projection. -/
theorem map_frestrictLe_map_inhomogeneousPathMeasure
    (Q : Nat → Kernel A A) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel B B) [∀ i, IsMarkovKernel (P i)]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (mu : Measure B) [IsProbabilityMeasure mu]
    {f : A → B} (hf : Measurable f)
    (hinit : Measure.map f nu = mu)
    (hstep : ∀ i x, Measure.map f (Q i x) = P i (f x)) (i : Nat) :
    Measure.map (frestrictLe i)
        (Measure.map (pathMap f) (inhomogeneousPathMeasure Q nu)) =
      Measure.map (frestrictLe i) (inhomogeneousPathMeasure P mu) := by
  let MQ := inhomogeneousPathMeasure Q nu
  let MP := inhomogeneousPathMeasure P mu
  induction i with
  | zero =>
      have hQ0 := Ttc.SequentialCost.map_eval_inhomogeneousPathMeasure_zero Q nu
      have hP0 := Ttc.SequentialCost.map_eval_inhomogeneousPathMeasure_zero P mu
      have hcA : Measurable (fun x : A => fun _ : Iic 0 => f x) := by fun_prop
      have hcB : Measurable (fun x : B => fun _ : Iic 0 => x) := by fun_prop
      have hfunQ : frestrictLe 0 ∘ pathMap f =
          (fun x : A => fun _ : Iic 0 => f x) ∘ (fun omega : Nat → A => omega 0) := by
        funext omega j
        change f (omega j.1) = f (omega 0)
        have hj : j.1 = 0 := congrArg Subtype.val
          (Subsingleton.elim j (⟨0, mem_Iic.2 le_rfl⟩ : Iic 0))
        rw [hj]
      have hfunP : (fun x : B => fun _ : Iic 0 => x) ∘
          (fun omega : Nat → B => omega 0) = frestrictLe 0 := by
        funext omega j
        change omega 0 = omega j.1
        have hj : j.1 = 0 := congrArg Subtype.val
          (Subsingleton.elim j (⟨0, mem_Iic.2 le_rfl⟩ : Iic 0))
        rw [hj]
      calc
        Measure.map (frestrictLe 0)
            (Measure.map (pathMap f) (inhomogeneousPathMeasure Q nu)) =
            Measure.map (frestrictLe 0 ∘ pathMap f)
              (inhomogeneousPathMeasure Q nu) :=
                Measure.map_map (measurable_frestrictLe 0) (measurable_pathMap hf)
        _ = Measure.map ((fun x : A => fun _ : Iic 0 => f x) ∘
              (fun omega : Nat → A => omega 0))
              (inhomogeneousPathMeasure Q nu) := by rw [hfunQ]
        _ = Measure.map (fun x : A => fun _ : Iic 0 => f x)
              (Measure.map (fun omega : Nat → A => omega 0)
                (inhomogeneousPathMeasure Q nu)) :=
              (Measure.map_map hcA (measurable_pi_apply 0)).symm
        _ = Measure.map (fun x : A => fun _ : Iic 0 => f x) nu := by rw [hQ0]
        _ = Measure.map (fun x : B => fun _ : Iic 0 => x) (Measure.map f nu) := by
              have hcf : (fun x : A => fun _ : Iic 0 => f x) =
                  (fun x : B => fun _ : Iic 0 => x) ∘ f := by
                funext x j
                rfl
              rw [hcf]
              exact (Measure.map_map hcB hf).symm
        _ = Measure.map (fun x : B => fun _ : Iic 0 => x) mu := by rw [hinit]
        _ = Measure.map (fun x : B => fun _ : Iic 0 => x)
              (Measure.map (fun omega : Nat → B => omega 0)
                (inhomogeneousPathMeasure P mu)) :=
              congrArg (Measure.map (fun x : B => fun _ : Iic 0 => x)) hP0.symm
        _ = Measure.map (frestrictLe 0) (inhomogeneousPathMeasure P mu) := by
              rw [Measure.map_map hcB (measurable_pi_apply 0), hfunP]
  | succ i ih =>
      have hQjoint := map_history_next_inhomogeneousPathMeasure Q nu i
      have hPjoint := map_history_next_inhomogeneousPathMeasure P mu i
      let hmf : ((j : Iic i) → A) → ((j : Iic i) → B) := historyMap f i
      have hkernel : ∀ h, Measure.map f (inhomogeneousHistoryKernel Q i h) =
          inhomogeneousHistoryKernel P i (hmf h) := by
        intro h
        change Measure.map f (Q i (h ⟨i, mem_Iic.2 le_rfl⟩)) =
          P i (f (h ⟨i, mem_Iic.2 le_rfl⟩))
        exact hstep i _
      have hhist : Measure.map hmf (Measure.map (frestrictLe i) MQ) =
          Measure.map (frestrictLe i) MP := by
        rw [Measure.map_map (measurable_historyMap hf i) (measurable_frestrictLe i)]
        rw [show hmf ∘ frestrictLe i = frestrictLe i ∘ pathMap f by rfl]
        rw [← Measure.map_map (measurable_frestrictLe i) (measurable_pathMap hf)]
        exact ih
      have hjoint :
          Measure.map (Prod.map hmf f)
              (Measure.map (fun omega : Nat → A =>
                (frestrictLe i omega, omega (i + 1))) MQ) =
            Measure.map (fun omega : Nat → B =>
              (frestrictLe i omega, omega (i + 1))) MP := by
        rw [← hQjoint]
        rw [map_compProd_prodMap_of_pointwise
          (Measure.map (frestrictLe i) MQ)
          (inhomogeneousHistoryKernel Q i)
          (inhomogeneousHistoryKernel P i)
          (measurable_historyMap hf i) hf hkernel]
        rw [hhist, hPjoint]
      have hext := congrArg (Measure.map (extendHistory (B := B) i)) hjoint
      have hfunQ :
          ((extendHistory (B := B) i) ∘ (Prod.map hmf f)) ∘
              (fun omega : Nat → A => (frestrictLe i omega, omega (i + 1))) =
            frestrictLe (i + 1) ∘ pathMap f := by
        funext omega
        exact extendHistory_history_next i (pathMap f omega)
      have hfunP :
          (extendHistory (B := B) i) ∘
              (fun omega : Nat → B => (frestrictLe i omega, omega (i + 1))) =
            frestrictLe (i + 1) := by
        funext omega
        exact extendHistory_history_next i omega
      rw [Measure.map_map (measurable_extendHistory i)
        ((measurable_historyMap hf i).prodMap hf)] at hext
      rw [Measure.map_map
        ((measurable_extendHistory i).comp ((measurable_historyMap hf i).prodMap hf))
        ((measurable_frestrictLe i).prodMk (measurable_pi_apply (i + 1))), hfunQ] at hext
      rw [Measure.map_map (measurable_extendHistory i)
        ((measurable_frestrictLe i).prodMk (measurable_pi_apply (i + 1))), hfunP] at hext
      rw [Measure.map_map (measurable_frestrictLe (i + 1)) (measurable_pathMap hf)]
      exact hext

/-- Probability laws on a countable path space are determined by all initial finite
histories. -/
theorem measure_eq_of_map_frestrictLe_eq
    (nu mu : Measure (Nat → B)) [IsProbabilityMeasure nu] [IsProbabilityMeasure mu]
    (h : ∀ i, Measure.map (frestrictLe i) nu = Measure.map (frestrictLe i) mu) :
    nu = mu := by
  let X : Nat → Type _ := fun _ => B
  let rho : (i : Nat) → Measure ((j : Iic i) → X j.1) :=
    fun i => Measure.map (frestrictLe i) mu
  have hrho : ∀ a b : Nat, ∀ hab : a ≤ b,
      Measure.map (frestrictLe₂ (π := X) hab) (rho b) = rho a := by
    intro a b hab
    dsimp [rho]
    rw [Measure.map_map (measurable_frestrictLe₂ hab) (measurable_frestrictLe b)]
    congr 1
  let fam := MeasureTheory.inducedFamily (X := X) rho
  have hfam : IsProjectiveMeasureFamily fam :=
    MeasureTheory.isProjectiveMeasureFamily_inducedFamily (X := X) rho hrho
  have hnu : IsProjectiveLimit nu fam :=
    (MeasureTheory.isProjectiveLimit_nat_iff (X := X) hfam nu).2 (fun i => by
      change Measure.map (frestrictLe i) nu = MeasureTheory.inducedFamily rho (Iic i)
      rw [MeasureTheory.inducedFamily_Iic]
      exact h i)
  have hmu : IsProjectiveLimit mu fam :=
    (MeasureTheory.isProjectiveLimit_nat_iff (X := X) hfam mu).2 (fun i => by
      change Measure.map (frestrictLe i) mu = MeasureTheory.inducedFamily rho (Iic i)
      rw [MeasureTheory.inducedFamily_Iic])
  exact hnu.unique hmu

/-- Generic full-path lumping for inhomogeneous Markov kernels. -/
theorem map_inhomogeneousPathMeasure_pathMap
    (Q : Nat → Kernel A A) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel B B) [∀ i, IsMarkovKernel (P i)]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (mu : Measure B) [IsProbabilityMeasure mu]
    {f : A → B} (hf : Measurable f)
    (hinit : Measure.map f nu = mu)
    (hstep : ∀ i x, Measure.map f (Q i x) = P i (f x)) :
    Measure.map (pathMap f) (inhomogeneousPathMeasure Q nu) =
      inhomogeneousPathMeasure P mu := by
  letI : IsProbabilityMeasure
      (Measure.map (pathMap f) (inhomogeneousPathMeasure Q nu)) :=
    Measure.isProbabilityMeasure_map (measurable_pathMap hf).aemeasurable
  apply measure_eq_of_map_frestrictLe_eq
  intro i
  exact map_frestrictLe_map_inhomogeneousPathMeasure Q P nu mu hf hinit hstep i

open Ttc.CostedStatefulSpeedyPhases

/-- A sequential costed execution has exactly the supplied uncosted state-path law whenever
each scheduled costed kernel has that state marginal. -/
theorem map_statePath_execution
    {S : Type*} [MeasurableSpace S]
    (Q : Nat → Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel S S) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure S) [IsProbabilityMeasure mu]
    (hstep : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) :
    Measure.map (pathMap Prod.snd) (Ttc.SequentialCost.execution Q mu) =
      inhomogeneousPathMeasure P mu := by
  apply map_inhomogeneousPathMeasure_pathMap
      (Ttc.SequentialCost.stepKernel Q) P
      (Arlib.MarkovChains.zeroCostLaw mu) mu measurable_snd
  · unfold Arlib.MarkovChains.zeroCostLaw
    rw [Measure.map_map measurable_snd (by fun_prop)]
    convert (Measure.map_id : Measure.map id mu = mu) using 1
    ext x
    rfl
  · intro i z
    change Measure.map Prod.snd (Q i z.2) = P i z.2
    exact hstep i z.2

/-- Full state-history projection of the recorded-query speedy phase execution. -/
theorem map_statePath_speedyPhaseExecution
    {n : Nat} {K : Set (Ttc.CostedStatefulSpeedyPhases.State n)} (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (hdelta : ∀ i, 0 < delta i) (steps : Nat → Nat)
    (mu : Measure (Ttc.CostedStatefulSpeedyPhases.State n)) [IsProbabilityMeasure mu] :
    Measure.map (statePath (n := n))
        (Ttc.SequentialCost.execution
          (speedyPhaseSchedule K hK delta sigmaSq hdelta steps) mu) =
      inhomogeneousPathMeasure (speedyPhaseStateSchedule K delta sigmaSq steps) mu := by
  change Measure.map (pathMap Prod.snd)
      (Ttc.SequentialCost.execution
        (speedyPhaseSchedule K hK delta sigmaSq hdelta steps) mu) = _
  apply map_statePath_execution
  intro i x
  exact map_snd_speedyPhaseCostedKernel hK (delta i) (sigmaSq i)
    (hdelta i) (steps i) x

#print axioms map_inhomogeneousPathMeasure_pathMap
#print axioms map_statePath_execution
#print axioms map_statePath_speedyPhaseExecution

end Ttc.SequentialCostedPathLumping

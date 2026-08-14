import Ttc.Exec.CostedPathwisePhaseLumping
import Ttc.Exec.CostedWarmPhaseRejection

/-! State-indexed iid stopped-rejection kernels. -/

namespace Ttc.StatewiseCostedRejectionKernel

open MeasureTheory ProbabilityTheory Function Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CostedWarmPhaseRejection
open Ttc.SequentialCostedPathLumping
open scoped ENNReal Classical

variable {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]

/-- Keep the frozen input parameter and independently resample one round. -/
noncomputable def iidLift (kappa : Kernel A E) : Kernel (A × E) (A × E) :=
  Kernel.comap (Kernel.id ×ₖ kappa) Prod.fst measurable_fst

instance (kappa : Kernel A E) [IsMarkovKernel kappa] : IsMarkovKernel (iidLift kappa) := by
  unfold iidLift
  infer_instance

/-- Full trajectory of frozen-parameter iid rounds, including its first sampled round. -/
noncomputable def iidPairPathKernel (kappa : Kernel A E) [IsMarkovKernel kappa] :
    Kernel A (Nat → A × E) :=
  Kernel.comp
    (Kernel.comap
      (Kernel.traj (Arlib.MarkovChains.chainKernel (iidLift kappa)) 0)
      (fun p : A × E => fun _ : Finset.Iic 0 => p)
      (measurable_pi_lambda _ fun _ => measurable_id))
    (Kernel.id ×ₖ kappa)

instance (kappa : Kernel A E) [IsMarkovKernel kappa] :
    IsMarkovKernel (iidPairPathKernel kappa) := by
  unfold iidPairPathKernel
  infer_instance

theorem iidPairPathKernel_apply
    (kappa : Kernel A E) [IsMarkovKernel kappa] (a : A) :
    iidPairPathKernel kappa a =
      inhomogeneousPathMeasure (fun _ : Nat => iidLift kappa)
        ((Kernel.id ×ₖ kappa) a) := by
  rw [iidPairPathKernel, Kernel.comp_apply, bind_comap]
  rfl

/-- Forget the frozen input from the iid round trajectory. -/
noncomputable def iidRoundsKernel (kappa : Kernel A E) [IsMarkovKernel kappa] :
    Kernel A (RoundSpace E) :=
  Kernel.map (iidPairPathKernel kappa) (pathMap Prod.snd)

instance (kappa : Kernel A E) [IsMarkovKernel kappa] :
    IsMarkovKernel (iidRoundsKernel kappa) := by
  unfold iidRoundsKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_pathMap measurable_snd)

/-- The history through `i` and the next coordinate under `roundsMeasure` factor as the
history law times one fresh copy. -/
theorem map_history_next_roundsMeasure
    (mu : Measure E) [IsProbabilityMeasure mu] (i : Nat) :
    Measure.map (fun omega : RoundSpace E =>
        (Preorder.frestrictLe i omega, omega (i + 1))) (roundsMeasure mu) =
      Measure.map (Preorder.frestrictLe i) (roundsMeasure mu) ⊗ₘ
        Kernel.const ((j : Finset.Iic i) → E) mu := by
  have hd : Disjoint (Finset.Iic i) ({i + 1} : Finset Nat) := by
    rw [Finset.disjoint_left]
    intro j hj hjs
    have hji : j ≤ i := Finset.mem_Iic.1 hj
    simp only [Finset.mem_singleton] at hjs
    omega
  have hind := (iIndepFun_draw mu).indepFun_finset
    (Finset.Iic i) ({i + 1} : Finset Nat) hd (fun _ => measurable_pi_apply _)
  let last : ((j : ({i + 1} : Finset Nat)) → E) → E :=
    fun h => h ⟨i + 1, Finset.mem_singleton_self _⟩
  have hind' := hind.comp measurable_id (measurable_pi_apply
    (⟨i + 1, Finset.mem_singleton_self _⟩ : ({i + 1} : Finset Nat)))
  have hind'' : IndepFun (Preorder.frestrictLe i)
      (fun omega : RoundSpace E => omega (i + 1)) (roundsMeasure mu) := by
    convert hind' using 1 <;> rfl
  rw [hind''.map_prod_eq_prod_map_map
    (Preorder.measurable_frestrictLe i).aemeasurable
    (measurable_pi_apply (i + 1)).aemeasurable]
  have hmarg : Measure.map (fun omega : RoundSpace E => omega (i + 1))
      (roundsMeasure mu) = mu := (measurePreserving_draw mu (i + 1)).map_eq
  rw [hmarg, Measure.compProd_const]

/-- A Markov chain which redraws from `mu` at every time is exactly the iid product law. -/
theorem inhomogeneousPathMeasure_const_eq_roundsMeasure
    (mu : Measure E) [IsProbabilityMeasure mu] :
    inhomogeneousPathMeasure (fun _ : Nat => Kernel.const E mu) mu = roundsMeasure mu := by
  apply measure_eq_of_map_frestrictLe_eq
  intro i
  induction i with
  | zero =>
      have hzero := Ttc.SequentialCost.map_eval_inhomogeneousPathMeasure_zero
        (fun _ : Nat => Kernel.const E mu) mu
      have hround := (measurePreserving_draw mu 0).map_eq
      have hc : Measurable (fun x : E => fun _ : Finset.Iic 0 => x) := by fun_prop
      calc
        Measure.map (Preorder.frestrictLe 0)
            (inhomogeneousPathMeasure (fun _ : Nat => Kernel.const E mu) mu) =
            Measure.map (fun x : E => fun _ : Finset.Iic 0 => x) mu := by
              calc
                _ = Measure.map (fun x : E => fun _ : Finset.Iic 0 => x)
                    (Measure.map (fun omega : Nat → E => omega 0)
                      (inhomogeneousPathMeasure
                        (fun _ : Nat => Kernel.const E mu) mu)) := by
                      rw [Measure.map_map hc (measurable_pi_apply 0)]
                      congr 1
                      funext omega j
                      have hj : j.1 = 0 := congrArg Subtype.val
                        (Subsingleton.elim j
                          (⟨0, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic 0))
                      simp [Preorder.frestrictLe_apply, hj]
                _ = _ := congrArg (Measure.map
                    (fun x : E => fun _ : Finset.Iic 0 => x)) hzero
        _ = Measure.map (Preorder.frestrictLe 0) (roundsMeasure mu) := by
              calc
                _ = Measure.map (fun x : E => fun _ : Finset.Iic 0 => x)
                    (Measure.map (draw 0) (roundsMeasure mu)) :=
                      congrArg (Measure.map
                        (fun x : E => fun _ : Finset.Iic 0 => x)) hround.symm
                _ = _ := by
                      rw [Measure.map_map hc (measurable_draw 0)]
                      congr 1
                      funext omega j
                      have hj : j.1 = 0 := congrArg Subtype.val
                        (Subsingleton.elim j
                          (⟨0, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic 0))
                      simp [Preorder.frestrictLe_apply, draw, hj]
  | succ i ih =>
      have hmarkov := map_history_next_inhomogeneousPathMeasure
        (fun _ : Nat => Kernel.const E mu) mu i
      have hiid := map_history_next_roundsMeasure mu i
      have hjoint :
          Measure.map (fun omega : Nat → E =>
              (Preorder.frestrictLe i omega, omega (i + 1)))
              (inhomogeneousPathMeasure (fun _ : Nat => Kernel.const E mu) mu) =
            Measure.map (fun omega : Nat → E =>
              (Preorder.frestrictLe i omega, omega (i + 1)))
              (roundsMeasure mu) := by
        rw [← hmarkov]
        change Measure.map (Preorder.frestrictLe i)
            (inhomogeneousPathMeasure (fun _ : Nat => Kernel.const E mu) mu) ⊗ₘ
              Kernel.const ((j : Finset.Iic i) → E) mu = _
        rw [ih, ← hiid]
      have hext := congrArg
        (Measure.map (extendHistory (B := E) i)) hjoint
      rw [Measure.map_map (measurable_extendHistory i) (by fun_prop)] at hext
      rw [Measure.map_map (measurable_extendHistory i) (by fun_prop)] at hext
      have hfun : extendHistory (B := E) i ∘
          (fun omega : Nat → E =>
            (Preorder.frestrictLe i omega, omega (i + 1))) =
          Preorder.frestrictLe (i + 1) := by
        funext omega
        exact extendHistory_history_next i omega
      simpa only [hfun] using hext

theorem map_snd_iidLift
    (kappa : Kernel A E) [IsMarkovKernel kappa] (p : A × E) :
    Measure.map Prod.snd (iidLift kappa p) =
      Kernel.const E (kappa p.1) p.2 := by
  rw [iidLift, Kernel.comap_apply, Kernel.const_apply]
  ext S hS
  rw [Measure.map_apply measurable_snd hS, Kernel.id_prod_apply' kappa p.1
    (hS.preimage measurable_snd)]
  rfl

theorem map_snd_id_prod
    (kappa : Kernel A E) [IsMarkovKernel kappa] (a : A) :
    Measure.map Prod.snd ((Kernel.id ×ₖ kappa) a) = kappa a := by
  ext S hS
  rw [Measure.map_apply measurable_snd hS,
    Kernel.id_prod_apply' kappa a (hS.preimage measurable_snd)]
  rfl

theorem map_embed_const_eq_iidLift
    (kappa : Kernel A E) [IsMarkovKernel kappa] (a : A) (e : E) :
    Measure.map (fun y : E => (a, y))
        (Kernel.const E (kappa a) e) = iidLift kappa (a, e) := by
  rw [Kernel.const_apply, iidLift, Kernel.comap_apply]
  ext S hS
  rw [Measure.map_apply (by fun_prop) hS,
    Kernel.id_prod_apply' kappa a hS]

theorem map_embed_inhomogeneousPathMeasure_const
    (kappa : Kernel A E) [IsMarkovKernel kappa] (a : A) :
    Measure.map (pathMap (fun y : E => (a, y)))
        (inhomogeneousPathMeasure (fun _ : Nat => Kernel.const E (kappa a))
          (kappa a)) =
      inhomogeneousPathMeasure (fun _ : Nat => iidLift kappa)
        ((Kernel.id ×ₖ kappa) a) := by
  apply map_inhomogeneousPathMeasure_pathMap
  · fun_prop
  · ext S hS
    rw [Measure.map_apply (by fun_prop) hS,
      Kernel.id_prod_apply' kappa a hS]
  · exact fun _ e => map_embed_const_eq_iidLift kappa a e

theorem iidRoundsKernel_apply_eq_roundsMeasure
    (kappa : Kernel A E) [IsMarkovKernel kappa] (a : A) :
    iidRoundsKernel kappa a = roundsMeasure (kappa a) := by
  rw [iidRoundsKernel, Kernel.map_apply _
    (measurable_pathMap measurable_snd), iidPairPathKernel_apply]
  have h := congrArg (Measure.map (pathMap Prod.snd))
    (map_embed_inhomogeneousPathMeasure_const kappa a)
  rw [Measure.map_map (measurable_pathMap measurable_snd)
    (measurable_pathMap (by fun_prop))] at h
  have hcomp : pathMap Prod.snd ∘ pathMap (fun y : E => (a, y)) =
      id := by
    funext omega
    ext i
    rfl
  rw [hcomp, Measure.map_id] at h
  rw [← h, inhomogeneousPathMeasure_const_eq_roundsMeasure]

/-- State-indexed stopped rejection: every executed iid round contributes its recorded
cost, including the accepted round. -/
noncomputable def costedRejectionKernel
    (kappa : Kernel A (ENNReal × E)) [IsMarkovKernel kappa]
    (S : Set E) (hS : MeasurableSet S) : Kernel A (ENNReal × E) :=
  Kernel.map (iidRoundsKernel kappa) (stoppedCostedOutput S)

instance (kappa : Kernel A (ENNReal × E)) [IsMarkovKernel kappa]
    (S : Set E) (hS : MeasurableSet S) :
    IsMarkovKernel (costedRejectionKernel kappa S hS) := by
  unfold costedRejectionKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_stoppedCostedOutput hS)

/-- The only remaining generic identification: the trajectory kernel above is the usual
`infinitePi` iid law at each frozen input.  Once established, all existing stopped-loop
state-law and expectation formulas apply verbatim. -/
def IidRoundsIdentified (kappa : Kernel A E) [IsMarkovKernel kappa] : Prop :=
  ∀ a, iidRoundsKernel kappa a = roundsMeasure (kappa a)

theorem iidRoundsIdentified
    (kappa : Kernel A E) [IsMarkovKernel kappa] :
    IidRoundsIdentified kappa :=
  iidRoundsKernel_apply_eq_roundsMeasure kappa

theorem costedRejectionKernel_apply_eq
    (kappa : Kernel A (ENNReal × E)) [IsMarkovKernel kappa]
    (S : Set E) (hS : MeasurableSet S)
    (hid : IidRoundsIdentified kappa) (a : A) :
    costedRejectionKernel kappa S hS a = costedRejectionLaw (kappa a) S := by
  rw [costedRejectionKernel, Kernel.map_apply _ (measurable_stoppedCostedOutput hS)]
  exact congrArg (Measure.map (stoppedCostedOutput S)) (hid a)

theorem map_snd_costedRejectionKernel
    (kappa : Kernel A (ENNReal × E)) [IsMarkovKernel kappa]
    (S : Set E) (hS : MeasurableSet S)
    (hid : IidRoundsIdentified kappa) (a : A)
    (hpos : 0 < kappa a (liftedAccept S)) :
    Measure.map Prod.snd (costedRejectionKernel kappa S hS a) =
      Arlib.condOn (Measure.map Prod.snd (kappa a)) S := by
  rw [costedRejectionKernel_apply_eq kappa S hS hid a]
  exact map_snd_costedRejectionLaw (kappa a) hS hpos

theorem lintegral_fst_costedRejectionKernel
    (kappa : Kernel A (ENNReal × E)) [IsMarkovKernel kappa]
    (S : Set E) (hS : MeasurableSet S)
    (hid : IidRoundsIdentified kappa) (a : A) :
    ∫⁻ z, z.1 ∂(costedRejectionKernel kappa S hS a) =
      (kappa a (liftedAccept S))⁻¹ * ∫⁻ z, z.1 ∂(kappa a) := by
  rw [costedRejectionKernel_apply_eq kappa S hS hid a]
  exact lintegral_fst_costedRejectionLaw (kappa a) hS

#print axioms iidRoundsKernel_apply_eq_roundsMeasure
#print axioms iidRoundsIdentified
#print axioms costedRejectionKernel_apply_eq
#print axioms map_snd_costedRejectionKernel
#print axioms lintegral_fst_costedRejectionKernel

end Ttc.StatewiseCostedRejectionKernel

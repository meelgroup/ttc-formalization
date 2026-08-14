/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.RawGaussianSequentialQueryCost
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Infinite raw Gaussian paths and stopped membership-query cost

The raw state remembers the actual proposal point queried in every round.  This file runs
those states on an infinite Ionescu--Tulcea path, maps the path to the existing marked
proper-proposal chain, and stops at its first proper mark.  The query count is an `ENNReal`
tail sum, so a nonterminating path honestly has infinite cost rather than being represented by
a finite list.
-/

namespace Ttc.RawGaussianStoppedQueryCost

open MeasureTheory ProbabilityTheory Metric Set Function
open Arlib Arlib.MarkovChains
open Ttc.MembershipQuery Ttc.RawGaussianMembership Ttc.RawGaussianQueryCost
open scoped ENNReal Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-! ## A generic path-lumping lemma -/

section PathLumping

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

def mapPath (f : S → T) (omega : Nat → S) : Nat → T := fun i => f (omega i)

theorem measurable_mapPath {f : S → T} (hf : Measurable f) :
    Measurable (mapPath f) :=
  measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)

def mapHistory (f : S → T) (b : Nat)
    (h : (_i : ↥(Finset.Iic b)) → S) : (_i : ↥(Finset.Iic b)) → T :=
  fun i => f (h i)

theorem measurable_mapHistory {f : S → T} (hf : Measurable f) (b : Nat) :
    Measurable (mapHistory f b) :=
  measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)

/-- Mapping both coordinates of a Markov `compProd` may also map the first coordinate,
provided the mapped second-coordinate kernel factors through that first-coordinate map. -/
theorem map_compProd_prodMap
    {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    {mu : Measure A} [IsFiniteMeasure mu]
    {kappa : Kernel A B} [IsMarkovKernel kappa]
    {eta : Kernel C D} [IsMarkovKernel eta]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (hlump : ∀ x, (kappa x).map g = eta (f x)) :
    (mu.compProd kappa).map (Prod.map f g) = (mu.map f).compProd eta := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply (hf.prodMap hg) (hA.prod hB)]
  have hpre : Prod.map f g ⁻¹' (A ×ˢ B) = (f ⁻¹' A) ×ˢ (g ⁻¹' B) := by
    ext p
    simp
  rw [hpre, Measure.compProd_apply_prod (hA.preimage hf) (hB.preimage hg),
    Measure.compProd_apply_prod hA hB,
    setLIntegral_map hA (eta.measurable_coe hB) hf]
  apply setLIntegral_congr_fun (hA.preimage hf)
  intro x hx
  have happ := congrArg (fun m : Measure D => m B) (hlump x)
  rw [Measure.map_apply hg hB] at happ
  exact happ

/-- Splitting a history through time `b+1` into its prefix and final state. -/
noncomputable def splitHistoryEquiv (b : Nat) :
    (((_i : ↥(Finset.Iic (b + 1))) → T) ≃ᵐ
      (((_i : ↥(Finset.Iic b)) → T) × T)) :=
  (MeasurableEquiv.IicProdIoc (X := fun _ : Nat => T) b.le_succ).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.piSingleton (X := fun _ : Nat => T) b).symm)

theorem splitHistoryEquiv_apply (b : Nat)
    (h : (_i : ↥(Finset.Iic (b + 1))) → T) :
    splitHistoryEquiv (T := T) b h =
      (fun i : ↥(Finset.Iic b) => h ⟨i.1,
          Finset.mem_Iic.2 ((Finset.mem_Iic.1 i.2).trans b.le_succ)⟩,
        h ⟨b + 1, Finset.mem_Iic.2 le_rfl⟩) := by
  rfl

/-- A history through time zero is measurably equivalent to its only state. -/
noncomputable def zeroHistoryEquiv :
    (((_i : ↥(Finset.Iic 0)) → T) ≃ᵐ T) where
  toFun h := h ⟨0, Finset.mem_Iic.2 le_rfl⟩
  invFun x := fun _ => x
  left_inv h := by
    funext i
    have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.1 i.2)
    rw [show i = ⟨0, Finset.mem_Iic.2 le_rfl⟩ by
      exact Subtype.ext hi]
  right_inv _ := rfl
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_id

/-- A one-step measurable lumping relation lifts to the entire infinite Markov path. -/
theorem map_pathMeasure_of_lumping
    (P : Kernel S S) [IsMarkovKernel P]
    (Q : Kernel T T) [IsMarkovKernel Q]
    (mu : Measure S) [IsProbabilityMeasure mu]
    {f : S → T} (hf : Measurable f)
    (hlump : ∀ x, (P x).map f = Q (f x)) :
    (pathMeasure P mu).map (mapPath f) = pathMeasure Q (mu.map f) := by
  let nuS : Measure (Nat → S) := pathMeasure P mu
  let nuT : Measure (Nat → T) := pathMeasure Q (mu.map f)
  have hmuT : IsProbabilityMeasure (mu.map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  letI := hmuT
  have hfin : ∀ b : Nat,
      (nuS.map (mapPath f)).map (Preorder.frestrictLe b) =
        nuT.map (Preorder.frestrictLe b) := by
    intro b
    induction b with
    | zero =>
        rw [Measure.map_map (Preorder.measurable_frestrictLe 0)
          (measurable_mapPath hf)]
        apply (MeasurableEquiv.map_measurableEquiv_injective
          (zeroHistoryEquiv (T := T)))
        rw [Measure.map_map (zeroHistoryEquiv (T := T)).measurable
            ((Preorder.measurable_frestrictLe 0).comp (measurable_mapPath hf)),
          Measure.map_map (zeroHistoryEquiv (T := T)).measurable
            (Preorder.measurable_frestrictLe 0)]
        change nuS.map (fun omega => f (omega 0)) = nuT.map (fun omega => omega 0)
        rw [show (fun omega : Nat → S => f (omega 0)) =
            f ∘ (fun omega : Nat → S => omega 0) from rfl,
          ← Measure.map_map hf (measurable_pi_apply 0),
          show nuS = pathMeasure P mu by rfl,
          show nuT = pathMeasure Q (mu.map f) by rfl,
          map_eval_pathMeasure_zero, map_eval_pathMeasure_zero]
    | succ b ih =>
        have hraw :=
          Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
            (X := fun _ : Nat => S) (μ₀ := mu) (κ := chainKernel P) (a := b)
        have htarget :=
          Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
            (X := fun _ : Nat => T) (μ₀ := mu.map f) (κ := chainKernel Q) (a := b)
        have hstep : ∀ h : ((_i : ↥(Finset.Iic b)) → S),
            ((chainKernel P b) h).map f =
              (chainKernel Q b) (mapHistory f b h) := by
          intro h
          change (P (h ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map f =
            Q (f (h ⟨b, Finset.mem_Iic.2 le_rfl⟩))
          exact hlump _
        have hjoint :
            (nuS.map (mapPath f)).map
                (fun omega => (Preorder.frestrictLe b omega, omega (b + 1))) =
              nuT.map (fun omega => (Preorder.frestrictLe b omega, omega (b + 1))) := by
          calc
            (nuS.map (mapPath f)).map
                (fun omega => (Preorder.frestrictLe b omega, omega (b + 1)))
                = (nuS.map (fun omega =>
                    (Preorder.frestrictLe b omega, omega (b + 1)))).map
                      (Prod.map (mapHistory f b) f) := by
                    rw [Measure.map_map (by fun_prop) (measurable_mapPath hf),
                      Measure.map_map ((measurable_mapHistory hf b).prodMap hf) (by fun_prop)]
                    rfl
            _ = ((nuS.map (Preorder.frestrictLe b)).compProd (chainKernel P b)).map
                    (Prod.map (mapHistory f b) f) := by
                    simpa only [nuS, pathMeasure] using
                      congrArg (Measure.map (Prod.map (mapHistory f b) f)) hraw.symm
            _ = ((nuS.map (Preorder.frestrictLe b)).map (mapHistory f b)).compProd
                  (chainKernel Q b) :=
                map_compProd_prodMap (measurable_mapHistory hf b) hf hstep
            _ = (nuT.map (Preorder.frestrictLe b)).compProd (chainKernel Q b) := by
                have ih' : (nuS.map (Preorder.frestrictLe b)).map (mapHistory f b) =
                    nuT.map (Preorder.frestrictLe b) := by
                  calc
                    (nuS.map (Preorder.frestrictLe b)).map (mapHistory f b) =
                        nuS.map (mapHistory f b ∘ Preorder.frestrictLe b) := by
                          rw [Measure.map_map (measurable_mapHistory hf b)
                            (Preorder.measurable_frestrictLe b)]
                    _ = nuS.map (Preorder.frestrictLe b ∘ mapPath f) := by rfl
                    _ = (nuS.map (mapPath f)).map (Preorder.frestrictLe b) := by
                          rw [Measure.map_map (Preorder.measurable_frestrictLe b)
                            (measurable_mapPath hf)]
                    _ = nuT.map (Preorder.frestrictLe b) := ih
                rw [ih']
            _ = nuT.map (fun omega =>
                  (Preorder.frestrictLe b omega, omega (b + 1))) := by
                exact htarget
        apply (MeasurableEquiv.map_measurableEquiv_injective
          (splitHistoryEquiv (T := T) b))
        rw [Measure.map_map (splitHistoryEquiv (T := T) b).measurable
            (Preorder.measurable_frestrictLe (b + 1)),
          Measure.map_map (splitHistoryEquiv (T := T) b).measurable
            (Preorder.measurable_frestrictLe (b + 1))]
        have hsplit : (splitHistoryEquiv (T := T) b) ∘
              Preorder.frestrictLe (b + 1) =
            fun omega : Nat → T =>
              (Preorder.frestrictLe b omega, omega (b + 1)) := by
          funext omega
          ext i <;> rfl
        rw [hsplit]
        exact hjoint
  let fam : (I : Finset Nat) → Measure ((i : I) → T) :=
    fun I => nuT.map (fun omega => I.restrict omega)
  have hproj0 : IsProjectiveMeasureFamily
      (fun I => nuT.map (fun omega => I.restrict omega)) :=
    isProjectiveMeasureFamily_map_restrict
      (P := nuT) (X := fun i omega => omega i)
      (fun i => (measurable_pi_apply i).aemeasurable)
  have hproj : @IsProjectiveMeasureFamily Nat (fun _ : Nat => T) _ fam := by
    simpa only [fam] using hproj0
  have ht : @IsProjectiveLimit Nat (fun _ : Nat => T) _ nuT fam :=
    by
      intro I
      rfl
  have hs : @IsProjectiveLimit Nat (fun _ : Nat => T) _
      (nuS.map (mapPath f)) fam := by
    intro I
    let b := I.sup id
    have hIb : I ⊆ Finset.Iic b := by
      intro i hi
      rw [Finset.mem_Iic]
      exact Finset.le_sup (f := id) hi
    have hrestrict : (fun omega : Nat → T => I.restrict omega) =
        Finset.restrict₂ hIb ∘ Preorder.frestrictLe b := by
      funext omega
      rfl
    have hrestrictMap : I.restrict ∘ mapPath f =
        Finset.restrict₂ hIb ∘ Preorder.frestrictLe b ∘ mapPath f := by
      rw [← Function.comp_assoc, ← hrestrict]
    change Measure.map I.restrict (Measure.map (mapPath f) nuS) =
      nuT.map (fun omega => I.restrict omega)
    rw [Measure.map_map (Finset.measurable_restrict I) (measurable_mapPath hf),
      hrestrictMap,
      ← Measure.map_map (Finset.measurable_restrict₂ hIb)
        ((Preorder.measurable_frestrictLe b).comp (measurable_mapPath hf)),
      ← Measure.map_map (Preorder.measurable_frestrictLe b) (measurable_mapPath hf),
      hfin b]
    rw [hrestrict, Measure.map_map (Finset.measurable_restrict₂ hIb)
      (Preorder.measurable_frestrictLe b)]
  exact hs.unique ht

end PathLumping

/-! ## Raw Gaussian infinite trajectory -/

/-- Time-zero raw record.  It has the required marked output `(false,x)` and makes no
proposal; query costs count transitions `1,2,...`, not this deterministic seed. -/
def rawInitial (x : State n) : RawRound n := (x, false, false, x)

@[simp] theorem rawRoundOutput_rawInitial (x : State n) :
    rawRoundOutput (rawInitial x) = (false, x) := rfl

theorem measurable_rawInitial : Measurable (rawInitial (n := n)) := by
  exact measurable_id.prodMk
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- The raw-round chain consults only the previous round's marked output state. -/
noncomputable def rawGaussianLift
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Kernel (RawRound n) (RawRound n) :=
  Kernel.comap
    (rawRoundKernel (MembershipOracle.ofMeasurableSet K hK) delta s hdelta)
    (fun r => (rawRoundOutput r).2)
    (measurable_snd.comp measurable_rawRoundOutput)

instance {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) : IsMarkovKernel (rawGaussianLift hK delta s hdelta) := by
  unfold rawGaussianLift
  infer_instance

/-- One raw transition lumps exactly to the repository's marked proper-proposal transition. -/
theorem map_rawGaussianLift_output
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (r : RawRound n) :
    (rawGaussianLift hK delta s hdelta r).map rawRoundOutput =
      properProposalGaussianLift K hK delta s (rawRoundOutput r) := by
  rw [rawGaussianLift, Kernel.comap_apply,
    map_rawRoundKernel_output hK delta s hdelta]
  rfl

/-- Kernel from a starting point to the whole raw trajectory, retaining every queried
proposal point forever. -/
noncomputable def rawTrajectoryKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Kernel (State n) (Nat → RawRound n) :=
  Kernel.comap
    (Kernel.traj (X := fun _ : Nat => RawRound n)
      (chainKernel (rawGaussianLift hK delta s hdelta)) 0)
    (fun x (_ : ↥(Finset.Iic 0)) => rawInitial x)
    (measurable_pi_lambda _ fun _ => measurable_rawInitial)

instance {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) : IsMarkovKernel (rawTrajectoryKernel hK delta s hdelta) := by
  unfold rawTrajectoryKernel
  infer_instance

theorem rawTrajectoryKernel_apply
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    rawTrajectoryKernel hK delta s hdelta x =
      pathMeasure (rawGaussianLift hK delta s hdelta) (Measure.dirac (rawInitial x)) := by
  letI : MeasurableSingletonClass
      ((_i : ↥(Finset.Iic 0)) → RawRound n) := ⟨fun z => by
    have heq : ({z} : Set ((_i : ↥(Finset.Iic 0)) → RawRound n)) =
        Set.univ.pi (fun i => {z i}) := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_const]
      exact ⟨fun h i => congrFun h i, fun h => funext h⟩
    rw [heq]
    exact MeasurableSet.pi Set.countable_univ fun i _ => measurableSet_singleton (z i)⟩
  rw [rawTrajectoryKernel, Kernel.comap_apply, pathMeasure,
    Kernel.trajMeasure, Measure.map_dirac]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  congr 2

/-- The entire raw path, not just each fixed marginal, maps to the existing marked chain. -/
theorem map_rawTrajectoryKernel_outputPath
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    (rawTrajectoryKernel hK delta s hdelta x).map
        (mapPath rawRoundOutput) =
      properProposalTrajectoryKernel K hK delta s x := by
  rw [rawTrajectoryKernel_apply, properProposalTrajectoryKernel_apply]
  calc
    (pathMeasure (rawGaussianLift hK delta s hdelta) (Measure.dirac (rawInitial x))).map
        (mapPath rawRoundOutput) =
      pathMeasure (properProposalGaussianLift K hK delta s)
        ((Measure.dirac (rawInitial x)).map rawRoundOutput) :=
      map_pathMeasure_of_lumping _ _ _ measurable_rawRoundOutput
        (map_rawGaussianLift_output hK delta s hdelta)
    _ = pathMeasure (properProposalGaussianLift K hK delta s)
        (Measure.dirac (false, x)) := by rw [Measure.map_dirac]; rfl

/-! ## Explicit extended query trace and stopped kernel -/

/-- Infinite-prefix membership-query count.  Each still-needed transition contributes the
cost of its retained proposal query; nontermination yields `∞`. -/
noncomputable def rawPathMembershipQueryCost
    {K : Set (State n)} (oracle : MembershipOracle K)
    (p : State n × (Nat → RawRound n)) : ENNReal :=
  markedPathMembershipQueryCost oracle (rawProposalPoint p.2)
    (p.1, mapPath rawRoundOutput p.2)

theorem rawPathMembershipQueryCost_eq_waitCost
    {K : Set (State n)} (oracle : MembershipOracle K)
    (p : State n × (Nat → RawRound n)) :
    rawPathMembershipQueryCost oracle p =
      properProposalWaitCost (p.1, mapPath rawRoundOutput p.2) :=
  markedPathMembershipQueryCost_eq_waitCost oracle (rawProposalPoint p.2)
    (p.1, mapPath rawRoundOutput p.2)

theorem measurable_rawPathMembershipQueryCost
    {K : Set (State n)} (oracle : MembershipOracle K) :
    Measurable (rawPathMembershipQueryCost oracle) := by
  have hpair : Measurable (fun p : State n × (Nat → RawRound n) =>
      (p.1, mapPath rawRoundOutput p.2)) :=
    measurable_fst.prodMk ((measurable_mapPath measurable_rawRoundOutput).comp measurable_snd)
  have heq : rawPathMembershipQueryCost oracle = fun p =>
      properProposalWaitCost (p.1, mapPath rawRoundOutput p.2) := by
    funext p
    exact rawPathMembershipQueryCost_eq_waitCost oracle p
  rw [heq]
  exact measurable_properProposalWaitCost.comp hpair

/-- Attach the start to the retained raw path. -/
noncomputable def rawStartedTrajectoryKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Kernel (State n) (State n × (Nat → RawRound n)) :=
  Kernel.compProd Kernel.id
    (Kernel.prodMkLeft (State n) (rawTrajectoryKernel hK delta s hdelta))

instance {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) : IsMarkovKernel (rawStartedTrajectoryKernel hK delta s hdelta) := by
  unfold rawStartedTrajectoryKernel
  infer_instance

theorem rawStartedTrajectoryKernel_apply
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    rawStartedTrajectoryKernel hK delta s hdelta x =
      (rawTrajectoryKernel hK delta s hdelta x).map (fun omega => (x, omega)) := by
  ext A hA
  rw [rawStartedTrajectoryKernel, Kernel.compProd_apply hA,
    Kernel.id_apply, lintegral_dirac']
  · rw [Kernel.prodMkLeft_apply, Measure.map_apply (by fun_prop) hA]
  · exact Kernel.measurable_kernel_prodMk_left' hA x

/-- One stopped raw experiment, returning the extended membership count and selected state. -/
noncomputable def rawProperProposalCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Kernel (State n) (ENNReal × State n) :=
  Kernel.map (rawStartedTrajectoryKernel hK delta s hdelta)
    (fun p => (rawPathMembershipQueryCost (MembershipOracle.ofMeasurableSet K hK) p,
      firstProperMarkedState (mapPath rawRoundOutput p.2)))

instance {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) : IsMarkovKernel (rawProperProposalCostedKernel hK delta s hdelta) := by
  unfold rawProperProposalCostedKernel
  exact Kernel.IsMarkovKernel.map _
    ((measurable_rawPathMembershipQueryCost _).prodMk
      (measurable_firstProperMarkedState.comp
        ((measurable_mapPath measurable_rawRoundOutput).comp measurable_snd)))

/-- At a non-stuck point the stopped raw output is exactly the speedy transition. -/
theorem map_snd_rawProperProposalCostedKernel_eq_speedy
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) (hell : ell K delta x ≠ 0) :
    (rawProperProposalCostedKernel hK delta s hdelta x).map Prod.snd =
      speedyMetropolisGaussian K delta s x := by
  have hout : Measurable
      (fun p : State n × (Nat → RawRound n) =>
        (rawPathMembershipQueryCost (MembershipOracle.ofMeasurableSet K hK) p,
          firstProperMarkedState (mapPath rawRoundOutput p.2))) :=
    (measurable_rawPathMembershipQueryCost _).prodMk
      (measurable_firstProperMarkedState.comp
        ((measurable_mapPath measurable_rawRoundOutput).comp measurable_snd))
  have hpairx : Measurable (fun omega : Nat → RawRound n => (x, omega)) :=
    measurable_const.prodMk measurable_id
  rw [rawProperProposalCostedKernel, Kernel.map_apply _ hout,
    Measure.map_map measurable_snd hout, rawStartedTrajectoryKernel_apply,
    Measure.map_map (measurable_snd.comp hout) hpairx]
  have hpath := map_rawTrajectoryKernel_outputPath hK delta s hdelta x
  have hcomp : (Prod.snd ∘ fun p : State n × (Nat → RawRound n) =>
        (rawPathMembershipQueryCost (MembershipOracle.ofMeasurableSet K hK) p,
          firstProperMarkedState (mapPath rawRoundOutput p.2))) ∘
      (fun omega => (x, omega)) =
      (fun omega : Nat → RawRound n =>
        firstProperMarkedState (mapPath rawRoundOutput omega)) := rfl
  rw [hcomp, show (fun omega : Nat → RawRound n =>
      firstProperMarkedState (mapPath rawRoundOutput omega)) =
      firstProperMarkedState ∘ mapPath rawRoundOutput from rfl,
    ← Measure.map_map measurable_firstProperMarkedState
      (measurable_mapPath measurable_rawRoundOutput), hpath]
  rw [← Kernel.map_apply _ measurable_firstProperMarkedState,
    ← properProposalStoppedKernel]
  exact properProposalStoppedKernel_apply_eq_speedy hK delta s x hell

/-- Expected recorded membership queries equal the existing geometric wait cost `ell⁻¹`.
This equality includes the extended-valued infinite-path semantics. -/
theorem lintegral_fst_rawProperProposalCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    ∫⁻ z, z.1 ∂(rawProperProposalCostedKernel hK delta s hdelta x) =
      (ell K delta x)⁻¹ := by
  have hout : Measurable
      (fun p : State n × (Nat → RawRound n) =>
        (rawPathMembershipQueryCost (MembershipOracle.ofMeasurableSet K hK) p,
          firstProperMarkedState (mapPath rawRoundOutput p.2))) :=
    (measurable_rawPathMembershipQueryCost _).prodMk
      (measurable_firstProperMarkedState.comp
        ((measurable_mapPath measurable_rawRoundOutput).comp measurable_snd))
  rw [rawProperProposalCostedKernel, Kernel.map_apply _ hout,
    lintegral_map measurable_fst hout, rawStartedTrajectoryKernel_apply,
    lintegral_map]
  · simp_rw [rawPathMembershipQueryCost_eq_waitCost]
    have hwaitx : Measurable (fun omega : LiftedGaussianPath n =>
        properProposalWaitCost (x, omega)) :=
      measurable_properProposalWaitCost.comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_map hwaitx
      (measurable_mapPath measurable_rawRoundOutput),
      map_rawTrajectoryKernel_outputPath hK delta s hdelta x,
      properProposalTrajectoryKernel_apply]
    have hcost : ∀ omega : LiftedGaussianPath n,
        properProposalWaitCost (x, omega) =
          ∑' k : Nat, {omega' : LiftedGaussianPath n |
            ∀ i ≤ k, omega' i = (false, x)}.indicator
              (1 : LiftedGaussianPath n → ENNReal) omega := by
      intro omega
      unfold properProposalWaitCost
      apply tsum_congr
      intro k
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    rw [lintegral_congr hcost]
    exact lintegral_firstProperTime_pathMeasure_properProposalGaussianLift hK delta s x
  · exact measurable_rawPathMembershipQueryCost _
  · fun_prop

/-! ## Almost-sure termination as an explicit raw-path event -/

def rawEventuallyProper (x : State n) : Set (Nat → RawRound n) :=
  mapPath rawRoundOutput ⁻¹'
    (⋃ j : Nat, firstProperCylinder x Set.univ j)

theorem measurableSet_rawEventuallyProper (x : State n) :
    MeasurableSet (rawEventuallyProper x) := by
  exact (MeasurableSet.iUnion fun j =>
    measurableSet_firstProperCylinder x MeasurableSet.univ j).preimage
      (measurable_mapPath measurable_rawRoundOutput)

theorem rawTrajectoryKernel_eventuallyProper
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) (hell : ell K delta x ≠ 0) :
    rawTrajectoryKernel hK delta s hdelta x (rawEventuallyProper x) = 1 := by
  have hmap := map_rawTrajectoryKernel_outputPath hK delta s hdelta x
  have happ := congrArg
    (fun m : Measure (Nat → Bool × State n) =>
      m (⋃ j : Nat, firstProperCylinder x Set.univ j)) hmap
  rw [Measure.map_apply (measurable_mapPath measurable_rawRoundOutput)
      (MeasurableSet.iUnion fun j =>
        measurableSet_firstProperCylinder x MeasurableSet.univ j)] at happ
  rw [properProposalTrajectoryKernel_apply,
    pathMeasure_iUnion_firstProperCylinder hK delta s x MeasurableSet.univ hell,
    measure_univ] at happ
  simpa only [rawEventuallyProper] using happ

#print axioms map_pathMeasure_of_lumping
#print axioms map_rawTrajectoryKernel_outputPath
#print axioms rawTrajectoryKernel_eventuallyProper
#print axioms map_snd_rawProperProposalCostedKernel_eq_speedy
#print axioms lintegral_fst_rawProperProposalCostedKernel

end Ttc.RawGaussianStoppedQueryCost

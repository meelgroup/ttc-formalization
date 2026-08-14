import Arlib.Probability.TVKernelHeterogeneous
import Ttc.Exec.CVHeterogeneousHistoryReference
import Ttc.Exec.CVGaussianWarmFallbackCappedOperational
import Ttc.Volume.CVSequentialPhaseSampler

/-!
# Score-preserving independent seed reset

After a phase has produced its score, replace only the seed carried to the next phase by
an independent draw.  This leaves the score and recorded query count unchanged, while
making the actual next-seed law exact.  It therefore removes any need to infer next-phase
warmth from a total-variation estimate.
-/

set_option autoImplicit false

namespace Ttc.CVScorePreservingSeedReset

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVSeedProjectedDependence
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVCorrected
open scoped ENNReal

variable {Seed Score : Type*} [MeasurableSpace Seed] [MeasurableSpace Score]

def scoreSeedResetOutput (z : (Score × Seed) × Seed) : Score × Seed :=
  (z.1.1, z.2)

theorem measurable_scoreSeedResetOutput :
    Measurable (scoreSeedResetOutput : (Score × Seed) × Seed → Score × Seed) :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

def costedScoreSeedResetOutput
    (z : (ENNReal × (Score × Seed)) × Seed) : ENNReal × (Score × Seed) :=
  (z.1.1, (z.1.2.1, z.2))

theorem measurable_costedScoreSeedResetOutput :
    Measurable (costedScoreSeedResetOutput :
      (ENNReal × (Score × Seed)) × Seed → ENNReal × (Score × Seed)) :=
  (measurable_fst.comp measurable_fst).prodMk
    (((measurable_fst.comp measurable_snd).comp measurable_fst).prodMk measurable_snd)

/-- Independently replace the seed while retaining the score. -/
noncomputable def scoreSeedResetPostKernel
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    Kernel (Score × Seed) (Score × Seed) :=
  Kernel.map
    (Kernel.prod Kernel.id (Kernel.const (Score × Seed) nu))
    scoreSeedResetOutput

instance scoreSeedResetPostKernel.isMarkovKernel
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    IsMarkovKernel (scoreSeedResetPostKernel (Score := Score) nu) := by
  unfold scoreSeedResetPostKernel
  exact Kernel.IsMarkovKernel.map _ measurable_scoreSeedResetOutput

/-- Postcompose an uncosted phase with the independent seed reset. -/
noncomputable def scoreSeedResetKernel
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    Kernel Seed (Score × Seed) :=
  Kernel.map (Kernel.prod P (Kernel.const Seed nu)) scoreSeedResetOutput

instance scoreSeedResetKernel.isMarkovKernel
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    IsMarkovKernel (scoreSeedResetKernel P nu) := by
  unfold scoreSeedResetKernel
  exact Kernel.IsMarkovKernel.map _ measurable_scoreSeedResetOutput

/-- The reset kernel is literally the product of the old score marginal and the fresh
seed law. -/
theorem scoreSeedResetKernel_eq_prod
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    scoreSeedResetKernel P nu =
      Kernel.prod (Kernel.map P Prod.fst) (Kernel.const Seed nu) := by
  unfold scoreSeedResetKernel
  change Kernel.map (Kernel.prod P (Kernel.const Seed nu))
      (Prod.map Prod.fst id) = _
  exact (Kernel.map_prod_eq P (Kernel.const Seed nu) measurable_fst).symm

/-- Costed postprocessing that retains both accumulated cost and score. -/
noncomputable def costedScoreSeedResetPostKernel
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    Kernel (ENNReal × (Score × Seed)) (ENNReal × (Score × Seed)) :=
  Kernel.map
    (Kernel.prod Kernel.id
      (Kernel.const (ENNReal × (Score × Seed)) nu))
    costedScoreSeedResetOutput

instance costedScoreSeedResetPostKernel.isMarkovKernel
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    IsMarkovKernel (costedScoreSeedResetPostKernel (Score := Score) nu) := by
  unfold costedScoreSeedResetPostKernel
  exact Kernel.IsMarkovKernel.map _ measurable_costedScoreSeedResetOutput

/-- Postcompose a costed phase with the independent seed reset. -/
noncomputable def costedScoreSeedResetKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    Kernel Seed (ENNReal × (Score × Seed)) :=
  Kernel.map (Kernel.prod Q (Kernel.const Seed nu)) costedScoreSeedResetOutput

instance costedScoreSeedResetKernel.isMarkovKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    IsMarkovKernel (costedScoreSeedResetKernel Q nu) := by
  unfold costedScoreSeedResetKernel
  exact Kernel.IsMarkovKernel.map _ measurable_costedScoreSeedResetOutput

theorem map_snd_scoreSeedResetPostKernel
    (nu : Measure Seed) [IsProbabilityMeasure nu] (z : Score × Seed) :
    Measure.map Prod.snd (scoreSeedResetPostKernel (Score := Score) nu z) = nu := by
  unfold scoreSeedResetPostKernel
  rw [Kernel.map_apply
    (Kernel.prod Kernel.id (Kernel.const (Score × Seed) nu))
    measurable_scoreSeedResetOutput z]
  rw [Measure.map_map measurable_snd
      measurable_scoreSeedResetOutput,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
  change Measure.map Prod.snd ((Measure.dirac z).prod nu) = nu
  rw [Measure.map_snd_prod, measure_univ, one_smul]

theorem map_fst_scoreSeedResetPostKernel
    (nu : Measure Seed) [IsProbabilityMeasure nu] (z : Score × Seed) :
    Measure.map Prod.fst (scoreSeedResetPostKernel (Score := Score) nu z) =
      Measure.dirac z.1 := by
  unfold scoreSeedResetPostKernel
  rw [Kernel.map_apply
    (Kernel.prod Kernel.id (Kernel.const (Score × Seed) nu))
    measurable_scoreSeedResetOutput z]
  rw [Measure.map_map measurable_fst
      measurable_scoreSeedResetOutput,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
  change Measure.map (Prod.fst ∘ Prod.fst) ((Measure.dirac z).prod nu) = _
  rw [← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul, Measure.map_dirac' measurable_fst]

/-- The reset makes the next seed exactly `nu`, for every incoming probability law. -/
theorem map_snd_bind_scoreSeedResetPostKernel
    (rho : Measure (Score × Seed)) [IsProbabilityMeasure rho]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    Measure.map Prod.snd
      (rho.bind (scoreSeedResetPostKernel (Score := Score) nu)) = nu := by
  rw [Measure.map_comp rho (scoreSeedResetPostKernel (Score := Score) nu)
    measurable_snd]
  change rho.bind
    (Kernel.map (scoreSeedResetPostKernel (Score := Score) nu) Prod.snd) = nu
  have hkernel : Kernel.map (scoreSeedResetPostKernel (Score := Score) nu) Prod.snd =
      Kernel.const (Score × Seed) nu := by
    apply Kernel.ext
    intro z
    rw [Kernel.map_apply _ measurable_snd z]
    exact map_snd_scoreSeedResetPostKernel (Score := Score) nu z
  rw [hkernel]
  change (fun _ : Score × Seed => nu) ∘ₘ rho = nu
  rw [Measure.bind_const, measure_univ, one_smul]

/-- Resetting does not alter the score marginal. -/
theorem map_fst_bind_scoreSeedResetPostKernel
    (rho : Measure (Score × Seed)) [IsProbabilityMeasure rho]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    Measure.map Prod.fst
      (rho.bind (scoreSeedResetPostKernel (Score := Score) nu)) =
      Measure.map Prod.fst rho := by
  rw [Measure.map_comp rho (scoreSeedResetPostKernel (Score := Score) nu)
    measurable_fst]
  change rho.bind
    (Kernel.map (scoreSeedResetPostKernel (Score := Score) nu) Prod.fst) = _
  have hkernel : Kernel.map (scoreSeedResetPostKernel (Score := Score) nu) Prod.fst =
      Kernel.deterministic Prod.fst measurable_fst := by
    apply Kernel.ext
    intro z
    rw [Kernel.map_apply _ measurable_fst z, Kernel.deterministic_apply]
    exact map_fst_scoreSeedResetPostKernel (Score := Score) nu z
  rw [hkernel]
  exact Measure.bind_dirac_eq_map rho measurable_fst

theorem map_snd_sampleFrom_scoreSeedResetKernel
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (rho : Measure Seed) [IsProbabilityMeasure rho]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    Measure.map Prod.snd (sampleFromKernel (scoreSeedResetKernel P nu) rho) = nu := by
  unfold sampleFromKernel
  rw [Measure.map_comp rho (scoreSeedResetKernel P nu) measurable_snd]
  have hkernel : Kernel.map (scoreSeedResetKernel P nu) Prod.snd =
      Kernel.const Seed nu := by
    apply Kernel.ext
    intro x
    unfold scoreSeedResetKernel
    rw [Kernel.map_apply _ measurable_snd x,
      Kernel.map_apply _ measurable_scoreSeedResetOutput x,
      Measure.map_map measurable_snd measurable_scoreSeedResetOutput,
      Kernel.prod_apply, Kernel.const_apply]
    change Measure.map Prod.snd ((P x).prod nu) = nu
    rw [Measure.map_snd_prod,
      measure_univ, one_smul]
  rw [hkernel]
  change (fun _ : Seed => nu) ∘ₘ rho = nu
  rw [Measure.bind_const, measure_univ, one_smul]

theorem map_fst_sampleFrom_scoreSeedResetKernel
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (rho : Measure Seed) [IsProbabilityMeasure rho]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    Measure.map Prod.fst (sampleFromKernel (scoreSeedResetKernel P nu) rho) =
      Measure.map Prod.fst (sampleFromKernel P rho) := by
  unfold sampleFromKernel
  rw [Measure.map_comp rho (scoreSeedResetKernel P nu) measurable_fst,
    Measure.map_comp rho P measurable_fst]
  have hkernel : Kernel.map (scoreSeedResetKernel P nu) Prod.fst =
      Kernel.map P Prod.fst := by
    apply Kernel.ext
    intro x
    unfold scoreSeedResetKernel
    rw [Kernel.map_apply _ measurable_fst x,
      Kernel.map_apply _ measurable_scoreSeedResetOutput x,
      Measure.map_map measurable_fst measurable_scoreSeedResetOutput,
      Kernel.map_apply _ measurable_fst x,
      Kernel.prod_apply, Kernel.const_apply]
    change Measure.map (Prod.fst ∘ Prod.fst) ((P x).prod nu) =
      Measure.map Prod.fst (P x)
    rw [← Measure.map_map measurable_fst measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul]
  rw [hkernel]

/-- Complete outgoing state law: the operational score marginal is independent of the
fresh next seed. -/
theorem sampleFrom_scoreSeedResetKernel_eq_prod
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (rho : Measure Seed) [IsProbabilityMeasure rho]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    sampleFromKernel (scoreSeedResetKernel P nu) rho =
      (Measure.map Prod.fst (sampleFromKernel P rho)).prod nu := by
  rw [scoreSeedResetKernel_eq_prod]
  have h := congrArg (fun K : Kernel Unit (Score × Seed) => K ())
    (Kernel.prod_const_comp (Kernel.const Unit rho) (Kernel.map P Prod.fst) nu)
  unfold sampleFromKernel
  rw [Measure.map_comp rho P measurable_fst]
  simpa [Kernel.comp_apply, Kernel.const_apply, Kernel.prod_apply] using h

/-- A score-marginal TV estimate tensorizes through the operational refresh without any
additional loss. -/
theorem tvLe_sampleFrom_scoreSeedResetKernel_prod
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (rho : Measure Seed) [IsProbabilityMeasure rho]
    (nu : Measure Seed) [IsProbabilityMeasure nu]
    (scoreTarget : Measure Score) [IsProbabilityMeasure scoreTarget]
    {e : ENNReal}
    (hscore : TVLe (Measure.map Prod.fst (sampleFromKernel P rho)) scoreTarget e) :
    TVLe (sampleFromKernel (scoreSeedResetKernel P nu) rho)
      (scoreTarget.prod nu) e := by
  letI : IsProbabilityMeasure
      (Measure.map Prod.fst (sampleFromKernel P rho)) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  rw [sampleFrom_scoreSeedResetKernel_eq_prod]
  simpa only [add_zero] using hscore.prod (TVLe.refl nu)

/-- Erasing cost from the reset refinement gives the reset of the erased phase. -/
theorem map_snd_costedScoreSeedResetKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (P : Kernel Seed (Score × Seed)) [IsMarkovKernel P]
    (nu : Measure Seed) [IsProbabilityMeasure nu]
    (hforget : ∀ x, Measure.map Prod.snd (Q x) = P x) (x : Seed) :
    Measure.map Prod.snd (costedScoreSeedResetKernel Q nu x) =
      scoreSeedResetKernel P nu x := by
  unfold costedScoreSeedResetKernel scoreSeedResetKernel
  rw [Kernel.map_apply _ measurable_costedScoreSeedResetOutput x,
    Measure.map_map measurable_snd measurable_costedScoreSeedResetOutput,
    Kernel.map_apply _ measurable_scoreSeedResetOutput x]
  rw [Kernel.prod_apply Q (Kernel.const Seed nu) x,
    Kernel.prod_apply P (Kernel.const Seed nu) x, Kernel.const_apply]
  change Measure.map (Prod.map (fun y : ENNReal × (Score × Seed) => y.2.1) id)
      ((Q x).prod nu) =
    Measure.map (Prod.map (fun y : Score × Seed => y.1) id) ((P x).prod nu)
  change Measure.map (Prod.map (Prod.fst ∘ Prod.snd) id) ((Q x).prod nu) =
    Measure.map (Prod.map Prod.fst id) ((P x).prod nu)
  rw [← Measure.map_prod_map (Q x) nu
      (measurable_fst.comp measurable_snd) measurable_id,
    ← Measure.map_prod_map (P x) nu measurable_fst measurable_id]
  congr 1
  rw [← hforget x, Measure.map_map measurable_fst measurable_snd]

/-- Full state marginal of a costed refreshed execution: the old operational score
marginal tensored with the independent fresh seed. -/
theorem map_snd_sampleFrom_costedScoreSeedResetKernel_eq_prod
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (rho : Measure Seed) [IsProbabilityMeasure rho]
    (nu : Measure Seed) [IsProbabilityMeasure nu] :
    Measure.map Prod.snd
        (sampleFromKernel (costedScoreSeedResetKernel Q nu) rho) =
      (Measure.map (fun y : ENNReal × (Score × Seed) => y.2.1)
        (sampleFromKernel Q rho)).prod nu := by
  let P : Kernel Seed (Score × Seed) := Kernel.map Q Prod.snd
  haveI : IsMarkovKernel P := by
    dsimp only [P]
    exact Kernel.IsMarkovKernel.map Q measurable_snd
  have hforget : ∀ x, Measure.map Prod.snd (Q x) = P x := by
    intro x
    dsimp only [P]
    rw [Kernel.map_apply _ measurable_snd x]
  unfold sampleFromKernel
  rw [Measure.map_comp rho (costedScoreSeedResetKernel Q nu) measurable_snd]
  have hkernel : Kernel.map (costedScoreSeedResetKernel Q nu) Prod.snd =
      scoreSeedResetKernel P nu := by
    apply Kernel.ext
    intro x
    rw [Kernel.map_apply _ measurable_snd x]
    exact map_snd_costedScoreSeedResetKernel Q P nu hforget x
  rw [hkernel]
  have hprod := sampleFrom_scoreSeedResetKernel_eq_prod P rho nu
  unfold sampleFromKernel at hprod
  rw [hprod]
  congr 1
  rw [Measure.map_comp rho P measurable_fst]
  change (Kernel.map P Prod.fst) ∘ₘ rho = _
  have hscoreKernel : Kernel.map P Prod.fst =
      Kernel.map Q (Prod.fst ∘ Prod.snd) := by
    apply Kernel.ext
    intro x
    dsimp only [P]
    rw [Kernel.map_apply _ measurable_fst x,
      Kernel.map_apply _ measurable_snd x,
      Measure.map_map measurable_fst measurable_snd,
      Kernel.map_apply _ (measurable_fst.comp measurable_snd) x]
  rw [hscoreKernel]
  change (Kernel.map Q (Prod.fst ∘ Prod.snd)) ∘ₘ rho =
    Measure.map (Prod.fst ∘ Prod.snd) (Q ∘ₘ rho)
  rw [← Measure.map_comp rho Q (measurable_fst.comp measurable_snd)]

/-- The independent reset leaves the pointwise expected recorded cost unchanged. -/
theorem heterogeneousStepMean_costedScoreSeedResetKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (nu : Measure Seed) [IsProbabilityMeasure nu] (x : Seed) :
    heterogeneousStepMean (costedScoreSeedResetKernel Q nu) x =
      heterogeneousStepMean Q x := by
  unfold heterogeneousStepMean costedScoreSeedResetKernel
  rw [Kernel.map_apply _ measurable_costedScoreSeedResetOutput x]
  rw [lintegral_map measurable_fst
      measurable_costedScoreSeedResetOutput,
    Kernel.prod_apply, Kernel.const_apply]
  simp only [costedScoreSeedResetOutput]
  rw [MeasureTheory.lintegral_prod (fun z : (ENNReal × (Score × Seed)) × Seed =>
    z.1.1) ((measurable_fst.comp measurable_fst).aemeasurable)]
  simp_rw [lintegral_const]
  simp only [measure_univ, mul_one]

/-! ## Active-tail operational constructor -/

/-- Always-refresh phase family.  Phase `i` carries an independent draw from `nu (i+1)`
as the seed for phase `i+1`. -/
noncomputable def scoreSeedResetSchedule
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)]
    (nu : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (nu i)] :
    Nat → Kernel Seed (Score × Seed) := fun i =>
  scoreSeedResetKernel (P i) (nu (i + 1))

instance scoreSeedResetSchedule.isMarkovKernel
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)]
    (nu : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (nu i)] (i : Nat) :
    IsMarkovKernel (scoreSeedResetSchedule P nu i) := by
  unfold scoreSeedResetSchedule
  infer_instance

noncomputable def costedScoreSeedResetSchedule
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (nu : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (nu i)] :
    Nat → Kernel Seed (ENNReal × (Score × Seed)) := fun i =>
  costedScoreSeedResetKernel (Q i) (nu (i + 1))

instance costedScoreSeedResetSchedule.isMarkovKernel
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (nu : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (nu i)] (i : Nat) :
    IsMarkovKernel (costedScoreSeedResetSchedule Q nu i) := by
  unfold costedScoreSeedResetSchedule
  infer_instance

theorem map_snd_costedScoreSeedResetSchedule
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)]
    (nu : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (nu i)]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x)
    (i : Nat) (x : Seed) :
    Measure.map Prod.snd (costedScoreSeedResetSchedule Q nu i x) =
      scoreSeedResetSchedule P nu i x :=
  map_snd_costedScoreSeedResetKernel (Q i) (P i) (nu (i + 1))
    (hforget i) x

theorem heterogeneousStepMean_costedScoreSeedResetSchedule
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (nu : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (nu i)]
    (i : Nat) (x : Seed) :
    heterogeneousStepMean (costedScoreSeedResetSchedule Q nu i) x =
      heterogeneousStepMean (Q i) x :=
  heterogeneousStepMean_costedScoreSeedResetKernel (Q i) (nu (i + 1)) x

/-- Active-tail operational package for independent refresh.  The actual-path recurrence
is completely discharged by the exact outgoing seed identity; callers only provide the
warmth of the directly sampleable refresh laws. -/
noncomputable def seedProjectedOperational_activeReferenceTail_reset
    (m : Nat)
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)]
    (nu : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (nu i)]
    (tail : Nat → Measure (Score × Seed)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (Score × Seed)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → Score × Seed) → Real) (eta : Real)
    (pi : Nat → Measure Seed) (tau : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tau i)]
    (warmBudget mixError : Nat → ENNReal)
    (hwarmOne : ∀ i, 1 ≤ warmBudget i)
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0) (pi 0))
    (hrefreshWarm : ∀ i, i + 1 < m →
      IsWarm (warmBudget (i + 1)) (nu (i + 1)) (pi (i + 1)))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) = pi i)
    (hactiveMixTop : ∀ i, i + 1 < m → mixError i ≠ ⊤)
    (hactiveMix : ∀ i, i + 1 < m → ∀ (rho : Measure Seed),
      IsWarm (2 * warmBudget i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe (sampleFromKernel (scoreSeedResetSchedule P nu i) rho)
          (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → Score × Seed) → Real)
    (v : Nat → Score → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (activeReferenceTailSchedule m (scoreSeedResetSchedule P nu) tail)) mu0)
          V (correctedAlpha m eta) i =
        fun omega => u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega => v i (omega (i + 1)).1)
    (hbudget : ∀ i, i + 1 < m →
      2 * (mixError i).toReal ≤ correctedNu m eta) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m (scoreSeedResetSchedule P nu) tail))
      (activeReferenceTailSchedule m (scoreSeedResetSchedule P nu) tail)
      Prod.snd Prod.fst mu0 V m eta := by
  apply seedProjectedOperational_activeReferenceTail m
    (scoreSeedResetSchedule P nu) tail mu0 V eta pi tau warmBudget mixError
    hwarmOne hstart
  · intro i hi rho hprob _hwarm
    letI : IsProbabilityMeasure rho := hprob
    rw [scoreSeedResetSchedule,
      map_snd_sampleFrom_scoreSeedResetKernel (P i) rho (nu (i + 1))]
    exact hrefreshWarm i hi
  · exact htailSeed
  · exact hactiveMixTop
  · exact hactiveMix
  · exact hu
  · exact hv
  · exact hU
  · exact hV
  · exact hbudget

#print axioms map_snd_sampleFrom_scoreSeedResetKernel
#print axioms map_fst_sampleFrom_scoreSeedResetKernel
#print axioms map_snd_costedScoreSeedResetKernel
#print axioms heterogeneousStepMean_costedScoreSeedResetKernel
#print axioms sampleFrom_scoreSeedResetKernel_eq_prod
#print axioms tvLe_sampleFrom_scoreSeedResetKernel_prod
#print axioms map_snd_sampleFrom_costedScoreSeedResetKernel_eq_prod
#print axioms seedProjectedOperational_activeReferenceTail_reset

end Ttc.CVScorePreservingSeedReset

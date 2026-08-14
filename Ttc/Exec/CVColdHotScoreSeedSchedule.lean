import Ttc.Exec.CVHeterogeneousHistoryReference

/-!
# Cold-law adapter and heterogeneous cold/hot score-seed schedule

The source fixed block was previously exposed only as a family of complete cost/output
measures.  A constant kernel gives a useful *denotational adapter*: it graph-lifts the
sampled score to the scaled raw seed and can be spliced with an arbitrary hot score-seed
kernel.  It is not by itself a genuine charged execution when producing the supplied
measure requires an uncharged sample.  Operational use therefore additionally requires
a separately costed realization of that measure (or an externally supplied sample).
-/

set_option autoImplicit false

namespace Ttc.CVColdHotScoreSeedSchedule

open MeasureTheory ProbabilityTheory
open Ttc.CVHeterogeneousHistoryReference
open scoped ENNReal Classical

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

def costScoreSeedLift (seedOfScore : Score → Seed)
    (z : ENNReal × Score) : ENNReal × (Score × Seed) :=
  (z.1, (z.2, seedOfScore z.2))

theorem measurable_costScoreSeedLift
    {seedOfScore : Score → Seed} (hseed : Measurable seedOfScore) :
    Measurable (costScoreSeedLift seedOfScore) := by
  unfold costScoreSeedLift
  fun_prop

/-- Turn a complete cold-phase cost/output law into a seed-indexed denotational kernel.
This construction does not assert that sampling `rho` is free. -/
noncomputable def coldLawCostedKernel
    (rho : Measure (ENNReal × Score)) (seedOfScore : Score → Seed)
    (_hseed : Measurable seedOfScore) :
    Kernel Seed (ENNReal × (Score × Seed)) :=
  Kernel.const Seed (Measure.map (costScoreSeedLift seedOfScore) rho)

instance coldLawCostedKernel.isMarkovKernel
    (rho : Measure (ENNReal × Score)) [IsProbabilityMeasure rho]
    (seedOfScore : Score → Seed) (hseed : Measurable seedOfScore) :
    IsMarkovKernel (coldLawCostedKernel rho seedOfScore hseed) := by
  unfold coldLawCostedKernel
  letI : IsProbabilityMeasure (Measure.map (costScoreSeedLift seedOfScore) rho) :=
    Measure.isProbabilityMeasure_map (measurable_costScoreSeedLift hseed).aemeasurable
  infer_instance

noncomputable def coldLawKernel
    (rho : Measure (ENNReal × Score)) (seedOfScore : Score → Seed)
    (hseed : Measurable seedOfScore) :
    Kernel Seed (Score × Seed) :=
  Kernel.map (coldLawCostedKernel rho seedOfScore hseed) Prod.snd

instance coldLawKernel.isMarkovKernel
    (rho : Measure (ENNReal × Score)) [IsProbabilityMeasure rho]
    (seedOfScore : Score → Seed) (hseed : Measurable seedOfScore) :
    IsMarkovKernel (coldLawKernel rho seedOfScore hseed) := by
  unfold coldLawKernel
  letI := coldLawCostedKernel.isMarkovKernel rho seedOfScore hseed
  exact Kernel.IsMarkovKernel.map _ measurable_snd

theorem map_snd_coldLawCostedKernel
    (rho : Measure (ENNReal × Score)) [IsProbabilityMeasure rho]
    (seedOfScore : Score → Seed) (hseed : Measurable seedOfScore) (x : Seed) :
    Measure.map Prod.snd (coldLawCostedKernel rho seedOfScore hseed x) =
      coldLawKernel rho seedOfScore hseed x := by
  letI := coldLawCostedKernel.isMarkovKernel rho seedOfScore hseed
  rw [coldLawKernel, Kernel.map_apply _ measurable_snd]

theorem coldLawCostedKernel_apply
    (rho : Measure (ENNReal × Score)) (seedOfScore : Score → Seed)
    (hseed : Measurable seedOfScore) (x : Seed) :
    coldLawCostedKernel rho seedOfScore hseed x =
      Measure.map (costScoreSeedLift seedOfScore) rho := by
  simp [coldLawCostedKernel]

theorem heterogeneousStepMean_coldLawCostedKernel
    (rho : Measure (ENNReal × Score)) [IsProbabilityMeasure rho]
    (seedOfScore : Score → Seed) (hseed : Measurable seedOfScore) (x : Seed) :
    heterogeneousStepMean (coldLawCostedKernel rho seedOfScore hseed) x =
      ∫⁻ z, z.1 ∂rho := by
  letI := coldLawCostedKernel.isMarkovKernel rho seedOfScore hseed
  unfold heterogeneousStepMean
  rw [coldLawCostedKernel_apply]
  rw [lintegral_map measurable_fst (measurable_costScoreSeedLift hseed)]
  rfl

theorem map_seed_coldLawCostedKernel
    (rho : Measure (ENNReal × Score)) [IsProbabilityMeasure rho]
    (seedOfScore : Score → Seed) (hseed : Measurable seedOfScore) (x : Seed) :
    Measure.map (fun y : ENNReal × (Score × Seed) ↦ y.2.2)
        (coldLawCostedKernel rho seedOfScore hseed x) =
      Measure.map (seedOfScore ∘ Prod.snd) rho := by
  letI := coldLawCostedKernel.isMarkovKernel rho seedOfScore hseed
  rw [coldLawCostedKernel_apply]
  rw [Measure.map_map (by fun_prop : Measurable
      (fun y : ENNReal × (Score × Seed) ↦ y.2.2))
    (measurable_costScoreSeedLift hseed)]
  congr 1

/-- Piecewise costed schedule with genuine, separately typed cold and hot blocks. -/
noncomputable def coldHotCostedSchedule
    (cold : Nat)
    (Qcold Qhot : Nat → Kernel Seed (ENNReal × (Score × Seed))) :
    Nat → Kernel Seed (ENNReal × (Score × Seed)) := fun i ↦
  if h : i < cold then Qcold i else Qhot (i - cold)

instance coldHotCostedSchedule.isMarkovKernel
    (cold : Nat)
    (Qcold Qhot : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Qcold i)] [∀ i, IsMarkovKernel (Qhot i)] (i : Nat) :
    IsMarkovKernel (coldHotCostedSchedule cold Qcold Qhot i) := by
  unfold coldHotCostedSchedule
  split <;> infer_instance

noncomputable def coldHotSchedule
    (cold : Nat) (Pcold Phot : Nat → Kernel Seed (Score × Seed)) :
    Nat → Kernel Seed (Score × Seed) := fun i ↦
  if h : i < cold then Pcold i else Phot (i - cold)

instance coldHotSchedule.isMarkovKernel
    (cold : Nat) (Pcold Phot : Nat → Kernel Seed (Score × Seed))
    [∀ i, IsMarkovKernel (Pcold i)] [∀ i, IsMarkovKernel (Phot i)] (i : Nat) :
    IsMarkovKernel (coldHotSchedule cold Pcold Phot i) := by
  unfold coldHotSchedule
  split <;> infer_instance

theorem map_snd_coldHotCostedSchedule
    (cold : Nat)
    (Qcold Qhot : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    (Pcold Phot : Nat → Kernel Seed (Score × Seed))
    [∀ i, IsMarkovKernel (Qcold i)] [∀ i, IsMarkovKernel (Qhot i)]
    [∀ i, IsMarkovKernel (Pcold i)] [∀ i, IsMarkovKernel (Phot i)]
    (hcold : ∀ i x, Measure.map Prod.snd (Qcold i x) = Pcold i x)
    (hhot : ∀ i x, Measure.map Prod.snd (Qhot i x) = Phot i x)
    (i : Nat) (x : Seed) :
    Measure.map Prod.snd (coldHotCostedSchedule cold Qcold Qhot i x) =
      coldHotSchedule cold Pcold Phot i x := by
  unfold coldHotCostedSchedule coldHotSchedule
  split_ifs with hi
  · exact hcold i x
  · exact hhot (i - cold) x

theorem heterogeneousStepMean_coldHotCostedSchedule
    (cold : Nat)
    (Qcold Qhot : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Qcold i)] [∀ i, IsMarkovKernel (Qhot i)]
    (i : Nat) (x : Seed) :
    heterogeneousStepMean (coldHotCostedSchedule cold Qcold Qhot i) x =
      if i < cold then heterogeneousStepMean (Qcold i) x
      else heterogeneousStepMean (Qhot (i - cold)) x := by
  unfold coldHotCostedSchedule
  split_ifs <;> rfl

#print axioms map_snd_coldLawCostedKernel
#print axioms heterogeneousStepMean_coldLawCostedKernel
#print axioms map_seed_coldLawCostedKernel
#print axioms map_snd_coldHotCostedSchedule
#print axioms heterogeneousStepMean_coldHotCostedSchedule

end Ttc.CVColdHotScoreSeedSchedule

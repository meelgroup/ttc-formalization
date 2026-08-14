import Ttc.Exec.CVSeedProjectedDependence

/-! Generic augmented `(score, seed)` phase kernels. -/

namespace Ttc.CVScoreSeedPhaseKernel

open MeasureTheory ProbabilityTheory
open Arlib Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

abbrev ScoreSeed (Score Seed : Type*) := Score × Seed

/-- Lift a seed-indexed phase kernel to an augmented-state transition.  The previous score
is intentionally ignored; the output carries both the new estimator score and the warm
seed for the following phase. -/
noncomputable def stateKernelFromSeed
    (Q : Kernel Seed (ScoreSeed Score Seed)) :
    Kernel (ScoreSeed Score Seed) (ScoreSeed Score Seed) :=
  Kernel.comap Q Prod.snd measurable_snd

instance stateKernelFromSeed.isMarkovKernel
    (Q : Kernel Seed (ScoreSeed Score Seed)) [IsMarkovKernel Q] :
    IsMarkovKernel (stateKernelFromSeed Q) := by
  unfold stateKernelFromSeed
  infer_instance

theorem stateKernelFromSeed_apply
    (Q : Kernel Seed (ScoreSeed Score Seed)) (z : ScoreSeed Score Seed) :
    stateKernelFromSeed Q z = Q z.2 := by
  rw [stateKernelFromSeed, Kernel.comap_apply]

/-- Cost-recording form of the same augmented transition. -/
noncomputable def costedStateKernelFromSeed
    (R : Kernel Seed (ENNReal × ScoreSeed Score Seed)) :
    Kernel (ScoreSeed Score Seed) (ENNReal × ScoreSeed Score Seed) :=
  Kernel.comap R Prod.snd measurable_snd

instance costedStateKernelFromSeed.isMarkovKernel
    (R : Kernel Seed (ENNReal × ScoreSeed Score Seed)) [IsMarkovKernel R] :
    IsMarkovKernel (costedStateKernelFromSeed R) := by
  unfold costedStateKernelFromSeed
  infer_instance

theorem map_snd_costedStateKernelFromSeed
    (Q : Kernel Seed (ScoreSeed Score Seed))
    (R : Kernel Seed (ENNReal × ScoreSeed Score Seed))
    (hforget : ∀ x, Measure.map Prod.snd (R x) = Q x)
    (z : ScoreSeed Score Seed) :
    Measure.map Prod.snd (costedStateKernelFromSeed R z) =
      stateKernelFromSeed Q z := by
  rw [costedStateKernelFromSeed, stateKernelFromSeed,
    Kernel.comap_apply, Kernel.comap_apply]
  exact hforget z.2

/-- Time-inhomogeneous schedule lift, in exactly the factorized shape consumed by
`SeedProjectedOperational`. -/
noncomputable def stateScheduleFromSeed
    (Q : Nat → Kernel Seed (ScoreSeed Score Seed)) :
    Nat → Kernel (ScoreSeed Score Seed) (ScoreSeed Score Seed) :=
  fun i ↦ stateKernelFromSeed (Q i)

instance stateScheduleFromSeed.isMarkovKernel
    (Q : Nat → Kernel Seed (ScoreSeed Score Seed)) [∀ i, IsMarkovKernel (Q i)] (i : Nat) :
    IsMarkovKernel (stateScheduleFromSeed Q i) := by
  unfold stateScheduleFromSeed
  infer_instance

theorem stateScheduleFromSeed_factor
    (Q : Nat → Kernel Seed (ScoreSeed Score Seed)) (i : Nat) :
    stateScheduleFromSeed Q i = Kernel.comap (Q i) Prod.snd measurable_snd := rfl

noncomputable def costedStateScheduleFromSeed
    (R : Nat → Kernel Seed (ENNReal × ScoreSeed Score Seed)) :
    Nat → Kernel (ScoreSeed Score Seed) (ENNReal × ScoreSeed Score Seed) :=
  fun i ↦ costedStateKernelFromSeed (R i)

instance costedStateScheduleFromSeed.isMarkovKernel
    (R : Nat → Kernel Seed (ENNReal × ScoreSeed Score Seed))
    [∀ i, IsMarkovKernel (R i)] (i : Nat) :
    IsMarkovKernel (costedStateScheduleFromSeed R i) := by
  unfold costedStateScheduleFromSeed
  infer_instance

theorem map_snd_costedStateScheduleFromSeed
    (Q : Nat → Kernel Seed (ScoreSeed Score Seed))
    (R : Nat → Kernel Seed (ENNReal × ScoreSeed Score Seed))
    (hforget : ∀ i x, Measure.map Prod.snd (R i x) = Q i x)
    (i : Nat) (z : ScoreSeed Score Seed) :
    Measure.map Prod.snd (costedStateScheduleFromSeed R i z) =
      stateScheduleFromSeed Q i z :=
  map_snd_costedStateKernelFromSeed (Q i) (R i) (hforget i) z

#print axioms stateKernelFromSeed_apply
#print axioms map_snd_costedStateKernelFromSeed
#print axioms stateScheduleFromSeed_factor
#print axioms map_snd_costedStateScheduleFromSeed

end Ttc.CVScoreSeedPhaseKernel

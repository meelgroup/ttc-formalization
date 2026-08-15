import Ttc.Exec.CVColdHotScoreSeedSchedule

/-! Reindexing one globally indexed operational schedule as literal cold/hot blocks. -/

set_option autoImplicit false

namespace Ttc.CVColdHotScheduleSplit

open MeasureTheory ProbabilityTheory
open Ttc.CVColdHotScoreSeedSchedule

variable {Seed Score : Type*} [MeasurableSpace Seed] [MeasurableSpace Score]

noncomputable def coldPrefix
    (P : Nat → Kernel Seed (Score × Seed)) : Nat → Kernel Seed (Score × Seed) :=
  fun i ↦ P i

noncomputable def hotSuffix
    (cold : Nat) (P : Nat → Kernel Seed (Score × Seed)) :
    Nat → Kernel Seed (Score × Seed) := fun j ↦ P (cold + j)

noncomputable def coldCostedPrefix
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed))) :
    Nat → Kernel Seed (ENNReal × (Score × Seed)) := fun i ↦ Q i

noncomputable def hotCostedSuffix
    (cold : Nat) (Q : Nat → Kernel Seed (ENNReal × (Score × Seed))) :
    Nat → Kernel Seed (ENNReal × (Score × Seed)) := fun j ↦ Q (cold + j)

instance coldPrefix.isMarkovKernel
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)] (i : Nat) :
    IsMarkovKernel (coldPrefix P i) := by
  unfold coldPrefix
  infer_instance

instance hotSuffix.isMarkovKernel
    (cold : Nat) (P : Nat → Kernel Seed (Score × Seed))
    [∀ i, IsMarkovKernel (P i)] (j : Nat) :
    IsMarkovKernel (hotSuffix cold P j) := by
  unfold hotSuffix
  infer_instance

instance coldCostedPrefix.isMarkovKernel
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)] (i : Nat) :
    IsMarkovKernel (coldCostedPrefix Q i) := by
  unfold coldCostedPrefix
  infer_instance

instance hotCostedSuffix.isMarkovKernel
    (cold : Nat) (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)] (j : Nat) :
    IsMarkovKernel (hotCostedSuffix cold Q j) := by
  unfold hotCostedSuffix
  infer_instance

theorem coldHotSchedule_prefix_suffix
    (cold : Nat) (P : Nat → Kernel Seed (Score × Seed)) :
    coldHotSchedule cold (coldPrefix P) (hotSuffix cold P) = P := by
  funext i
  unfold coldHotSchedule coldPrefix hotSuffix
  split_ifs with hi
  · rfl
  · congr 1
    omega

theorem coldHotCostedSchedule_prefix_suffix
    (cold : Nat) (Q : Nat → Kernel Seed (ENNReal × (Score × Seed))) :
    coldHotCostedSchedule cold (coldCostedPrefix Q) (hotCostedSuffix cold Q) = Q := by
  funext i
  unfold coldHotCostedSchedule coldCostedPrefix hotCostedSuffix
  split_ifs with hi
  · rfl
  · congr 1
    omega

theorem coldHotSchedule_prefix_suffix_apply
    (cold : Nat) (P : Nat → Kernel Seed (Score × Seed)) (i : Nat) :
    coldHotSchedule cold (coldPrefix P) (hotSuffix cold P) i = P i := by
  rw [coldHotSchedule_prefix_suffix]

theorem coldHotCostedSchedule_prefix_suffix_apply
    (cold : Nat) (Q : Nat → Kernel Seed (ENNReal × (Score × Seed))) (i : Nat) :
    coldHotCostedSchedule cold (coldCostedPrefix Q) (hotCostedSuffix cold Q) i = Q i := by
  rw [coldHotCostedSchedule_prefix_suffix]

#print axioms coldHotSchedule_prefix_suffix
#print axioms coldHotCostedSchedule_prefix_suffix

end Ttc.CVColdHotScheduleSplit

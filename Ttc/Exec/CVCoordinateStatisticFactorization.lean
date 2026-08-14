import Ttc.Exec.CVIndependentStreamDependence

/-!
# Finite-history factorization of coordinatewise corrected CV statistics

The corrected phase statistic at paper index `j+1` reads only the block of states at
time `j+1`.  This file packages the otherwise repetitive proof that the recursive
`accuracyU` prefix reads only the history through time `i`.
-/

namespace Ttc.CVCoordinateStatisticFactorization

open MeasureTheory
open Arlib.GaussianCooling
open scoped Classical

variable {X : Type*} [MeasurableSpace X]

abbrev BlockPath (k : Nat) := Fin k → Nat → X
abbrev BlockHistory (k i : Nat) := Fin k → Finset.Iic i → X

/-- The block of all independent streams at one time. -/
def blockAt {k : Nat} (i : Nat) (omega : BlockPath k) : Fin k → X :=
  fun l => omega l i

/-- A paper-indexed phase family: index zero is a harmless dummy, while `j+1` reads
the phase-`j` statistic from the block at time `j+1`. -/
def coordinatePhases {k : Nat} (v : Nat → (Fin k → X) → Real) :
    Nat → BlockPath k → Real
  | 0 => fun _ => 0
  | j + 1 => fun omega => v j (blockAt (j + 1) omega)

/-- Restrict a history through `i+1` to the preceding history through `i`. -/
def historyInit {k i : Nat} (h : BlockHistory k (i + 1)) : BlockHistory k i :=
  fun l j => h l ⟨j, j.2.trans (Nat.le_succ i)⟩

/-- Last block of a history through `i`. -/
def historyLast {k i : Nat} (h : BlockHistory k i) : Fin k → X :=
  fun l => h l ⟨i, Finset.mem_Iic.2 le_rfl⟩

/-- Finite-history version of `accuracyU` for a coordinatewise phase statistic. -/
noncomputable def historyAccuracy {k : Nat} (mu : Measure (BlockPath k))
    (v : Nat → (Fin k → X) → Real) (alpha : Real) :
    (i : Nat) → BlockHistory k i → Real
  | 0 => fun _ => 1
  | i + 1 => fun h =>
      min (historyAccuracy mu v alpha i (historyInit h) * v i (historyLast h))
        (alpha * prefixMean mu (coordinatePhases v) (i + 1))

theorem measurable_blockAt {k i : Nat} :
    Measurable (blockAt (X := X) (k := k) i) := by
  exact measurable_pi_lambda _ fun l => measurable_pi_apply l |>.comp
    (measurable_pi_apply i)

theorem measurable_historyInit {k i : Nat} :
    Measurable (historyInit (X := X) (k := k) (i := i)) := by
  exact measurable_pi_lambda _ fun l => measurable_pi_lambda _ fun j =>
    (measurable_pi_apply l).comp
      (measurable_pi_apply ⟨j, j.2.trans (Nat.le_succ i)⟩)

theorem measurable_historyLast {k i : Nat} :
    Measurable (historyLast (X := X) (k := k) (i := i)) := by
  exact measurable_pi_lambda _ fun l => (measurable_pi_apply l).comp
    (measurable_pi_apply ⟨i, Finset.mem_Iic.2 le_rfl⟩)

theorem measurable_coordinatePhases {k : Nat}
    (v : Nat → (Fin k → X) → Real) (hv : ∀ i, Measurable (v i)) :
    ∀ j, Measurable (coordinatePhases v j)
  | 0 => measurable_const
  | j + 1 => (hv j).comp measurable_blockAt

theorem measurable_historyAccuracy {k : Nat} (mu : Measure (BlockPath k))
    (v : Nat → (Fin k → X) → Real) (hv : ∀ i, Measurable (v i)) (alpha : Real) :
    ∀ i, Measurable (historyAccuracy mu v alpha i)
  | 0 => measurable_const
  | i + 1 =>
      (((measurable_historyAccuracy mu v hv alpha i).comp measurable_historyInit).mul
        ((hv i).comp measurable_historyLast)).min measurable_const

theorem coordinatePhases_succ_restrict {k i : Nat}
    (v : Nat → (Fin k → X) → Real) (omega : BlockPath k) :
    coordinatePhases v (i + 1) omega =
      v i (historyLast (fun l => Preorder.frestrictLe (π := fun _ : Nat => X) i
        (omega l))) := by
  rfl

/-- The recursive corrected prefix factors exactly through the finite history. -/
theorem accuracyU_eq_historyAccuracy {k : Nat} (mu : Measure (BlockPath k))
    (v : Nat → (Fin k → X) → Real) (alpha : Real) :
    ∀ i, accuracyU mu (coordinatePhases v) alpha i =
      fun omega => historyAccuracy mu v alpha i
        (fun l => Preorder.frestrictLe (π := fun _ : Nat => X) i (omega l))
  | 0 => by
      funext omega
      rfl
  | i + 1 => by
      funext omega
      rw [accuracyU_succ]
      change min
          (accuracyU mu (coordinatePhases v) alpha i omega *
            v i (blockAt (i + 1) omega))
          (alpha * prefixMean mu (coordinatePhases v) (i + 1)) = _
      rw [congrFun (accuracyU_eq_historyAccuracy mu v alpha i) omega]
      rfl

/-- Both factorization fields required by `IndependentStreamOperational`, supplied for
every coordinatewise phase family. -/
theorem coordinate_factorizations {k m : Nat} (mu : Measure (BlockPath k))
    (v : Nat → (Fin k → X) → Real) (alpha : Real) :
    (∀ i, accuracyU mu (coordinatePhases v) alpha i =
      fun omega => historyAccuracy mu v alpha i
        (fun l => Preorder.frestrictLe (π := fun _ : Nat => X) i (omega l))) ∧
    (∀ i, coordinatePhases v (i + 1) =
      fun omega => v i (fun l => omega l (i + 1))) := by
  exact ⟨accuracyU_eq_historyAccuracy mu v alpha, fun i => rfl⟩

#print axioms accuracyU_eq_historyAccuracy
#print axioms coordinate_factorizations

end Ttc.CVCoordinateStatisticFactorization

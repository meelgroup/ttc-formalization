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

abbrev BlockPath (X : Type*) (k : Nat) := Fin k → Nat → X
abbrev BlockHistory (X : Type*) (k i : Nat) := Fin k → Finset.Iic i → X

def initIndex {i : Nat} (j : Finset.Iic i) : Finset.Iic (i + 1) :=
  ⟨j.1, Finset.mem_Iic.2 ((Finset.mem_Iic.1 j.2).trans (Nat.le_succ i))⟩

def lastIndex (i : Nat) : Finset.Iic i :=
  ⟨i, Finset.mem_Iic.2 le_rfl⟩

/-- The block of all independent streams at one time. -/
def blockAt {k : Nat} (i : Nat) (omega : BlockPath X k) : Fin k → X :=
  fun l => omega l i

/-- A paper-indexed phase family: index zero is a harmless dummy, while `j+1` reads
the phase-`j` statistic from the block at time `j+1`. -/
def coordinatePhases {k : Nat} (v : Nat → (Fin k → X) → Real) :
    Nat → BlockPath X k → Real
  | 0 => fun _ => 0
  | j + 1 => fun omega => v j (blockAt (j + 1) omega)

/-- Restrict a history through `i+1` to the preceding history through `i`. -/
def historyInit {k i : Nat} (h : BlockHistory X k (i + 1)) : BlockHistory X k i :=
  fun l j => h l (initIndex j)

/-- Last block of a history through `i`. -/
def historyLast {k i : Nat} (h : BlockHistory X k i) : Fin k → X :=
  fun l => h l (lastIndex i)

/-- Finite-history version of `accuracyU` for a coordinatewise phase statistic. -/
noncomputable def historyAccuracy {k : Nat} (mu : Measure (BlockPath X k))
    (v : Nat → (Fin k → X) → Real) (alpha : Real) :
    (i : Nat) → BlockHistory X k i → Real
  | 0 => fun _ => 1
  | i + 1 => fun h =>
      min (historyAccuracy mu v alpha i (historyInit h) * v i (historyLast h))
        (alpha * prefixMean mu (coordinatePhases v) (i + 1))

theorem measurable_blockAt {k i : Nat} :
    Measurable (blockAt (X := X) (k := k) i) := by
  exact measurable_pi_lambda _ fun l =>
    (measurable_pi_apply i).comp (measurable_pi_apply l)

theorem measurable_historyInit {k i : Nat} :
    Measurable (historyInit (X := X) (k := k) (i := i)) := by
  exact measurable_pi_lambda _ fun l => measurable_pi_lambda _ fun j =>
    (measurable_pi_apply (initIndex j)).comp
      (measurable_pi_apply l)

theorem measurable_historyLast {k i : Nat} :
    Measurable (historyLast (X := X) (k := k) (i := i)) := by
  exact measurable_pi_lambda _ fun l =>
    (measurable_pi_apply (lastIndex i)).comp
      (measurable_pi_apply l)

theorem measurable_coordinatePhases {k : Nat}
    (v : Nat → (Fin k → X) → Real) (hv : ∀ i, Measurable (v i)) :
    ∀ j, Measurable (coordinatePhases v j)
  | 0 => measurable_const
  | j + 1 => (hv j).comp measurable_blockAt

theorem measurable_historyAccuracy {k : Nat} (mu : Measure (BlockPath X k))
    (v : Nat → (Fin k → X) → Real) (hv : ∀ i, Measurable (v i)) (alpha : Real) :
    ∀ i, Measurable (historyAccuracy mu v alpha i)
  | 0 => measurable_const
  | i + 1 =>
      (((measurable_historyAccuracy mu v hv alpha i).comp measurable_historyInit).mul
        ((hv i).comp measurable_historyLast)).min measurable_const

theorem coordinatePhases_succ_restrict {k i : Nat}
    (v : Nat → (Fin k → X) → Real) (omega : BlockPath X k) :
    coordinatePhases v (i + 1) omega =
      v i (historyLast (fun l => Preorder.frestrictLe (π := fun _ : Nat => X) (i + 1)
        (omega l))) := by
  change v i (fun l => omega l (i + 1)) = v i (fun l => _)
  congr 1

/-- The recursive corrected prefix factors exactly through the finite history. -/
theorem accuracyU_eq_historyAccuracy {k : Nat} (mu : Measure (BlockPath X k))
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
theorem coordinate_factorizations {k m : Nat} (mu : Measure (BlockPath X k))
    (v : Nat → (Fin k → X) → Real) (alpha : Real) :
    (∀ i, accuracyU mu (coordinatePhases v) alpha i =
      fun omega => historyAccuracy mu v alpha i
        (fun l => Preorder.frestrictLe (π := fun _ : Nat => X) i (omega l))) ∧
    (∀ i, coordinatePhases v (i + 1) =
      fun omega => v i (fun l => omega l (i + 1))) := by
  exact ⟨accuracyU_eq_historyAccuracy mu v alpha, fun i => rfl⟩

/-! ## Scalar-stream specialization -/

/-- A paper-indexed statistic on one path. -/
def pathPhases (v : Nat → X → Real) : Nat → (Nat → X) → Real
  | 0 => fun _ => 0
  | j + 1 => fun omega => v j (omega (j + 1))

/-- Finite-history recursion for the scalar corrected prefix. -/
noncomputable def pathHistoryAccuracy (mu : Measure (Nat → X))
    (v : Nat → X → Real) (alpha : Real) :
    (i : Nat) → (Finset.Iic i → X) → Real
  | 0 => fun _ => 1
  | i + 1 => fun h =>
      min (pathHistoryAccuracy mu v alpha i (fun j => h (initIndex j)) *
          v i (h (lastIndex (i + 1))))
        (alpha * prefixMean mu (pathPhases v) (i + 1))

theorem measurable_pathPhases (v : Nat → X → Real)
    (hv : ∀ i, Measurable (v i)) : ∀ j, Measurable (pathPhases v j)
  | 0 => measurable_const
  | j + 1 => (hv j).comp (measurable_pi_apply (j + 1))

theorem measurable_pathHistoryAccuracy (mu : Measure (Nat → X))
    (v : Nat → X → Real) (hv : ∀ i, Measurable (v i)) (alpha : Real) :
    ∀ i, Measurable (pathHistoryAccuracy mu v alpha i)
  | 0 => measurable_const
  | i + 1 =>
      (((measurable_pathHistoryAccuracy mu v hv alpha i).comp
          (measurable_pi_lambda _ fun j => measurable_pi_apply (initIndex j))).mul
        ((hv i).comp (measurable_pi_apply (lastIndex (i + 1))))).min measurable_const

theorem accuracyU_pathPhases_eq_pathHistoryAccuracy
    (mu : Measure (Nat → X)) (v : Nat → X → Real) (alpha : Real) :
    ∀ i, accuracyU mu (pathPhases v) alpha i =
      fun omega => pathHistoryAccuracy mu v alpha i
        (Preorder.frestrictLe (π := fun _ : Nat => X) i omega)
  | 0 => by
      funext omega
      rfl
  | i + 1 => by
      funext omega
      rw [accuracyU_succ]
      change min
          (accuracyU mu (pathPhases v) alpha i omega * v i (omega (i + 1)))
          (alpha * prefixMean mu (pathPhases v) (i + 1)) = _
      rw [congrFun (accuracyU_pathPhases_eq_pathHistoryAccuracy mu v alpha i) omega]
      rfl

/-- Both scalar factorization fields required by `SeedProjectedOperational`. -/
theorem path_factorizations (mu : Measure (Nat → X))
    (v : Nat → X → Real) (alpha : Real) :
    (∀ i, accuracyU mu (pathPhases v) alpha i =
      fun omega => pathHistoryAccuracy mu v alpha i
        (Preorder.frestrictLe (π := fun _ : Nat => X) i omega)) ∧
    (∀ i, pathPhases v (i + 1) = fun omega => v i (omega (i + 1))) := by
  exact ⟨accuracyU_pathPhases_eq_pathHistoryAccuracy mu v alpha, fun i => rfl⟩

#print axioms accuracyU_eq_historyAccuracy
#print axioms coordinate_factorizations
#print axioms path_factorizations

end Ttc.CVCoordinateStatisticFactorization

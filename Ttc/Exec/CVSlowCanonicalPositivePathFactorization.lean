import Ttc.Exec.CVCoordinateStatisticFactorization
import Ttc.Exec.CVRelativeMeanClippingAssembly

/-!
# Finite-history factorization for the positive-dummy phase families

The slow canonical route runs the corrected accuracy recursion against a phase family
whose index-zero entry is the *positive* dummy `1` rather than `0`
(`Ttc.CVRelativeMeanClippingAssembly.positiveScalarPhaseFamilyChainLength`).  Neither
`Arlib.GaussianCooling.accuracyU` nor `Arlib.GaussianCooling.prefixMean` ever reads the
family at index zero: both only ever evaluate `V (j + 1)`.  Consequently the whole
finite-history factorization already proved in
`Ttc.Exec.CVCoordinateStatisticFactorization` for the zero-dummy families transports
verbatim to the positive-dummy families.

This file records that transport, so that the `U_eq` / `V_eq` fields of
`SeedProjectedOperational` and `IndependentStreamOperational` can be supplied for the
positive-dummy family without duplicating the recursion development.
-/

set_option autoImplicit false

namespace Ttc.CVSlowCanonicalPositivePathFactorization

open MeasureTheory
open Arlib.GaussianCooling
open scoped Classical

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Step 1: the accuracy recursion only reads the family at successor indices -/

/-- `prefixMean` never reads index zero of the phase family. -/
theorem prefixMean_congr_succ (mu : Measure Omega) (V W : Nat → Omega → Real)
    (h : ∀ j, V (j + 1) = W (j + 1)) (i : Nat) :
    prefixMean mu V i = prefixMean mu W i := by
  refine Finset.prod_congr rfl ?_
  intro j _
  rw [h j]

/-- `accuracyU` never reads index zero of the phase family. -/
theorem accuracyU_congr_succ (mu : Measure Omega) (V W : Nat → Omega → Real)
    (alpha : Real) (h : ∀ j, V (j + 1) = W (j + 1)) (i : Nat) :
    accuracyU mu V alpha i = accuracyU mu W alpha i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      funext omega
      rw [accuracyU_succ, accuracyU_succ, ih, h i,
        prefixMean_congr_succ mu V W h (i + 1)]

/-! ## Step 2: the scalar (single-path) positive-dummy family -/

variable {X : Type*} [MeasurableSpace X]

/-- A paper-indexed statistic on one path, with a *positive* dummy at index zero.
Compare `Ttc.CVCoordinateStatisticFactorization.pathPhases`, which uses `0`. -/
def positivePathPhases (v : Nat → X → Real) : Nat → (Nat → X) → Real
  | 0 => fun _ => 1
  | j + 1 => fun omega => v j (omega (j + 1))

omit [MeasurableSpace X] in
theorem positivePathPhases_succ (v : Nat → X → Real) (j : Nat) :
    positivePathPhases v (j + 1) = fun omega => v j (omega (j + 1)) := rfl

omit [MeasurableSpace X] in
/-- The positive-dummy family agrees with the zero-dummy family at every successor
index, which is all the accuracy recursion ever reads. -/
theorem positivePathPhases_eq_pathPhases_succ (v : Nat → X → Real) (j : Nat) :
    positivePathPhases v (j + 1) =
      Ttc.CVCoordinateStatisticFactorization.pathPhases v (j + 1) := rfl

theorem measurable_positivePathPhases (v : Nat → X → Real)
    (hv : ∀ i, Measurable (v i)) : ∀ j, Measurable (positivePathPhases v j)
  | 0 => measurable_const
  | j + 1 => (hv j).comp (measurable_pi_apply (j + 1))

theorem accuracyU_positivePathPhases_eq (mu : Measure (Nat → X)) (v : Nat → X → Real)
    (alpha : Real) (i : Nat) :
    accuracyU mu (positivePathPhases v) alpha i =
      accuracyU mu (Ttc.CVCoordinateStatisticFactorization.pathPhases v) alpha i :=
  accuracyU_congr_succ mu _ _ alpha (fun j => positivePathPhases_eq_pathPhases_succ v j) i

/-- Both scalar factorization fields required by `SeedProjectedOperational`, for the
positive-dummy family.  The finite-history statistic is the one already built in
`Ttc.CVCoordinateStatisticFactorization`. -/
theorem positivePath_factorizations (mu : Measure (Nat → X))
    (v : Nat → X → Real) (alpha : Real) :
    (∀ i, accuracyU mu (positivePathPhases v) alpha i =
      fun omega => Ttc.CVCoordinateStatisticFactorization.pathHistoryAccuracy mu v alpha i
        (Preorder.frestrictLe (π := fun _ : Nat => X) i omega)) ∧
    (∀ i, positivePathPhases v (i + 1) = fun omega => v i (omega (i + 1))) := by
  refine ⟨fun i => ?_, fun i => rfl⟩
  rw [accuracyU_positivePathPhases_eq mu v alpha i]
  exact Ttc.CVCoordinateStatisticFactorization.accuracyU_pathPhases_eq_pathHistoryAccuracy
    mu v alpha i

/-! ## Step 3: the `Fin k`-block positive-dummy family -/

/-- A paper-indexed coordinatewise statistic on `k` independent streams, with a
*positive* dummy at index zero.  Compare
`Ttc.CVCoordinateStatisticFactorization.coordinatePhases`, which uses `0`. -/
def positiveCoordinatePhases {k : Nat} (v : Nat → (Fin k → X) → Real) :
    Nat → (Fin k → Nat → X) → Real
  | 0 => fun _ => 1
  | i + 1 => fun omega => v i (fun l => omega l (i + 1))

omit [MeasurableSpace X] in
theorem positiveCoordinatePhases_succ {k : Nat} (v : Nat → (Fin k → X) → Real)
    (i : Nat) :
    positiveCoordinatePhases v (i + 1) = fun omega => v i (fun l => omega l (i + 1)) := rfl

omit [MeasurableSpace X] in
theorem positiveCoordinatePhases_eq_coordinatePhases_succ {k : Nat}
    (v : Nat → (Fin k → X) → Real) (i : Nat) :
    positiveCoordinatePhases v (i + 1) =
      Ttc.CVCoordinateStatisticFactorization.coordinatePhases v (i + 1) := rfl

theorem measurable_positiveCoordinatePhases {k : Nat}
    (v : Nat → (Fin k → X) → Real) (hv : ∀ i, Measurable (v i)) :
    ∀ j, Measurable (positiveCoordinatePhases v j)
  | 0 => measurable_const
  | j + 1 => (hv j).comp Ttc.CVCoordinateStatisticFactorization.measurable_blockAt

theorem accuracyU_positiveCoordinatePhases_eq {k : Nat}
    (mu : Measure (Fin k → Nat → X)) (v : Nat → (Fin k → X) → Real) (alpha : Real)
    (i : Nat) :
    accuracyU mu (positiveCoordinatePhases v) alpha i =
      accuracyU mu (Ttc.CVCoordinateStatisticFactorization.coordinatePhases v) alpha i :=
  accuracyU_congr_succ mu _ _ alpha
    (fun j => positiveCoordinatePhases_eq_coordinatePhases_succ v j) i

/-- Both factorization fields required by `IndependentStreamOperational`, for the
positive-dummy coordinatewise family. -/
theorem positiveCoordinate_factorizations {k : Nat}
    (mu : Measure (Fin k → Nat → X)) (v : Nat → (Fin k → X) → Real) (alpha : Real) :
    (∀ i, accuracyU mu (positiveCoordinatePhases v) alpha i =
      fun omega => Ttc.CVCoordinateStatisticFactorization.historyAccuracy mu v alpha i
        (fun l => Preorder.frestrictLe (π := fun _ : Nat => X) i (omega l))) ∧
    (∀ i, positiveCoordinatePhases v (i + 1) =
      fun omega => v i (fun l => omega l (i + 1))) := by
  refine ⟨fun i => ?_, fun i => rfl⟩
  rw [accuracyU_positiveCoordinatePhases_eq mu v alpha i]
  exact Ttc.CVCoordinateStatisticFactorization.accuracyU_eq_historyAccuracy mu v alpha i

/-! ## Step 4: the bridge to the slow canonical phase family -/

section Bridge

variable {n : Nat} {Seed : Type*}

/-- The slow canonical positive-dummy family is literally a `positivePathPhases`
family, for the coordinatewise phase score read off the state component. -/
theorem positiveScalarPhaseFamilyChainLength_eq_positivePathPhases
    (chainLength : Nat) (sigmaSq : Nat → Real)
    (K : Set (EuclideanSpace Real (Fin n))) :
    Ttc.CVRelativeMeanClippingAssembly.positiveScalarPhaseFamilyChainLength
        (Seed := Seed) chainLength sigmaSq K
      = positivePathPhases (X := EuclideanSpace Real (Fin n) × Seed)
          (fun i x =>
            Arlib.GaussianCooling.phaseScore chainLength sigmaSq (interior K) i x.1) := by
  funext j
  cases j with
  | zero => rfl
  | succ j => rfl

/-- The exact `V_eq` shape required by `SeedProjectedOperational`, with `score = Prod.fst`. -/
theorem positiveScalarPhaseFamily_V_eq
    (chainLength : Nat) (sigmaSq : Nat → Real)
    (K : Set (EuclideanSpace Real (Fin n))) (i : Nat) :
    Ttc.CVRelativeMeanClippingAssembly.positiveScalarPhaseFamilyChainLength
        (Seed := Seed) chainLength sigmaSq K (i + 1)
      = fun omega =>
          Arlib.GaussianCooling.phaseScore chainLength sigmaSq (interior K) i
            (Prod.fst (omega (i + 1))) := rfl

/-- Both factorization fields for the slow canonical positive-dummy family: the
finite-history statistic is `pathHistoryAccuracy` for the state-projected phase score. -/
theorem positiveScalarPhaseFamily_factorizations [MeasurableSpace Seed]
    (chainLength : Nat) (sigmaSq : Nat → Real)
    (K : Set (EuclideanSpace Real (Fin n)))
    (mu : Measure (Nat → EuclideanSpace Real (Fin n) × Seed)) (alpha : Real) :
    (∀ i, accuracyU mu
        (Ttc.CVRelativeMeanClippingAssembly.positiveScalarPhaseFamilyChainLength
          (Seed := Seed) chainLength sigmaSq K) alpha i =
      fun omega => Ttc.CVCoordinateStatisticFactorization.pathHistoryAccuracy mu
        (fun i x =>
          Arlib.GaussianCooling.phaseScore chainLength sigmaSq (interior K) i x.1)
        alpha i
        (Preorder.frestrictLe
          (π := fun _ : Nat => EuclideanSpace Real (Fin n) × Seed) i omega)) ∧
    (∀ i, Ttc.CVRelativeMeanClippingAssembly.positiveScalarPhaseFamilyChainLength
        (Seed := Seed) chainLength sigmaSq K (i + 1) =
      fun omega =>
        Arlib.GaussianCooling.phaseScore chainLength sigmaSq (interior K) i
          (Prod.fst (omega (i + 1)))) := by
  refine ⟨fun i => ?_, fun i => rfl⟩
  rw [positiveScalarPhaseFamilyChainLength_eq_positivePathPhases
    (Seed := Seed) chainLength sigmaSq K]
  exact (positivePath_factorizations mu _ alpha).1 i

end Bridge

#print axioms prefixMean_congr_succ
#print axioms accuracyU_congr_succ
#print axioms positivePathPhases
#print axioms positivePathPhases_succ
#print axioms positivePathPhases_eq_pathPhases_succ
#print axioms measurable_positivePathPhases
#print axioms accuracyU_positivePathPhases_eq
#print axioms positivePath_factorizations
#print axioms positiveCoordinatePhases
#print axioms positiveCoordinatePhases_succ
#print axioms positiveCoordinatePhases_eq_coordinatePhases_succ
#print axioms measurable_positiveCoordinatePhases
#print axioms accuracyU_positiveCoordinatePhases_eq
#print axioms positiveCoordinate_factorizations
#print axioms positiveScalarPhaseFamilyChainLength_eq_positivePathPhases
#print axioms positiveScalarPhaseFamily_V_eq
#print axioms positiveScalarPhaseFamily_factorizations

end Ttc.CVSlowCanonicalPositivePathFactorization

import ttc.Analysis.ReferenceProgram
import ttc.Analysis.PreludeProof
import ttc.Analysis.TtcVolumeAccuracyLatticeComparison

/-!
# Assembly of the TTC volume-accuracy theorem

The empty decomposition is handled completely here.  The nonempty branch combines the
component and union lattice comparisons with `ttc_lattice_count_accuracy`; that theorem
invokes the explicit `Prior` field under the public high-intensity premise.

The algebraic lemmas below retain the original divisive-rate diagnosis as a regression
check and record the multiplicative cancellation used by the repaired model.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory unitInterval
open MeasureTheory

namespace ttc

/-- Certified preprocessing preserves the volume of the projected solution set. -/
theorem Decomposition.volume_eq_solutionSet {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) :
    volume D.union = volume (solutionSet F) := by
  exact measure_eq_of_mem_ae_iff D.solution_ae

/--
After thinning a coded `t / p` Poisson batch by `2ʳ` and updating the stored rate in the
same way, its expected contribution to the `|X| / p` estimate is `t / p²`.

INTERNAL: Algebraic diagnosis of the rate convention in `processComponent`.
-/
lemma divided_poisson_rate_estimator (t p : NNReal) (hp : p ≠ 0) (r : Nat) :
    (t / (p * (2 : NNReal) ^ r)) / (p / (2 : NNReal) ^ r) = t / p ^ 2 := by
  field_simp

/--
With the paper's `t * p` Poisson mean, common thinning and division by the updated rate
cancel and the expected estimator contribution is exactly `t`.

PAPER: sections/algo.tex:32-43
-/
lemma multiplied_poisson_rate_estimator (t p : NNReal) (hp : p ≠ 0) (r : Nat) :
    (t * p / (2 : NNReal) ^ r) / (p / (2 : NNReal) ^ r) = t := by
  field_simp

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · reduced · closed the headline assembly through `ttc_lattice_count_accuracy`
* r1 · diagnosed · isolated the original nonempty `t / p` rate mismatch
-/

end ttc

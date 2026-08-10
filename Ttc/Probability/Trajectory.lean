/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The ½-thinning and the coupled trajectory law

`alg:ttc`'s sample coins are a trajectory of the coupled level family: a level-`0`
vector of independent Poisson counts, thinned by a fair coin at every level.  Ionescu–
Tulcea (`ProbabilityTheory.Kernel.trajMeasure`) turns the one-step thinning kernel into
the law of the *whole* trajectory on one space, which is what makes every level's event
unconditional.

**Vocabulary only.**  Four definitions and the two Markov-kernel instances the
Ionescu–Tulcea construction takes as instance arguments.  Nothing here is a `Prop`,
nothing is assumed, and nothing mentions `TTC`, a formula or a convex body: the file
imports Mathlib and nothing of ours.  Every property of these objects — that the
thinning is the paper's `lem:process`, that the loops terminate almost surely — is
proved downstream (`Process/Thinning`, `Process/Truncation`, `Coupling/Family`).

This file used to be the second half of `Model/Prelude`; see
`Ttc/Audit/ClosureCheck.lean` for why the audit surface is `Ttc/Model/` **together
with** `Ttc/Probability/`.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory

/-- The thinning probability `½`, as an element of `unitInterval`. -/
noncomputable def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- **One thinning step, as a Markov kernel.** Each coordinate is thinned
`Binomial(·, ½)`, independently across lattice points. -/
noncomputable def thinKernel (L : ℕ) : Kernel (Fin L → ℕ) (Fin L → ℕ) where
  toFun k := Measure.pi fun s => binomial (k s) half
  measurable' := Measurable.of_discrete

instance isMarkovKernel_thinKernel (L : ℕ) : IsMarkovKernel (thinKernel L) :=
  ⟨fun k => by
    show IsProbabilityMeasure (Measure.pi fun s => binomial (k s) half)
    infer_instance⟩

/-- The chain's kernel at step `n`: thin the state at time `n`. The history is
available but only its last coordinate is read — the chain is Markov. -/
noncomputable def chainKernel (L n : ℕ) :
    Kernel ((_i : ↥(Finset.Iic n)) → (Fin L → ℕ)) (Fin L → ℕ) :=
  Kernel.comap (thinKernel L) (fun h => h ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance isMarkovKernel_chainKernel (L n : ℕ) : IsMarkovKernel (chainKernel L n) := by
  rw [chainKernel]; infer_instance

/-- **The coupled family, as one measure on trajectories.** Start from the
level-`0` product of Poissons and thin forever. -/
noncomputable def trajLaw {L : ℕ} (θ : Fin L → ℝ) : Measure (ℕ → (Fin L → ℕ)) :=
  Kernel.trajMeasure (Measure.pi fun s => poissonMeasure (θ s).toNNReal) (chainKernel L)

end Ttc

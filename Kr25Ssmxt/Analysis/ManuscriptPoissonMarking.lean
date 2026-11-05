import Arlib.Probability.PoissonSplitting
import Arlib.Probability.PoissonThinning

/-! Exact marked-Poisson identities needed for manuscript Theorem 1.

The paper's process lemma must use the actual intensity `μ * q x` at point
`x`. Bounds on that intensity alone do not specify an equal distribution. -/

namespace Kr25Ssmxt

open Arlib.Probability

theorem manuscript_poisson_marking_exact {X : Type*} [DecidableEq X]
    (S : Finset X) (q : X → Real) (hq : ∑ x ∈ S, q x = 1)
    (mu : Real) (counts : X → Nat) :
    (∑' total : Nat, poissonPMF mu total * countMass S q total counts) =
      ∏ x ∈ S, poissonPMF (q x * mu) (counts x) :=
  tsum_poissonPMF_mul_countMass S q hq mu counts

theorem manuscript_poisson_half_thinning_exact (mu : Real) (kept : Nat) :
    (∑' total : Nat,
      poissonPMF mu total * binomialPMF total (1 / 2) kept) =
      poissonPMF ((1 / 2) * mu) kept :=
  tsum_poissonPMF_mul_binomialPMF mu (1 / 2) kept

end Kr25Ssmxt

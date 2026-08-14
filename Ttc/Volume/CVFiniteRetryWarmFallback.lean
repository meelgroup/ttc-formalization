import Arlib.Probability.WarmMixture

/-!
# Warmness of finite retries with a self fallback

The useful cancellation in a continuing-retry phase occurs before normalising each
accepted component.  If every unnormalised first-hit increment is `C`-warm, summing
`L` attempts costs only `L*C`.  If the no-hit fallback is the incoming state, its tail
law is a submeasure of the incoming law and costs one further incoming warmness constant.
-/

namespace Ttc.CVFiniteRetryWarmFallback

open MeasureTheory
open Arlib
open scoped ENNReal BigOperators

variable {E : Type*} [MeasurableSpace E]

/-- Generic finite-retry warmness assembly.  `accepted i` is the *unnormalised*
first-acceptance output increment at attempt `i`; `tail` is the no-acceptance
fallback sublaw. -/
theorem isWarm_sum_accepted_add_tail
    {L : Nat} {pi rho tail : Measure E} {M C : ENNReal}
    (accepted : Fin L → Measure E)
    (hrho : IsWarm M rho pi) (htail : tail ≤ rho)
    (haccepted : ∀ i, IsWarm C (accepted i) pi) :
    IsWarm ((∑ _ : Fin L, C) + M) ((∑ i, accepted i) + tail) pi := by
  exact (isWarm_sum accepted (fun _ ↦ C) pi haccepted).add
    (IsWarm.of_le htail hrho)

/-- Uniform-component specialization: `L` accepted increments, each costing
`C`, plus an `M`-warm self-fallback tail. -/
theorem isWarm_sum_accepted_add_tail_uniform
    {L : Nat} {pi rho tail : Measure E} {M C : ENNReal}
    (accepted : Fin L → Measure E)
    (hrho : IsWarm M rho pi) (htail : tail ≤ rho)
    (haccepted : ∀ i, IsWarm C (accepted i) pi) :
    IsWarm ((L : ENNReal) * C + M) ((∑ i, accepted i) + tail) pi := by
  simpa using isWarm_sum_accepted_add_tail accepted hrho htail haccepted

/-- Source-shaped cancellation package.  Once each unnormalised accepted increment
is `(C*M)`-warm, the entire self-fallback phase is `(L*C*M + M)`-warm.

This statement intentionally asks for warmness of the unnormalised increments:
there is no division by a possibly tiny survival mass in either the theorem or its
conclusion. -/
theorem isWarm_finiteRetry_selfFallback
    {L : Nat} {pi rho tail : Measure E} {M C : ENNReal}
    (accepted : Fin L → Measure E)
    (hrho : IsWarm M rho pi) (htail : tail ≤ rho)
    (haccepted : ∀ i, IsWarm (C * M) (accepted i) pi) :
    IsWarm ((L : ENNReal) * (C * M) + M)
      ((∑ i, accepted i) + tail) pi :=
  isWarm_sum_accepted_add_tail_uniform accepted hrho htail haccepted

#print axioms isWarm_sum_accepted_add_tail
#print axioms isWarm_sum_accepted_add_tail_uniform
#print axioms isWarm_finiteRetry_selfFallback

end Ttc.CVFiniteRetryWarmFallback

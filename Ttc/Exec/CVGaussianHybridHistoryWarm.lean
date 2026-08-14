import Ttc.Exec.CVRadiusAwareScaledRawWarm

/-!
# Constant-warm reference inputs for the full hybrid schedule

This packages the radius-aware hot-phase theorem in exactly the `referenceInputFamily`
shape used by `exists_gaussianHistoryReference`.  Active predecessor targets are
uniformly `2e`-warm; only the operational initial seed and the deliberately inactive
exact tail remain to be identified by the caller.
-/

set_option autoImplicit false

namespace Ttc.CVGaussianHybridHistoryWarm

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVRadiusAwareScaledRawWarm
open Ttc.CVHybridSchedule
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev GaussianScoreSeed (n : Nat) := State n × State n

noncomputable def hybridGaussianReferenceWarm : ENNReal :=
  ENNReal.ofReal (2 * Real.exp 1)

noncomputable def hybridReferenceInputFamily
    {X : Type*} [MeasurableSpace X]
    (mu0 : Measure X) (target : Nat → Measure X) : Nat → Measure X
  | 0 => mu0
  | i + 1 => target i

/-- The exact predecessor family required by retained-history induction is uniformly
`2e`-warm throughout the active hybrid schedule. -/
theorem isWarm_referenceInputFamily_hybrid
    (hn : 1 ≤ n) {m : Nat} {N s0 R : Real}
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R) (hR2 : R ^ 2 ≤ N)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (mu0 : Measure (GaussianScoreSeed n)) [IsProbabilityMeasure mu0]
    (target : Nat → Measure (GaussianScoreSeed n))
    [∀ i, IsProbabilityMeasure (target i)]
    (htarget : ∀ i, i + 1 < m →
      target i = scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m (sigmaSq n N s0) K i))
    (hstart : IsWarm hybridGaussianReferenceWarm (Measure.map Prod.snd mu0)
      (ellGaussianProb K delta (sigmaSq n N s0 0)))
    (htail : ∀ i, m ≤ i → IsWarm hybridGaussianReferenceWarm
      (Measure.map Prod.snd (hybridReferenceInputFamily mu0 target i))
      (ellGaussianProb K delta (sigmaSq n N s0 i))) :
    ∀ i, IsWarm hybridGaussianReferenceWarm
      (Measure.map Prod.snd (hybridReferenceInputFamily mu0 target i))
      (ellGaussianProb K delta (sigmaSq n N s0 i)) := by
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [hybridReferenceInputFamily, hybridGaussianReferenceWarm] using hstart
  · by_cases him : i < m
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      rw [hybridReferenceInputFamily, htarget j (by omega)]
      simpa only [hybridGaussianReferenceWarm] using
        isWarm_scoreSeedReference_hybrid_twoE hn hN hs0 hK hKc hball hfin
          hKR hR2 (by omega) hdelta hdeltan
    · exact htail i (Nat.le_of_not_gt him)

#print axioms isWarm_referenceInputFamily_hybrid

end Ttc.CVGaussianHybridHistoryWarm

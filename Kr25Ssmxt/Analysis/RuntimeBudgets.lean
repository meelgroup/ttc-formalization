import Kr25Ssmxt.Model.Constants
import Kr25Ssmxt.Analysis.CV18Admissible
import Kr25Ssmxt.Model.Run

/-! # Intermediate runtime allowances

Per-component and uniform operation allowances used inside the proof of Theorem 3. They
are not part of any public statement, so they live here rather than in `Model/`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace

namespace Kr25Ssmxt

/-- Explicit TTC CV18 query envelope obtained by inserting `ρ` into the
imported scheduled complexity rate. -/
noncomputable def TTCRuntime.theorem3CV18QueryEnvelope
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (i : Fin D.componentCount) : Nat :=
  let q := CommunityCV18.params (by omega) (D.component i) p.ε'
    (p.δ' D.componentCount) (CommunityCV18.admissibleTTCRequest D p i)
  Nat.ceil (45 * (64 *
    ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
    + 1) *
    (n : Real) ^ 3 * (TTCRuntime.theorem3Rho D) ^ 2 / (p.ε' / 2) ^ 2 *
    TTCRuntime.theorem3CV18LogEnvelope q)

/-- Uniform CV18 query cap after maximizing only its logarithmic product
over components. -/
noncomputable def TTCRuntime.theorem3CV18QueryMax
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) : Nat :=
  Nat.ceil (45 * (64 *
    ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
    + 1) *
    (n : Real) ^ 3 * (TTCRuntime.theorem3Rho D) ^ 2 / (p.ε' / 2) ^ 2 *
    TTCRuntime.theorem3CV18LogMax hn D p)

/-- Explicit logarithmic envelope for the normalized TTC sampler deadline.
The unit-ball term depends only on the dimension. -/
noncomputable def TTCRuntime.theorem3SamplerLogEnvelope
    (n b : Nat) (rho outerRadiusMax eta : Real) : Real :=
  Real.log 8 + (n : Real) * Real.log (4 * rho + 1) +
    2 * ((n : Real) * ((b : Real) * Real.log 10 + Real.log 6 +
      max 0 (Real.log outerRadiusMax)) +
      Real.log (1 + 8 / eta) +
      Real.log (1 +
        (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal))

/-- A logarithmic factor independent of decimal precision and outer radius. -/
noncomputable def TTCRuntime.theorem3SamplerLogFactor
    (n : Nat) (rho eta : Real) : Real :=
  Real.log 8 + Real.log (4 * rho + 1) +
    2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / eta) +
      Real.log (1 +
        (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal))

/-- Explicit arithmetic-operation allowance for one component of the charged
paper run. The finite sum of these allowances is proved to bound the
whole run's expected cost in `Analysis/ComponentExpectation`. -/
noncomputable def TTCRuntime.expectedComponentBudget {n : Nat}
    (hn : 21 ≤ n) (p : ApproxParams) (m b cv18NonQueryFactor : Nat)
    (P : PolytopeData n) : ENNReal :=
  let cap := TTCRuntime.sampleCap p m
  let upperIntensity := ttcPseudocode.t b n (p.Thresh m)
    (max (P.volumeClipLower p.ε')
      (P.volumeClipUpper p.ε'))
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε' (p.δ' m)) +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε' (p.δ' m) + 1) :
      ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  (Nat.clog 2 (Nat.ceil ((upperIntensity : Real) / p.Thresh m) + 1) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      (normalizedHitAndRunSteps P b p.ε') +
      TTCRuntime.appendCopyOperations)

/-- The same component allowance with decimal precision exposed linearly.
The remaining volume logarithm is the clipped geometric volume bound. -/
noncomputable def TTCRuntime.expectedComponentBudgetLinearPrecision {n : Nat}
    (hn : 21 ≤ n) (p : ApproxParams) (m b cv18NonQueryFactor : Nat)
    (P : PolytopeData n) : ENNReal :=
  let cap := TTCRuntime.sampleCap p m
  let v := max (P.volumeClipLower p.ε')
    (P.volumeClipUpper p.ε')
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε' (p.δ' m)) +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε' (p.δ' m) + 1) :
      ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  ((4 * (b * n) + Nat.clog 2 (Nat.ceil (v : Real) + 1) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      (normalizedHitAndRunSteps P b p.ε') +
      TTCRuntime.appendCopyOperations)

/-- Component budget after replacing the concrete sampler walk length by the
radius-ratio and precision envelope proved in `Analysis/NormalizedDiameterRuntime`. -/
noncomputable def TTCRuntime.expectedComponentBudgetGeometric
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) : ENNReal :=
  let P := D.component i
  let cap := TTCRuntime.sampleCap p D.componentCount
  let v := max (P.volumeClipLower p.ε')
    (P.volumeClipUpper p.ε')
  let samplerSteps := Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
    (TTCRuntime.theorem3Rho D) ^ 2 *
    TTCRuntime.theorem3SamplerLogEnvelope n b
      (TTCRuntime.theorem3Rho D)
      (TTCRuntime.theorem3OuterRadiusMax D) p.ε')
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε'
        (p.δ' D.componentCount)) +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε'
        (p.δ' D.componentCount) + 1) : ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  ((4 * (b * n) + Nat.clog 2 (Nat.ceil (v : Real) + 1) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      samplerSteps + TTCRuntime.appendCopyOperations)

/-- The same geometric allowance with the first-loop volume clip reduced to
the global outer-radius logarithm. -/
noncomputable def TTCRuntime.expectedComponentBudgetGeometricClip
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) : ENNReal :=
  let P := D.component i
  let cap := TTCRuntime.sampleCap p D.componentCount
  let samplerSteps := Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
    (TTCRuntime.theorem3Rho D) ^ 2 *
    TTCRuntime.theorem3SamplerLogEnvelope n b
      (TTCRuntime.theorem3Rho D)
      (TTCRuntime.theorem3OuterRadiusMax D) p.ε')
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε'
        (p.δ' D.componentCount)) +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε'
        (p.δ' D.componentCount) + 1) : ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  ((4 * (b * n) + (2 + n * Nat.clog 2
      (Nat.ceil (4 * TTCRuntime.theorem3OuterRadiusMax D) + 1)) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      samplerSteps + TTCRuntime.appendCopyOperations)

/-- Fully substituted per-component allowance: CV18 queries and normalized
Hit-and-Run steps use their proved polynomial-times-logarithmic envelopes. -/
noncomputable def TTCRuntime.expectedComponentBudgetTheorem3
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) : ENNReal :=
  let P := D.component i
  let cap := TTCRuntime.sampleCap p D.componentCount
  let queries := TTCRuntime.theorem3CV18QueryEnvelope hn D p i
  let samplerSteps := Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
    (TTCRuntime.theorem3Rho D) ^ 2 *
    TTCRuntime.theorem3SamplerLogEnvelope n b
      (TTCRuntime.theorem3Rho D)
      (TTCRuntime.theorem3OuterRadiusMax D) p.ε')
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount queries +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount (queries + 1) : ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  ((4 * (b * n) + (2 + n * Nat.clog 2
      (Nat.ceil (4 * TTCRuntime.theorem3OuterRadiusMax D) + 1)) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      samplerSteps + TTCRuntime.appendCopyOperations)

/-- One allowance valid for every component after taking only the maximum
facet count and maximum CV18 logarithmic product. -/
noncomputable def TTCRuntime.theorem3UniformComponentBudget
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat) :
    ENNReal :=
  let r := TTCRuntime.theorem3RMax D
  let cap := TTCRuntime.sampleCap p D.componentCount
  let queries := TTCRuntime.theorem3CV18QueryMax hn D p
  let samplerSteps := Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
    (TTCRuntime.theorem3Rho D) ^ 2 *
    TTCRuntime.theorem3SamplerLogEnvelope n b
      (TTCRuntime.theorem3Rho D)
      (TTCRuntime.theorem3OuterRadiusMax D) p.ε')
  (TTCRuntime.membershipQueryOperations n r queries +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n r (queries + 1) :
      ENNReal) +
  cap * (TTCRuntime.facetScanOperations n r + 1) +
  ((4 * (b * n) + (2 + n * Nat.clog 2
      (Nat.ceil (4 * TTCRuntime.theorem3OuterRadiusMax D) + 1)) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n r samplerSteps +
      TTCRuntime.appendCopyOperations)

end Kr25Ssmxt

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVConcreteRunwiseCapstone
import Ttc.Volume.CVRunwiseTailParameters

/-!
# Source-regime concrete runwise volume accuracy

This is the arithmetic capstone for the source branch.  It replaces the abstract
`RunwiseRadiusFourTailFits` premise of `concrete_adaptive_runwise_volume_accuracy` by the
explicit polynomial-call-envelope versus `2^(-8n)` inequality proved sufficient in
`CVRunwiseTailParameters`.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive

variable {n : Nat}

/-- Fully concrete source-regime runwise accuracy, with the fixed radius-four truncation
tail discharged by an explicit polynomial-versus-exponential inequality. -/
theorem concrete_source_adaptive_runwise_volume_accuracy
    (hn : 21 <= n)
    {K : Set (Space n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C epsilon p : Real} (hC : 0 < C) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon <= 1) (hp : 0 < p) (hp1 : p < 1)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (hsource : (1 / 2 : Real) ^ n <= epsilon / 4)
    (henvelope :
      (80 * C ^ 2 * (n : Real) ^ 2 + 3) *
          (4800 * (16 * C ^ 2 * (n : Real) ^ 2 + 3) / epsilon ^ 2) *
          (1 / 256 : Real) ^ n <= 1 / 20) :
    let eta := epsilon / 4
    let epsEst := epsilon / 4
    let s0 := polynomialEndpointSigmaSq n eta
    let J := adaptiveTerminalChunk (C ^ 2 * n) s0
    let m := adaptiveChunkOffset (C ^ 2 * n) s0 J
    let k := concreteEstimatorSamples J epsEst
    let r := concreteRunwiseReps p
    let epsMix := runwiseChosenMixError m k
    let steps := runwiseMixingSteps n (C ^ 2 * n) s0 m k
    let nu : Fin (m + 1) -> Fin k -> Measure (Space n) := fun i _ =>
      adaptiveTerminalWarmLaw (C ^ 2 * n) s0 endpointRho K steps i
    let g : Fin (m + 1) -> Fin k -> Space n -> Real := fun i _ =>
      phaseScore (m + 1) (adaptiveSigmaSq (C ^ 2 * n) s0) K i
    1 - p <=
      (runMeasure (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))).real
        {omega | medianSel (fun t =>
          (2 * Real.pi * s0) ^ ((n : Real) / 2) *
            ∏ i, oneRunPhaseAvg k g i (omega t)) ∈
          Ttc.relErr epsilon (volume K).toReal} := by
  have htail := concrete_source_runwiseRadiusFourTailFits hn hC hepsilon hepsilon1
    hsource henvelope
  apply concrete_adaptive_runwise_volume_accuracy hn hKc hKcl hKb hvol hclosedBall hfin
    hC hepsilon hepsilon1 hp hp1 hKR
  simpa only [terminalPhaseCount, terminalChunk, terminalTarget] using htail

#print axioms concrete_source_adaptive_runwise_volume_accuracy

end Ttc.CVAdaptive

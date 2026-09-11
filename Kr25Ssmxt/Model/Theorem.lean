import Kr25Ssmxt.Model.Run
import Kr25Ssmxt.Analysis.CV18HitAndRunOracles
import Kr25Ssmxt.Analysis.TTCPaperRuntime

namespace Kr25Ssmxt

/-!
# The public TTC theorems

The headline is stated for the measure-valued law of the on-disk algorithm.  The model
repairs two defects exposed by formalization: fresh Poisson counts use the multiplicative
mean `t * p`, and the invalid low-count concentration step is excluded by a public
high-intensity premise.

`Prior` exposes the remaining high-intensity Poissonized streaming theorem as a hypothesis.
The deterministic preprocessing, oracle contracts, empty case, lattice
comparison, measure normalization, and final error composition are proved in this project.
-/

/--
The concrete TTC program using the current arlib-community CV18 and finite-step
Hit-and-Run/KV97 implementations returns a probability law on single nonnegative estimates,
and its estimate is within relative error `ε` of the Lebesgue volume of the existentially
projected real solution set with probability at least `1 - δ`.  The two geometric-oracle
contracts are discharged in the proof rather than exposed as assumptions.  This is an
accuracy statement only; it makes no runtime claim.

PAPER: sections/analysis.tex:314-326
-/
theorem ttc_volume_accuracy
    (hprior : Prior)
    {n k : Nat}
    (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (prep : TTCPreprocessor n k)
    (hregime :
      let D := prep.run F hbounded
      let b := (prep.choosePrecision D params).value
      D.componentCount = 0 ∨
        params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real)) :
    MeasureTheory.IsProbabilityMeasure (communityTTC hn F hbounded params prep) ∧
      (communityTTC hn F hbounded params prep).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr params.epsilon
              (MeasureTheory.volume (solutionSet F)).toReal} ≥
        1 - params.delta := by
  exact ttc_volume_accuracy_communityCV18_hitAndRun
    hprior hn F hbounded params prep hregime

/--
The public audit-surface statement of Theorem 3 (`thm:runtime`).  For the decomposition
actually produced by TTC, the current arlib-community CV18 implementation and finite-step
Hit-and-Run/KV97 sampler produce a membership-operation certificate satisfying the paper's
`m n^5 rho^2 r_max` bound.  Here `rho` and `r_max` are the finite maxima computed from that
decomposition, and the two overheads are the finite maxima of the exact community schedule
and mixing costs after normalization by the displayed paper kernels.

In particular, the caller supplies neither query/step counts nor an oracle-cost bound.

PAPER: sections/analysis.tex:52-72
-/
theorem ttc_total_runtime_theorem3 {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k) :
    let D := prep.run F hbounded
    ∃ cert : TTCRuntime.TTCMembershipRuntimeCertificate D p,
      ∃ bounds : TTCRuntime.Theorem3OracleBounds cert
          (TTCRuntime.theorem3Rho D) (TTCRuntime.theorem3RMax D),
        (cert.operations : Real) ≤
          TTCRuntime.theorem3HeadlineCore D.componentCount n
              (TTCRuntime.theorem3RMax D) (TTCRuntime.theorem3Rho D) *
            TTCRuntime.theorem3SuppressedFactor p.epsilon
              (TTCRuntime.sampleCap p D.componentCount)
              bounds.volumeOverhead bounds.samplingOverhead := by
  exact PaperRuntime.model_ttc_total_runtime_theorem3 hn F hbounded p prep

#krModelClosureOfType ttc_total_runtime_theorem3
#krSurplusIn Kr25Ssmxt.Model from ttc_volume_accuracy ttc_total_runtime_theorem3 StreamingCoreAccuracy

/-!
The runtime statement is recursively sealed above.  The accuracy statement deliberately is
not yet passed to `#krModelClosureOfType`: `communityTTC` fixes the external implementations
through certified adapter definitions that still live under `Analysis/`.  Separating their
executable constructors into `Model/Run.lean` while leaving proof-only lemmas under
`Analysis/` is the remaining dependency-direction step required for the same recursive
statement seal on `ttc_volume_accuracy`.
-/

#print axioms ttc_volume_accuracy
#print axioms ttc_total_runtime_theorem3

end Kr25Ssmxt

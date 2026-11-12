import Kr25Ssmxt.Model.Run

/-!
# The constants in the Theorem 3 bound

The quantities the statement of Theorem 3 is written in. None of them is used by the
algorithm itself (`Model/Program.lean`, `Model/Run.lean`); they only measure its cost.

* Geometry of the decomposition: the facet bound `r_max`, the outer radius `R_max`, the
  radius ratio `ρ`, and the input-only precision scale that replaces `b`.
* The sample cap `⌈Thresh⌉` charged per component.
* The factors inherited from the concrete subroutines: the scheduled CV18 logarithmic
  product and the Hit-and-Run constant `2⁶⁸`, combined in `theorem3ParameterFactor`.
-/

noncomputable section

open MeasureTheory

namespace Kr25Ssmxt

/-! ## Geometry of the decomposition and the sample cap -/

namespace TTCRuntime

/-- Maximum number of accepted samples charged per component. -/
def sampleCap (p : ApproxParams) (componentCount : Nat) : Nat :=
  Nat.ceil (p.Thresh componentCount)

/-- The largest facet count among TTC's normalized components. -/
def theorem3RMax {n k : Nat} {F : LRAFormula n k} (D : Decomposition F) : Nat :=
  Finset.univ.sup fun i : Fin D.componentCount =>
    (D.component i).presentation.facetCount

/-- The largest outer-radius certificate used by the corrected TTC runtime
statement. The empty family has radius zero. -/
noncomputable def theorem3OuterRadiusMax {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Real :=
  ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal (D.component i).outerRadius : NNReal) : Real)

/-- The reciprocal `1 / minᵢ γᵢ` of the smallest certified inradius; zero for the
empty family. -/
noncomputable def theorem3InverseInradiusMax {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Real :=
  ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal (1 / (D.component i).inradius) : NNReal) : Real)

/-- An input-only bound on the precision `b` chosen by `getprec` at `ε / 96`:
`1 + log₁₀⁺ γ + log₁₀⁺ (1 / minᵢ γᵢ)`, with `γ` the required radius. -/
noncomputable def theorem3PrecisionBound {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : Real :=
  1 + max 0 (Real.logb 10 (latticeRadiusRequirement D p.precisionEta)) +
    max 0 (Real.logb 10 (theorem3InverseInradiusMax D))

/-- The precision scale `1 + b + log⁺ R_max` with `b` replaced by its input-only
bound. -/
noncomputable def theorem3InputScale {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : Real :=
  1 + theorem3PrecisionBound D p + max 0 (Real.log (theorem3OuterRadiusMax D))

/-- The paper's common radius ratio `ρ = maxᵢ Rᵢ / γᵢ`, protected below by one.
The `NNReal` finite supremum gives the empty decomposition the canonical value zero before
the outer maximum is applied. -/
noncomputable def theorem3Rho {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Real :=
  max 1 ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal ((D.component i).outerRadius / (D.component i).inradius) : NNReal) : Real)

end TTCRuntime

/-! ## Factors inherited from CV18 and Hit-and-Run -/


/-- The six logarithmic factors in the scheduled amplified CV18 query rate.
The exact terminal scale and block mixing error are retained. -/
noncomputable def TTCRuntime.theorem3CV18LogEnvelope
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams) : Real :=
  ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p) *
  ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.eps) ^ 2 *
  ArlibCommunity.Algorithms.CV18.protectedLog ((q.n : Real) / q.eps) ^ 2 *
  ArlibCommunity.Algorithms.CV18.protectedLog
    (ArlibCommunity.Algorithms.CV18.volumeTerminalScale q) ^ 2 *
  ArlibCommunity.Algorithms.CV18.figureOneScheduledAccuracyLog q *
  ArlibCommunity.Algorithms.CV18.protectedLog
    (1 / ArlibCommunity.Algorithms.CV18.figureOneCorrectedBlockMixingError q
      (ArlibCommunity.Algorithms.CV18.figureOneSafeRetryCount q - 1)) ^ 2

open Classical in
/-- Largest of the explicit scheduled CV18 logarithmic products across TTC's
normalized components. The empty family's value is zero. -/
noncomputable def TTCRuntime.theorem3CV18LogMax
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) : Real :=
  ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal (if h : CommunityCV18.AdmissibleCV18Request p.ε' (p.δ' D.componentCount)
      then TTCRuntime.theorem3CV18LogEnvelope
        (CommunityCV18.params (by omega) (D.component i) p.ε' (p.δ' D.componentCount) h)
      else 0) : NNReal) : Real)

/-- The explicit factors suppressed in the corrected Theorem 3 headline after
the oracle rates and the thinning counter are put on a common scale. -/
noncomputable def TTCRuntime.theorem3ParameterFactor
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) : Real :=
  45 * (64 *
      ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant + 1) *
      TTCRuntime.theorem3CV18LogMax hn D p / (p.ε' / 2) ^ 2 +
    (2 : Real) ^ 68 *
      (Real.log 8 + Real.log (4 * TTCRuntime.theorem3Rho D + 1) +
        2 * (Real.log 10 + Real.log 6 + 1 +
          Real.log (1 + 8 / p.ε') + 2)) + 20

end Kr25Ssmxt

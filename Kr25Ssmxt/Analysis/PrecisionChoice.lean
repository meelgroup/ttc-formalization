import Kr25Ssmxt.Model.Run

/-! Proof-side name for TTC's precision stage. -/

namespace Kr25Ssmxt

/-- TTC's precision stage, Algorithm `getprec` at `ε / 96`: the `choosePrecision` slot of
`communityManuscriptOracles` (definitionally). -/
noncomputable def TTCPreprocessor.choosePrecision {n k : Nat}
    (_prep : TTCPreprocessor n k) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) : PrecisionChoice D p :=
  getPrecisionChoice D p

end Kr25Ssmxt

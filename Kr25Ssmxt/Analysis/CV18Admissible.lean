import Kr25Ssmxt.Model.Run

/-! Every CV18 call TTC makes is within CV18's parameter domain. -/

namespace Kr25Ssmxt

namespace CommunityCV18

/-- Every component request made by TTC is within the imported CV18
parameter domain. -/
theorem admissibleTTCRequest {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (i : Fin D.componentCount) :
    AdmissibleCV18Request p.ε' (p.δ' D.componentCount) := by
  have hcount : 0 < D.componentCount := lt_of_le_of_lt (Nat.zero_le i) i.isLt
  have hdenom : 0 < (4 * D.componentCount : Real) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 4) hcount
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact div_pos p.epsilon_pos (by norm_num)
  · dsimp only [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  · exact div_pos p.delta_pos hdenom
  · dsimp only [ApproxParams.δ']
    rw [div_le_iff₀ hdenom]
    have hcountR : (1 : Real) ≤ D.componentCount := by exact_mod_cast hcount
    nlinarith [p.delta_le_one]

end CommunityCV18

end Kr25Ssmxt

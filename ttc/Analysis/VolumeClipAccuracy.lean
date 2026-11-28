import ttc.Analysis.OracleContracts
import ttc.Analysis.MathlibCompat
import ttc.Analysis.ComponentExpectation

/-! The unclipped CV18 volume law meets the `ComputeVolume` contract. -/

namespace ttc

open MeasureTheory

theorem community_volume_contract_of_cv18
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams) :
    ComputeVolumeContract (ttcSubroutines hn prep)
      F hbounded p := by
  let D := prep.run F hbounded
  intro i
  have hn3 : 3 ≤ n := by omega
  have hspec := CommunityCV18.communityCV18VolumeLaw_spec
    hn3 (D.component i) p.ε'
    (p.δ' D.componentCount)
    (PaperRuntime.ttc_request_admissible D p i)
  simpa only [ttcSubroutines, D] using hspec

end ttc

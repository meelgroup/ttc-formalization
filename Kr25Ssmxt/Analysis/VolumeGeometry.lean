import Kr25Ssmxt.Analysis.OracleContracts
import Kr25Ssmxt.Analysis.VolumeClipAccuracy
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The geometric volume envelope of a component, and the `ComputeVolume` contract. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem community_volume_contract
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams) :
    ComputeVolumeContract (ttcSubroutines hn prep)
      F hbounded p := by
  exact community_volume_contract_of_cv18 hn prep F hbounded p

end Kr25Ssmxt

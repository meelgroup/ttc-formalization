import ttc.Analysis.PrecisionChoice
import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.PrecisionAdequateSplit
import ttc.Analysis.OriginVolumeFold
import ttc.Analysis.OracleNormalization

/-! Equip each preprocessed component with the geometric sampling route and
the normalized CV18 volume law. -/

namespace ttc

open MeasureTheory

noncomputable def communityCertifiedComponents
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k) :
    List (OriginCertifiedComponent n k hn prep
      (prep.choosePrecision D p).value p.ε'
      (p.δ' D.componentCount)) := by
  let choice := prep.choosePrecision D p
  let b := choice.value
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have heta0 : 0 < p.ε' :=
    div_pos p.epsilon_pos (by norm_num)
  have heta1 : p.ε' ≤ 1 := by
    dsimp only [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  exact List.ofFn (fun i : Fin D.componentCount =>
    { polytope := D.component i
      route := by
        have hset := coded_lattice_points_finite_nonempty hn0 D p b
          choice.adequate i
        have hunit : samplerRadiusRequirement (D.component i) p.ε' ≤
            decimalScale b * (D.component i).inradius :=
          (le_max_right _ _).trans (choice.adequate.split i)
        exact ⟨hunit, heta0, heta1, hset.1, hset.2⟩
      volumeProbability :=
        community_volume_isProbabilityMeasure hn D p prep i })

theorem communityCertifiedComponents_polytope
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k) :
    (communityCertifiedComponents hn D p prep).map
      (fun d => d.polytope) = List.ofFn D.component := by
  simp [communityCertifiedComponents]
  funext i
  rfl

set_option maxHeartbeats 1000000 in
theorem communityCertifiedRun_map_state
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k) :
    let b := (prep.choosePrecision D p).value
    let threshold := p.Thresh D.componentCount
    (communityOriginComponentsLaw hn prep b p.ε'
      (p.δ' D.componentCount) threshold
      (communityCertifiedComponents hn D p prep)
      (OriginConfiguration.initial n)).map
        (fun next : OriginConfiguration n => next.state) =
    ttcReference.loop (ttcSubroutines hn prep)
      b p.ε' (p.δ' D.componentCount) threshold
      (List.ofFn D.component) (TTCState.unitInitial n) := by
  dsimp only
  rw [communityOriginComponentsLaw_map_state hn prep
    (prep.choosePrecision D p).value p.ε'
    (p.δ' D.componentCount) (p.Thresh D.componentCount)
    (p.threshold_pos D.componentCount)
    (communityCertifiedComponents hn D p prep)
    (OriginConfiguration.initial n)]
  rw [communityCertifiedComponents_polytope]
  rfl

end ttc

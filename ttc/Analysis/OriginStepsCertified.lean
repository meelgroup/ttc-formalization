import ttc.Analysis.PrecisionChoice
import ttc.Analysis.OriginGivenVolumesFold
import ttc.Analysis.ConcreteFixedLevelBounds
import ttc.Analysis.OriginCertifiedRun

/-! The fixed-level steps produced by the ghost fold over the certified
component list are exactly the certified fixed-level steps. -/

namespace ttc

open Classical MeasureTheory

/-- One ghost-fold step for a certified component and its volume outcome. -/
noncomputable def originGivenVolumesStep
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real)
    (S : Finset (LatticePoint n)) (level : Nat)
    (d : OriginCertifiedComponent n k hn prep b eta delta)
    (o : VolumeOutcome) : FixedLevelStep S :=
  { deleted := componentDeletedCodes S d.polytope
    incoming := fun x => Real.toNNReal
      ((normalizedHitAndRunPointLaw hn d.polytope b eta d.route.1
        d.route.2.1 d.route.2.2.1 d.route.2.2.2.1
          d.route.2.2.2.2).real {(x : LatticePoint n)} *
        ((unitInterval.toNNReal (survivalProbability level) *
          ttcReference.t b n threshold o.2 : NNReal) : Real)) }

theorem originGivenVolumesSteps_eq_ofFn_get
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real)
    (S : Finset (LatticePoint n)) (level : Nat) :
    ∀ (l : List (OriginCertifiedComponent n k hn prep b eta delta))
      (outcomes : Fin l.length → VolumeOutcome),
    originGivenVolumesSteps hn prep b eta delta threshold S level
        l outcomes =
      List.ofFn (fun i => originGivenVolumesStep hn prep b eta delta
        threshold S level (l.get i) (outcomes i))
  | [], _ => rfl
  | d :: rest, outcomes => by
      rw [List.ofFn_succ, originGivenVolumesSteps,
        originGivenVolumesSteps_eq_ofFn_get hn prep b eta delta
          threshold S level rest]
      rfl

theorem communityCertifiedComponents_length
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k) :
    (communityCertifiedComponents hn D p prep).length =
      D.componentCount := by
  unfold communityCertifiedComponents
  simp

theorem community_givenVolumesSteps_eq_certified
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k)
    (S : Finset (LatticePoint n)) (level : Nat)
    (outcomes : Fin (communityCertifiedComponents hn D p prep).length →
      VolumeOutcome) :
    originGivenVolumesSteps hn prep (prep.choosePrecision D p).value
        p.ε' (p.δ' D.componentCount)
        (p.Thresh D.componentCount) S level
        (communityCertifiedComponents hn D p prep) outcomes =
      certifiedFixedLevelSteps D (prep.choosePrecision D p).value S
        (p.Thresh D.componentCount)
        (fun i => (outcomes (Fin.cast
          (communityCertifiedComponents_length hn D p prep).symm
            i)).2)
        (communityPointLaw hn D p (prep.choosePrecision D p).value
          (prep.choosePrecision D p).adequate)
        (1 / (2 : NNReal) ^ level) := by
  rw [originGivenVolumesSteps_eq_ofFn_get,
    List.ofFn_congr (communityCertifiedComponents_length hn D p prep)]
  unfold certifiedFixedLevelSteps fixedLevelComponentSteps
  congr 1
  funext i
  have hrate : unitInterval.toNNReal (survivalProbability level) =
      1 / (2 : NNReal) ^ level := by
    apply NNReal.coe_injective
    rw [unitInterval.coe_toNNReal]
    simp [survivalProbability]
  simp only [originGivenVolumesStep, hrate, mul_comm (1 / (2 : NNReal) ^ level)]
  unfold communityCertifiedComponents communityPointLaw
  simp only [List.get_ofFn]
  rfl

end ttc

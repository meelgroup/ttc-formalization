import Kr25Ssmxt.Analysis.ManuscriptOriginGivenVolumesFold
import Kr25Ssmxt.Analysis.ManuscriptConcreteFixedLevelBounds
import Kr25Ssmxt.Analysis.ManuscriptOriginCertifiedRun

/-! The fixed-level steps produced by the ghost fold over the certified
component list are exactly the certified fixed-level steps. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

/-- One ghost-fold step for a certified component and its volume outcome. -/
noncomputable def manuscriptOriginGivenVolumesStep
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real)
    (S : Finset (LatticePoint n)) (level : Nat)
    (d : ManuscriptOriginCertifiedComponent n k hn prep b eta delta)
    (o : VolumeOutcome) : FixedLevelStep S :=
  { deleted := componentDeletedCodes S d.polytope
    incoming := fun x => Real.toNNReal
      ((normalizedHitAndRunPointLaw hn d.polytope b d.route.1 eta
        d.route.2.1 d.route.2.2.1 d.route.2.2.2.1
          d.route.2.2.2.2).real {(x : LatticePoint n)} *
        ((unitInterval.toNNReal (survivalProbability level) *
          manuscriptIntensity b n threshold o.2 : NNReal) : Real)) }

theorem manuscriptOriginGivenVolumesSteps_eq_ofFn_get
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real)
    (S : Finset (LatticePoint n)) (level : Nat) :
    ∀ (l : List (ManuscriptOriginCertifiedComponent n k hn prep b eta delta))
      (outcomes : Fin l.length → VolumeOutcome),
    manuscriptOriginGivenVolumesSteps hn prep b eta delta threshold S level
        l outcomes =
      List.ofFn (fun i => manuscriptOriginGivenVolumesStep hn prep b eta delta
        threshold S level (l.get i) (outcomes i))
  | [], _ => rfl
  | d :: rest, outcomes => by
      rw [List.ofFn_succ, manuscriptOriginGivenVolumesSteps,
        manuscriptOriginGivenVolumesSteps_eq_ofFn_get hn prep b eta delta
          threshold S level rest]
      rfl

theorem communityManuscriptCertifiedComponents_length
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k) :
    (communityManuscriptCertifiedComponents hn D p prep).length =
      D.componentCount := by
  unfold communityManuscriptCertifiedComponents
  simp

theorem communityManuscript_givenVolumesSteps_eq_certified
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k)
    (S : Finset (LatticePoint n)) (level : Nat)
    (outcomes : Fin (communityManuscriptCertifiedComponents hn D p prep).length →
      VolumeOutcome) :
    manuscriptOriginGivenVolumesSteps hn prep (prep.choosePrecision D p).value
        p.epsilonPrime (p.deltaPrime D.componentCount)
        (p.threshold D.componentCount) S level
        (communityManuscriptCertifiedComponents hn D p prep) outcomes =
      manuscriptCertifiedFixedLevelSteps D (prep.choosePrecision D p).value S
        (p.threshold D.componentCount)
        (fun i => (outcomes (Fin.cast
          (communityManuscriptCertifiedComponents_length hn D p prep).symm
            i)).2)
        (communityManuscriptPointLaw hn D p (prep.choosePrecision D p).value
          (prep.choosePrecision D p).adequate)
        (1 / (2 : NNReal) ^ level) := by
  rw [manuscriptOriginGivenVolumesSteps_eq_ofFn_get,
    List.ofFn_congr (communityManuscriptCertifiedComponents_length hn D p prep)]
  unfold manuscriptCertifiedFixedLevelSteps fixedLevelComponentSteps
  congr 1
  funext i
  have hrate : unitInterval.toNNReal (survivalProbability level) =
      1 / (2 : NNReal) ^ level := by
    apply NNReal.coe_injective
    rw [unitInterval.coe_toNNReal]
    simp [survivalProbability]
  simp only [manuscriptOriginGivenVolumesStep, hrate, mul_comm (1 / (2 : NNReal) ^ level)]
  unfold communityManuscriptCertifiedComponents communityManuscriptPointLaw
  simp only [List.get_ofFn]
  rfl

end Kr25Ssmxt

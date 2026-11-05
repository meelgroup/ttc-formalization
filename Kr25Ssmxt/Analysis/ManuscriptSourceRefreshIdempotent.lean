import Kr25Ssmxt.Analysis.ManuscriptOriginMeasurable
import Kr25Ssmxt.Analysis.ManuscriptVolumeTrace

/-! Replacing the unused source tail twice at the same observed level has
exactly the law of replacing it once. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem ManuscriptOriginConfiguration.observedRepresentative_refreshLaw
    {n : Nat} (c : ManuscriptOriginConfiguration n) :
    c.observedRepresentative.refreshLaw = c.refreshLaw := by
  unfold ManuscriptOriginConfiguration.refreshLaw
  rw [c.observedRepresentative_refreshFuture_fun]

theorem ManuscriptOriginConfiguration.refreshLaw_idempotent
    {n : Nat} (c : ManuscriptOriginConfiguration n) :
    c.refreshLaw.bind
      (fun next : ManuscriptOriginConfiguration n => next.refreshLaw) =
    c.refreshLaw := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  have hkernel : Measurable
      (fun next : ManuscriptOriginConfiguration n => next.refreshLaw) :=
    measurable_manuscriptOriginConfiguration_refreshLaw
  calc
    c.refreshLaw.bind
        (fun next : ManuscriptOriginConfiguration n => next.refreshLaw) =
      sourceLaw.bind (fun first => (c.refreshFuture first).refreshLaw) := by
        exact bind_mapped_measure sourceLaw c.refreshFuture
          c.measurable_refreshFuture _ hkernel
    _ = sourceLaw.bind (fun _ => c.refreshLaw) := by
      congr 1
      funext first
      unfold ManuscriptOriginConfiguration.refreshLaw
      congr 1
      funext second
      exact c.refreshFuture_twice first second
    _ = c.refreshLaw := by
      rw [Measure.bind_const, measure_univ, one_smul]

/-- The refresh kernel is a projection on arbitrary ghost laws. -/
theorem manuscriptOrigin_refreshLaw_projector
    {n : Nat} (μ : Measure (ManuscriptOriginConfiguration n)) :
    (μ.bind (fun c => c.refreshLaw)).bind
      (fun c => c.refreshLaw) =
    μ.bind (fun c => c.refreshLaw) := by
  have hkernel : Measurable
      (fun c : ManuscriptOriginConfiguration n => c.refreshLaw) :=
    measurable_manuscriptOriginConfiguration_refreshLaw
  rw [Measure.bind_bind hkernel.aemeasurable hkernel.aemeasurable]
  congr 1
  funext c
  exact c.refreshLaw_idempotent

end Kr25Ssmxt

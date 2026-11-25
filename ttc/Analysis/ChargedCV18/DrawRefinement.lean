/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18

/-!
# Refining a point draw into random numbers

`cv18Program` draws its random points the way a real-RAM machine does: a ball-walk
proposal from a standard Gaussian vector and a uniform number, and the starting point
from a standard Gaussian vector, each pushed through counted arithmetic.  The program
the accuracy proof was developed against draws the same points directly from their laws
(`uniformBall`, `initialGaussianLaw`).

`Refines p p'` says that `p'` is `p` with some point draws `μ` replaced by draws from
`ν` (and `ρ`) pushed through a measurable `f`, where `μ` is the law of the pushed point.
Such a replacement keeps the output law whenever `p` is measurable in the sense the
accuracy proof already establishes (`Refines.runEstimate_eq`), and it can only lower the
worst-case number of membership queries (`Refines.queryCost_le`).
-/

open MeasureTheory

namespace ttc.ChargedCV18

open ArlibCommunity.Algorithms.CV18
open MembershipOracleProgram

section Refinement

/-- `p'` is `p` with some point draws replaced by draws that produce the same law. -/
inductive Refines {n : ℕ} {α : Type} :
    MembershipOracleProgram n α → MembershipOracleProgram n α → Prop where
  | pure (r : α) : Refines (.pure r) (.pure r)
  | query (x : AmbientSpace n) {k k' : Bool → MembershipOracleProgram n α}
      (h : ∀ b, Refines (k b) (k' b)) : Refines (.query x k) (.query x k')
  | randomNat (law : PMF ℕ) {k k' : ℕ → MembershipOracleProgram n α}
      (h : ∀ s, Refines (k s) (k' s)) : Refines (.randomNat law k) (.randomNat law k')
  | randomPoint (law : Measure (AmbientSpace n)) (hlaw : IsProbabilityMeasure law)
      {k k' : AmbientSpace n → MembershipOracleProgram n α}
      (h : ∀ y, Refines (k y) (k' y)) :
      Refines (.randomPoint law hlaw k) (.randomPoint law hlaw k')
  | randomReal (law : Measure ℝ) (hlaw : IsProbabilityMeasure law)
      {k k' : ℝ → MembershipOracleProgram n α}
      (h : ∀ v, Refines (k v) (k' v)) :
      Refines (.randomReal law hlaw k) (.randomReal law hlaw k')
  /-- A point draw from `μ` becomes a draw `g` from `ν` and `u` from `ρ`, then `f (g, u)`. -/
  | split (μ : Measure (AmbientSpace n)) (hμ : IsProbabilityMeasure μ)
      (ν : Measure (AmbientSpace n)) (hν : IsProbabilityMeasure ν)
      (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ)
      (f : AmbientSpace n × ℝ → AmbientSpace n) (hf : Measurable f)
      (heq : μ = (ν.prod ρ).map f)
      {k k' : AmbientSpace n → MembershipOracleProgram n α}
      (h : ∀ y, Refines (k y) (k' y)) :
      Refines (.randomPoint μ hμ k)
        (.randomPoint ν hν fun g => .randomReal ρ hρ fun u => k' (f (g, u)))
  /-- A point draw from `μ` becomes a draw `g` from `ν`, then `f g`. -/
  | push (μ : Measure (AmbientSpace n)) (hμ : IsProbabilityMeasure μ)
      (ν : Measure (AmbientSpace n)) (hν : IsProbabilityMeasure ν)
      (f : AmbientSpace n → AmbientSpace n) (hf : Measurable f) (heq : μ = ν.map f)
      {k k' : AmbientSpace n → MembershipOracleProgram n α}
      (h : ∀ y, Refines (k y) (k' y)) :
      Refines (.randomPoint μ hμ k) (.randomPoint ν hν fun g => k' (f g))

variable {n : ℕ} {α β : Type}

theorem Refines.refl : ∀ p : MembershipOracleProgram n α, Refines p p
  | .pure r => .pure r
  | .query x k => .query x fun b => Refines.refl (k b)
  | .randomNat law k => .randomNat law fun s => Refines.refl (k s)
  | .randomPoint law h k => .randomPoint law h fun y => Refines.refl (k y)
  | .randomReal law h k => .randomReal law h fun v => Refines.refl (k v)

theorem Refines.of_eq {p p' : MembershipOracleProgram n α} (h : p = p') : Refines p p' :=
  h ▸ Refines.refl p

/-- Refinement is preserved by sequential composition. -/
theorem Refines.bind {p p' : MembershipOracleProgram n α}
    {f f' : α → MembershipOracleProgram n β} (hp : Refines p p')
    (hf : ∀ a, Refines (f a) (f' a)) : Refines (p.bind f) (p'.bind f') := by
  induction hp with
  | pure r => exact hf r
  | query x h ih => exact .query x ih
  | randomNat law h ih => exact .randomNat law ih
  | randomPoint law hlaw h ih => exact .randomPoint law hlaw ih
  | randomReal law hlaw h ih => exact .randomReal law hlaw ih
  | split μ hμ ν hν ρ hρ g hg heq h ih => exact .split μ hμ ν hν ρ hρ g hg heq ih
  | push μ hμ ν hν g hg heq h ih => exact .push μ hμ ν hν g hg heq ih

/-- Refinement is preserved by the global query cap. -/
theorem Refines.withQueryCap {p p' : MembershipOracleProgram n α} (hp : Refines p p')
    (budget : ℕ) : Refines (p.withQueryCap budget) (p'.withQueryCap budget) := by
  induction hp generalizing budget with
  | pure r => exact .pure _
  | query x h ih =>
      cases budget with
      | zero => exact .pure _
      | succ budget => exact .query x fun b => ih b budget
  | randomNat law h ih => exact .randomNat law fun s => ih s budget
  | randomPoint law hlaw h ih => exact .randomPoint law hlaw fun y => ih y budget
  | randomReal law hlaw h ih => exact .randomReal law hlaw fun v => ih v budget
  | split μ hμ ν hν ρ hρ g hg heq h ih =>
      exact .split μ hμ ν hν ρ hρ g hg heq fun y => ih y budget
  | push μ hμ ν hν g hg heq h ih => exact .push μ hμ ν hν g hg heq fun y => ih y budget

/-- **Refining can only lower the worst-case query count.** -/
theorem Refines.queryCost_le {p p' : MembershipOracleProgram n α} (hp : Refines p p') :
    p'.queryCost ≤ p.queryCost := by
  induction hp with
  | pure r => exact le_rfl
  | query x h ih =>
      simp only [queryCost]
      exact add_le_add le_rfl (iSup_mono ih)
  | randomNat law h ih => exact iSup_mono ih
  | randomPoint law hlaw h ih => exact iSup_mono ih
  | randomReal law hlaw h ih => exact iSup_mono ih
  | split μ hμ ν hν ρ hρ g hg heq h ih =>
      simp only [queryCost]
      exact iSup_le fun a => iSup_le fun b => le_iSup_of_le (g (a, b)) (ih _)
  | push μ hμ ν hν g hg heq h ih =>
      simp only [queryCost]
      exact iSup_le fun a => le_iSup_of_le (g a) (ih _)

/-- Binding a pushforward of a product: `((ν ⊗ ρ).map f).bind R` draws `g`, then `u`. -/
theorem bind_map_prod {γ : Type} [MeasurableSpace γ] (ν : Measure (AmbientSpace n))
    [IsProbabilityMeasure ν] (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f : AmbientSpace n × ℝ → AmbientSpace n) (hf : Measurable f)
    (R : AmbientSpace n → Measure γ) (hR : Measurable R) :
    ((ν.prod ρ).map f).bind R = ν.bind fun g => ρ.bind fun u => R (f (g, u)) := by
  have hRf : Measurable fun ω : AmbientSpace n × ℝ => R (f ω) := hR.comp hf
  have hinner : ∀ g, Measurable fun u : ℝ => R (f (g, u)) := fun g =>
    hRf.comp (measurable_prodMk_left)
  have hG : Measurable fun g => ρ.bind fun u => R (f (g, u)) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.bind_apply hs (hinner _).aemeasurable]
    exact ((Measure.measurable_coe hs).comp hRf).lintegral_prod_right'
  ext s hs
  have hRs : Measurable fun y => R y s := (Measure.measurable_coe hs).comp hR
  rw [Measure.bind_apply hs hR.aemeasurable, Measure.bind_apply hs hG.aemeasurable,
    lintegral_map hRs hf,
    lintegral_prod (fun ω => R (f ω) s)
      (((Measure.measurable_coe hs).comp hRf).aemeasurable)]
  refine lintegral_congr fun g => ?_
  rw [Measure.bind_apply hs (hinner g).aemeasurable]

/-- Binding a pushforward: `(ν.map f).bind R = ν.bind (R ∘ f)`. -/
theorem bind_map' {γ : Type} [MeasurableSpace γ] (ν : Measure (AmbientSpace n))
    (f : AmbientSpace n → AmbientSpace n) (hf : Measurable f)
    (R : AmbientSpace n → Measure γ) (hR : Measurable R) :
    (ν.map f).bind R = ν.bind fun g => R (f g) := by
  ext s hs
  have hRs : Measurable fun y => R y s := (Measure.measurable_coe hs).comp hR
  rw [Measure.bind_apply hs hR.aemeasurable, lintegral_map hRs hf,
    Measure.bind_apply hs (f := fun g => R (f g)) (hR.comp hf).aemeasurable]

/-- **Refining keeps the output law** of a program that is measurable in the sense of the
accuracy proof. -/
theorem Refines.runEstimate_eq [MeasurableSpace α] (oracle : AmbientSpace n → Bool)
    {p p' : MembershipOracleProgram n α} (hp : Refines p p')
    (hmeas : p.StronglyMeasurable oracle) :
    p'.runEstimate oracle = p.runEstimate oracle := by
  induction hp with
  | pure r => rfl
  | query x h ih => exact ih _ hmeas
  | randomNat law h ih =>
      simp only [runEstimate]
      congr 1
      funext s
      exact ih s (hmeas.2 s)
  | randomPoint law hlaw h ih =>
      simp only [runEstimate]
      congr 1
      funext y
      exact ih y (hmeas.2 y)
  | randomReal law hlaw h ih =>
      simp only [runEstimate]
      congr 1
      funext v
      exact ih v (hmeas.2 v)
  | split μ hμ ν hν ρ hρ g hg heq h ih =>
      simp only [runEstimate]
      have hk : ∀ y, (_ : MembershipOracleProgram n α).runEstimate oracle = _ :=
        fun y => ih y (hmeas.2 y)
      simp_rw [hk, heq]
      exact (bind_map_prod ν ρ g hg _ hmeas.1).symm
  | push μ hμ ν hν g hg heq h ih =>
      simp only [runEstimate]
      have hk : ∀ y, (_ : MembershipOracleProgram n α).runEstimate oracle = _ :=
        fun y => ih y (hmeas.2 y)
      simp_rw [hk, heq]
      exact (bind_map' ν g hg _ hmeas.1).symm

end Refinement

end ttc.ChargedCV18

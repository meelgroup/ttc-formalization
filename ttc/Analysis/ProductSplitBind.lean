import ttc.Analysis.MathlibCompat
import ttc.Analysis.CostedMeasureMonad
import ttc.Analysis.VolumeTrace

/-! A law whose observation is independent of a tail with a fixed law keeps
this product split under arbitrary measurable mixtures. -/

namespace ttc

open MeasureTheory

/-- Mixing the first factor of a product with a fixed second factor. -/
theorem measure_bind_prod_const
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (M : Measure α) (κ : α → Measure β) (hκ : Measurable κ)
    (ν : Measure γ) [SFinite ν] :
    M.bind (fun a => (κ a).prod ν) = (M.bind κ).prod ν := by
  have hinner : Measurable (fun b : β => ν.map (Prod.mk b)) :=
    Measurable.map_prodMk_left
  have hfun : (fun a => (κ a).prod ν) =
      fun a => (κ a).bind (fun b => ν.map (Prod.mk b)) := by
    funext a
    rw [Measure.prod_eq_bind_map]
  rw [hfun, Measure.prod_eq_bind_map, Measure.bind_bind hκ.aemeasurable
    hinner.aemeasurable]

/-- The observation of a law is independent of a tail with law `ν`. -/
def ProductSplit {X O T : Type*}
    [MeasurableSpace X] [MeasurableSpace O] [MeasurableSpace T]
    (obs : X → O) (tail : X → T) (ν : Measure T) (ρ : Measure X) : Prop :=
  ρ.map (fun x => (obs x, tail x)) = (ρ.map obs).prod ν

theorem ProductSplit.bind
    {α X O T : Type*}
    [MeasurableSpace α] [MeasurableSpace X] [MeasurableSpace O]
    [MeasurableSpace T]
    {obs : X → O} {tail : X → T} {ν : Measure T} [SFinite ν]
    (hobs : Measurable obs) (htail : Measurable tail)
    (M : Measure α) (K : α → Measure X) (hK : Measurable K)
    (hsplit : ∀ a, ProductSplit obs tail ν (K a)) :
    ProductSplit obs tail ν (M.bind K) := by
  unfold ProductSplit at hsplit ⊢
  have hobsK : Measurable (fun a => (K a).map obs) :=
    (Measure.measurable_map obs hobs).comp hK
  rw [map_bind_measure M K _ hK.aemeasurable (hobs.prodMk htail),
    map_bind_measure M K obs hK.aemeasurable hobs]
  calc
    M.bind (fun a => (K a).map (fun x => (obs x, tail x))) =
        M.bind (fun a => ((K a).map obs).prod ν) := by
      congr 1
      funext a
      exact hsplit a
    _ = (M.bind (fun a => (K a).map obs)).prod ν :=
      measure_bind_prod_const M (fun a => (K a).map obs) hobsK ν

/-- Pushing a law with a known product split through a pair of maps, one
reading only the observation and one only the tail. -/
theorem ProductSplit.of_map_factor
    {Y A B X O T : Type*}
    [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace O] [MeasurableSpace T]
    (μ : Measure Y) [IsFiniteMeasure μ] (lam : Measure B) [SFinite lam]
    (a : Y → A) (b : Y → B) (ha : Measurable a) (hb : Measurable b)
    (hab : μ.map (fun y => (a y, b y)) = (μ.map a).prod lam)
    (f : Y → X) (obs : X → O) (tail : X → T)
    (Ψ : A → O) (Φ : B → T) (hΨ : Measurable Ψ) (hΦ : Measurable Φ)
    (hobs : Measurable obs) (htail : Measurable tail) (hf : Measurable f)
    (hobsEq : ∀ᵐ y ∂μ, obs (f y) = Ψ (a y))
    (htailEq : ∀ y, tail (f y) = Φ (b y)) :
    ProductSplit obs tail (lam.map Φ) (μ.map f) := by
  unfold ProductSplit
  rw [Measure.map_map (hobs.prodMk htail) hf, Measure.map_map hobs hf]
  have hleft : μ.map ((fun x => (obs x, tail x)) ∘ f) =
      μ.map (fun y => (Ψ (a y), Φ (b y))) := by
    apply Measure.map_congr
    filter_upwards [hobsEq] with y hy
    simp only [Function.comp_apply, hy, htailEq y]
  have hright : μ.map (obs ∘ f) = μ.map (fun y => Ψ (a y)) := by
    apply Measure.map_congr
    filter_upwards [hobsEq] with y hy
    simp only [Function.comp_apply, hy]
  rw [hleft, hright]
  have hpair : Measurable (fun y => (a y, b y)) := ha.prodMk hb
  calc
    μ.map (fun y => (Ψ (a y), Φ (b y))) =
        (μ.map (fun y => (a y, b y))).map (Prod.map Ψ Φ) := by
      rw [Measure.map_map (hΨ.prodMap hΦ) hpair]
      rfl
    _ = ((μ.map a).prod lam).map (Prod.map Ψ Φ) := by rw [hab]
    _ = ((μ.map a).map Ψ).prod (lam.map Φ) :=
      (Measure.map_prod_map (μ.map a) lam hΨ hΦ).symm
    _ = (μ.map (fun y => Ψ (a y))).prod (lam.map Φ) := by
      rw [Measure.map_map hΨ ha]
      rfl

end ttc

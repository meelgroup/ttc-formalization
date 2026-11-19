import ttc.Analysis.MathlibCompat
import ttc.Analysis.CoinLabelMergeLaw

/-! At fixed shifts, replacing one component of a global fair source by an
independent fair stream and shifting all rows still gives a global fair
source. The adaptive shift will be handled by stopped-prefix independence. -/

namespace ttc

open MeasureTheory

theorem combinedTail_fixedShift_law
    (component oldShift newShift : Nat) :
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw).map
      (fun z index =>
        if index.1 = component then
          z.2 (newShift + index.2.1, index.2.2)
        else
          z.1 (index.1, (oldShift + index.2.1, index.2.2))) =
    Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let global : Measure (Fin 2 × (Nat × (Nat × Nat)) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  have hnew : sourceLaw.map
      (fun src => fun pair : Nat × Nat => src (component, pair)) =
      fairCoinStreamLaw := by
    exact @Measure.map_infinitePi_infinitePi_of_inj
      (Nat × (Nat × Nat)) (Nat × Nat) (fun _ => Bool)
      (fun _ => inferInstance) (fun _ => fairCoinLaw)
      (fun _ => fairCoinLaw_isProbabilityMeasure)
      (fun pair => (component, pair))
      (by intro a b hab; exact congrArg Prod.snd hab)
  have hpair : global.map (fun coins =>
      ((fun index => coins (0, index)),
        (fun pair => coins (1, (component, pair))))) =
      sourceLaw.prod fairCoinStreamLaw := by
    have hcurry : global.map
        (MeasurableEquiv.curry (Fin 2) (Nat × (Nat × Nat)) Bool) =
        Measure.infinitePi (fun _ : Fin 2 => sourceLaw) := by
      exact Measure.infinitePi_map_curry
        (hμ := fun _ _ => fairCoinLaw_isProbabilityMeasure)
        (fun _ : Fin 2 => fun _ : Nat × (Nat × Nat) => fairCoinLaw)
    have htwo :
        (Measure.infinitePi (fun _ : Fin 2 => sourceLaw)).map
          MeasurableEquiv.finTwoArrow =
        sourceLaw.prod sourceLaw := by
      rw [Measure.infinitePi_eq_pi]
      exact (measurePreserving_finTwoArrow sourceLaw).map_eq
    have hbase : global.map (fun coins =>
        ((fun index => coins (0, index)),
          (fun index => coins (1, index)))) =
        sourceLaw.prod sourceLaw := by
      calc
        _ = (global.map
            (MeasurableEquiv.curry (Fin 2)
              (Nat × (Nat × Nat)) Bool)).map
              MeasurableEquiv.finTwoArrow := by
                rw [Measure.map_map
                  MeasurableEquiv.finTwoArrow.measurable
                  (MeasurableEquiv.curry (Fin 2)
                    (Nat × (Nat × Nat)) Bool).measurable]
                congr 1
        _ = _ := by rw [hcurry, htwo]
    let restrict : (Nat × (Nat × Nat) → Bool) →
        Nat × Nat → Bool :=
      fun src pair => src (component, pair)
    have hrestrict : Measurable restrict :=
      Measurable.of_eval (fun pair =>
        measurable_pi_apply (component, pair))
    have hbaseMap : Measurable
        (fun coins : Fin 2 × (Nat × (Nat × Nat)) → Bool =>
          ((fun index => coins (0, index)),
            (fun index => coins (1, index)))) := by fun_prop
    have hprodMap : Measurable
        (Prod.map (id : (Nat × (Nat × Nat) → Bool) →
          (Nat × (Nat × Nat) → Bool)) restrict) := by
      exact measurable_fst.prodMk (hrestrict.comp measurable_snd)
    calc
      global.map (fun coins =>
          ((fun index => coins (0, index)),
            (fun pair => coins (1, (component, pair))))) =
        (global.map (fun coins =>
          ((fun index => coins (0, index)),
            (fun index => coins (1, index))))).map
            (Prod.map id restrict) := by
              rw [Measure.map_map hprodMap hbaseMap]
              rfl
      _ = (sourceLaw.prod sourceLaw).map (Prod.map id restrict) := by
        rw [hbase]
      _ = (sourceLaw.map id).prod (sourceLaw.map restrict) := by
        exact (Measure.map_prod_map sourceLaw sourceLaw measurable_id
          hrestrict).symm
      _ = _ := by rw [Measure.map_id, hnew]
  let index : Nat × (Nat × Nat) →
      Fin 2 × (Nat × (Nat × Nat)) := fun tag =>
    if tag.1 = component then
      (1, (component, (newShift + tag.2.1, tag.2.2)))
    else
      (0, (tag.1, (oldShift + tag.2.1, tag.2.2)))
  have hinj : Function.Injective index := by
    intro a b hab
    by_cases ha : a.1 = component <;> by_cases hb : b.1 = component
    · simp only [index, ha, hb, ite_true, Prod.mk.injEq] at hab
      apply Prod.ext
      · exact ha.trans hb.symm
      · apply Prod.ext
        · omega
        · exact hab.2.2.2
    · simp [index, ha, hb] at hab
    · simp [index, ha, hb] at hab
    · simp only [index, ha, hb, ite_false, Prod.mk.injEq] at hab
      apply Prod.ext
      · exact hab.2.1
      · apply Prod.ext
        · omega
        · exact hab.2.2.2
  have hmap : Measurable
      (fun coins : Fin 2 × (Nat × (Nat × Nat)) → Bool =>
        ((fun index => coins (0, index)),
          (fun pair => coins (1, (component, pair))))) := by fun_prop
  have hcombine : Measurable
      (fun z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) =>
        fun tag : Nat × (Nat × Nat) =>
          if tag.1 = component then
            z.2 (newShift + tag.2.1, tag.2.2)
          else z.1 (tag.1, (oldShift + tag.2.1, tag.2.2))) := by
    apply Measurable.of_eval
    intro tag
    by_cases htag : tag.1 = component
    · simpa only [htag, ite_true, Function.comp_def] using
        (measurable_pi_apply (newShift + tag.2.1, tag.2.2)).comp
          measurable_snd
    · simpa only [htag, ite_false, Function.comp_def] using
        (measurable_pi_apply
          (tag.1, (oldShift + tag.2.1, tag.2.2))).comp measurable_fst
  calc
    (sourceLaw.prod fairCoinStreamLaw).map
        (fun z tag =>
          if tag.1 = component then
            z.2 (newShift + tag.2.1, tag.2.2)
          else z.1 (tag.1, (oldShift + tag.2.1, tag.2.2))) =
      (global.map (fun coins =>
        ((fun tag => coins (0, tag)),
          (fun pair => coins (1, (component, pair)))))).map
        (fun z tag =>
          if tag.1 = component then
            z.2 (newShift + tag.2.1, tag.2.2)
          else z.1 (tag.1, (oldShift + tag.2.1, tag.2.2))) := by
            rw [hpair]
    _ = global.map (fun coins tag => coins (index tag)) := by
      rw [Measure.map_map hcombine hmap]
      congr 1
      funext coins tag
      by_cases htag : tag.1 = component <;>
        simp [index, htag]
    _ = sourceLaw := by
      exact @Measure.map_infinitePi_infinitePi_of_inj
        (Fin 2 × (Nat × (Nat × Nat))) (Nat × (Nat × Nat))
        (fun _ => Bool) (fun _ => inferInstance)
        (fun _ => fairCoinLaw)
        (fun _ => fairCoinLaw_isProbabilityMeasure)
        index hinj

/-- A prefix may choose the component and both shifts. Conditional on that
prefix, independent old and new fair sources still combine into one fair
global tail, jointly independent of the prefix. -/
theorem combinedTail_conditional_product
    {α : Type*} [MeasurableSpace α] (preLaw : Measure α)
    (component oldShift newShift : α → Nat) :
    preLaw.bind (fun pre =>
      (((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw).map
        (fun z index =>
          if index.1 = component pre then
            z.2 (newShift pre + index.2.1, index.2.2)
          else
            z.1 (index.1,
              (oldShift pre + index.2.1, index.2.2)))).map
        (Prod.mk pre)) =
    preLaw.prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  haveI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  conv_rhs => rw [Measure.prod_eq_bind_map]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pre
  exact congrArg (fun law : Measure (Nat × (Nat × Nat) → Bool) =>
      law.map (Prod.mk pre))
    (combinedTail_fixedShift_law
      (component pre) (oldShift pre) (newShift pre))

end ttc
